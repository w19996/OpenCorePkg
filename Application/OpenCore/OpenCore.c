/** @file
  OpenCore driver.

Copyright (c) 2019, vit9696. All rights reserved.<BR>
This program and the accompanying materials
are licensed and made available under the terms and conditions of the BSD License
which accompanies this distribution.  The full text of the license may be found at
http://opensource.org/licenses/bsd-license.php

THE PROGRAM IS DISTRIBUTED UNDER THE BSD LICENSE ON AN "AS IS" BASIS,
WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.

**/

#include <Uefi.h>

#include <Guid/GlobalVariable.h>
#include <Guid/OcVariable.h>

#include <Protocol/DevicePath.h>
#include <Protocol/LoadedImage.h>
#include <Protocol/OcBootstrap.h>
#include <Protocol/SimpleFileSystem.h>
#include <Protocol/VMwareDebug.h>

#include <Library/OcMainLib.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/OcDebugLogLib.h>
#include <Library/DevicePathLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/OcAppleBootPolicyLib.h>
#include <Library/OcBootManagementLib.h>
#include <Library/OcConfigurationLib.h>
#include <Library/OcConsoleLib.h>
#include <Library/OcCpuLib.h>
#include <Library/OcDevicePathLib.h>
#include <Library/OcStorageLib.h>
#include <Library/OcVariableLib.h>
#include <Library/PrintLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiRuntimeServicesTableLib.h>
#include <Library/UefiDriverEntryPoint.h>
#include <Library/UefiLib.h>

#define OC_DEFAULT_BOOT_OPTION       0x80
#define OC_DEFAULT_BOOT_OPTION_NAME  L"Boot0080"

STATIC
OC_GLOBAL_CONFIG
  mOpenCoreConfiguration;

STATIC
OC_STORAGE_CONTEXT
  mOpenCoreStorage;

STATIC
OC_CPU_INFO
  mOpenCoreCpuInfo;

STATIC
UINT8
  mOpenCoreBooterHash[SHA1_DIGEST_SIZE];

STATIC
OC_RSA_PUBLIC_KEY *
  mOpenCoreVaultKey;

STATIC
OC_PRIVILEGE_CONTEXT
  mOpenCorePrivilege;

STATIC
BOOLEAN
  mOpenCoreAppleSupportLoaded;

STATIC
EFI_HANDLE
  mStorageHandle;

STATIC
EFI_DEVICE_PATH_PROTOCOL *
  mStoragePath;

STATIC
CHAR16 *
  mStorageRoot;

STATIC
EFI_DEVICE_PATH_PROTOCOL *
OcGetLoadOptionDevicePath (
  IN EFI_LOAD_OPTION  *LoadOption,
  IN UINTN            LoadOptionSize
  )
{
  UINTN  DescriptionSize;
  UINTN  DevicePathOffset;

  if (LoadOptionSize < sizeof (*LoadOption)) {
    return NULL;
  }

  DescriptionSize = StrSize ((CHAR16 *)(LoadOption + 1));
  DevicePathOffset = sizeof (*LoadOption) + DescriptionSize;

  if (  (DevicePathOffset > LoadOptionSize)
     || (LoadOption->FilePathListLength == 0)
     || (LoadOption->FilePathListLength > LoadOptionSize - DevicePathOffset))
  {
    return NULL;
  }

  return (EFI_DEVICE_PATH_PROTOCOL *)((UINT8 *)LoadOption + DevicePathOffset);
}

STATIC
BOOLEAN
OcFlavourHasApple (
  IN CONST CHAR8  *Flavour OPTIONAL
  )
{
  CONST CHAR8  *Token;
  CONST CHAR8  *End;
  UINTN        AppleLen;

  if (Flavour == NULL) {
    return FALSE;
  }

  AppleLen = AsciiStrLen (OC_FLAVOUR_APPLE_OS);
  Token    = Flavour;

  while (*Token != '\0') {
    End = Token;
    while ((*End != '\0') && (*End != ':')) {
      ++End;
    }

    if (  ((UINTN)(End - Token) == AppleLen)
       && (AsciiStrnCmp (Token, OC_FLAVOUR_APPLE_OS, AppleLen) == 0))
    {
      return TRUE;
    }

    Token = (*End == ':') ? End + 1 : End;
  }

  return FALSE;
}

STATIC
BOOLEAN
OcIsAppleBootEntry (
  IN OC_BOOT_ENTRY  *Chosen OPTIONAL
  )
{
  OC_BOOT_ENTRY_TYPE  DevicePathType;

  if (Chosen == NULL) {
    return FALSE;
  }

  if ((Chosen->Type & OC_BOOT_APPLE_ANY) != 0) {
    return TRUE;
  }

  if (Chosen->DevicePath != NULL) {
    DevicePathType = OcGetBootDevicePathType (Chosen->DevicePath, NULL, NULL);
    if ((DevicePathType & OC_BOOT_APPLE_ANY) != 0) {
      return TRUE;
    }
  }

  return OcFlavourHasApple (Chosen->Flavour);
}

STATIC
BOOLEAN
OcSameDevicePath (
  IN EFI_DEVICE_PATH_PROTOCOL  *First,
  IN EFI_DEVICE_PATH_PROTOCOL  *Second
  )
{
  UINTN  FirstSize;
  UINTN  SecondSize;

  FirstSize  = GetDevicePathSize (First);
  SecondSize = GetDevicePathSize (Second);

  return (FirstSize == SecondSize) && (CompareMem (First, Second, FirstSize) == 0);
}

STATIC
EFI_STATUS
OcRemoveBootOrderEntry (
  IN UINT16  BootOption
  )
{
  EFI_STATUS  Status;
  UINT16      *BootOrder;
  UINTN       BootOrderSize;
  UINTN       Index;
  UINTN       NewCount;

  Status = GetVariable2 (
             EFI_BOOT_ORDER_VARIABLE_NAME,
             &gEfiGlobalVariableGuid,
             (VOID **)&BootOrder,
             &BootOrderSize
             );
  if (EFI_ERROR (Status) || (BootOrderSize < sizeof (*BootOrder)) || (BootOrderSize % sizeof (*BootOrder) != 0)) {
    return Status;
  }

  NewCount = 0;
  for (Index = 0; Index < BootOrderSize / sizeof (*BootOrder); ++Index) {
    if (BootOrder[Index] != BootOption) {
      BootOrder[NewCount++] = BootOrder[Index];
    }
  }

  if (NewCount == BootOrderSize / sizeof (*BootOrder)) {
    FreePool (BootOrder);
    return EFI_NOT_FOUND;
  }

  Status = gRT->SetVariable (
                  EFI_BOOT_ORDER_VARIABLE_NAME,
                  &gEfiGlobalVariableGuid,
                  EFI_VARIABLE_BOOTSERVICE_ACCESS
                  | EFI_VARIABLE_RUNTIME_ACCESS
                  | EFI_VARIABLE_NON_VOLATILE,
                  NewCount * sizeof (*BootOrder),
                  BootOrder
                  );

  FreePool (BootOrder);
  return Status;
}

STATIC
EFI_STATUS
OcRemoveGeneratedDefaultBootEntry (
  IN OC_BOOT_ENTRY  *Chosen
  )
{
  EFI_STATUS                Status;
  EFI_LOAD_OPTION           *LoadOption;
  EFI_DEVICE_PATH_PROTOCOL  *LoadOptionPath;
  UINTN                     LoadOptionSize;

  if ((Chosen == NULL) || (Chosen->DevicePath == NULL) || OcIsAppleBootEntry (Chosen)) {
    return EFI_UNSUPPORTED;
  }

  Status = GetVariable2 (
             OC_DEFAULT_BOOT_OPTION_NAME,
             &gEfiGlobalVariableGuid,
             (VOID **)&LoadOption,
             &LoadOptionSize
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  LoadOptionPath = OcGetLoadOptionDevicePath (LoadOption, LoadOptionSize);
  if ((LoadOptionPath == NULL) || !OcSameDevicePath (LoadOptionPath, Chosen->DevicePath)) {
    FreePool (LoadOption);
    return EFI_NOT_FOUND;
  }

  FreePool (LoadOption);

  Status = gRT->SetVariable (
                  OC_DEFAULT_BOOT_OPTION_NAME,
                  &gEfiGlobalVariableGuid,
                  0,
                  0,
                  NULL
                  );
  DEBUG ((DEBUG_INFO, "OC: Removing generated default boot option %s - %r\n", OC_DEFAULT_BOOT_OPTION_NAME, Status));

  OcRemoveBootOrderEntry (OC_DEFAULT_BOOT_OPTION);

  return EFI_SUCCESS;
}

STATIC
VOID
OcLoadAppleSupport (
  IN OC_BOOT_ENTRY  *Chosen OPTIONAL
  )
{
  if (mOpenCoreAppleSupportLoaded) {
    return;
  }

  if (  mOpenCoreConfiguration.Misc.Security.ApplyAppleSupportOnly
     && !OcIsAppleBootEntry (Chosen))
  {
    DEBUG ((DEBUG_INFO, "OC: Skipping Apple support for non-Apple boot entry\n"));
    return;
  }

  mOpenCoreAppleSupportLoaded = TRUE;

  DEBUG ((DEBUG_INFO, "OC: OcLoadNvramSupport...\n"));
  OcLoadNvramSupport (&mOpenCoreStorage, &mOpenCoreConfiguration);
  DEBUG ((DEBUG_INFO, "OC: OcLoadAcpiSupport...\n"));
  OcLoadAcpiSupport (&mOpenCoreStorage, &mOpenCoreConfiguration);
  DEBUG ((DEBUG_INFO, "OC: OcLoadPlatformSupport...\n"));
  OcLoadPlatformSupport (&mOpenCoreConfiguration, &mOpenCoreCpuInfo);
  DEBUG ((DEBUG_INFO, "OC: OcLoadDevPropsSupport...\n"));
  OcLoadDevPropsSupport (&mOpenCoreConfiguration);
  DEBUG ((DEBUG_INFO, "OC: OcMiscLateInit...\n"));
  OcMiscLateInit (&mOpenCoreStorage, &mOpenCoreConfiguration);
  DEBUG ((DEBUG_INFO, "OC: OcLoadKernelSupport...\n"));
  OcLoadKernelSupport (&mOpenCoreStorage, &mOpenCoreConfiguration, &mOpenCoreCpuInfo);
}

STATIC
EFI_STATUS
EFIAPI
OcStartImage (
  IN  OC_BOOT_ENTRY  *Chosen,
  IN  EFI_HANDLE     ImageHandle,
  OUT UINTN          *ExitDataSize,
  OUT CHAR16         **ExitData    OPTIONAL,
  IN  BOOLEAN        LaunchInText
  )
{
  EFI_STATUS                       Status;
  EFI_CONSOLE_CONTROL_SCREEN_MODE  OldMode;

  if (mOpenCoreConfiguration.Misc.Security.ApplyAppleSupportOnly) {
    OcRemoveGeneratedDefaultBootEntry (Chosen);
  }

  OcLoadAppleSupport (Chosen);

  OldMode = OcConsoleControlSetMode (
              LaunchInText ? EfiConsoleControlScreenText : EfiConsoleControlScreenGraphics
              );

  Status = gBS->StartImage (
                  ImageHandle,
                  ExitDataSize,
                  ExitData
                  );

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Boot failed - %r\n", Status));
  }

  OcConsoleControlSetMode (OldMode);

  return Status;
}

STATIC
VOID
OcMain (
  IN OC_STORAGE_CONTEXT        *Storage,
  IN EFI_DEVICE_PATH_PROTOCOL  *LoadPath
  )
{
  EFI_STATUS            Status;
  OC_PRIVILEGE_CONTEXT  *Privilege;

  DEBUG ((DEBUG_INFO, "OC: OcMiscEarlyInit...\n"));
  Status = OcMiscEarlyInit (
             Storage,
             &mOpenCoreConfiguration,
             mOpenCoreVaultKey
             );

  if (EFI_ERROR (Status)) {
    return;
  }

  OcCpuScanProcessor (&mOpenCoreCpuInfo);

  DEBUG ((DEBUG_INFO, "OC: OcMiscMiddleInit...\n"));
  OcMiscMiddleInit (
    Storage,
    &mOpenCoreConfiguration,
    mStorageRoot,
    LoadPath,
    mStorageHandle,
    mOpenCoreConfiguration.Booter.Quirks.ForceBooterSignature ? mOpenCoreBooterHash : NULL
    );
  DEBUG ((DEBUG_INFO, "OC: OcLoadUefiSupport...\n"));
  OcLoadUefiSupport (Storage, &mOpenCoreConfiguration, &mOpenCoreCpuInfo, mOpenCoreBooterHash);
  DEBUG_CODE_BEGIN ();
  DEBUG ((DEBUG_INFO, "OC: OcMiscLoadSystemReport...\n"));
  OcMiscLoadSystemReport (&mOpenCoreConfiguration, mStorageHandle);
  DEBUG_CODE_END ();

  if (mOpenCoreConfiguration.Misc.Security.ApplyAppleSupportOnly) {
    DEBUG ((DEBUG_INFO, "OC: Deferring Apple support until Apple boot entry starts\n"));
  } else {
    OcLoadAppleSupport (NULL);
  }

  if (mOpenCoreConfiguration.Misc.Security.EnablePassword) {
    mOpenCorePrivilege.CurrentLevel = OcPrivilegeUnauthorized;
    mOpenCorePrivilege.Hash         = mOpenCoreConfiguration.Misc.Security.PasswordHash;
    mOpenCorePrivilege.Salt         = OC_BLOB_GET (&mOpenCoreConfiguration.Misc.Security.PasswordSalt);
    mOpenCorePrivilege.SaltSize     = mOpenCoreConfiguration.Misc.Security.PasswordSalt.Size;

    Privilege = &mOpenCorePrivilege;
  } else {
    Privilege = NULL;
  }

  DEBUG ((DEBUG_INFO, "OC: All green, starting boot management...\n"));

  OcMiscBoot (
    &mOpenCoreStorage,
    &mOpenCoreConfiguration,
    Privilege,
    OcStartImage,
    mOpenCoreConfiguration.Uefi.Quirks.RequestBootVarRouting,
    mStorageHandle
    );
}

STATIC
EFI_STATUS
OcBootstrap (
  IN EFI_HANDLE                       DeviceHandle,
  IN EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *FileSystem,
  IN EFI_DEVICE_PATH_PROTOCOL         *LoadPath
  )
{
  EFI_STATUS                Status;
  EFI_DEVICE_PATH_PROTOCOL  *RemainingPath;
  UINTN                     StoragePathSize;

  mOpenCoreVaultKey = OcGetVaultKey ();
  mStorageHandle    = DeviceHandle;

  //
  // Calculate root path (never freed).
  //
  RemainingPath = NULL;
  mStorageRoot  = OcCopyDevicePathFullName (LoadPath, &RemainingPath);
  //
  // Skipping this or later failing to call UnicodeGetParentDirectory means
  // we got valid path to the root of the partition. This happens when
  // OpenCore.efi was loaded from e.g. firmware and then bootstrapped
  // on a different partition.
  //
  if (mStorageRoot == NULL) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to get launcher path\n"));
    return EFI_UNSUPPORTED;
  }

  DEBUG ((DEBUG_INFO, "OC: Storage root %s\n", mStorageRoot));

  ASSERT (RemainingPath != NULL);

  if (!UnicodeGetParentDirectory (mStorageRoot)) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to get launcher root path\n"));
    FreePool (mStorageRoot);
    return EFI_UNSUPPORTED;
  }

  StoragePathSize = (UINTN)RemainingPath - (UINTN)LoadPath;
  mStoragePath    = AllocatePool (StoragePathSize + END_DEVICE_PATH_LENGTH);
  if (mStoragePath == NULL) {
    FreePool (mStorageRoot);
    return EFI_OUT_OF_RESOURCES;
  }

  CopyMem (mStoragePath, LoadPath, StoragePathSize);
  SetDevicePathEndNode ((UINT8 *)mStoragePath + StoragePathSize);

  Status = OcStorageInitFromFs (
             &mOpenCoreStorage,
             FileSystem,
             mStorageHandle,
             mStoragePath,
             mStorageRoot,
             mOpenCoreVaultKey
             );

  if (!EFI_ERROR (Status)) {
    OcMain (&mOpenCoreStorage, LoadPath);
    OcStorageFree (&mOpenCoreStorage);
  } else {
    DEBUG ((DEBUG_ERROR, "OC: Failed to open root FS - %r!\n", Status));
    if (Status == EFI_SECURITY_VIOLATION) {
      CpuDeadLoop (); ///< Should not return.
    }
  }

  return Status;
}

STATIC
EFI_HANDLE
EFIAPI
OcGetLoadHandle (
  IN OC_BOOTSTRAP_PROTOCOL  *This
  )
{
  return mStorageHandle;
}

STATIC
OC_BOOTSTRAP_PROTOCOL
  mOpenCoreBootStrap = {
  .Revision      = OC_BOOTSTRAP_PROTOCOL_REVISION,
  .GetLoadHandle = OcGetLoadHandle,
};

EFI_STATUS
EFIAPI
UefiMain (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  EFI_STATUS                       Status;
  EFI_LOADED_IMAGE_PROTOCOL        *LoadedImage;
  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *FileSystem;
  EFI_HANDLE                       BootstrapHandle;
  OC_BOOTSTRAP_PROTOCOL            *Bootstrap;
  EFI_DEVICE_PATH_PROTOCOL         *AbsPath;

  DEBUG ((DEBUG_INFO, "OC: Starting OpenCore...\n"));

  //
  // We have just started by bootstrap or manually at EFI/OC/OpenCore.efi.
  // When bootstrap runs us, we only install the protocol.
  // Otherwise we do self start.
  //

  Bootstrap = NULL;
  Status    = gBS->LocateProtocol (
                     &gOcBootstrapProtocolGuid,
                     NULL,
                     (VOID **)&Bootstrap
                     );

  if (!EFI_ERROR (Status)) {
    DEBUG ((DEBUG_INFO, "OC: Found previous image, aborting\n"));
    return EFI_ALREADY_STARTED;
  }

  LoadedImage = NULL;
  Status      = gBS->HandleProtocol (
                       ImageHandle,
                       &gEfiLoadedImageProtocolGuid,
                       (VOID **)&LoadedImage
                       );

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to locate loaded image - %r\n", Status));
    return EFI_NOT_FOUND;
  }

  if (LoadedImage->DeviceHandle == NULL) {
    DEBUG ((DEBUG_INFO, "OC: Missing boot device\n"));
    //
    // This is not critical as boot path may be complete.
    //
  }

  if (LoadedImage->FilePath == NULL) {
    DEBUG ((DEBUG_ERROR, "OC: Missing boot path\n"));
    return EFI_INVALID_PARAMETER;
  }

  DebugPrintDevicePath (DEBUG_INFO, "OC: Booter path", LoadedImage->FilePath);

  //
  // Obtain the file system device path
  //
  FileSystem = OcLocateFileSystem (
                 LoadedImage->DeviceHandle,
                 LoadedImage->FilePath
                 );
  if (FileSystem == NULL) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to locate file system\n"));
    return EFI_INVALID_PARAMETER;
  }

  AbsPath = AbsoluteDevicePath (LoadedImage->DeviceHandle, LoadedImage->FilePath);
  if (AbsPath == NULL) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to allocate absolute path\n"));
    return EFI_OUT_OF_RESOURCES;
  }

  DebugPrintDevicePath (DEBUG_INFO, "OC: Absolute booter path", LoadedImage->FilePath);

  BootstrapHandle = NULL;
  Status          = gBS->InstallMultipleProtocolInterfaces (
                           &BootstrapHandle,
                           &gOcBootstrapProtocolGuid,
                           &mOpenCoreBootStrap,
                           NULL
                           );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "OC: Failed to install bootstrap protocol - %r\n", Status));
    FreePool (AbsPath);
    return Status;
  }

  OcBootstrap (LoadedImage->DeviceHandle, FileSystem, AbsPath);
  DEBUG ((DEBUG_ERROR, "OC: Failed to boot\n"));
  CpuDeadLoop ();

  return EFI_SUCCESS;
}
