/*
 * SPDX-FileCopyrightText: This file has no copyright assigned and is placed in the Public Domain.
 * SPDX-License-Identifier: CC0-1.0
 *
 * This file is part of the w64 mingw-runtime package.
 * No warranty is given; refer to https://github.com/kinke/mingw-w64-crt/blob/master/DISCLAIMER.PD.
 *
 * Additional code derived from the windows-rs repository on GitHub
 * (https://github.com/microsoft/windows-rs) with the MIT license:
 *
 * MIT License
 *
 * Copyright (c) Microsoft Corporation.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE
 */

typedef interface IPackageManager IPackageManager;
typedef interface IPackage IPackage;
typedef interface IPackageId IPackageId;
typedef interface IPackageVersion IPackageVersion;
typedef interface IPackage2 IPackage2;

DEFINE_GUID(IID_IPackageManager, 0x9A7D4B65, 0x5E8F, 0x4FC7, 0xA2, 0xE5, 0x7F, 0x69, 0x25, 0xCB, 0x8B, 0x53);
DEFINE_GUID(IID_IPackage, 0x163C792F, 0xBD75, 0x413C, 0xBF, 0x23, 0xB1, 0xFE, 0x7B, 0x95, 0xD8, 0x25);
DEFINE_GUID(IID_IPackage2, 0xA6612fb6, 0x7688, 0x4ACE, 0x95, 0xFB, 0x35, 0x95, 0x38, 0xE7, 0xAA, 0x01);

/* IPackageManager */
typedef struct IPackageManagerVtbl {
  BEGIN_INTERFACE

  /*** IUnknown methods ***/
  HRESULT (STDMETHODCALLTYPE *QueryInterface)(
    IPackageManager *This,
    REFIID riid,
    void **ppvObject);

  ULONG (STDMETHODCALLTYPE *AddRef)(
    IPackageManager *This);

  ULONG (STDMETHODCALLTYPE *Release)(
    IPackageManager *This);

  /*** IInspectable methods ***/
  HRESULT (STDMETHODCALLTYPE *GetIids)(
    IPackageManager *This,
    UINT32 *count,
    IID **ids);

  HRESULT (STDMETHODCALLTYPE *GetRuntimeClassName)(
    IPackageManager *This,
    HSTRING *className);

  HRESULT (STDMETHODCALLTYPE *GetTrustLevel)(
    IPackageManager *This,
    TrustLevel *trustLevel);

  /*** IPackageManager methods ***/
  HRESULT (STDMETHODCALLTYPE *stub_AddPackageAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_UpdatePackageAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_RemovePackageAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_StagePackageAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_RegisterPackageAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *FindPackages)(
    IPackageManager *This,
    IIterable **retval);

  HRESULT (STDMETHODCALLTYPE *FindPackagesByUserSecurityId)(
    IPackageManager *This,
    HSTRING userSecurityId,
    IIterable **retval);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackagesByNamePublisher)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackagesByUserSecurityIdNamePublisher)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindUsers)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_SetPackageState)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackageByPackageFullName)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_CleanupPackageForUserAsync)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackagesByPackageFamilyName)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackagesByUserSecurityIdPackageFamilyName)(
    IPackageManager *This);

  HRESULT (STDMETHODCALLTYPE *stub_FindPackageByUserSecurityIdPackageFullName)(
    IPackageManager *This);

  END_INTERFACE
} IPackageManagerVtbl;

interface IPackageManager {
  CONST_VTBL IPackageManagerVtbl* lpVtbl;
};

/*** IUnknown methods ***/
#define IPackageManager_QueryInterface(This,riid,ppvObject) (This)->lpVtbl->QueryInterface(This,riid,ppvObject)
#define IPackageManager_AddRef(This) (This)->lpVtbl->AddRef(This)
#define IPackageManager_Release(This) (This)->lpVtbl->Release(This)
/*** IInspectable methods ***/
#define IPackageManager_GetIids(This,count,ids) (This)->lpVtbl->GetIids(This,count,ids)
#define IPackageManager_GetRuntimeClassName(This,name) (This)->lpVtbl->GetRuntimeClassName(This,name)
#define IPackageManager_GetTrustLevel(This,level) (This)->lpVtbl->GetTrustLevel(This,level)
/*** IPackageManager methods ***/
#define IPackageManager_FindPackages(This,retval) (This)->lpVtbl->FindPackages(This,retval)
#define IPackageManager_FindPackagesByUserSecurityId(This,userSecurityId,retval) (This)->lpVtbl->FindPackagesByUserSecurityId(This,userSecurityId,retval)

/* IPackageId */
typedef struct IPackageIdVtbl {
  BEGIN_INTERFACE

  /*** IUnknown methods ***/
  HRESULT (STDMETHODCALLTYPE *QueryInterface)(
    IPackageId *This,
    REFIID riid,
    void **ppvObject);

  ULONG (STDMETHODCALLTYPE *AddRef)(
    IPackageId *This);

  ULONG (STDMETHODCALLTYPE *Release)(
    IPackageId *This);

  /*** IInspectable methods ***/
  HRESULT (STDMETHODCALLTYPE *GetIids)(
    IPackageId *This,
    UINT32 *count,
    IID **ids);

  HRESULT (STDMETHODCALLTYPE *GetRuntimeClassName)(
    IPackageId *This,
    HSTRING *className);

  HRESULT (STDMETHODCALLTYPE *GetTrustLevel)(
    IPackageId *This,
    TrustLevel *trustLevel);

  /*** IPackageId methods ***/
  HRESULT (STDMETHODCALLTYPE *get_Name)(
    IPackageId *This,
    HSTRING *value);

  HRESULT (STDMETHODCALLTYPE *get_Version)(
    IPackageId *This,
    IPackageVersion *value);

  HRESULT (STDMETHODCALLTYPE *get_Architecture)(
    IPackageId *This,
    IProcessorArchitecture *value);

  HRESULT (STDMETHODCALLTYPE *get_ResourceId)(
    IPackageId *This,
    HSTRING *value);

  HRESULT (STDMETHODCALLTYPE *get_Publisher)(
    IPackageId *This,
    HSTRING *value);

  HRESULT (STDMETHODCALLTYPE *get_PublisherId)(
    IPackageId *This,
    HSTRING *value);

  HRESULT (STDMETHODCALLTYPE *get_FullName)(
    IPackageId *This,
    HSTRING *value);

  HRESULT (STDMETHODCALLTYPE *get_FamilyName)(
    IPackageId *This,
    HSTRING *value);

  END_INTERFACE
} IPackageIdVtbl;

interface IPackageId {
  CONST_VTBL IPackageIdVtbl* lpVtbl;
};

/*** IUnknown methods ***/
#define IPackageId_QueryInterface(This,riid,ppvObject) (This)->lpVtbl->QueryInterface(This,riid,ppvObject)
#define IPackageId_AddRef(This) (This)->lpVtbl->AddRef(This)
#define IPackageId_Release(This) (This)->lpVtbl->Release(This)
/*** IInspectable methods ***/
#define IPackageId_GetIids(This,count,ids) (This)->lpVtbl->GetIids(This,count,ids)
#define IPackageId_GetRuntimeClassName(This,name) (This)->lpVtbl->GetRuntimeClassName(This,name)
#define IPackageId_GetTrustLevel(This,level) (This)->lpVtbl->GetTrustLevel(This,level)
/*** IPackageId methods ***/
#define IPackageId_get_Name(This,value) (This)->lpVtbl->get_Name(This,value)
#define IPackageId_get_Version(This,value) (This)->lpVtbl->get_Version(This,value)
#define IPackageId_get_Architecture(This,value) (This)->lpVtbl->get_Architecture(This,value)
#define IPackageId_get_ResourceId(This,value) (This)->lpVtbl->get_ResourceId(This,value)
#define IPackageId_get_Publisher(This,value) (This)->lpVtbl->get_Publisher(This,value)
#define IPackageId_get_PublisherId(This,value) (This)->lpVtbl->get_PublisherId(This,value)
#define IPackageId_get_FullName(This,value) (This)->lpVtbl->get_FullName(This,value)
#define IPackageId_get_FamilyName(This,value) (This)->lpVtbl->get_FamilyName(This,value)

/* IPackage */
typedef struct IPackageVtbl {
  BEGIN_INTERFACE

  /*** IUnknown methods ***/
  HRESULT (STDMETHODCALLTYPE *QueryInterface)(
    IPackage *This,
    REFIID riid,
    void **ppvObject);

  ULONG (STDMETHODCALLTYPE *AddRef)(
    IPackage *This);

  ULONG (STDMETHODCALLTYPE *Release)(
    IPackage *This);

  /*** IInspectable methods ***/
  HRESULT (STDMETHODCALLTYPE *GetIids)(
    IPackage *This,
    UINT32 *count,
    IID **ids);

  HRESULT (STDMETHODCALLTYPE *GetRuntimeClassName)(
    IPackage *This,
    HSTRING *className);

  HRESULT (STDMETHODCALLTYPE *GetTrustLevel)(
    IPackage *This,
    TrustLevel *trustLevel);

  /*** IPackage methods ***/
  HRESULT (STDMETHODCALLTYPE *get_Id)(
    IPackage *This,
    IPackageId **value);

  HRESULT (STDMETHODCALLTYPE *get_InstalledLocation)(
    IPackage *This,
    IUnknown **value);

  HRESULT (STDMETHODCALLTYPE *get_IsFramework)(
    IPackage *This,
    CHAR *value);

  HRESULT (STDMETHODCALLTYPE *get_Dependencies)(
    IPackage *This,
    void **value);

  END_INTERFACE
} IPackageVtbl;

interface IPackage {
  CONST_VTBL IPackageVtbl* lpVtbl;
};

/*** IUnknown methods ***/
#define IPackage_QueryInterface(This,riid,ppvObject) (This)->lpVtbl->QueryInterface(This,riid,ppvObject)
#define IPackage_AddRef(This) (This)->lpVtbl->AddRef(This)
#define IPackage_Release(This) (This)->lpVtbl->Release(This)
/*** IInspectable methods ***/
#define IPackage_GetIids(This,count,ids) (This)->lpVtbl->GetIids(This,count,ids)
#define IPackage_GetRuntimeClassName(This,name) (This)->lpVtbl->GetRuntimeClassName(This,name)
#define IPackage_GetTrustLevel(This,level) (This)->lpVtbl->GetTrustLevel(This,level)
/*** IPackage methods ***/
#define IPackage_get_Id(This,value) (This)->lpVtbl->get_Id(This,value)
#define IPackage_get_InstalledLocation(This,value) (This)->lpVtbl->get_InstalledLocation(This,value)
#define IPackage_get_IsFramework(This,value) (This)->lpVtbl->get_IsFramework(This,value)
#define IPackage_get_Dependencies(This,value) (This)->lpVtbl->get_Dependencies(This,value)

/* IPackage2 */
typedef struct IPackage2Vtbl {
  BEGIN_INTERFACE

  /*** IUnknown methods ***/
  HRESULT (STDMETHODCALLTYPE *QueryInterface)(
    IPackage2  *This,
    REFIID      riid,
    void      **ppvObject);

  ULONG (STDMETHODCALLTYPE *AddRef)(
    IPackage2  *This);

  ULONG (STDMETHODCALLTYPE *Release)(
    IPackage2  *This);

  /*** IInspectable methods ***/
  HRESULT (STDMETHODCALLTYPE *GetIids)(
    IPackage2  *This,
    UINT32     *count,
    IID       **ids);

  HRESULT (STDMETHODCALLTYPE *GetRuntimeClassName)(
    IPackage2  *This,
    HSTRING    *className);

  HRESULT (STDMETHODCALLTYPE *GetTrustLevel)(
    IPackage2  *This,
    TrustLevel *trustLevel);

  /*** IPackage2 methods ***/
  HRESULT (STDMETHODCALLTYPE *get_DisplayName)(
    IPackage2  *This,
    HSTRING    *value);

  HRESULT (STDMETHODCALLTYPE *get_PublisherDisplayName)(
    IPackage2  *This,
    HSTRING    *value);

  HRESULT (STDMETHODCALLTYPE *get_Description)(
    IPackage2  *This,
    HSTRING    *value);

  HRESULT (STDMETHODCALLTYPE *get_Logo)(
    IPackage2  *This,
    void      **value);

  HRESULT (STDMETHODCALLTYPE *get_IsResourcePackage)(
    IPackage2  *This,
    UCHAR      *value);

  HRESULT (STDMETHODCALLTYPE *get_IsBundle)(
    IPackage2  *This,
    UCHAR      *value);

  HRESULT (STDMETHODCALLTYPE *get_IsDevelopmentMode)(
    IPackage2  *This,
    UCHAR      *value);

  END_INTERFACE
} IPackage2Vtbl;

interface IPackage2 {
  CONST_VTBL IPackage2Vtbl* lpVtbl;
};

/*** IUnknown methods ***/
#define IPackage2_QueryInterface(This,riid,ppvObject) (This)->lpVtbl->QueryInterface(This,riid,ppvObject)
#define IPackage2_AddRef(This) (This)->lpVtbl->AddRef(This)
#define IPackage2_Release(This) (This)->lpVtbl->Release(This)
/*** IInspectable methods ***/
#define IPackage2_GetIids(This,count,ids) (This)->lpVtbl->GetIids(This,count,ids)
#define IPackage2_GetRuntimeClassName(This,name) (This)->lpVtbl->GetRuntimeClassName(This,name)
#define IPackage2_GetTrustLevel(This,level) (This)->lpVtbl->GetTrustLevel(This,level)
/*** IPackage2 methods ***/
#define IPackage2_get_DisplayName(This,value) (This)->lpVtbl->get_DisplayName(This,value)
#define IPackage2_get_PublisherDisplayName(This,value) (This)->lpVtbl->get_PublisherDisplayName(This,value)
#define IPackage2_get_Description(This,value) (This)->lpVtbl->get_Description(This,value)
#define IPackage2_get_Logo(This,value) (This)->lpVtbl->get_Logo(This,value)
#define IPackage2_get_IsResourcePackage(This,value) (This)->lpVtbl->get_IsResourcePackage(This,value)
#define IPackage2_get_IsBundle(This,value) (This)->lpVtbl->get_IsBundle(This,value)
#define IPackage2_get_IsDevelopmentMode(This,value) (This)->lpVtbl->get_IsDevelopmentMode(This,value)
