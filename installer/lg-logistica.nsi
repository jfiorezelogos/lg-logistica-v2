; lg-logistica.nsi — Instalador NSIS per-user (sem admin, onedir)
Unicode True
!include "MUI2.nsh"
!include "LogicLib.nsh"

!define APP_NAME        "lg-logistica"
!define APP_PUBLISHER   "Logos Editora"
!define APP_VERSION     "2.0.0"
!define COMPANY_DIR     "Logos Editora"

; Caminho ABSOLUTO para a pasta dist baseado na localização deste .nsi
!define DISTDIR "${__FILEDIR__}\..\dist\lg-logistica"

Name "${APP_NAME} ${APP_VERSION}"
OutFile "lg-logistica-${APP_VERSION}-setup.exe"

RequestExecutionLevel user
InstallDir "$LOCALAPPDATA\${COMPANY_DIR}\${APP_NAME}"

Function .onInit
  SetShellVarContext current
FunctionEnd

!define MUI_ABORTWARNING
!insertmacro MUI_PAGE_WELCOME
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_INSTFILES
!insertmacro MUI_PAGE_FINISH

!insertmacro MUI_UNPAGE_CONFIRM
!insertmacro MUI_UNPAGE_INSTFILES
!insertmacro MUI_LANGUAGE "PortugueseBR"

Section "Instalar" SEC01
  ; 1) Copia a pasta do PyInstaller (onedir) exatamente como está
  ;    Usando caminho absoluto robusto: ${DISTDIR}\*
  SetOutPath "$INSTDIR"
  File /r "${DISTDIR}\*"   ; copia tudo (pastas e arquivos)

  ; 2) Garante .env (ordem: já existe? dist\.env? dist\.env.example? cria básico)
  ${IfNot} ${FileExists} "$INSTDIR\.env"
    ${If} ${FileExists} "${DISTDIR}\.env"
      SetOutPath "$INSTDIR"
      File "${DISTDIR}\.env"
    ${ElseIf} ${FileExists} "${DISTDIR}\.env.example"
      File "/oname=$INSTDIR\.env" "${DISTDIR}\.env.example"
    ${Else}
      FileOpen $1 "$INSTDIR\.env" w
      FileWrite $1 "APP_ENV=prod$\r$\n"
      FileWrite $1 "API_KEY_GURU=$\r$\n"
      FileWrite $1 "SHOP_URL=$\r$\n"
      FileWrite $1 "SHOPIFY_TOKEN=$\r$\n"
      FileWrite $1 "FRETEBARATO_URL=$\r$\n"
      FileWrite $1 "OPENAI_API_KEY=$\r$\n"
      FileClose $1
    ${EndIf}
  ${EndIf}

  ; 3) Garante pasta Logs/ (se veio vazia e foi ignorada por algum passo)
  CreateDirectory "$INSTDIR\Logs"

  ; 4) Atalhos
  CreateDirectory "$SMPROGRAMS\${COMPANY_DIR}"
  ${If} ${FileExists} "$INSTDIR\assets\app.ico"
    CreateShortCut "$SMPROGRAMS\${COMPANY_DIR}\${APP_NAME}.lnk" "$INSTDIR\lg-logistica.exe" "" "$INSTDIR\assets\app.ico" 0
  ${Else}
    CreateShortCut "$SMPROGRAMS\${COMPANY_DIR}\${APP_NAME}.lnk" "$INSTDIR\lg-logistica.exe"
  ${EndIf}
  CreateShortCut "$SMPROGRAMS\${COMPANY_DIR}\Desinstalar ${APP_NAME}.lnk" "$INSTDIR\Uninstall.exe"

  ; 5) Registro
  WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "DisplayName"       "${APP_NAME}"
  WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "DisplayVersion"    "${APP_VERSION}"
  WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "Publisher"         "${APP_PUBLISHER}"
  WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "InstallLocation"   "$INSTDIR"
  ${If} ${FileExists} "$INSTDIR\assets\app.ico"
    WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "DisplayIcon"     "$INSTDIR\assets\app.ico"
  ${EndIf}
  WriteRegStr HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "UninstallString"   "$INSTDIR\Uninstall.exe"
  WriteRegDWORD HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "NoModify" 1
  WriteRegDWORD HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}" "NoRepair" 1

  ; 6) Desinstalador
  WriteUninstaller "$INSTDIR\Uninstall.exe"

  ; 7) Atalho de diagnóstico
    FileOpen $0 "$INSTDIR\run_debug.bat" w
    FileWrite $0 "@echo off$\r$\n"
    FileWrite $0 "set QT_DEBUG_PLUGINS=1$\r$\n"
    FileWrite $0 "$\"%~dp0lg-logistica.exe$\" 1>$\"%LOCALAPPDATA%\\Logos Editora\\lg-logistica\\run_out.txt$\" 2>$\"%LOCALAPPDATA%\\Logos Editora\\lg-logistica\\run_err.txt$\"$\r$\n"
    FileWrite $0 "echo. & echo === Pressione qualquer tecla para sair === & pause >nul$\r$\n"
    FileClose $0
    CreateShortCut "$SMPROGRAMS\${COMPANY_DIR}\${APP_NAME} (Diagnóstico).lnk" "$INSTDIR\run_debug.bat"
SectionEnd

Section "Uninstall"
  Delete "$SMPROGRAMS\${COMPANY_DIR}\${APP_NAME}.lnk"
  Delete "$SMPROGRAMS\${COMPANY_DIR}\Desinstalar ${APP_NAME}.lnk"
  RMDir  "$SMPROGRAMS\${COMPANY_DIR}"
  RMDir /r "$INSTDIR"
  DeleteRegKey HKCU "Software\Microsoft\Windows\CurrentVersion\Uninstall\${APP_NAME}"
SectionEnd
