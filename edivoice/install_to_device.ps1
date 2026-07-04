# Edivoice — Build & Install to connected Android device
# Run this from the edivoice/ directory in PowerShell:
#   Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
#   .\install_to_device.ps1

$ErrorActionPreference = "Stop"

Write-Host "=== Edivoice Install Script ===" -ForegroundColor Cyan

# ── Locate ADB ──────────────────────────────────────────────────────────────
$adb = $null
$candidates = @(
    "adb",
    "$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe",
    "$env:USERPROFILE\AppData\Local\Android\Sdk\platform-tools\adb.exe",
    "C:\Users\$env:USERNAME\AppData\Local\Android\Sdk\platform-tools\adb.exe",
    "${env:ProgramFiles(x86)}\Android\android-sdk\platform-tools\adb.exe",
    "$env:ProgramFiles\Android\Android Studio\platform-tools\adb.exe"
)
foreach ($c in $candidates) {
    if (Get-Command $c -ErrorAction SilentlyContinue) { $adb = $c; break }
    if (Test-Path $c) { $adb = $c; break }
}
if (-not $adb) {
    Write-Host "ADB not found. Installing via winget..." -ForegroundColor Yellow
    winget install Google.PlatformTools --accept-source-agreements --accept-package-agreements
    $adb = "$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe"
    if (-not (Test-Path $adb)) { $adb = "adb" }
}
Write-Host "ADB: $adb" -ForegroundColor Green

# ── Locate Java ─────────────────────────────────────────────────────────────
$javaHome = $env:JAVA_HOME
if (-not $javaHome) {
    # Try Android Studio's bundled JDK
    $studioJdk = Get-ChildItem "C:\Program Files\Android\Android Studio\jbr" -ErrorAction SilentlyContinue |
                 Select-Object -First 1 -ExpandProperty FullName
    if ($studioJdk) { $javaHome = $studioJdk }
}
if ($javaHome) {
    $env:JAVA_HOME = $javaHome
    $env:PATH = "$javaHome\bin;$env:PATH"
    Write-Host "JAVA_HOME: $javaHome" -ForegroundColor Green
} else {
    Write-Host "JAVA_HOME not set — using system java" -ForegroundColor Yellow
}

# ── Check device connected ───────────────────────────────────────────────────
Write-Host "`nChecking connected devices..." -ForegroundColor Cyan
$devices = & $adb devices 2>&1
Write-Host $devices

$deviceLine = ($devices -split "`n") | Where-Object { $_ -match "\tdevice$" }
if (-not $deviceLine) {
    Write-Host "`nERROR: No Android device found in 'adb devices'." -ForegroundColor Red
    Write-Host "Make sure USB debugging is ON and you tapped 'Allow' on the tablet." -ForegroundColor Yellow
    exit 1
}
Write-Host "Device found: $($deviceLine.Trim())" -ForegroundColor Green

# ── Build ────────────────────────────────────────────────────────────────────
Write-Host "`nBuilding debug APK..." -ForegroundColor Cyan
$script = Join-Path $PSScriptRoot "gradlew.bat"
& $script assembleDebug
if ($LASTEXITCODE -ne 0) {
    Write-Host "Build failed!" -ForegroundColor Red
    exit 1
}

# ── Install ──────────────────────────────────────────────────────────────────
$apk = Join-Path $PSScriptRoot "app\build\outputs\apk\debug\app-debug.apk"
if (-not (Test-Path $apk)) {
    Write-Host "APK not found at: $apk" -ForegroundColor Red
    exit 1
}

Write-Host "`nInstalling APK..." -ForegroundColor Cyan
& $adb install -r $apk
if ($LASTEXITCODE -ne 0) {
    Write-Host "Install failed!" -ForegroundColor Red
    exit 1
}

# ── Launch ───────────────────────────────────────────────────────────────────
Write-Host "`nLaunching app..." -ForegroundColor Cyan
& $adb shell am start -n "jp.gr.java_conf.sh.edivoice.debug/jp.gr.java_conf.sh.edivoice.MainActivity"

Write-Host "`n=== Done! Edivoice is running on your device ===" -ForegroundColor Green
Write-Host "`nTo watch Logcat:" -ForegroundColor Cyan
Write-Host "  $adb logcat -s Edivoice" -ForegroundColor White
