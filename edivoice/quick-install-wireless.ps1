# Edivoice — Wireless ADB install script
# Usage:
#   .\quick-install-wireless.ps1                          # auto-discover device
#   .\quick-install-wireless.ps1 -ApkPath .\app-debug.apk
#   .\quick-install-wireless.ps1 -Host 192.168.0.140
#   .\quick-install-wireless.ps1 -GitHubToken ghp_xxx     # auto-download latest
#
# Run with:
#   Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
#   .\quick-install-wireless.ps1

param(
    [string]$Host      = "192.168.0.140",
    [int]   $Port      = 5555,
    [string]$ApkPath   = "",
    [string]$GitHubToken = $env:GITHUB_TOKEN,
    [switch]$SkipLaunch
)

$ErrorActionPreference = "Stop"
$REPO   = "ussycat/python"
$PKG    = "jp.gr.java_conf.sh.edivoice.debug"
$ACT    = "jp.gr.java_conf.sh.edivoice.MainActivity"

Write-Host "=== Edivoice Wireless Install ===" -ForegroundColor Cyan

# ── Locate ADB ───────────────────────────────────────────────────────────────
$adb = $null
foreach ($c in @(
    "adb",
    "$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe",
    "$env:USERPROFILE\AppData\Local\Android\Sdk\platform-tools\adb.exe",
    "C:\Users\$env:USERNAME\AppData\Local\Android\Sdk\platform-tools\adb.exe"
)) {
    if (Get-Command $c -ErrorAction SilentlyContinue) { $adb = $c; break }
    if ($c -ne "adb" -and (Test-Path $c))             { $adb = $c; break }
}
if (-not $adb) {
    Write-Host "ADB not found. Install Android Platform-Tools first." -ForegroundColor Red
    exit 1
}
Write-Host "ADB: $adb" -ForegroundColor Green

# ── Download APK if not supplied ─────────────────────────────────────────────
if (-not $ApkPath) {
    if ($GitHubToken) {
        Write-Host "`nDownloading latest APK artifact from GitHub..." -ForegroundColor Cyan
        $headers = @{ Authorization = "Bearer $GitHubToken"; Accept = "application/vnd.github+json" }

        # Find the most recent successful run on the branch
        $runs = Invoke-RestMethod -Uri "https://api.github.com/repos/$REPO/actions/workflows/build.yml/runs?branch=claude/android-latest-compatibility-ilsfxz&status=success&per_page=1" -Headers $headers
        $runId = $runs.workflow_runs[0].id
        Write-Host "Latest successful run: $runId"

        $arts = Invoke-RestMethod -Uri "https://api.github.com/repos/$REPO/actions/runs/$runId/artifacts" -Headers $headers
        $art  = $arts.artifacts | Where-Object { $_.name -like "edivoice-debug-*" } | Select-Object -First 1
        if (-not $art) { Write-Host "No APK artifact found." -ForegroundColor Red; exit 1 }

        Write-Host "Artifact: $($art.name) ($([math]::Round($art.size_in_bytes/1MB,1)) MB)"
        $zipPath = "$env:TEMP\edivoice-artifact.zip"
        Invoke-RestMethod -Uri $art.archive_download_url -Headers $headers -OutFile $zipPath

        $extractDir = "$env:TEMP\edivoice-apk"
        if (Test-Path $extractDir) { Remove-Item $extractDir -Recurse -Force }
        Expand-Archive $zipPath $extractDir
        $ApkPath = Get-ChildItem $extractDir -Filter "*.apk" -Recurse | Select-Object -First 1 -ExpandProperty FullName
        Write-Host "APK extracted: $ApkPath" -ForegroundColor Green
    } else {
        Write-Host "`nNo APK found. Options:" -ForegroundColor Yellow
        Write-Host "  1. Download from https://github.com/$REPO/actions/runs/28704127306"
        Write-Host "     then run: .\quick-install-wireless.ps1 -ApkPath <path>\app-debug.apk"
        Write-Host "  2. Provide a GitHub token:"
        Write-Host "     .\quick-install-wireless.ps1 -GitHubToken ghp_XXXX"
        Write-Host "  3. Set env var:  `$env:GITHUB_TOKEN = 'ghp_XXXX'"
        exit 1
    }
}

if (-not (Test-Path $ApkPath)) {
    Write-Host "APK not found: $ApkPath" -ForegroundColor Red; exit 1
}
Write-Host "APK: $ApkPath ($([math]::Round((Get-Item $ApkPath).Length/1MB,1)) MB)"

# ── Connect wireless ADB ─────────────────────────────────────────────────────
Write-Host "`nConnecting to ${Host}:${Port}..." -ForegroundColor Cyan
& $adb connect "${Host}:${Port}" 2>&1 | Write-Host
Start-Sleep -Seconds 2

$devLine = (& $adb devices 2>&1) -split "`n" | Where-Object { $_ -match "\tdevice$" }
if (-not $devLine) {
    Write-Host "`nDevice not found. Trying nearby IPs..." -ForegroundColor Yellow
    $subnet = ($Host -replace "\.\d+$", "")
    $found  = $false
    170..180 | ForEach-Object {
        $ip = "${subnet}.$_"
        $result = & $adb connect "${ip}:${Port}" 2>&1
        if ($result -match "connected") {
            Write-Host "Connected: $ip" -ForegroundColor Green
            $Host  = $ip
            $found = $true
        }
    }
    if (-not $found) {
        Write-Host "No device found. Make sure:" -ForegroundColor Red
        Write-Host "  - Tablet WiFi is ON and on same network"
        Write-Host "  - USB debugging / wireless debugging is enabled on tablet"
        Write-Host "  - Pair via: adb pair <ip>:<pair-port>  (Android 11+)"
        exit 1
    }
}
Write-Host "Device: $($devLine.Trim())" -ForegroundColor Green

# ── Install ───────────────────────────────────────────────────────────────────
Write-Host "`nInstalling APK..." -ForegroundColor Cyan
$result = & $adb install -r $ApkPath 2>&1
Write-Host $result
if ($LASTEXITCODE -ne 0 -or $result -match "Failure") {
    Write-Host "Install failed!" -ForegroundColor Red; exit 1
}
Write-Host "Install succeeded." -ForegroundColor Green

# ── Launch ────────────────────────────────────────────────────────────────────
if (-not $SkipLaunch) {
    Write-Host "`nLaunching Edivoice..." -ForegroundColor Cyan
    & $adb shell am start -n "$PKG/$ACT"
}

Write-Host "`n=== Done! ===" -ForegroundColor Green
Write-Host "Logcat: $adb logcat -s Edivoice" -ForegroundColor Cyan
