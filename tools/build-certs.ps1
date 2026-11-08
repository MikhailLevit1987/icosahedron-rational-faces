# Build the 48 kernel certificates one at a time, then the whole library (Windows PowerShell).
#
# Each complex certificate (Icosahedron.CertC.P*) needs 8-13 GB of memory while the Lean kernel
# checks it, each real one (Icosahedron.CertR.R*) up to about 7 GB. A plain `lake build` checks
# as many of them in parallel as there are CPU threads and can exhaust the memory of the machine.
#
# Usage:  powershell -NoProfile -ExecutionPolicy Bypass -File tools\build-certs.ps1
$ErrorActionPreference = 'Stop'
Set-Location (Join-Path $PSScriptRoot '..\lean')

$modules = @()
foreach ($ch in 0..5) { foreach ($sg in 'f', 't') { $modules += "Icosahedron.CertR.R$ch$sg" } }
foreach ($i in 0..5) { foreach ($j in 0..5) { $modules += "Icosahedron.CertC.P$i$j" } }

foreach ($m in $modules) {
    Write-Output "== $m"
    lake build $m
    if ($LASTEXITCODE -ne 0) { throw "lake build $m failed" }
}
Write-Output '== Icosahedron (all certificates are built; the rest is light)'
lake build
if ($LASTEXITCODE -ne 0) { throw 'lake build failed' }
