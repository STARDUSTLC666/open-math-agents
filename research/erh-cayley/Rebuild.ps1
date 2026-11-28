[CmdletBinding()]
param([string]$FormalConjectures,[switch]$CheckSourcesOnly)
$ErrorActionPreference='Stop'
$manifest=Get-Content -LiteralPath (Join-Path $PSScriptRoot 'build-order.json') -Raw | ConvertFrom-Json
foreach ($m in $manifest.modules) {
  $source=Join-Path $PSScriptRoot $m.source
  if ((Get-FileHash -LiteralPath $source).Hash.ToLowerInvariant() -cne $m.sha256) { throw "Source hash differs for $($m.module)." }
}
if ($CheckSourcesOnly) {
  Write-Output "All $($manifest.modules.Count) Lean sources match the manifest."
  return
}
if (!$FormalConjectures) { throw 'Pass the path to the pinned FormalConjectures checkout with its Mathlib cache.' }
$formal=(Resolve-Path -LiteralPath $FormalConjectures).Path
if ((git -C $formal rev-parse HEAD) -cne $manifest.formalConjectures -or
    (git -C (Join-Path $formal '.lake/packages/mathlib') rev-parse HEAD) -cne $manifest.mathlib) {
  throw 'FormalConjectures or Mathlib revision differs from the verified build.'
}
$build=Join-Path $PSScriptRoot '.build'
$null=New-Item -ItemType Directory -Force -Path (Join-Path $build 'OMAReductions')
$previousPath=$env:LEAN_PATH
Push-Location -LiteralPath $formal
try {
  $lakePath=(& lake env pwsh -NoProfile -Command "[Console]::WriteLine([Environment]::GetEnvironmentVariable('LEAN_PATH'))")
  if ($LASTEXITCODE -ne 0 -or !$lakePath) { throw 'Lake environment unavailable.' }
  $env:LEAN_PATH=$build+[IO.Path]::PathSeparator+$lakePath
  foreach ($m in $manifest.modules) {
    $src=Join-Path $PSScriptRoot $m.source
    $obj=Join-Path $build ([IO.Path]::ChangeExtension($m.source,'olean'))
    $lines=@(& lean -j 2 -R $PSScriptRoot -o $obj $src 2>&1)
    if ($LASTEXITCODE -ne 0 -or $lines -match 'sorryAx|error:|declaration uses .sorry.') {
      $lines | Out-Host
      throw "Compilation failed in $($m.module)."
    }
    if ($m.declarations) {
      $expected=@($m.declarations | ForEach-Object {"'OMA.$($m.module).$_' depends on axioms: [propext, Classical.choice, Quot.sound]"})
      $reports=@($lines | Where-Object {$_ -match 'depends on axioms:'} | ForEach-Object {$_.ToString()})
      if ($reports.Count -ne $expected.Count -or (Compare-Object $reports $expected -CaseSensitive)) { throw "Unexpected axiom reports in $($m.module)." }
    }
    Write-Output "Checked $($m.module)"
  }
} finally {
  Pop-Location
  $env:LEAN_PATH=$previousPath
}
