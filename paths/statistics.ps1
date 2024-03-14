$directoryPath = "D:\IdeaProjects\test_native_build\paths\"
$smt2Files = Get-ChildItem -Path $directoryPath -Recurse -File -Filter "*.path"

$satCount = 0
$unsatCount = 0
$deviants = 0

foreach ($file in $smt2Files) {
    $z3Output = & z3 -smt2 $file.FullName

    # Check if Z3 output indicates the file is valid (this is a placeholder condition)
    if (($z3Output -split '\n')[0] | Select-String "unsat") {
        $unsatCount++
    } else {
        $satCount++
        if ($file.FullName -match "deviant") {
            Write $file.FullName
            $deviants++
        }
    }
}

Write-Host "Total sat SMT2 files: $satCount"
Write-Host "Total unsat SMT2 files: $unsatCount"
Write-Host "Total sat deviants: $deviants"