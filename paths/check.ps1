$directoryPath = "D:\IdeaProjects\test_native_build\paths\"
$smt2Files = Get-ChildItem -Path $directoryPath -Recurse -File -Filter "*.path"

$validCount = 0
$invalidCount = 0

foreach ($file in $smt2Files) {
    $z3Output = & z3 -smt2 $file.FullName
    # Write $file.FullName
    # Write $z3Output

    # Check if Z3 output indicates the file is valid (this is a placeholder condition)
    if ($z3Output | Select-String "\(error" | Select-String -NotMatch "unsat core" | Select-String -NotMatch "model is not available") {
        $invalidCount++
        Write-Host "Invalid file: $($file.FullName)"
    } else {
        $validCount++
    }
}

Write-Host "Total valid SMT2 files: $validCount"
Write-Host "Total invalid SMT2 files: $invalidCount"