# Define the directory to search for .smt2 files
$directoryPath = "D:\IdeaProjects\test_native_build\paths\"

# Get all .smt2 files in the directory
$smt2Files = Get-ChildItem -Path $directoryPath -Recurse -File -Filter "*.path"

# Initialize counters for valid and invalid files
$validCount = 0
$invalidCount = 0

# Loop through each .smt2 file
foreach ($file in $smt2Files) {
    $z3Output = & z3 -smt2 $file.FullName
    
    # Check if Z3 output indicates the file is valid (this is a placeholder condition)
    if ($z3Output | Select-String "\(error" | Select-String -NotMatch "unsat core" | Select-String -NotMatch "model is not available") {
        $invalidCount++
        Write-Host "Invalid file: $($file.FullName)"
    } else {
        $validCount++
    }
}

# Print the total number of valid and invalid files
Write-Host "Total valid SMT2 files: $validCount"
Write-Host "Total invalid SMT2 files: $invalidCount"