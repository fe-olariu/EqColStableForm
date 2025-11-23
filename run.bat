@echo off
if "%~2"=="" (
    echo Usage: run.bat CuttingPane fileName
    echo Usage: run.bat BranchPrice fileName
    exit /b 1
)

SET MAIN_CLASS=%1
SET FILE_NAME=%2
SET CP="lib/algorithms-4.0.1.jar;lib/algs4.jar;lib/graph4j-1.0.8.jar;lib/gurobi.jar;lib/j3d-core-1.3.1.jar;lib/j3d-core-utils-1.3.1.jar;lib/jama-1.0.3.jar;lib/stdlib-1.0.1.jar;lib/vecmath-1.3.1.jar;bin/"

java -cp "%CP%" "%MAIN_CLASS%" "%FILE_NAME%"