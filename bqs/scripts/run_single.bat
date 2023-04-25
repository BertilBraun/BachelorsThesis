@echo off
setlocal enabledelayedexpansion

REM Usage:
REM Call this script with the following arguments:
REM 1. The function name to be tested
REM 2. Optional argument: The maximum array size
REM 3. Optional argument: The unwinding bound
REM 4. Optional argument: Stop on fail (true/false)
REM Example: run.bat partition 5 7 true

set function_name=%1
set max_array_size=%2
set unwinding_bound=%3
set stop_on_fail=%4

REM If the maximum array size is not specified, set it to 5
if "%max_array_size%" == "" set max_array_size=5

REM If the unwinding bound is not specified, set it to 7
if "%unwinding_bound%" == "" set unwinding_bound=7

REM If the stop on fail flag is not specified, set it to false
if "%stop_on_fail%" == "" set stop_on_fail=false

REM If the stop on fail flag is true, set the stop on fail flag to true
if "%stop_on_fail%" == "true" set stop_on_fail=true

REM If the stop on fail flag is false, set the stop on fail flag to false
if "%stop_on_fail%" == "false" set stop_on_fail=false

REM If the stop on fail flag is not true or false, set the stop on fail flag to false
if "%stop_on_fail%" NEQ "true" if "%stop_on_fail%" NEQ "false" set stop_on_fail=false

REM If the stop on fail is true, set JBMC_parameters to -j=--stop-on-fail
if "%stop_on_fail%" == "true" set JBMC_parameters=-j=--stop-on-fail
if "%stop_on_fail%" == "false" set JBMC_parameters= 


for /F "tokens=1-4 delims=:. " %%a in ("%TIME%") do (
  set hour=%%a
  set minute=%%b
  set second=%%c
)

if %hour% LSS 10 set hour=0%hour%

for /F "tokens=1 delims=," %%a in ("%second%") do (
  set second=%%a
)

set current_time=%hour%_%minute%_%second%
REM create a folder bqs/run/"current_time" to store the results
mkdir ..\run\%current_time%
REM copy the source code to the folder

echo Running in folder bqs\run\%current_time%
echo Running in folder %current_time%

copy ..\BlockQuickSort.java ..\run\%current_time%

REM wsl ../../gradlew fatJar

java -jar ..\..\JJBMC.jar -mas %max_array_size% -u %unwinding_bound% -tr -c -kt -timeout=72000000 ..\run\%current_time%\BlockQuickSort.java %function_name% %JBMC_parameters%

echo Results are stored in bqs\run\%current_time%\tmp\xmlout.xml and bqs\run\%current_time%\tmp\BlockQuickSort.java
echo Results are stored in %current_time%\tmp\xmlout.xml and %current_time%\tmp\BlockQuickSort.java