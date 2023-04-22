@echo off
setlocal enabledelayedexpansion

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
mkdir bqs\run\%current_time%
REM copy the source code to the folder

echo Running in folder bqs\run\%current_time%
echo Running in folder %current_time%

copy bqs\BlockQuickSort.java bqs\run\%current_time%

wsl ./gradlew fatJar

java -jar JJBMC.jar -mas 4 -u 5 -tr -c -kt -timeout=36000000 bqs\run\%current_time%\BlockQuickSort.java quickSort -rv begin -rv end -rv originalBegin -rv originalEnd -rv pivot -rv top -rv depth -rv array -rv stack
REM -j=--stop-on-fail

echo Results are stored in bqs\run\%current_time%\tmp\xmlout.xml and bqs\run\%current_time%\tmp\BlockQuickSort.java
echo Results are stored in %current_time%\tmp\xmlout.xml and %current_time%\tmp\BlockQuickSort.java