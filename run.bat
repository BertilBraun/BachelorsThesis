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
copy bqs\BlockQuickSort.java bqs\run\%current_time%

wsl ./gradlew fatJar

java -jar JJBMC.jar -mas 6 -u 8 -tr -c -kt -timeout=18000000 bqs\run\%current_time%\BlockQuickSort.java hoareBlockPartition -rv upper -rv lowerI -rv indexL -rv indexR -rv array -rv startLeft -rv startRight -rv numLeft -rv numRight -rv num -rv originalBegin -rv originalEnd -rv swapI -rv swapJ -rv begin -rv end -rv originalArray