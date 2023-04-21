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

java -jar JJBMC.jar -mas 6 -u 7 -tr -c -kt -timeout=36000000 bqs\run\%current_time%\BlockQuickSort.java hoareBlockPartition -rv indexL -rv indexR -rv array -rv startLeft -rv startRight -rv numLeft -rv numRight -rv num -rv originalBegin -rv originalEnd -rv begin -rv end -rv originalArray -rv i -rv j -rv last -rv did_run_loop -rv lastNumLeft -rv lastNumRight -rv lastArray -rv lastBegin -rv lastLast -rv lastIndexL -rv lastIndexR -rv lastStartLeft -rv lastStartRight -rv lastNum -rv pivot -rv originalPivotPosition -rv originalArrayLength -rv indexL0 -rv indexL1 -rv indexR0 -rv indexR1 -rv afterLoopNumLeft -rv afterLoopNumRight -rv afterLoopArray -rv afterLoopBegin -rv afterLoopLast -rv afterLoopIndexL -rv afterLoopIndexR -rv afterLoopStartLeft -rv afterLoopStartRight -rv afterLoopNum -rv secLoopNumLeft -rv secLoopNumRight -rv secLoopArray -rv secLoopBegin -rv secLoopLast -rv secLoopIndexL -rv secLoopIndexR -rv secLoopStartLeft -rv secLoopStartRight -rv secLoopNum 
REM -j=--stop-on-fail

echo Results are stored in bqs\run\%current_time%\tmp\xmlout.xml and bqs\run\%current_time%\tmp\BlockQuickSort.java
echo Results are stored in %current_time%\tmp\xmlout.xml and %current_time%\tmp\BlockQuickSort.java