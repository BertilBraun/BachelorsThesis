@echo off

REM delete all files in bqs\processed ending with .png
REM del bqs\processed\*.png


python plot_generator.py

python plot_gen_grid.py

python plot_combined_generator.py

REM open bqs\processed\all_plots.png
cd bqs\processed
start all_plots.png
cd ..\..