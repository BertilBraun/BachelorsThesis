#!/bin/sh

# run process.py

python3 process.py

# run eval.py

python3 eval.py

# open processed.csv via csvtool (sudo apt-get install csvtool)

csvtool readable processed.csv | view -
