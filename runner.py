import os
import subprocess

# this file should run a command for multiple inputs sequentially

MS_OF_72_HOURS = 259200000

CMD = "java -jar ../../../../JJBMC.jar -mas {mas} -u {u} {fil} -sc -tr -c -kt -timeout={timeout} BlockQuickSort.java {function}"

FUNCTIONS = [
    "swap",
    "sortPair",
    "permutation",
    "permutation",
    "medianOf3",
    "partition",
    "insertionSort",
    "quickSortRec",
    "quickSortRecImpl",
    "hoareBlockPartition",
    "permutation",
]

BOUNDS = list(range(3, 4)) # TODO 10

BASE_FOLDER = "bqs/results"

def process_JJBMC_example(folder, bound, function, force_loop_inline):

    # Copy the java file in the folder
    
    os.system(f"cp bqs/BlockQuickSort.java {folder}/BlockQuickSort.java")
    
    # Start with -mas -u -t set properly to complete in 72h
    
    cmd = CMD.format(
        mas=bound, 
        u=bound + 2, 
        timeout=MS_OF_72_HOURS, 
        function=function, 
        fil='-fil' if force_loop_inline else ''
    )
    print("Running command: " + cmd)
    
    # Run the command using subprocess and write output to file and wait for it to finish
    os.chdir(folder)
    p = subprocess.Popen(cmd.split(' '), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    with open("JJBMC output.txt", "w") as f:
        # Write stdout and stderr to file
        stdout = p.stdout.read().decode("utf-8")
        stderr = p.stderr.read().decode("utf-8")
        print(stdout)
        print(stderr)
        f.write(stdout)
        f.write(stderr)
        
    p.wait()        
    os.chdir("../../../..")
    
    
def process_JBMC_example(folder, bound, function):
    pass # TODO do the same for JBMC
    # Run command via jbmc CLASS_FILE (without .class) --unwind bound+2 --java-max-input-array-length bound --function function --trace --stop-on-fail --timestamp monotonic

for bound in BOUNDS:
    for function in FUNCTIONS:
        # Create a new folder for each
        
        folder = f"{BASE_FOLDER}/{bound}/{function}"
        os.makedirs(folder, exist_ok=True)
        
        process_JJBMC_example(folder, bound, function, True)
        process_JJBMC_example(folder, bound, function, False)
        process_JBMC_example(folder, bound, function)
        
        