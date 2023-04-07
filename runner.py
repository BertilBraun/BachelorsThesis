import os
import subprocess
from concurrent.futures import ProcessPoolExecutor

# this file should run a command for multiple inputs sequentially

MS_OF_24_HOURS = 24 * 60 * 60 * 1000

JJBMC_CMD = "java -jar ../../../../JJBMC.jar -mas {mas} -u {u}{fil} -sc -tr -c -kt -timeout={timeout} BlockQuickSort.java {function}"

JBMC_CMD = "jbmc {file} --unwind {u} --java-max-input-array-length {mas} --function {function} --trace --stop-on-fail --timestamp monotonic"
    
FUNCTIONS = [
    "swap",
    "sortPair",
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

HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"

MAX_WORKERS = 4

def process_JJBMC_example(folder, bound, function, force_loop_inline):

    # Copy the java file in the folder
    
    os.system(f"cp {HOME_FOLDER}/bqs/BlockQuickSort.java {folder}/BlockQuickSort.java")
    
    # Start with -mas -u -t set properly to complete in 72h
    
    cmd = JJBMC_CMD.format(
        mas=bound, 
        u=bound + 2, 
        timeout=MS_OF_24_HOURS, 
        function=function, 
        fil=' -fil' if force_loop_inline else ''
    )
    print("Running command: " + cmd)
    
    # Run the command using subprocess and write output to file and wait for it to finish
    os.chdir(folder)
    p = subprocess.Popen(cmd.split(' '), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    with open("JJBMC output{0}.txt".format(' fil' if force_loop_inline else ''), "w") as f:
        # Write stdout and stderr to file
        stdout = p.stdout.read().decode("utf-8")
        stderr = p.stderr.read().decode("utf-8")
        print(stdout)
        print(stderr)
        f.write(stdout)
        f.write(stderr)
        
    try:
        p.wait(timeout=MS_OF_24_HOURS / 1000)
    except subprocess.TimeoutExpired:
        print(f"JJBMC process (force_loop_inline={force_loop_inline}) timed out after 24 hours.")
        p.terminate()       
    os.chdir(HOME_FOLDER)
    
    
def process_JBMC_example(folder, file, bound, function):
        # Compile the Java file
    file = f"JBMC_BlockQuickSort_{function}"
    os.system(f"cp {HOME_FOLDER}/bqs/jbmc/{file}.java {folder}/{file}.java")

    # Compile the Java file
    os.system(f"javac {folder}/{file}.java")
    
    cmd = JBMC_CMD.format(
        file=file,
        mas=bound,
        u=bound + 2,
        function=function
    )
    print("Running command: " + cmd)

    os.chdir(folder)
    p = subprocess.Popen(cmd.split(' '), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    with open("JBMC output.txt", "w") as f:
        # Write stdout and stderr to file
        stdout = p.stdout.read().decode("utf-8")
        stderr = p.stderr.read().decode("utf-8")
        print(stdout)
        print(stderr)
        f.write(stdout)
        f.write(stderr)

    try:
        p.wait(timeout=MS_OF_24_HOURS / 1000)
    except subprocess.TimeoutExpired:
        print("JBMC process timed out after 24 hours.")
        p.terminate()
    os.chdir(HOME_FOLDER)


def worker(bound, function):
    folder = f"{BASE_FOLDER}/{bound}/{function}"
    os.makedirs(folder, exist_ok=True)

    process_JJBMC_example(folder, bound, function, True)
    process_JJBMC_example(folder, bound, function, False)
    process_JBMC_example(folder, bound, function)

if __name__ == "__main__":
    tasks = []

    for bound in BOUNDS:
        for function in FUNCTIONS:
            tasks.append((bound, function))

    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = [executor.submit(worker, *task) for task in tasks]

        for future in futures:
            future.result()