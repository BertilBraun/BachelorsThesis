import os
import subprocess
import shutil
from concurrent.futures import ProcessPoolExecutor

# this file should run a command for multiple inputs sequentially

MS_OF_24_HOURS = 24 * 60 * 60 * 1000

JJBMC_CMD = "java -jar ../../../../JJBMC.jar -mas {mas} -u {u}{inline} -tr -c -kt -timeout={timeout} BlockQuickSort.java {function}"

FUNCTIONS = [
    "swap",
    "sortPair",
    "permutation",
    "medianOf3",
    "partition",
    "insertionSort",
    "quickSortRec",
    "quickSortRecImpl",
    # "hoareBlockPartition",
    "permutation",
]

BOUNDS = list(range(3, 10))

HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"

MAX_WORKERS = 4

def process_JJBMC_example(folder, bound, function, inline_arg):

    # Copy the java file in the folder
    
    shutil.copyfile(f"{HOME_FOLDER}/bqs/BlockQuickSort.java", f"{folder}/BlockQuickSort.java")
    
    cmd = JJBMC_CMD.format(
        mas=bound, 
        u=bound + 2, 
        timeout=MS_OF_24_HOURS, 
        function=function, 
        inline=inline_arg
    )
    print("Running command: " + cmd)
    
    # Run the command using subprocess and write output to file and wait for it to finish
    os.chdir(folder)
    p = subprocess.Popen(cmd.split(' '), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    with open("JJBMC output{0}.txt".format(inline_arg), "w") as f:
        # Write stdout and stderr to file
        stdout = p.stdout.read().decode("utf-8")
        stderr = p.stderr.read().decode("utf-8")
        print(stdout)
        print(stderr)
        print(f"Finished running function {function} with bound {bound} and inline arg {inline_arg}")
        f.write(stdout)
        f.write(stderr)
        
    p.wait(timeout=MS_OF_24_HOURS / 1000)
    os.chdir(HOME_FOLDER)
    

def worker(bound, function):
    folder = f"{BASE_FOLDER}/{bound}/{function}"
    os.makedirs(folder, exist_ok=True)

    process_JJBMC_example(folder, bound, function, '')
    process_JJBMC_example(folder, bound, function, ' -fil')
    process_JJBMC_example(folder, bound, function, ' -fi')


def run(tasks):
    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = [executor.submit(worker, *task) for task in tasks]

        for future in futures:
            future.result()
            
            
if __name__ == "__main__":
    tasks = []

    for bound in BOUNDS:
        for function in FUNCTIONS:
            tasks.append((bound, function))
            
    run(tasks)
    run([(bound, "hoareBlockPartition") for bound in BOUNDS])