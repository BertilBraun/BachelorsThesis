import os
import time

if os.name != 'nt':
    import shlex

import shutil
import subprocess
from concurrent.futures import ProcessPoolExecutor

HOME_FOLDER = os.getcwd() + "/../.."
BASE_FOLDER = HOME_FOLDER + "/bqs/results"
SAT_SOLVER = "/home/bertil/kissat/build/kissat"

MS_OF_1_HOUR = 60 * 60 * 1000
FUNCTION_TIMEOUT = 2 * MS_OF_1_HOUR

JJBMC_CMD_SC = "java -jar JJBMC.jar -mas {mas} -u {u} -tr -c -kt -timeout={timeout} BlockQuickSort.java {function} -j=\"--stop-on-fail --external-sat-solver {solver}\" -sc"
JJBMC_CMD_UNWIND_ASSERT = "java -jar JJBMC.jar -mas {mas} -u {u} -tr -c -kt -timeout={timeout} BlockQuickSort.java {function} -j=\"--stop-on-fail --external-sat-solver {solver} --unwinding-assertions\""

OUTPUT_SC_FILE_NAME = "output-sc.txt"
OUTPUT_UNWINDING_ASSERT_FILE_NAME = "output-ua.txt"

FOLDER_F_STRING = "{BASE_FOLDER}/check/{function}/"

BOUND = 5
UNWIND_SUCCESS = 6
UNWIND_FAIL = 4

SC_SUCCESS_STRING = "Sanity check ok for function:"
SUCCESS = "SUCCESS"
FAILURE = "FAILURE"

FUNCTIONS = [
    "swap",
    "sortPair",
    "partition",
    "medianOf3",
    "insertionSort",
    "permutation",
    "hoareBlockPartition",
    "quickSort",
]


def run_command(cmd):
    print("Running command: " + cmd)
    # if is windows
    if os.name == 'nt':
        subprocess_command = cmd.split(' ')
    else:
        subprocess_command = shlex.split(cmd)

    # Run the command using subprocess and write output to file and wait for it to finish
    p = subprocess.run(subprocess_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # sleep for 5 seconds to make sure that jbmc has finished
    time.sleep(5)

    try:
        shutil.copyfile("tmp/xmlout.xml", "xmlout.xml")
    except:
        print("Error copying xmlout.xml")

    try:
        shutil.copyfile("tmp/BlockQuickSort.java", "BlockQuickSort_compiled.java")
        shutil.copyfile("tmp/compilationErrors.txt", "compilationErrors.txt")
    except:
        print("Error copying BlockQuickSort.java or compilationErrors.txt")

    return p.stdout.decode("utf-8"), p.stderr.decode("utf-8")


def process(function):
    folder = FOLDER_F_STRING.format(BASE_FOLDER=BASE_FOLDER, function=function)

    os.makedirs(folder, exist_ok=True)

    if not os.path.exists(f"{folder}/JJBMC.jar"):
        shutil.copyfile(f"{HOME_FOLDER}/JJBMC.jar", f"{folder}/JJBMC.jar")

    if not os.path.exists(f"{folder}/BlockQuickSort.java"):
        shutil.copyfile(f"{HOME_FOLDER}/bqs/BlockQuickSort.java", f"{folder}/BlockQuickSort.java")

    os.chdir(folder)

    if os.path.exists(OUTPUT_SC_FILE_NAME):
        print(f"Skipping Sanity Check for function '{function}' because it already exists")
    else:
        cmd = JJBMC_CMD_SC.format(
            mas=BOUND,
            u=UNWIND_SUCCESS,
            timeout=FUNCTION_TIMEOUT,
            function=function,
            solver=SAT_SOLVER,
        )
        stdout, stderr = run_command(cmd)

        if SC_SUCCESS_STRING not in stdout and SC_SUCCESS_STRING not in stderr:
            print(f"Sanity Check failed for function '{function}'")

        with open(OUTPUT_SC_FILE_NAME, "w") as f:
            f.write(stdout)
            f.write(stderr)

    if os.path.exists(OUTPUT_UNWINDING_ASSERT_FILE_NAME):
        print(f"Skipping Unwinding Assertions for function '{function}' because it already exists")
    else:
        cmd = JJBMC_CMD_UNWIND_ASSERT.format(
            mas=BOUND,
            u=UNWIND_SUCCESS,
            timeout=FUNCTION_TIMEOUT,
            function=function,
            solver=SAT_SOLVER,
        )
        stdout, stderr = run_command(cmd)

        if SUCCESS not in stdout and SUCCESS not in stderr:
            print(f"Unwinding Assertions failed for function '{function}'")

        with open(OUTPUT_UNWINDING_ASSERT_FILE_NAME, "w") as f:
            f.write(stdout)
            f.write(stderr)

        cmd = JJBMC_CMD_UNWIND_ASSERT.format(
            mas=BOUND,
            u=UNWIND_FAIL,
            timeout=FUNCTION_TIMEOUT,
            function=function,
            solver=SAT_SOLVER,
        )
        stdout, stderr = run_command(cmd)

        if SUCCESS in stdout or SUCCESS in stderr:
            print(f"Unwinding Assertions succeeded for function '{function}' even though it should fail")

        with open(OUTPUT_UNWINDING_ASSERT_FILE_NAME, "a") as f:
            f.write("\n\n\n---------------------------------------------------\n\n\n")
            f.write(stdout)
            f.write(stderr)

    try:
        # remove tmp and everything in it
        shutil.rmtree("tmp")
        os.remove("JJBMC.jar")
    except:
        print("Error cleaning up tmp folder")

    os.chdir(HOME_FOLDER)


def run(workers, tasks):
    with ProcessPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(process, *task) for task in tasks]

        for future in futures:
            future.result()


if __name__ == "__main__":
    run(len(FUNCTIONS), [(f,) for f in FUNCTIONS])
