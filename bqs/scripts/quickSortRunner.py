import os
import re
import time

if os.name != 'nt':
    import shlex

import shutil
import subprocess
from concurrent.futures import ProcessPoolExecutor

# this file should run a command for multiple inputs sequentially


HOME_FOLDER = os.getcwd() + "/../.."
BASE_FOLDER = HOME_FOLDER + "/bqs/results"
SAT_SOLVER = "/home/bertil/kissat/build/kissat"
MAX_BOUND = 300
ITERATIONS = 1  # TODO Should be run with 5

MS_OF_1_HOUR = 60 * 60 * 1000
MS_OF_2_HOURS = 2 * MS_OF_1_HOUR
MS_OF_10_HOURS = 10 * MS_OF_1_HOUR
DO_NOT_RETRY_FUNCTION_AFTER_THIS_TIME = MS_OF_2_HOURS  # TODO Should be run with MS_OF_2_HOURS
FUNCTION_TIMEOUT = 3 * MS_OF_1_HOUR  # TODO Should be run with MS_OF_10_HOURS

JJBMC_CMD = "java -jar JJBMC.jar -mas {mas} -u {u} {inline} -tr -c -kt -t {timeout} BlockQuickSort.java {function} -j \"--stop-on-fail --external-sat-solver {solver} --unwinding-assertions\" -rv array -rv originalBegin -rv originalEnd -rv begin -rv end -rv depth -rv depthLimit -rv stack -rv depthStack -rv stackPointer -rv depthPointer"

OUTPUT_FILE_NAME = "output.txt"

WORKERS = 16

FOLDER_F_STRING = "{BASE_FOLDER}/bound_{bound}/{function}/iter_{iteration}"


def process_JJBMC_example(folder, bound, unwind, function, inline_arg):
    folder = f"{folder}/inline{inline_arg}/unwind_{unwind}"

    if os.path.exists(f"{folder}/{OUTPUT_FILE_NAME}"):
        print(f"Skipping function '{function}' with bound '{bound}' and inline arg '{inline_arg}' because it already exists")
        return

    # Copy the java file in the folder

    os.makedirs(folder, exist_ok=True)

    if not os.path.exists(f"{folder}/JJBMC.jar"):
        shutil.copyfile(f"{HOME_FOLDER}/JJBMC.jar", f"{folder}/JJBMC.jar")

    if not os.path.exists(f"{folder}/BlockQuickSort.java"):
        shutil.copyfile(f"{HOME_FOLDER}/bqs/BlockQuickSort.java", f"{folder}/BlockQuickSort.java")

    cmd = JJBMC_CMD.format(
        mas=bound,
        u=unwind,
        timeout=FUNCTION_TIMEOUT,
        function=function,
        inline=inline_arg,
        solver=SAT_SOLVER,
    )
    print(f"Running function '{function}' with bound '{bound}' and  unwind '{unwind}' and inline arg '{inline_arg}'")
    # if is windows
    if os.name == 'nt':
        subprocess_command = cmd.split(' ')
    else:
        subprocess_command = shlex.split(cmd)

    # Run the command using subprocess and write output to file and wait for it to finish
    os.chdir(folder)
    p = subprocess.run(subprocess_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # sleep for 5 seconds to make sure that jbmc has finished
    time.sleep(5)

    stdout = p.stdout.decode("utf-8").replace("\x00", "")
    stderr = p.stderr.decode("utf-8").replace("\x00", "")
    # print(stdout)
    # print(stderr)
    print(
        f"Finished running function '{function}' with bound '{bound}' and  unwind '{unwind}' and inline arg '{inline_arg}'")

    with open(OUTPUT_FILE_NAME, "w") as f:
        # Write stdout and stderr to file
        f.write(stdout)
        f.write(stderr)

    if not "SUCCESS" in stdout and not "SUCCESS" in stderr:
        try:
            shutil.copyfile("tmp/xmlout.xml", "xmlout.xml")
        except:
            print("Error copying xmlout.xml")
        try:
            shutil.copyfile("tmp/BlockQuickSort.java", "BlockQuickSort_compiled.java")
            shutil.copyfile("tmp/compilationErrors.txt", "compilationErrors.txt")
        except:
            print("Error copying BlockQuickSort.java or compilationErrors.txt")

    try:
        # remove tmp and everything in it
        shutil.rmtree("tmp")
        os.remove("JJBMC.jar")
    except:
        print("Error cleaning up tmp folder")

    if "SUCCESS" in stdout or "SUCCESS" in stderr:
        try:
            # parse runtime from output "JBMC took XXXms." parse XXX using regex
            runtime = re.search(r"JBMC took (\d+)ms.", stdout).group(1)
            # set runtime in ms for this function and bound and inline arg
            print(
                f"Runtime for function '{function}' with bound '{bound}' and unwind '{unwind}' and inline arg '{inline_arg}' was {runtime}ms")
        except:
            print("Error parsing runtime")
    else:
        print(f"Failed function '{function}' with bound '{bound}' and unwind '{unwind}' and inline arg '{inline_arg}'")

    os.chdir(HOME_FOLDER)


def generate_tasks(iteration, bound, unwind, function, inline_arg):
    folder = FOLDER_F_STRING.format(BASE_FOLDER=BASE_FOLDER, bound=bound, function=function, iteration=iteration)

    return [(folder, bound, unwind, function, inline_arg)]


def run(workers, tasks):
    with ProcessPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(process_JJBMC_example, *task) for task in tasks]

        for future in futures:
            future.result()


if True:  # change to True and setup function and inline args for cleanup
    for function in ["quickSort"]:
        for bound in range(MAX_BOUND):
            for iteration in range(ITERATIONS):
                for inline_arg in [""]:
                    folder = FOLDER_F_STRING.format(
                        BASE_FOLDER=BASE_FOLDER,
                        bound=bound,
                        function=function,
                        iteration=iteration
                    )

                    if os.path.exists(folder):
                        shutil.rmtree(folder)

if __name__ == "__main__":
    for i in range(ITERATIONS):
        tasks = []
        for bound in range(1, 6):
            for inline_arg in ['', '-fi', '-fil']:
                tasks += generate_tasks(i, bound, 6, "quickSort", inline_arg)
        for bound in range(6, 9):
            for unwind in range(bound + 1, bound + 5):
                for inline_arg in ['', '-fil']:
                    tasks += generate_tasks(i, bound, unwind, "quickSort", inline_arg)

        tasks = list(sorted(tasks, key=lambda x: x[1]))
        run(WORKERS, tasks)
