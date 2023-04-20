# pip install ushlex
import os
import re

if os.name != 'nt':
    import shlex

import shutil
import subprocess
from concurrent.futures import ProcessPoolExecutor

# this file should run a command for multiple inputs sequentially


HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"
MAX_BOUND = 100
ITERATIONS = 5

MS_OF_1_HOUR = 60 * 60 * 1000
MS_OF_2_HOURS = 2 * MS_OF_1_HOUR
MS_OF_10_HOURS = 10 * MS_OF_1_HOUR

JJBMC_CMD = "java -jar ../../../../../../JJBMC.jar -mas {mas} -u {u} {inline} -tr -c -kt -timeout={timeout} BlockQuickSort.java {function} -j=--stop-on-fail"

OUTPUT_FILE_NAME = "output.txt"

EASY_WORKERS = 24
MEDIUM_WORKERS = 24
HARD_WORKERS = 12
VERY_HARD_WORKERS = 4

TASKS = [
    (EASY_WORKERS, [
        ("swap", list(range(1, 15)), 3),
        ("sortPair", list(range(1, 15)), 3),
        ("medianOf3", list(range(1, 14)), 3),
    ]),
    (MEDIUM_WORKERS, [
        ("partition", list(range(1, 12)), 3),
        ("insertionSort", list(range(1, 9)), 3),
        ("quickSortRec", list(range(1, 12)), 2),  # TODO no idea whether this is slow
    ]),
    (HARD_WORKERS, [
        ("permutation", list(range(1, 7)), 2),
        ("hoareBlockPartition", list(range(1, 7)), 2),  # TODO no idea how slow this is
    ]),
    (VERY_HARD_WORKERS, [
        ("quickSortRecImpl", list(range(1, 5)), 2),  # TODO 6 should be possible, even though it takes about 15h
    ])
]

failed_examples = {}
runtimes = {}


def process_JJBMC_example(folder, bound, function, inline_arg):
    folder = f"{folder}/inline{inline_arg}"

    # Copy the java file in the folder

    os.makedirs(folder, exist_ok=True)

    if os.path.exists(f"{folder}/{OUTPUT_FILE_NAME}"):
        print(f"Skipping function {function} with bound {bound} and inline arg {inline_arg} because it already exists")
        return

    # if runtime of previous bound is > MS_OF_2_HOURS, skip
    if runtimes.get((function, bound - 1, inline_arg), 0) > MS_OF_2_HOURS:
        print(
            f"Skipping function {function} with bound {bound} and inline arg {inline_arg} because previous bound took too long")
        return

    if not os.path.exists(f"{folder}/BlockQuickSort.java"):
        shutil.copyfile(f"{HOME_FOLDER}/bqs/BlockQuickSort.java", f"{folder}/BlockQuickSort.java")

    cmd = JJBMC_CMD.format(
        mas=bound,
        u=bound + 2,
        timeout=MS_OF_10_HOURS,
        function=function,
        inline=inline_arg
    )
    print("Running command: " + cmd)
    # if is windows
    if os.name == 'nt':
        subprocess_command = cmd.split(' ')
    else:
        subprocess_command = shlex.split(cmd)

    # Run the command using subprocess and write output to file and wait for it to finish
    os.chdir(folder)
    p = subprocess.Popen(subprocess_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        p.wait()
    except:
        print(f"Timeout for function {function} with bound {bound} and inline arg {inline_arg}")

    stdout = p.stdout.read().decode("utf-8")
    stderr = p.stderr.read().decode("utf-8")
    print(f"Finished running function {function} with bound {bound} and inline arg {inline_arg}")
    print(stdout)
    print(stderr)

    with open(OUTPUT_FILE_NAME, "w") as f:
        # Write stdout and stderr to file
        f.write(stdout)
        f.write(stderr)

    try:
        shutil.copyfile("tmp/xmlout.xml", "xmlout.xml")
        shutil.copyfile("tmp/BlockQuickSort.java", "BlockQuickSort_compiled.java")
        shutil.copyfile("tmp/compilationErrors.txt", "compilationErrors.txt")
        # remove tmp and everything in it
        shutil.rmtree("tmp")
    except:
        print("Error cleaning up tmp folder")

    try:
        # parse runtime from output "JBMC took XXXms." parse XXX using regex
        runtime = re.search(r"JBMC took (\d+)ms.", stdout).group(1)
        # set runtime in ms for this function and bound and inline arg
        runtimes[(function, bound, inline_arg)] = int(runtime)
    except:
        print("Error parsing runtime")

    if not "SUCCESS" in stdout and not "SUCCESS" in stderr:
        failed_examples[(function, inline_arg)] = min(failed_examples.get((function, inline_arg), MAX_BOUND), bound)

    os.chdir(HOME_FOLDER)


def generate_tasks(iteration, bound, function):
    folder = f"{BASE_FOLDER}/bound_{bound}/{function}/iter_{iteration}"

    tasks = []
    # check if we have already failed for this function and bound
    if failed_examples.get((function, ''), MAX_BOUND) > bound:
        tasks.append((folder, bound, function, ''))
    if failed_examples.get((function, '-fil'), MAX_BOUND) > bound:
        tasks.append((folder, bound, function, '-fil'))
    if failed_examples.get((function, '-fi'), MAX_BOUND) > bound:
        tasks.append((folder, bound, function, '-fi'))

    return tasks


def run(workers, tasks):
    with ProcessPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(process_JJBMC_example, *task) for task in tasks]

        for future in futures:
            future.result()


if __name__ == "__main__":
    for i in range(ITERATIONS):
        for (workers, functions) in TASKS:
            tasks = []
            for (function, bounds, times_per_iteration) in functions:
                for j in range(times_per_iteration):
                    for bound in bounds:
                        tasks += generate_tasks(i * times_per_iteration + j, bound, function)

            tasks = list(sorted(tasks, key=lambda x: x[1]))
            run(workers, tasks)
