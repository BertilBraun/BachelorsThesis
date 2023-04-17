# pip install ushlex
import os

if os.name != 'nt':
    import shlex

import shutil
import subprocess
from concurrent.futures import ProcessPoolExecutor

# this file should run a command for multiple inputs sequentially

MS_OF_24_HOURS = 24 * 60 * 60 * 1000

JJBMC_CMD = "java -jar ../../../../../JJBMC.jar -mas {mas} -u {u}{inline} -tr -c -kt -timeout={timeout} BlockQuickSort.java {function} -j=\"--stop-on-fail\""

EASY_WORKERS = 4
MEDIUM_WORKERS = 2
HARD_WORKERS = 1

TASKS = [
    (EASY_WORKERS, [
        "swap",
        "sortPair",
    ], list(range(1, 10)), 3),
    (MEDIUM_WORKERS, [
        "partition",
        "permutation",
        "medianOf3",
        "insertionSort",
    ], list(range(1, 8)), 2),
    (HARD_WORKERS, [
        "quickSortRec",
        "quickSortRecImpl",
        "hoareBlockPartition",
    ], list(range(1, 7)), 1),
]

HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"


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
    # if is windows
    if os.name == 'nt':
        subprocess_command = cmd.split(' ')
    else:
        subprocess_command = shlex.split(cmd)
    p = subprocess.Popen(subprocess_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

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


def worker(iteration, bound, function):
    folder = f"{BASE_FOLDER}/{bound}/{function}/{iteration}"
    os.makedirs(folder, exist_ok=True)

    process_JJBMC_example(folder, bound, function, '')
    if function not in ['quickSortRec', 'quickSortRecImpl'] or bound < 4:
        process_JJBMC_example(folder, bound, function, ' -fil')
        process_JJBMC_example(folder, bound, function, ' -fi')


def run(workers, tasks):
    with ProcessPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(worker, *task) for task in tasks]

        for future in futures:
            future.result()


if __name__ == "__main__":
    for i in range(5):
        for (workers, functions, bounds, times_per_iteration) in TASKS:
            tasks = []
            for j in range(times_per_iteration):
                for bound in bounds:
                    for function in functions:
                        tasks.append((i * times_per_iteration + j, bound, function))

            run(workers, tasks)
