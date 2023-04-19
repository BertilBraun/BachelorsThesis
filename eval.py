import os
import re

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

ITERATIONS = 5
MAX_TIMES_PER_ITERATION = 3
MAX_BOUNDS = 15
MAX_ITERATIONS = MAX_BOUNDS * ITERATIONS * MAX_TIMES_PER_ITERATION

BOUNDS = list(range(1, MAX_BOUNDS))

HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"


out_file = open("out.csv", "w")
out_file.write("bound,iter,function,inline_arg,result,runtime\n")


def process_JJBMC_example(folder, bound, iter, function, inline_arg):
    file = f"{folder}/JJBMC output{inline_arg}.txt"

    if not os.path.exists(file):
        return

    with open(file) as f:
        content = f.read()

    if "SUCCESS" in content:
        runtime = re.search(r"JBMC took (\d+)ms.", open(file).read()).group(1)
        runtime_in_minutes = round(int(runtime) / 1000 / 60, 4)
        out_file.write(f"{bound},{iter},{function},{inline_arg},SUCCESS,{runtime_in_minutes}\n")
    elif not content.strip():
        out_file.write(f"{bound},{iter},{function},{inline_arg},NOT_DONE,N/A\n")
    elif "FAILURE" in content:
        out_file.write(f"{bound},{iter},{function},{inline_arg},FAILURE,N/A\n")
    elif "JBMC did not terminate as expected" in content:
        out_file.write(f"{bound},{iter},{function},{inline_arg},TIMEOUT / MEMORY_LIMIT,N/A\n")
    else:
        out_file.write(f"{bound},{iter},{function},{inline_arg},ERROR,N/A\n")


def worker(iteration, bound, function):
    folder = f"{BASE_FOLDER}/bound_{bound}/{function}/iter_{iteration}"
    if not os.path.exists(folder):
        return

    process_JJBMC_example(folder, bound, iteration, function, '')
    process_JJBMC_example(folder, bound, iteration, function, ' -fil')
    process_JJBMC_example(folder, bound, iteration, function, ' -fi')


if __name__ == "__main__":

    for i in range(MAX_ITERATIONS):
        for bound in BOUNDS:
            for function in FUNCTIONS:
                worker(i, bound, function)
