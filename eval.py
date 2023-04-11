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

BOUNDS = list(range(3, 10))

HOME_FOLDER = os.getcwd()
BASE_FOLDER = HOME_FOLDER + "/bqs/results"

out_file = open("out.csv", "w")
out_file.write("bound,function,inline_arg,result,runtime\n")


def process_JJBMC_example(folder, bound, function, inline_arg):
    file = f"{folder}/JJBMC output{inline_arg}.txt"

    if not os.path.exists(file):
        return

    with open(file) as f:
        content = f.read()

    if "FAILURE" in content:
        out_file.write(f"{bound},{function},{inline_arg},FAILURE,-1\n")
    elif "SUCCESS" in content:
        runtime = re.search(r"JBMC took (\d+)ms.", open(file).read()).group(1)
        runtime_in_minutes = round(int(runtime) / 1000 / 60, 4)
        out_file.write(f"{bound},{function},{inline_arg},SUCCESS,{runtime_in_minutes}\n")
    elif "JBMC did not terminate as expected" in content:
        out_file.write(f"{bound},{function},{inline_arg},TIMEOUT / MEMORY_LIMIT,-1\n")
    else:
        out_file.write(f"{bound},{function},{inline_arg},ERROR,-1\n")


def worker(bound, function):
    folder = f"{BASE_FOLDER}/{bound}/{function}"
    if not os.path.exists(folder):
        return

    process_JJBMC_example(folder, bound, function, '')
    process_JJBMC_example(folder, bound, function, ' -fil')
    process_JJBMC_example(folder, bound, function, ' -fi')


if __name__ == "__main__":

    for bound in BOUNDS:
        for function in FUNCTIONS:
            worker(bound, function)
