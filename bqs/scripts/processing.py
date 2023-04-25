import csv
import os
import re
from collections import defaultdict

FUNCTIONS = [
    "swap",
    "sortPair",
    "medianOf3",
    "partition",
    "insertionSort",
    "quickSort",
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
BASE_FOLDER = HOME_FOLDER + "/../results"

EVAL_FILE = "out.csv"
PROCESSED_FOLDER = "../processed"

if not os.path.exists(PROCESSED_FOLDER):
    os.mkdir(PROCESSED_FOLDER)


out_file = open(EVAL_FILE, "w")
out_file.write("bound,iter,function,inline_arg,result,runtime\n")


def process_JJBMC_example(folder, bound, iter, function, inline_arg):
    file = f"{folder}/inline{inline_arg}/output.txt"

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
    elif "timed out" in content or "cli.CLI.translateAndRunJBMC" in content:
        out_file.write(f"{bound},{iter},{function},{inline_arg},TIMEOUT,N/A\n")
    elif "JBMC did not terminate as expected" in content:
        out_file.write(f"{bound},{iter},{function},{inline_arg},MEMORY_LIMIT,N/A\n")
    else:
        out_file.write(f"{bound},{iter},{function},{inline_arg},ERROR,N/A\n")


def process(iteration, bound, function):
    folder = f"{BASE_FOLDER}/bound_{bound}/{function}/iter_{iteration}"
    if not os.path.exists(folder):
        return

    process_JJBMC_example(folder, bound, iteration, function, '')
    process_JJBMC_example(folder, bound, iteration, function, '-fil')
    process_JJBMC_example(folder, bound, iteration, function, '-fi')


def group_data_from_csv(input_csv: str) -> dict:
    data = csv.reader(input_csv.strip().split('\n'))
    header = next(data)

    grouped_data = defaultdict(lambda: [[defaultdict(lambda: ("N/A", "N/A")) for _ in range(MAX_ITERATIONS)]
                               for _ in range(MAX_BOUNDS)])

    for row in data:
        bound, iter, function, inline_arg, result, runtime = row
        grouped_data[function][int(bound)][int(iter)][inline_arg] = (result, runtime)

    return grouped_data


def write_processed_csv(output_file_path: str, grouped_data: dict) -> None:
    for function, bounds in grouped_data.items():
        with open(f"{output_file_path}/{function}.csv", 'w', newline='') as file:
            file.write("bound,iter,JJBMC_result,FIL_result,FI_result,JJBMC_runtime,FIL_runtime,FI_runtime\n")

            for bound, iters in enumerate(bounds):

                for iter, inline_args in enumerate(iters):
                    results = []
                    runtimes = []

                    for inline_arg in ['', '-fil', '-fi']:
                        result, runtime = inline_args[inline_arg]
                        results.append(result)
                        runtimes.append(runtime)

                    # if all results are N/A, skip this iteration
                    if all(result == "N/A" for result in results):
                        continue

                    file.write(f"{bound},{iter}")
                    for result in results:
                        file.write(f",{result}")
                    for runtime in runtimes:
                        file.write(f",{runtime}")
                    file.write("\n")


if __name__ == "__main__":

    for i in range(MAX_ITERATIONS):
        for bound in BOUNDS:
            for function in FUNCTIONS:
                process(i, bound, function)

    grouped_data = group_data_from_csv(open(EVAL_FILE).read())
    write_processed_csv(PROCESSED_FOLDER, grouped_data)
