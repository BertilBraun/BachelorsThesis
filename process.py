import csv
import os
from collections import defaultdict

INPUT_FILE = "out.csv"
OUTPUT_FILE_PATH = "bqs/processed"

ITERATIONS = 5
MAX_TIMES_PER_ITERATION = 3
MAX_BOUNDS = 15
MAX_ITERATIONS = MAX_BOUNDS * ITERATIONS * MAX_TIMES_PER_ITERATION

if not os.path.exists(OUTPUT_FILE_PATH):
    os.mkdir(OUTPUT_FILE_PATH)


def process_csv(input_csv: str) -> dict:
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
    grouped_data = process_csv(open(INPUT_FILE).read())
    write_processed_csv(OUTPUT_FILE_PATH, grouped_data)
