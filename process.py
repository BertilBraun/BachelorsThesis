import csv
from collections import defaultdict

INPUT_FILE = "out.csv"
OUTPUT_FILE = "processed.csv"


def process_csv(input_csv: str) -> dict:
    data = csv.reader(input_csv.strip().split('\n'))
    header = next(data)

    grouped_data = defaultdict(lambda: defaultdict(lambda: ('N/A', 'N/A')))

    for row in data:
        bound, function, inline_arg, result, runtime = row
        grouped_data[(bound, function)][inline_arg] = (result, runtime)

    return grouped_data


def write_processed_csv(output_file_path: str, grouped_data: dict) -> None:
    with open(output_file_path, 'w', newline='') as file:
        file.write("bound,function,JJBMC_result,FIL_result,FI_result,JJBMC_runtime,FIL_runtime,FI_runtime\n")

        for (bound, function), value in sorted(grouped_data.items(), key=lambda e: (e[0][1], e[0][0])):

            file.write(f"{bound},{function}")

            results = []
            runtimes = []

            for inline_arg in ['', ' -fil', ' -fi']:
                result, runtime = value[inline_arg]

                results.append(result)
                runtimes.append(runtime)

            for result in results:
                file.write(f",{result}")
            for runtime in runtimes:
                file.write(f",{runtime}")

            file.write("\n")


if __name__ == "__main__":
    grouped_data = process_csv(open(INPUT_FILE).read())
    write_processed_csv(OUTPUT_FILE, grouped_data)
