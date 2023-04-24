import os

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

FOLDER = "bqs/processed"


def process_data_file(file_path, y_scale):
    # Read the data
    data = pd.read_csv(file_path)

    # Calculate unsuccessful bounds
    unsuccessful_bounds = data[(data['JJBMC_result'] != "SUCCESS") |
                               (data['FIL_result'] != "SUCCESS") |
                               (data['FI_result'] != "SUCCESS")]['bound'].unique()

    # Plot the data
    fig, ax = plt.subplots()

    lines = []
    labels = []
    for func_name, color in zip(['JJBMC', 'FIL', 'FI'], ['blue', 'green', 'red']):
        func_data = data[data[f'{func_name}_result'] == "SUCCESS"]
        agg_data = func_data.groupby('bound').agg(
            runtime_median=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='median'),
            runtime_std=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='std'),
            count=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='count')
        )

        bounds = agg_data.index
        line, = ax.plot(bounds, agg_data['runtime_median'], marker='o', color=color)
        ax.errorbar(bounds, agg_data['runtime_median'], yerr=agg_data['runtime_std'],
                    linestyle='None', capsize=5, color=color)

        # Add function line and modified label with successful iteration count
        lines.append(line)
        max_count = int(agg_data['count'].max())
        min_count = int(agg_data['count'].min())
        if max_count == min_count:
            labels.append(f"{func_name} ran {max_count} times")
        else:
            labels.append(f"{func_name} ran {max_count} times but min {min_count} times")

    # Configure plot
    ax.set_xlabel('Bound')
    ax.set_ylabel('Runtime (minutes)')
    ax.set_yscale(y_scale)
    ax.legend(lines, labels)

    # Save plot
    file_name = os.path.splitext(os.path.basename(file_path))[0]
    plt.savefig(os.path.join(FOLDER, f"{file_name}_{y_scale}.png"))

    plt.close()

    # Print the bounds with unsuccessful runs
    print(f"Bounds with unsuccessful runs for {file_name}: {', '.join(map(str, unsuccessful_bounds))}")


if not os.path.exists(FOLDER):
    os.makedirs(FOLDER)

for file in os.listdir(FOLDER):
    if file.endswith(".csv"):
        process_data_file(os.path.join(FOLDER, file), 'linear')
        process_data_file(os.path.join(FOLDER, file), 'log')
