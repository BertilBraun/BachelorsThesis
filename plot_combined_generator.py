import os

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

FOLDER = "bqs/processed"


def process_data_file(file_path):
    # Read the data
    data = pd.read_csv(file_path)

    # Filter successful runs
    data = data[data['JJBMC_result'] == "SUCCESS"]
    data = data[data['FIL_result'] == "SUCCESS"]
    data = data[data['FI_result'] == "SUCCESS"]

    # Calculate median
    agg_data = data.groupby('bound').agg(
        JJBMC_runtime_median=pd.NamedAgg(column='JJBMC_runtime', aggfunc='median'),
        FIL_runtime_median=pd.NamedAgg(column='FIL_runtime', aggfunc='median'),
        FI_runtime_median=pd.NamedAgg(column='FI_runtime', aggfunc='median')
    )

    return agg_data


def plot_combined_data(file_data_dict, y_scale):
    fig, ax = plt.subplots()

    colors = plt.cm.get_cmap('tab10', len(file_data_dict) * 3).colors

    for idx, (file_name, data) in enumerate(file_data_dict.items()):
        bounds = data.index
        ax.plot(bounds, data['JJBMC_runtime_median'], label=f'{file_name} - JJBMC', marker='o', color=colors[idx*3])
        ax.plot(bounds, data['FIL_runtime_median'], label=f'{file_name} - FIL', marker='o', color=colors[idx*3+1])
        ax.plot(bounds, data['FI_runtime_median'], label=f'{file_name} - FI', marker='o', color=colors[idx*3+2])

    # Configure plot
    ax.set_xlabel('Bound')
    ax.set_ylabel('Runtime (minutes)')
    ax.set_yscale(y_scale)
    ax.legend()

    # Save plot
    plt.savefig(os.path.join(FOLDER, f"combined_plot_{y_scale}.png"))

    plt.close()


if not os.path.exists(FOLDER):
    os.makedirs(FOLDER)

file_data_dict = {}
for file in os.listdir(FOLDER):
    if file.endswith(".csv"):
        file_name = os.path.splitext(file)[0]
        file_data_dict[file_name] = process_data_file(os.path.join(FOLDER, file))

plot_combined_data(file_data_dict, 'linear')
plot_combined_data(file_data_dict, 'log')
