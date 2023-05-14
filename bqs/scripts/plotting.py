import os

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from matplotlib.image import imread
from scipy import stats

FOLDER = "../processed"
SUCCESS = "SUCCESS"
FAILURE = "FAILURE"


def process_data_file(file_path, y_scale):
    # Read the data
    data = pd.read_csv(file_path)

    # Calculate unsuccessful bounds
    unsuccessful_bounds = data[(data['JJBMC_result'] == FAILURE) |
                               (data['FIL_result'] == FAILURE) |
                               (data['FI_result'] == FAILURE)]['bound'].unique()

    # Plot the data
    fig, ax = plt.subplots()

    lines = []
    labels = []
    for func_name, color in zip(['JJBMC', 'FIL', 'FI'], ['blue', 'green', 'red']):
        func_data = data[data[f'{func_name}_result'] == SUCCESS]
        agg_data = func_data.groupby('bound').agg(
            runtime_median=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='median'),
            runtime_std=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='std'),
            count=pd.NamedAgg(column=f'{func_name}_runtime', aggfunc='count')
        )

        bounds = agg_data.index
        line, = ax.plot(bounds, agg_data['runtime_median'], marker='o', color=color)

        # only show error bar if std is not NaN
        if not np.isnan(agg_data['runtime_std']).all():
            ax.errorbar(bounds, agg_data['runtime_median'], yerr=agg_data['runtime_std'],
                        linestyle='None', capsize=5, color=color)

        # Add function line and modified label with successful iteration count
        lines.append(line)
        max_count = agg_data['count'].max()
        min_count = agg_data['count'].min()
        labels.append(func_name)

        # Log-linear regression for prediction
        log_runtimes = np.log(agg_data['runtime_median'])
        slope, intercept, r_value, p_value, std_err = stats.linregress(bounds, log_runtimes)
        next_bound = bounds[-1] + 1
        log_predicted_value = slope * next_bound + intercept
        predicted_value = np.exp(log_predicted_value)
        ax.plot([bounds[-1], next_bound], [agg_data['runtime_median'].iloc[-1], predicted_value], 'o--', color=color)

    # Configure plot
    ax.set_xlabel('Bound')
    ax.set_ylabel('Runtime (minutes)')
    ax.set_yscale(y_scale)
    ax.set_ylim(ymax=130)  # Set max y value to 2 hours (120 minutes)
    ax.legend(lines, labels)

    # Save plot
    file_name = os.path.splitext(os.path.basename(file_path))[0]
    plt.savefig(os.path.join(FOLDER, f"{file_name}_{y_scale}.png"))

    plt.close()

    # Print the bounds with unsuccessful runs
    print(f"Bounds with unsuccessful runs for {file_name}: {', '.join(map(str, unsuccessful_bounds))}")


def create_grid_layout(folder):
    png_files = [f for f in os.listdir(folder) if f.endswith(".png")]

    if not png_files:
        print("No PNG files found in the specified folder.")
        return

    num_files = len(png_files)
    num_cols = min(4, num_files)
    num_rows = int(np.ceil(num_files / num_cols))

    fig, axs = plt.subplots(num_rows, num_cols, figsize=(4 * num_cols, 4 * num_rows))

    for idx, png_file in enumerate(png_files):
        img = imread(os.path.join(folder, png_file))
        row = idx // num_cols
        col = idx % num_cols

        if num_rows > 1:
            ax = axs[row, col]
        else:
            ax = axs[col]

        ax.imshow(img)
        ax.axis('off')
        ax.set_title(png_file, fontsize=8)

    # Hide empty subplots
    for idx in range(num_files, num_rows * num_cols):
        row = idx // num_cols
        col = idx % num_cols

        if num_rows > 1:
            ax = axs[row, col]
        else:
            ax = axs[col]

        ax.axis('off')

    plt.tight_layout()
    plt.savefig(os.path.join(folder, "all_plots.png"), dpi=300)
    plt.close()


def get_grouped_data_from_file(file_path):
    # Read the data
    data = pd.read_csv(file_path)

    # Filter successful runs
    data = data[data['JJBMC_result'] == SUCCESS]
    data = data[data['FIL_result'] == SUCCESS]
    data = data[data['FI_result'] == SUCCESS]

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


if __name__ == "__main__":

    if not os.path.exists(FOLDER):
        os.makedirs(FOLDER)

    if False:  # Set to True to re-generate the plots aka clear the folder and regenerate all plots
        for file in os.listdir(FOLDER):
            if file.endswith(".png"):
                os.remove(os.path.join(FOLDER, file))

    for file in os.listdir(FOLDER):
        if file.endswith(".csv"):
            process_data_file(os.path.join(FOLDER, file), 'linear')
            process_data_file(os.path.join(FOLDER, file), 'log')

    file_data_dict = {}
    for file in os.listdir(FOLDER):
        if file.endswith(".csv"):
            file_name = os.path.splitext(file)[0]
            file_data_dict[file_name] = get_grouped_data_from_file(os.path.join(FOLDER, file))

    plot_combined_data(file_data_dict, 'linear')
    plot_combined_data(file_data_dict, 'log')

    create_grid_layout(FOLDER)

    os.system(f"start {FOLDER}/all_plots.png")
