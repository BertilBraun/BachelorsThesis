import os

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.image import imread

FOLDER = "bqs/processed"


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


create_grid_layout(FOLDER)
