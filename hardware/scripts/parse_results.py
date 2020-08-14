#!/usr/bin/env python3

import argparse
import sys
import pandas as pd
import numpy as np
import ast
import seaborn as sns
import itertools

import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties


def get_runtime(data):
    # Get runtime of each segment in each run
    columns = ['run', 'section', 'runtime', 'cycles']
    result = pd.DataFrame(columns=columns)
    for run in data['run'].unique():
        for sec in data[data['run'] == run]['section'].unique():
            subset = (data[(data['run'] == run) & (data['section'] == sec)])
            runtime = subset['end'].max() - subset['start'].min()
            s = pd.Series([run, sec, runtime, subset['cycles'].to_list()], index=columns)
            result = result.append(s, ignore_index=True)
    return result

def get_speedup(data):
    runs = data['run'].unique()
    columns = ['section']
    result = pd.DataFrame(index=data['section'].unique())
    for i, pair in enumerate(itertools.permutations(runs, 2)):
        runtime_old = data.loc[data.run == pair[0],'runtime'].to_list()
        index_old   = data.loc[data.run == pair[0],'section'].to_list()
        runtime_old = [runtime_old[i] for i in index_old]
        runtime_new = data.loc[data.run == pair[1],'runtime'].to_list()
        index_new   = data.loc[data.run == pair[1],'section'].to_list()
        runtime_new = [runtime_new[i] for i in index_new]
        speedup = np.divide(runtime_old, runtime_new)
        result.insert(i, ''.join(pair), speedup)
    return result

def main():
    # Parse the arguments.
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", nargs="+", help="File to parse")
    parser.add_argument("--name", nargs="*", help="Names to use in plot")
    parser.add_argument("-o", "--output", metavar="PNG", nargs="?", help="PNG file to write; interactive if omitted")
    args = parser.parse_args()

    print(args)
    # Parse optional names for data runs
    names = args.filename[:]
    if args.name is not None:
        if len(args.filename) > len(args.name):
            print("Warning: More input files than names")
            for i, name in enumerate(args.name):
                names[i] = name
        else:
            names = args.name

    # Read data from files specified in arguments
    dataframes = []
    # Convert the lists in snitch_load_latency to lists instead of interpreting them as strings
    generic = lambda x: ast.literal_eval(x)
    conv = {'snitch_load_latency': generic}
    for i, file in enumerate(args.filename):
        dataframes.append(pd.read_csv(file, converters=conv))
        dataframes[-1]['run'] = names[i]

    data = pd.concat(dataframes)
    data = data.sort_values(by=['run', 'section', 'core'])
    # Extract data
    runtime = get_runtime(data)

    plt.figure(1)
    # ax = runtime.set_index(['section', 'run']).unstack('run').plot.bar(colormap='Pastel2')
#    ax = sns.barplot(x='section', y='runtime', hue='run', data=runtime,
#        palette='vlag')
    ax = sns.barplot(x='run', y='runtime', data=runtime, palette='vlag')
    ax.set_ylabel('Runtime [cycles]')
    ax.set_title('Runtime')

    plt.figure(2)
    # df = sns.load_dataset('tips')
    # sns.violinplot(x='day', y="total_bill", hue="smoker", data=df, palette="Pastel1")
    # sns.violinplot(x='section', y='cycles', hue='run', data=data, palette="Pastel2")
    sns.violinplot(x='run', y='cycles', data=data, palette="vlag")
    sns.swarmplot(x='run', y='cycles', data=data, size=2, color='.3', linewidth=0);
    #plt.show()

    plt.figure(3, figsize=(16, 8), dpi=300)
    load_latency = data[data['section'] == 0]
    load_latency = load_latency.explode('snitch_load_latency').infer_objects()
    # df = sns.load_dataset('tips')
    # sns.violinplot(x='day', y="total_bill", hue="smoker", data=df, palette="Pastel1")
    sns.violinplot(x='core', y='snitch_load_latency', hue='run',
        data=load_latency[load_latency['core'] < 4], palette="vlag")
#    sns.boxplot(x='core', y='snitch_load_latency', hue='run',
#        data=load_latency[load_latency['core'] < 4],
#        whis=[0,100], palette='vlag')
#    sns.swarmplot(x='core', y='snitch_load_latency', hue='run',
#        data=load_latency[load_latency['core'] < 1], size=2, color='.3',
#        linewidth=0)

    # plt.figure(3)
    # ax = runtime.set_index(['section','run']).unstack('run').plot.bar()
    # ax.set_ylabel('Runtime [cycles]')
    # plt.show()

    speedup = get_speedup(runtime)
    print(speedup)
    with pd.option_context('display.max_rows', None, 'display.max_columns', None):
        print(runtime.drop(columns='cycles').set_index(['section', 'run']).unstack('run'))
        print(speedup)

    plt.figure(4)
    sns.heatmap(speedup, annot=True, linewidth=.5)

    plt.show()
    exit(0)

    X = np.arange(4)
    fig = plt.figure()
    ax = fig.add_axes([0, 0, 1, 1])
    ax.bar(X + 0.00, data[0], color='b', width=0.25)
    ax.bar(X + 0.25, data[1], color='g', width=0.25)
    ax.bar(X + 0.50, data[2], color='r', width=0.25)

    # Plot the data.
    font = FontProperties()
    font.set_size('larger')
    labels = ["Best Cost Function"]
    plt.figure(figsize=(12.5, 6))
    plt.plot(range(len(data["best"])), data["best"], label=labels[0])
    plt.xlabel("Iteration #")
    plt.ylabel("Value [-]")
    plt.legend(loc="best", prop=font)
    plt.grid()

    if args.output is None:
        plt.show()
    else:
        plt.savefig(args.output)

    print(data["solution"])
    print(data["best"][-1])


if __name__ == '__main__':
    sys.exit(main())
