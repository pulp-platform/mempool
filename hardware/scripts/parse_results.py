#!/usr/bin/env python3

# Copyright 2019 ETH Zurich and University of Bologna.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Samuel Riedel, ETH Zurich

import argparse
import ast
import itertools
import sys

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
from matplotlib.font_manager import FontProperties
from matplotlib import rc

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

def boxplot(x, y, data, hue=None, whis=[10,90], fliersize=0.1, palette='vlag', flierprops=None, violin=False):
	if violin:
		ax = sns.violinplot(x=x, y=y, hue=hue, data=data, palette=palette)
	else:
		if flierprops is None:
			flierprops = dict(marker='o', markersize=1, markerfacecolor='none')
		ax = sns.boxplot(x=x, y=y, hue=hue, data=data, whis=whis, fliersize=fliersize, palette=palette, flierprops=flierprops)
	return ax

def main():
	# Parse the arguments.
	parser = argparse.ArgumentParser()
	parser.add_argument("filename", nargs="+", help="File to parse")
	parser.add_argument("--name", nargs="*", help="Names to use in plot")
	parser.add_argument("--sections", action='store_true', help="Use Sections")
	parser.add_argument("--violin", action='store_true', help="Use Violin plots")
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

	load_latency = data[data['section'] == 0]
	load_latency = load_latency.explode('snitch_load_latency').infer_objects()
	load_latency_1tile = load_latency[load_latency['core'] < 8]

	speedup = get_speedup(runtime)
	with pd.option_context('display.max_rows', None, 'display.max_columns', None):
		print(runtime.drop(columns='cycles').set_index(['section', 'run']).unstack('run'))
		print(speedup)

	load_latency_cores = data[data['section'] == 0]
	load_latency_cores = load_latency_cores[['core','run','snitch_load_latency']]
	explode = load_latency_cores.explode('snitch_load_latency').infer_objects()
	info = None
	for run in data['run'].unique():
		statistics = explode[explode['run'] == run]['snitch_load_latency'].describe(percentiles=[0.1,0.25,0.5,0.75,0.9]).to_frame(run)
		if info is None:
			info = statistics
		else:
			info = info.join(statistics)
	print(info)

	# Plotting
	# colorpalette = 'vlag'
	colorpalette = 'RdBu'
	# colorpalette = 'icefire'
	# colorpalette = 'mako_r'
	# colorpalette = 'GnBu_r'
	# colorpalette = 'gnuplot'

	print(plt.style.available)
	plt.style.use('mempool')

	f = plt.figure(1)
	if (args.sections):
		ax = sns.barplot(x='section', y='runtime', hue='run', data=runtime, palette=colorpalette)
		ax.set_xlabel('Section')
	else:
		ax = sns.barplot(x='run', y='runtime', data=runtime, palette=colorpalette)
		ax.set_xlabel('Configuration')
	ax.set_ylabel('Runtime [cycles]')
	ax.set_title('Runtime')
	plt.show()
	f.savefig("Runtime.pdf", bbox_inches='tight')

	runtime['speedup'] = runtime['runtime'][0]/runtime['runtime']
	f = plt.figure(4)
	if (args.sections):
		ax = sns.barplot(x='section', y='speedup', hue='run', data=runtime, palette=colorpalette)
		ax.set_xlabel('Section')
	else:
		ax = sns.barplot(x='run', y='speedup', data=runtime, palette=colorpalette)
		# ax.set_xlabel('Configuration')
		ax.set_xlabel(None)
	ax.set_ylabel('Speedup')
	# ax.set_title('Speedup')
	plt.show()
	f.savefig("Speedup.pdf", bbox_inches='tight')

	f = plt.figure(2)
	if (args.sections):
		ax = boxplot(x='run', y='cycles', data=data, hue='run', palette=colorpalette, violin=args.violin)
		ax.set_xlabel('Section')
	else:
		ax = boxplot(x='run', y='cycles', data=data, palette=colorpalette, violin=args.violin)
		ax.set_xlabel('Configuration')
	ax.set_ylabel('Runtime [cycles]')
	ax.set_title('Runtime')
	plt.show()
	f.savefig("Runtime_Distribution.pdf", bbox_inches='tight')

	f = plt.figure(3)
	ax = boxplot(x='core', y='snitch_load_latency', hue='run', palette=colorpalette,
		data=load_latency_1tile, violin=args.violin)
	ax.set_xlabel('Core')
	ax.set_ylabel('Load Latency [cycles]')
	ax.set_title('Load Latency distribution')
	plt.show()
	f.savefig("LoadLatency.pdf", bbox_inches='tight')

if __name__ == '__main__':
	sys.exit(main())
