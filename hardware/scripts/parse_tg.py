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
import os
import sys
import glob
from parse import *
from parse import compile
import re
import pandas as pd

def main():
	# Parse the arguments.
	parser = argparse.ArgumentParser()
	parser.add_argument("dirname", nargs="+", help="Directory to parse")
	parser.add_argument("--file", nargs="*", help="Files to parse")
	args = parser.parse_args()

	print(args)

	# Read data from files specified in arguments
	dirs = []
	for dir in args.dirname:
		dirs += glob.glob("{}/build_*".format(dir))

	p_result = compile("# Latency {:d}\tFrequency {:d}")
	p_cycles = compile("# NUMCYCLES {:d}")
	p_dir_2 = compile("build_{:d}_{:d}")
	p_dir_1 = compile("build_{:d}")

	result = pd.DataFrame()
	for dir in dirs:
		# req_prob = int(re.sub('.*?([0-9]*)$',r'\1',dir))
		req_prob = p_dir_2.parse(os.path.basename(dir))
		if req_prob is None:
			req_prob = int(re.sub('.*?([0-9]*)$',r'\1',dir))
		else:
			req_prob = int(req_prob[0])
		file = "{}/transcript".format(dir)
		try:
			with open(file) as f:
				parsed = False
				requests = 0
				latency = 0
				cycles = 0
				for line in f:
					data = p_result.parse(line)
					if data is not None:
						parsed = True
						requests += data[1]
						latency += (data[0] * data[1])
					elif parsed:
						c = p_cycles.parse(line)
						if c is not None:
							cycles = c[0]
							break
						else:
							print("No NUMCYCLES found after the data")
				if parsed:
					data_points = [req_prob, requests, latency, cycles, requests/cycles/255, latency/requests]
					labels = ['req_prob', 'requests', 'latency', 'cycles', 'throughput', 'avg_latency']
					r = pd.DataFrame([data_points], columns=labels)
					result = pd.concat([result, r])
		# Do something with the file
		except IOError:
			print("{} does not exist".format(file))

	result = result.sort_values(by=['req_prob'])
	print(result)

	# Seq probability
	seq_prob = parse('results_{}/',args.dirname[0])[0]
	# Write results
	result.to_csv('latency_{}'.format(seq_prob), columns= ['req_prob', 'avg_latency'], index=False, sep=' ', header=None)
	result.to_csv('throughput_{}'.format(seq_prob), columns= ['req_prob', 'throughput'], index=False, sep=' ', header=None)

	exit(0)


if __name__ == '__main__':
	sys.exit(main())
