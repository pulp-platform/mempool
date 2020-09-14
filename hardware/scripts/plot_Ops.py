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
import os
import subprocess

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from matplotlib import colors

git_dir = subprocess.Popen(['git', 'rev-parse', '--show-toplevel'], stdout=subprocess.PIPE).communicate()[0].rstrip().decode('utf-8')
plot_dir = os.path.join(git_dir,'hardware','plots')

plt.style.use(os.path.join(git_dir,'hardware','scripts','mempool.mplstyle'))
# color_map = colors.to_rgb(['midnightblue', 'forestgreen', 'plum'])
# color_map = [(70.0, 137.0, 102.0), (255.0, 176.0, 59.0), (142.0, 40.0, 0.0)]
color_map = [(223, 90, 73), (239, 201, 76), (51, 77, 92)]

for i, c in enumerate(color_map):
	if type(c) == tuple:
		c = tuple([x/255 for x in c])
	color_map[i] = colors.to_rgb(c)


legend = ['Top\_1','Top\_1 scrambled','Top\_4','Top\_4 scrambled','Top\_H','Top\_H scrambled']
labels = ['Matrix Multiplication', '2D Convolution', '8x8 DCT']

mat_runtime = np.array([92722,96425,33688,33720,27152,29679])
con_runtime = np.array([32379,31892,30709,30928,30374,30352])
dct_runtime = np.array([36222,14643,33227,15286,17044,14772])
frequency = 500*10**6

mat_ops = 2*256*8*256
con_ops = (1024-2)*(80-2)*(3*3*3+1)
dct_ops = 2048*16*54

mat_ops_per_s = mat_ops / mat_runtime
con_ops_per_s = con_ops / con_runtime
dct_ops_per_s = dct_ops / dct_runtime

data = np.row_stack((mat_ops_per_s, con_ops_per_s, dct_ops_per_s))
data = np.transpose(data)

# Make OPS from OP/cycle
data = data * frequency / 10**9

x = np.arange(len(labels))  # the label locations
width = 1/(len(legend) + 2) # the width of the bars

fig, ax = plt.subplots()
bars = []
for i, l in enumerate(legend):
	c = color_map[int(np.floor(i/2))]
	if i % 2:
		# c = np.clip(np.array(colors.to_rgba(c))*1.3,0,1)
		c = colors.hsv_to_rgb(np.clip(np.array(colors.rgb_to_hsv(c))*[1,0.7,1.5],0,1))
	bar = ax.bar(x - width*((len(legend)-1)/2) + width*i, data[i], width, label=legend[i], color=c)
	bars.append(bar)

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('GOPS')
ax.set_title('Performance with different topologies')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()


def autolabel(rects):
    """Attach a text label above each bar in *rects*, displaying its height."""
    for rect in rects:
        height = rect.get_height()
        ax.annotate('{}'.format(height),
                    xy=(rect.get_x() + rect.get_width() / 2, height),
                    xytext=(0, 3),  # 3 points vertical offset
                    textcoords="offset points",
                    ha='center', va='bottom')

# for bar in bars:
# 	autolabel(bar)

fig.tight_layout()

plt.show()
fig.savefig(os.path.join(plot_dir,'Benchmarks.pdf'), bbox_inches='tight')
