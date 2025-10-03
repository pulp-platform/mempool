# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>

import numpy as np
import torch 
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
import argparse
import dump_utils as dump
import os

# COMPUTE:
# Z[m_size, k_size] = ( X[m_size, n_size] max W[n_size, k_size] ) + Y[m_size, k_size]

#Visualize data with more precision
torch.set_printoptions(precision=10, sci_mode=False)
torch.random.manual_seed(1337)

parser = argparse.ArgumentParser("mm Operation Test")
parser.add_argument( '--m_size', type=int, default=3 )
parser.add_argument( '--n_size', type=int, default=3 )
parser.add_argument( '--k_size', type=int, default=3 )
parser.add_argument( '--file_name', type=str, default='net_parameters.h')
parser.add_argument( '--inc_dir', type=str)
parser.add_argument( '--txt_dir', type=str)
parser.add_argument( '--transpose', type=int, default=0)
args = parser.parse_args()

transpose = args.transpose
# Network parameters
m_size = args.m_size
n_size = args.n_size
k_size = args.k_size

assert (n_size % 2 == 0), "Number of columns must be even for packing fp16 to 32-bit"

def pack_fp16(tensor):
  t_int16 = tensor.contiguous().view(torch.int16)
  new_shape = tensor.shape[:-1] + (tensor.shape[-1] // 2, 2)
  t_int16_pairs = t_int16.view(new_shape)
  lower = t_int16_pairs[..., 0].to(torch.int32) & 0xFFFF
  upper = t_int16_pairs[..., 1].to(torch.int32) & 0xFFFF
  packed = lower | (upper << 16)
  return packed

def unpack_fp16(packed_val):
  lower_int = int(packed_val.item() & 0xFFFF)
  upper_int = int((packed_val.item() >> 16) & 0xFFFF)
  lower_fp16 = torch.tensor([lower_int], dtype=torch.int16).view(torch.float16)[0]
  upper_fp16 = torch.tensor([upper_int], dtype=torch.int16).view(torch.float16)[0]
  return lower_fp16, upper_fp16


def pack_fp16_axis0(tensor):
  N = tensor.shape[0]
  assert N % 2 == 0, "Number of rows must be even for packing"
  t_int16 = tensor.contiguous().view(torch.int16)
  new_shape = (N // 2, 2) + tensor.shape[1:]
  t_int16_pairs = t_int16.view(new_shape)
  lower = t_int16_pairs[:, 0].to(torch.int32) & 0xFFFF
  upper = t_int16_pairs[:, 1].to(torch.int32) & 0xFFFF
  packed = lower | (upper << 16)
  return packed

f = open(args.file_name, "w")

# We want to perform a GEMM, of the kind Z = Y + X*W
# Test Matrices
X = torch.rand(m_size, n_size).float()
W = torch.rand(n_size, k_size).float()
Y = torch.rand(m_size, k_size).float()
Z = torch.rand(m_size, k_size).float()


print("\nInput Data: ")
print("\nX is: ", X, X.shape, X.dtype)
f.write('fp32 X[IN_CH*MID_CH] = {'+dump.tensor_to_string(X)+'};\n')

print("\nW is: ", W, W.shape, W.dtype)
f.write('fp32 W[MID_CH*OUT_CH] = {'+dump.tensor_to_string(W)+'};\n')

print("\nY is: ", Y, Y.shape, Y.dtype)
f.write('fp32 Y[MID_CH*OUT_CH] = {'+dump.tensor_to_string(Y)+'};\n')

print("\nComputing matrix multiplication with FP16 mult..")
X_half = X.half()
W_half = W.half()
X_packed = pack_fp16(X_half)
W_packed = pack_fp16_axis0(W_half)
print("\nPacked X (32-bit words): ", X_packed, X_packed.shape, X_packed.dtype)
print("\nPacked W (32-bit words): ", W_packed, W_packed.shape, W_packed.dtype)

product = torch.zeros((m_size, m_size), dtype=torch.float32)

for i in range(m_size): 
  for j in range(k_size): 
    dot_sum = 0.0
    for p in range(n_size // 2):
      lower_x, upper_x = unpack_fp16(X_packed[i, p])
      lower_w, upper_w = unpack_fp16(W_packed[p, j])
      dot_sum += lower_x * lower_w + upper_x * upper_w
    product[i, j] = dot_sum

print("\nProduct from packed multiplications is: ", product, product.shape, product.dtype)
Z = torch.add(input = Y, other = product)
print("\nZ | gemm packed is: ", Z, Z.shape, Z.dtype)
f.write('fp32 Z[IN_CH*OUT_CH] = {'+dump.tensor_to_string(Z)+'};\n')
f.close()

Z_golden = torch.add(input = Y, other = torch.mm(input = X, mat2 = W))
print("\nZ_golden | gemm packed is: ", Z_golden, Z_golden.shape, Z_golden.dtype)
if (np.allclose(Z, Z_golden, rtol=1e-2, atol=1e-2)): print("\nGolden model and packed model are equivalent.")
else: print("\nGolden model and packed model are not equivalent.")

# Matrices conversion to hexadecimal and txt files generation
txt_path = args.txt_dir
for f in os.listdir(txt_path): os.remove(os.path.join(txt_path, f))
f_x = open(''+txt_path+'/x_input.txt', "w")
for i in range(m_size):
  for j in range (n_size):
    x_bin = bin(np.float16(X[i][j]).view('H'))[2:].zfill(16)
    x_hex = hex(int(x_bin, 2))[2:]
    f_x.write(x_hex)
    f_x.write(' ')
  f_x.write("\n")
f_x.close()

f_w = open(''+txt_path+'/w_input.txt', "w")
for i in range(n_size):
  for j in range (k_size):
    w_bin = bin(np.float16(W[i][j]).view('H'))[2:].zfill(16)
    w_hex = hex(int(w_bin, 2))[2:]
    f_w.write(w_hex)
    f_w.write(' ')
  f_w.write("\n")
f_w.close()

f_y = open(''+txt_path+'/y_input.txt', "w")
for i in range(m_size):
  for j in range (k_size):
    y_bin = bin(np.float32(Y[i][j]).view('I'))[2:].zfill(32)
    y_hex = hex(int(y_bin, 2))[2:]
    f_y.write(y_hex)
    f_y.write(' ')
  f_y.write("\n")
f_y.close()

f_z = open(''+txt_path+'/z_output.txt', "w")
for i in range(m_size):
  for j in range (k_size):
    z_bin = bin(np.float32(Z[i][j]).view('I'))[2:].zfill(32)
    z_hex = hex(int(z_bin, 2))[2:]
    f_z.write(z_hex)
    f_z.write(' ')
  f_z.write("\n")
f_z.close()

in_rows  = str(m_size)
in_cols  = str(n_size)
out_cols = str(k_size)
x_dim  = str(m_size*n_size)
w_dim  = str(n_size*k_size)
y_dim  = str(m_size*k_size)
z_dim  = str(m_size*k_size)
out_int  = str(int(m_size*k_size/2))

header   = ' /* Header file generated by O-POPE Golden Model */\n'

# ------------------------------------------------------------------------------------#
#               Header files generation                 #
# ------------------------------------------------------------------------------------#


# Packed 2 16-bits values into 32-bit value only support multiples of 2

# Path to the genereted files
inc_path = args.inc_dir
for f in os.listdir(inc_path):
  os.remove(os.path.join(inc_path, f))

new_in_rows = str(m_size)
new_in_cols = str(n_size//2)
new_out_cols = str(k_size)
new_x_dim = str(m_size*n_size//2)
new_w_dim = str(n_size//2*k_size)
new_y_dim = str(m_size*k_size)
new_z_dim = str(m_size*k_size)
new_out_int = str(int(m_size*k_size))

if (transpose == 1):
  X_packed = X_packed.T

  f_x = open(os.path.join(inc_path, 'x_input.h'), "w")
  f_x.write(header)
  f_x.write('uint32_t x_inp [' + new_x_dim + '] __attribute__((section(".x_buffer"))) = {\n')
  total_values = X_packed.numel() 
  value_index = 0
  for i in range(X_packed.shape[0]):
    for j in range(X_packed.shape[1]):
      x_val = int(X_packed[i, j].item())
      value_index += 1
      if value_index == total_values: f_x.write('0x' + hex(x_val)[2:] + ' ')
      else: f_x.write('0x' + hex(x_val)[2:] + ', ')
    f_x.write("\n")
  f_x.write("};")
  f_x.close()


  f_x2 = open(os.path.join(inc_path, 'x_2D.h'), "w")
  f_x2.write(header)
  f_x2.write('uint32_t x_inp_2D [' + new_in_cols + '][' + new_in_rows + '] = {\n')
  value_index = 0
  for i in range(X_packed.shape[0]):
    for j in range(X_packed.shape[1]):
      x_val = int(X_packed[i, j].item())
      value_index += 1
      if value_index == total_values: f_x2.write('0x' + hex(x_val)[2:] + ' ')
      else: f_x2.write('0x' + hex(x_val)[2:] + ', ')
    f_x2.write("\n")
  f_x2.write("};")
  f_x2.close()
else: 
  f_x = open(os.path.join(inc_path, 'x_input.h'), "w")
  f_x.write(header)
  f_x.write('uint32_t x_inp [' + new_x_dim + '] __attribute__((section(".x_buffer"))) = {\n')
  total_values = X_packed.numel() 
  value_index = 0
  for i in range(X_packed.shape[0]):
    for j in range(X_packed.shape[1]):
      x_val = int(X_packed[i, j].item())
      value_index += 1
      if value_index == total_values: f_x.write('0x' + hex(x_val)[2:] + ' ')
      else: f_x.write('0x' + hex(x_val)[2:] + ', ')
    f_x.write("\n")
  f_x.write("};")
  f_x.close()


  f_x2 = open(os.path.join(inc_path, 'x_2D.h'), "w")
  f_x2.write(header)
  f_x2.write('uint32_t x_inp_2D [' + new_in_rows + '][' + new_in_cols + '] = {\n')
  value_index = 0
  for i in range(X_packed.shape[0]):
    for j in range(X_packed.shape[1]):
      x_val = int(X_packed[i, j].item())
      value_index += 1
      if value_index == total_values: f_x2.write('0x' + hex(x_val)[2:] + ' ')
      else: f_x2.write('0x' + hex(x_val)[2:] + ', ')
    f_x2.write("\n")
  f_x2.write("};")
  f_x2.close()

f_w = open(os.path.join(inc_path, 'w_input.h'), "w")
f_w.write(header)
f_w.write('uint32_t w_inp [' + new_w_dim + '] __attribute__((section(".w_buffer"))) = {\n')
total_values = W_packed.numel() 
value_index = 0
for i in range(W_packed.shape[0]):
  for j in range(W_packed.shape[1]):
    w_val = int(W_packed[i, j].item())
    value_index += 1
    if value_index == total_values: f_w.write('0x' + hex(w_val)[2:] + ' ')
    else: f_w.write('0x' + hex(w_val)[2:] + ', ')
  f_w.write("\n")
f_w.write("};")
f_w.close()

f_w2 = open(os.path.join(inc_path, 'w_2D.h'), "w")
f_w2.write(header)
f_w2.write('uint32_t w_inp_2D [' + new_in_cols + '][' + new_out_cols + '] = {\n')
value_index = 0
for i in range(W_packed.shape[0]):
  for j in range(W_packed.shape[1]):
    w_val = int(W_packed[i, j].item())
    value_index += 1
    if value_index == total_values: f_w2.write('0x' + hex(w_val)[2:] + ' ')
    else: f_w2.write('0x' + hex(w_val)[2:] + ', ')
  f_w2.write("\n")
f_w2.write("};")
f_w2.close()

# --- Write Y as a flat array ---
f_y = open(inc_path + '/y_input.h', "w")
f_y.write(header)
f_y.write('uint32_t y_inp [' + new_y_dim + '] __attribute__((section(".y_buffer"))) = {\n')
total_values = m_size * k_size
value_index = 0
for i in range(m_size):
  for j in range(k_size):
    y_val = np.array(Y[i][j].item(), dtype=np.float32).view(np.uint32)
    value_index += 1
    if value_index == total_values: f_y.write('0x' + hex(y_val)[2:] + ' ')
    else: f_y.write('0x' + hex(y_val)[2:] + ', ')
  f_y.write("\n")
f_y.write("};")
f_y.close()

# --- Write Y as a 2D array ---
f_y = open(inc_path + '/y_2D.h', "w")
f_y.write(header)
f_y.write('uint32_t y_inp_2D [' + new_in_rows + '][' + new_out_cols + '] = {\n')
value_index = 0
for i in range(m_size):
  for j in range(k_size):
    y_val = np.array(Y[i][j].item(), dtype=np.float32).view(np.uint32)
    value_index += 1
    if value_index == total_values: f_y.write('0x' + hex(y_val)[2:] + ' ')
    else: f_y.write('0x' + hex(y_val)[2:] + ', ')
  f_y.write("\n")
f_y.write("};")
f_y.close()

f_z = open(inc_path + '/z_output.h', "w")
f_z.write(header)
f_z.write('uint32_t z_oup [' + new_z_dim + '] = {\n')
total_values = m_size * k_size
value_index = 0
for i in range(m_size):
  for j in range(k_size):
    z_val = np.array(Z[i][j].item(), dtype=np.float32).view(np.uint32)
    value_index += 1
    if value_index == total_values: f_z.write('0x' + hex(z_val)[2:] + ' ')
    else: f_z.write('0x' + hex(z_val)[2:] + ', ')
  f_z.write("\n")
f_z.write("};")
f_z.close()

# --- Write Z as a 2D array ---
f_z = open(inc_path + '/z_2D.h', "w")
f_z.write(header)
f_z.write('uint32_t z_oup_2D [' + new_in_rows + '][' + new_out_cols + '] = {\n')
value_index = 0
for i in range(m_size):
  for j in range(k_size):
    z_val = np.array(Z[i][j].item(), dtype=np.float32).view(np.uint32)
    value_index += 1
    if value_index == total_values: f_z.write('0x' + hex(z_val)[2:] + ' ')
    else: f_z.write('0x' + hex(z_val)[2:] + ', ')
  f_z.write("\n")
f_z.write("};")
f_z.close()

# Writing tensors' dimensions
f_d = open(''+inc_path+'/tensor_dim.h', "w")
f_d.write(''+header+'')
f_d.write('#ifndef __TENSOR_DIM__\n'            )
f_d.write('#define __TENSOR_DIM__\n\n'          )
f_d.write('#include "archi_opope.h"\n\n'      )
f_d.write('#define M_SIZE  '+new_in_rows+' \n'  )
f_d.write('#define N_SIZE  '+new_in_cols+' \n'  )
f_d.write('#define K_SIZE  '+new_out_cols+'\n'  )
f_d.write('#define COMP_FMT FP16\n'             )
f_d.write('#define MEM_FMT FP32\n'              )
f_d.write('#define FPFORMAT 32\n'               )
f_d.write('#define ERR 0x00ffff \n\n'           )
f_d.write('uint8_t gemm_ops = GEMM; \n'         )
f_d.write('\n#endif\n'                          )
f_d.close()

#------------------------------------------------------------------------------------------#
#                   32-bits parser                                                         #
#------------------------------------------------------------------------------------------#

f_c = open(inc_path + '/golden.h', "w")
f_c.write(header)
f_c.write('uint32_t golden [' + new_out_int + '] __attribute__((section(".golden_output"))) = {\n')

ZFlattened = torch.flatten(Z)
for i in range(ZFlattened.size(dim=-1)):
  val_uint32 = np.array(ZFlattened[i].item(), dtype=np.float32).view(np.uint32)
  f_c.write('0x' + hex(val_uint32)[2:] + ',\n')
f_c.write("};")
f_c.close()