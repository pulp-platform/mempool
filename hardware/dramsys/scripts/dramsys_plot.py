import sqlite3
import pandas as pd
import matplotlib.pyplot as plt
import sys

def plot_power(df_pow, figsize=(8,2)):
	fig, ax = plt.subplots(figsize=figsize)

	ax.plot(df_pow['time']*(10**9),df_pow['AveragePower'],'-', color='blue',label='power')
	ax.set_ylabel('power (mW)')
	ax.set_xlabel('time (ns)')

	plt.show()
	pass

def plot_bw(df_bw, figsize=(8,2)):
	fig, ax = plt.subplots(figsize=figsize)

	# ax.set_ylim([0, 1.0])
	ax.set_ylabel('bandwidth utilization')
	ax.set_xlabel('time (ns)')
	ax.plot(df_bw['Time']*(10**9),df_bw['AverageBandwidth'],'-', color='red',label='bandwidth')

	plt.show()
	pass

if __name__ == '__main__':
	if len(sys.argv) > 1:
		db_file_name = sys.argv[1]
	else:
		print("Error. Give me one argument: the DRAMSys database file path.")
		sys.exit()
		pass

	con = sqlite3.connect(db_file_name)
	df_bw = pd.read_sql_query('SELECT * FROM Bandwidth', con)
	plot_bw(df_bw)
	df_pow = pd.read_sql_query('SELECT * FROM Power', con)
	plot_power(df_pow)
	
