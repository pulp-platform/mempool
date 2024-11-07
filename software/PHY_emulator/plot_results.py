import pandas as pd
import matplotlib.pyplot as plt

# file_path = "BER_20241029_103957.ods"  
file_path = "BER_20241029_231916.ods"  
file_path = "BER_umi_Tx4_Rx4_16QAM_20241031_190314.ods"  

df_ber = pd.read_excel(file_path, engine='odf', index_col=0)

snr_values = [float(snr.split()[0]) for snr in df_ber.index]

plt.figure(figsize=(10, 6))
for precision in df_ber.columns:
    plt.plot(snr_values, df_ber[precision], marker='o', label=f'Precision: {precision}')

plt.xlabel("Eb/No (dB)")
plt.ylabel("BER")
plt.yscale("log")  
plt.title("BER vs SNR for Different Precisions")
plt.legend()
plt.grid(True, which="both", linestyle="--", linewidth=0.5)

plt.show()
