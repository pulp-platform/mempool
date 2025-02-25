import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.linear_model import LinearRegression
from sklearn.ensemble import RandomForestRegressor
from sklearn.metrics import mean_squared_error, r2_score
import statsmodels.api as sm

# ---------------------------
# Step 1: Load the Data
# ---------------------------
df = pd.read_csv('cycles_analysis_data.csv')

# Add total_cycles by summing cycles_section1 and cycles_section2
df['total_cycles'] = df['cycles_section1'] + df['cycles_section2']

# Configuration parameters (features) and performance metric (target)
X = df[['noc_req_rd_channel_num', 'noc_req_rdwr_channel_num', 'tile_id_remap', 
        'spm_bank_id_remap', 'noc_router_input_fifo_dep', 'noc_router_output_fifo_dep']]
y = df['total_cycles']

# ---------------------------
# Step 2: Regression Analysis
# ---------------------------
X_with_const = sm.add_constant(X)
model = sm.OLS(y, X_with_const).fit()
print("### Regression Analysis for total_cycles ###")
print(model.summary())

# ---------------------------
# Step 3: Feature Importance with Random Forest
# ---------------------------
rf = RandomForestRegressor(n_estimators=100, random_state=42)
rf.fit(X, y)
importances = rf.feature_importances_

# Plot Feature Importances
plt.figure(figsize=(10, 6))
sns.barplot(x=importances, y=X.columns)
plt.title('Feature Importance (total_cycles)')
plt.xlabel('Importance')
plt.show()

# ---------------------------
# Step 4: Correlation Heatmap
# ---------------------------
plt.figure(figsize=(10, 8))
correlation_matrix = df.corr()
sns.heatmap(correlation_matrix, annot=True, cmap='coolwarm', fmt=".2f")
plt.title('Correlation Matrix')
plt.show()

# ---------------------------
# Step 5: Save Combined Data
# ---------------------------
df.to_csv('cycles_with_total.csv', index=False)
print("\n### Combined data saved to 'cycles_with_total.csv' ###")




# import pandas as pd
# import matplotlib.pyplot as plt
# import seaborn as sns
# from sklearn.linear_model import LinearRegression
# from sklearn.ensemble import RandomForestRegressor
# from sklearn.metrics import mean_squared_error, r2_score
# import statsmodels.api as sm

# # ---------------------------
# # Step 1: Load the Data
# # ---------------------------
# df = pd.read_csv('cycles_analysis_data.csv')

# # Configuration parameters (features) and performance metrics (targets)
# X = df[['noc_req_rd_channel_num', 'noc_req_rdwr_channel_num', 'tile_id_remap', 
#         'spm_bank_id_remap', 'noc_router_input_fifo_dep', 'noc_router_output_fifo_dep']]
# y_section1 = df['cycles_section1']
# y_section2 = df['cycles_section2']

# # ---------------------------
# # Step 2: Regression Analysis (Section 1)
# # ---------------------------
# X_with_const = sm.add_constant(X)
# model_section1 = sm.OLS(y_section1, X_with_const).fit()
# print("### Regression Analysis for cycles_section1 ###")
# print(model_section1.summary())

# # Regression Analysis (Section 2)
# model_section2 = sm.OLS(y_section2, X_with_const).fit()
# print("\n### Regression Analysis for cycles_section2 ###")
# print(model_section2.summary())

# # ---------------------------
# # Step 3: Feature Importance with Random Forest
# # ---------------------------
# # Random Forest for Section 1
# rf_section1 = RandomForestRegressor(n_estimators=100, random_state=42)
# rf_section1.fit(X, y_section1)
# importances_section1 = rf_section1.feature_importances_

# # Random Forest for Section 2
# rf_section2 = RandomForestRegressor(n_estimators=100, random_state=42)
# rf_section2.fit(X, y_section2)
# importances_section2 = rf_section2.feature_importances_

# # Plot Feature Importances
# fig, axs = plt.subplots(1, 2, figsize=(14, 6))

# # Section 1 Feature Importance
# axs[0].barh(X.columns, importances_section1)
# axs[0].set_title('Feature Importance (cycles_section1)')
# axs[0].set_xlabel('Importance')

# # Section 2 Feature Importance
# axs[1].barh(X.columns, importances_section2)
# axs[1].set_title('Feature Importance (cycles_section2)')
# axs[1].set_xlabel('Importance')

# plt.tight_layout()
# plt.show()

# # ---------------------------
# # Step 4: Correlation Heatmap
# # ---------------------------
# plt.figure(figsize=(10, 8))
# correlation_matrix = df.corr()
# sns.heatmap(correlation_matrix, annot=True, cmap='coolwarm', fmt=".2f")
# plt.title('Correlation Matrix')
# plt.show()
