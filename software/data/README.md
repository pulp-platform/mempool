# Data Generation

Data for mempool applications is generated with the `gendata_header.py` script.
The `gendata_*.py` libaries contain the golden models for the applications under test.
The application parameters are passed to the script by means of the `gendata_params.hjson` file.

## To test a new application:
If a new application requires to be tested with data generated from a reference golden model:
- Add a new golden model to the existing libraries, or create a new one.
- Add a golden model function call to the `gendata_header.py`.
- Add a new item in the `gendata_params.hjson` to make function parameters configurable.
