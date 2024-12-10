# Data Generation

Data for mempool applications is generated with the `gendata_header.py` script.
The `gendatalib.py` libaries generate random inputs and a reference golden model for the applications under test.
The application parameters are passed to the script with the `gendata_params.hjson` file.

An example entry follows: `matmul_f32` is the name of MemPool application under test, the `type` refers to numpy precision, the `defines` are application parameters, turned into C constant declarations in the form `#define matrix_M (16)`, the `arrays` encode the C-type and name of input vectors for the application under test.

```
  "matmul_f32": {
    "type": "float32",
    "defines": [
      ("matrix_M", 16)
      ("matrix_N", 16)
      ("matrix_P", 16)
    ]
    "arrays": [
      ("float", "l2_A")
      ("float", "l2_B")
      ("float", "l2_C")
    ]
  }
```

## To test a new application:
If a new application requires to be tested with data generated from a reference golden model:
- Add a new golden model to the existing library `gendatalib.py`.
- Add a golden model function call to the `gendata_header.py`.
- Add a new item in the `gendata_params.hjson` to make function parameters configurable.
