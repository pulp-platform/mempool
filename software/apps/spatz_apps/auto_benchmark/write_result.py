import sys

def extract_uart_lines(input_file_path, output_file_path, config=None):
    with open(input_file_path, 'r') as input_file:
        with open(output_file_path, 'a') as output_file:  # Open in append mode
            # Write three empty lines before appending new content
            output_file.write('\n\n\n')
            # If config is provided, print it before the content
            if config is not None:
                output_file.write(f"Configuration: {config}\n\n")
            for line in input_file:
                if '[UART]' in line:
                    output_file.write(line)

if __name__ == "__main__":
    argc = len(sys.argv)
    if argc == 3:
        input_file_path = sys.argv[1]
        output_file_path = sys.argv[2]
        extract_uart_lines(input_file_path, output_file_path)
    elif argc == 4:
        input_file_path = sys.argv[1]
        output_file_path = sys.argv[2]
        config = sys.argv[3]
        extract_uart_lines(input_file_path, output_file_path, config)
    else:
        print("Usage: python3 script.py <input_file> <output_file> [config]")
