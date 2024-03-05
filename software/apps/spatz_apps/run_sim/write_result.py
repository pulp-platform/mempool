import sys

def extract_uart_lines(input_file_path, output_file_path):
    with open(input_file_path, 'r') as input_file:
        with open(output_file_path, 'a') as output_file:  # Open in append mode
            # Write three empty lines before appending new content
            output_file.write('\n\n\n')
            for line in input_file:
                if '[UART]' in line:
                    output_file.write(line)

if __name__ == "__main__":
    if len(sys.argv) == 3:
        input_file_path = sys.argv[1]
        output_file_path = sys.argv[2]
        extract_uart_lines(input_file_path, output_file_path)
    else:
        print("Usage: python3 script.py <input_file> <output_file>")
