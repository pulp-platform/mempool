def average_manhattan_distance_mesh(N, M):
    total_distance = 0
    num_points = N * M
    
    for i1 in range(N):
        for j1 in range(M):
            for i2 in range(N):
                for j2 in range(M):
                    total_distance += abs(i1 - i2) + abs(j1 - j2)
    
    average_distance = total_distance / (num_points ** 2)
    return average_distance

def average_manhattan_distance_torus(N, M):
    total_distance = 0
    num_points = N * M
    
    for i1 in range(N):
        for j1 in range(M):
            for i2 in range(N):
                for j2 in range(M):
                    distance = min(abs(i1 - i2), N - abs(i1 - i2)) + min(abs(j1 - j2), M - abs(j1 - j2))
                    total_distance += distance
    
    average_distance = total_distance / (num_points ** 2)
    return average_distance

def average_distance_point_mesh(N, M, i1, j1):
    total_distance = 0
    num_points = N * M
    
    for i2 in range(N):
        for j2 in range(M):
            total_distance += abs(i1 - i2) + abs(j1 - j2)
    
    average_distance = total_distance / num_points
    return average_distance

def average_distance_point_torus(N, M, i1, j1):
    total_distance = 0
    num_points = N * M
    
    for i2 in range(N):
        for j2 in range(M):
            distance = min(abs(i1 - i2), N - abs(i1 - i2)) + min(abs(j1 - j2), M - abs(j1 - j2))
            total_distance += distance
    
    average_distance = total_distance / num_points
    return average_distance

# Example usage
N, M = 4, 4  # Example dimensions
i1, j1 = 0, 0  # Example point
i2, j2 = 1, 1  # Example point

average_distance_mesh = average_distance_point_mesh(N, M, i1, j1)
average_distance_torus = average_distance_point_torus(N, M, i1, j1)

print(average_distance_mesh, average_distance_torus)

average_distance_mesh = average_distance_point_mesh(N, M, i2, j2)
average_distance_torus = average_distance_point_torus(N, M, i2, j2)

print(average_distance_mesh, average_distance_torus)


# Example usage
average_distance_mesh = average_manhattan_distance_mesh(N, M)
average_distance_torus = average_manhattan_distance_torus(N, M)

print(average_distance_mesh, average_distance_torus)
