def fibonacci_of(n):
    if n == 0:
        return n
    if n == 1:
        return n
    return fibonacci_of(n - 1) + fibonacci_of(n - 2)

print(fibonacci_of(35))
