for n in range(1,100):
    current_max = -1
    new_max = 0
    i = 0
    while current_max < new_max:
        current_max = new_max
        new_max = min(2**(n-i), 2**(2**i)-1)
        i += 1
    print(n,current_max)
