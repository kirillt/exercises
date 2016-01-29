def sum_odd(a,b):
    sum = 0
    for i in range(a,b):
        if i % 2 == 1:
            sum += i
    print sum

sum_odd(4094,8440)
