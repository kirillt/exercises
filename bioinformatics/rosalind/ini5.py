import sys

file = open("rosalind_ini5.txt")
i = 1
for line in file:
    if i % 2 == 0:
        sys.stdout.write(line)
    i = i+1
