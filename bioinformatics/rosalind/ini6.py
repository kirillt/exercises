dict = {}
for w in open("rosalind_ini6.txt").read().split():
    if w in dict.keys():
        dict[w] = dict[w]+1
    else:
        dict[w] = 1

for w in dict.keys():
    print w, dict[w]
