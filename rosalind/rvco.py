from Bio.Seq import Seq
from Bio.Alphabet import IUPAC

def revcomp(s):
    r = ""
    for c in s:
        if c == 'A': o = 'T'
        if c == 'T': o = 'A'
        if c == 'G': o = 'C'
        if c == 'C': o = 'G'
        r = o + r
    return r

ls = open("rosalind_rvco.txt", "r").read().splitlines()

n = -1
ds = []
for l in ls:
    if l[0] == '>':
        ds = ds + [""]
        n = n + 1
        continue
    ds[n] = ds[n] + l

c = 0
for d in ds:
    x = Seq(d, IUPAC.unambiguous_dna).reverse_complement()
    y = revcomp(d)
    if x != y:
        print("ERROR")
        break
    if d == x:
        c = c + 1

print(c)
