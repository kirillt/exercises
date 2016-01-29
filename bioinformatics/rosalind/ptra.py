from Bio.Seq import translate

input   = open("rosalind_ptra.txt")
dna     = input.readline()[:-1]
protein = input.readline()[:-1]

xs = [1,2,3,4,5,6,9,10,11,12,13,14,15]
for x in xs:
    t = translate(sequence=dna, table=x)
    while t[-1] == '*':
        t = t[:-1]
    if t == protein:
        print(x)
        break;
