from Bio import SeqIO

def average(xs):
    s = 0
    for x in xs:
        s = s + x
    return s / len(xs)

fastq = open("rosalind_phre.txt", "r");
threshold = int(fastq.readline())
rs = list(SeqIO.parse(fastq, "fastq"))

c = 0
for r in rs:
    if average(r.letter_annotations["phred_quality"]) < threshold:
        c = c+1
print(c)
