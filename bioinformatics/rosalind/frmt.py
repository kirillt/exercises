from Bio import Entrez
from Bio import SeqIO

ids = open("rosalind_frmt.txt").read()
#ids = "FJ817486 JX069768 JX469983"

Entrez.email = "anonymous@nowhere.space"
handle = Entrez.efetch(db="nucleotide", id=ids, rettype="fasta")
records = list(SeqIO.parse(handle, "fasta"))

result = records[0]
m = len(result.seq)
for r in records:
    l = len(r.seq)
    if l < m:
        m = l
        result = r

print(m)
print('>'+result.description)
print(result.seq)
