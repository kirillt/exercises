from Bio import SeqIO

fastq = open("rosalind_tfsq.txt", "r")
fasta = open("out.txt", "w")

x = SeqIO.parse(fastq, "fastq")
SeqIO.write(x, fasta, "fasta")
