import urllib2
import re, string

pattern = re.compile('.*GO.*P:(.*);')

def list_bioprocesses(id):
    url = "http://www.uniprot.org/uniprot/"+ id +".txt"
    for l in urllib2.urlopen(url):
        m = pattern.search(l[:-1])
	if m != None: print m.group(1)

id = open("rosalind_dbpr.txt").read()[:-1]
list_bioprocesses(id)
