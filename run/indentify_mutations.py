#!/usr/bin/env python
# -*- coding: utf-8 -*-

from itertools import izip
from subprocess import call, Popen, PIPE
import glob
import csv

srcirorPath = "/home/igormeira/Documents/Git/srciror"
example = "vm"
numberOfMutants = 287

# Compare reference with mutations
# Get line diff
def mutations(baseFile, mutantFile):
    lineN = 0
    with open(baseFile) as base, open(mutantFile) as mutant:
        for lineB, lineM in izip(base, mutant):
            lineB = lineB.strip()
            lineM = lineM.strip()
            lineN += 1
            if (lineB != lineM) and (lineB != "") and (lineM != ""):
                mutation = [lineN, lineB, lineM]
                return mutation
    base.close()
    mutant.close()

def generateCSV(csvData):
    fileName = "%s_mutation_analyses.csv" %(example)

    with open("%s_mutation_analyses.csv" % (example), 'w') as csvFile:
        writer = csv.writer(csvFile)
        writer.writerows(csvData)
    csvFile.close()

def run():
    csvData = [["Line Number", "Base File", "Mutated File"]]
    baseFile = srcirorPath + "/%s_srciror/mutants/%s.c" %(example, example)
    for n in range(1, numberOfMutants + 1):
        mutantFile = srcirorPath + "/%s_srciror/mutants/%s%d.c" %(example, example, n)
        mutation = mutations(baseFile, mutantFile)
        csvData.append(mutation)
    generateCSV(csvData)

run()

# Run with equivalent mutants
def runEquiv():
    baseFile = srcirorPath + "/%s_srciror/mutants/%s.c" %(example, example)
    file = open(baseFile, "r")
    content = file.read()
    for n in range(1, numberOfMutants + 1):
        mutantFile = srcirorPath + "/%s_srciror/mutants/%s%d.c" %(example, example, n)
        fm = open(mutantFile, "w")
        fm.write(content)
        print("DONE: %s" %(mutantFile))
    call("./run.sh", cwd="%s/%s_srciror/" %
                             (srcirorPath, example), shell=True, stdout=PIPE)

#runEquiv()
