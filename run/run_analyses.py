#!/usr/bin/env python
# -*- coding: utf-8 -*-

from subprocess import call, Popen, PIPE
import datetime
import glob

def rewrite_main(srcirorPath, exampleName, tcPath):
    mainPath = "%s/%s_srciror/main.c" % (srcirorPath, exampleName)
    tcs = glob.glob(tcPath + "*.csv")
    filesNumber = len(tcs)
    text = ""

    file = open(mainPath, 'r')
    for line in file:
        if "#define NUM_TCs " in line:
            text = text + "#define NUM_TCs %d\n" % (filesNumber)
        else:
            text = text + line
    file.close()

    file = open(mainPath, 'w')
    file.write(text)
    file.close()


def rewrite_renamer(srcirorPath, exampleName, mutantsPath):
    renamerPath = "%s/%s_srciror/renamer.java" % (srcirorPath, exampleName)
    mutants = glob.glob(mutantsPath + "*.c")
    mutantsNumber = len(mutants) - 1
    text = ""

    file = open(renamerPath, 'r')
    for line in file:
        if "	private static int MUTANTS = " in line:
            text = text + \
                "	private static int MUTANTS = %d;\n" % (mutantsNumber)
        else:
            text = text + line
    file.close()

    file = open(renamerPath, 'w')
    file.write(text)
    file.close()

    call("javac renamer.java", cwd="%s/%s_srciror/" %
         (srcirorPath, exampleName), shell=True)

def getTime(lines):
    start = float(int(lines[0])) / 1.00
    end = float(int(lines[1])) / 1.00
    return end - start

def killedMutants(srcirorPath, ename):
    renamerPath = "%s/%s_srciror/output.txt" % (srcirorPath, ename)
    passed = 0.000000000000
    killed = 0.000000000000

    file = open(renamerPath, 'r')
    for line in file:
	if ("Passed" in line):
            passed += 1.000000000000
        elif ("Failed" in line):
            killed += 1.000000000000

    file.close()
    
    total = passed + killed
    result = (killed / total) * 100.000000000000
    return round(result, 10)

def getResults(srcirorPath, ename, fname, data):
    lines = data[0].split("\n")
    time = getTime(lines)

    index_samples_begin = fname.find("_") + 1
    index_samples_end = fname.find("_samples_")
    n_samples = fname[index_samples_begin : index_samples_end]

    index_rep_begin = fname.find("output_") + 7
    index_rep_end = len(fname) - 1
    n_rep = fname[index_rep_begin : index_rep_end]

    m = killedMutants(srcirorPath, ename)

    analyses = [ename, int(n_samples), int(n_rep), time, m]
    return analyses


def runAnalyses(exampleName, srcirorPath):
    tcPath = "%s/%s_srciror/testcases/" % (srcirorPath, exampleName)
    csvPath = "../src/examples/%s/CSV/" % (exampleName)
    mutantsPath = "%s/%s_srciror/mutants/" % (srcirorPath, exampleName)
    folders = glob.glob(csvPath + "**/")
    results = []
    mutated = False
    for folder in folders:
        # Clear test cases
        call("rm *.csv", cwd=tcPath, shell=True)

        # Copy all test data (csv files) into the testcases directory (ExampleName_srciror/testcases)
        call("cp -a %s/. %s" % (folder, tcPath), shell=True)

        # Open main.c, and change "NUM_TCs" (line 2) to the number of csv files
        rewrite_main(srcirorPath, exampleName, tcPath)
        
	# Rename test casess
        call("javac renameTCs.java", cwd="%s/%s_srciror/" %
             (srcirorPath, exampleName), shell=True)
        call("java renameTCs", cwd="%s/%s_srciror/" %
             (srcirorPath, exampleName), shell=True)

        # Run main as test
        call("gcc main.c -o main", cwd="%s/%s_srciror/" %
             (srcirorPath, exampleName), shell=True)
        response = Popen("./main", cwd="%s/%s_srciror/" %
                         (srcirorPath, exampleName), shell=True, stdout=PIPE)
        response_data = str(response.communicate())
        print response_data

        if ("Failed" in response_data):
            print("Something is wrong!!!")
        elif ("Passed" in response_data):
            print("All good!!!")

	    if (mutated != True):
		print("Starting mutation")
		# Clear mutants
		call("rm -r %s*.c" % (mutantsPath), shell=True)

		# Copy vars file to mutants folder
		call("cp -a %s/%s_srciror/reference/%s_vars.c %s" %
		 (srcirorPath, exampleName, exampleName, mutantsPath), shell=True)

		# Copy reference file to mutants folder
		call("cp -a %s/%s_srciror/reference/%s.c %s" %
		 (srcirorPath, exampleName, exampleName, mutantsPath), shell=True)

		# Run mutateSRC.sh to generate mutants for the *.c file in /mutants 
		# (ExampleName_srciror/mutants)
		call("cd %s && ./mutateSRC.sh" % (mutantsPath), shell=True)

		# Open renamer.java, and change "MUTANTS" (line 12) to the number of generated mutants AND
		# Compile renamer.java (javac renamer.java)
		rewrite_renamer(srcirorPath, exampleName, mutantsPath)
		mutated = True

            # Run renamer.class (java renamer)
            call("java renamer", cwd="%s/%s_srciror/" % (srcirorPath, exampleName), shell=True)

            # Copy again the _vars file
            call("cp -a %s/%s_srciror/reference/%s_vars.c %s" %
                 (srcirorPath, exampleName, exampleName, mutantsPath), shell=True)            

            # Run the script run.sh to perform mutant-based strength analysis (performance data printed to the console)
            response = Popen("./run.sh", cwd="%s/%s_srciror/" %
                             (srcirorPath, exampleName), shell=True, stdout=PIPE)
            data = response.communicate()
            result = getResults(srcirorPath, exampleName, folder, data)
            results.append(result)
	print(folder)
    return results

#r = runAnalyses("vm", "/home/igormeira/Documents/Git/srciror")
#print(r)
