#!/usr/bin/env python
# -*- coding: utf-8 -*-

from subprocess import call, Popen, PIPE
import datetime
import glob
import csv
import run_samples
import run_csv
import run_analyses

# List of examples you want to run  
examplesToRun = ["vm"]
# List of number of samples you want to run in each replication for each example
samplesNumber = [1]
# Number of replications for example
replications = 1
# Path to SRCIROR
srcirorPath = "/home/ghpc/Documents/srciror" 

def getTime(begin, end):
    formatted_time_begin = float(begin.strftime('%S.%f'))
    formatted_time_end = float(end.strftime('%S.%f'))
    formatted_time_begin = formatted_time_begin + (begin.minute * 60.00)
    formatted_time_end = formatted_time_end + (end.minute * 60.00)
    return (formatted_time_end - formatted_time_begin)

def clear_all(etr):
    pathOutputs = "../src/examples/%s/Outputs/" % (etr)
    examplePath = "../src/examples/%s/" % (etr)
    call("rm *", cwd=pathOutputs, shell=True)
    call("rm -r %sCSV/*" % (examplePath), shell=True)

def writeRFiles(data):
    for etr in examplesToRun:
        code = ""
        vtrs = ""
        columns = "at = c("
        names = "names = c("
        n_columns = 0
        for sn in samplesNumber:
            vector = "l%d <- c(" % (sn)
            vtrs = vtrs + "l%d " % (sn)
            n_columns += 1
            columns = columns + str(n_columns) + ","
            names = names + "\"%dx Sample\"," % (sn)
            for d in data:
                if (d[0] == etr) and (d[1] == sn):
                    vector = vector + "%f," % (d[6])
            vector = vector[0 : (len(vector) - 1)] + ")\n"
            code = code + vector
        vtrs = vtrs.replace(" ", ",")
        code = code + \
            "df = data.frame(%s)\n\npar(cex.lab=1.6)" % (vtrs[0:len(vtrs) - 1]) + \
            "# is for y-axis\npar(cex.axis=1.6) # is for x-axis\n\n"
        
        code = code + "boxplot(df,\n"
        columns = columns[0: (len(columns) - 1)] + "),\n"
        code = code + columns

        names = names[0: (len(names) - 1)] + "),\n"
        code = code + names

        code = code + \
            "xlab = \"Number of calls to Sample\",\nylab = \"Mutation score\",\nylim = c(0, 100)\n)"
        
        f = open("R/%s.R" % (etr), "w+")
        f.write(code)
        f.close


def run():
    analyses = [["Example", "Number of Samples", "Replication Number", "Time Samples",
                 "Valid Traces (%)", "Mutation Time", "Mutation Score (%)"]]

    for etr in examplesToRun:
        clear_all(etr)

        # Samples
        for sn in samplesNumber:
            analyses_rs = run_samples.runSamples(etr, sn, replications)
            for a in analyses_rs:
                analyses.append(a)

        # CSV (test cases from samples)
        print("Start %s csv files") % (etr)
        begin = datetime.datetime.now().time()
        run_csv.runCSV(etr)
        end = datetime.datetime.now().time()
        print("Time CSV: %f \n------------------------" % (getTime(begin, end)))

        # Analyses
        # Copy etr_srciror from DFRS folder to SRCIROR folder
        print("Start %s Analyses") % (etr)
        call("cp -a ../analyses/%s_srciror %s" % (etr, srcirorPath), shell=True)
        results = run_analyses.runAnalyses(etr, srcirorPath)

        # Add analyses time
        for res in results:
            for i, data in enumerate(analyses):
                if (res[0] == data[0]) and (res[1] == data[1]) and (res[2] == data[2]):
                    analyses[i].append(res[3])
                    analyses[i].append(res[4])
        print("End %s Analyses") % (etr)

    # Create CSV with results
    fileName = "Analyses/all_results.csv"
    with open("%s" % (fileName), 'w') as csvFile:
        writer = csv.writer(csvFile)
        writer.writerows(analyses)
    csvFile.close()
    
    # Create R files
    writeRFiles(analyses)

    # Final
    print("DONE!")

run()