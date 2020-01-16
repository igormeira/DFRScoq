#!/usr/bin/env python
# -*- coding: utf-8 -*-

from subprocess import call, Popen, PIPE
import datetime

def write_samples_file(exampleName, file_name, samplesNumber):
    path = "../src/examples/%s/%s" % (exampleName, file_name)
    file = open(path, 'w')
    file.write(
        "Require Import " + exampleName + "_tests.\n" +
        "Require Import qc_instances.\n\n"
    )

    text = ""
    sampleLine = ""

    if exampleName == "vm":
        sampleLine = "Sample (genValidTrace vm_initial_state VM_s_dfrs vm_possibilities 600).\n"
    #elif (exampleName == "npp") or (exampleName == "tis"):
    #    sampleLine = "Sample (genValidTrace %s_initial_state %s_s_dfrs %s_possibilities 500).\n" % (exampleName, exampleName, exampleName)        
    else:
        sampleLine = "Sample (genValidTrace %s_initial_state %s_s_dfrs %s_possibilities 600).\n" % (
            exampleName, exampleName, exampleName)

    for i in range(0, samplesNumber):
        text = text + sampleLine
    file.write(text)


def getTime(begin, end):
    formatted_time_begin = float(begin.strftime('%S.%f'))
    formatted_time_end = float(end.strftime('%S.%f'))
    formatted_time_begin = formatted_time_begin + (begin.minute * 60.00)
    formatted_time_end = formatted_time_end + (end.minute * 60.00)
    return round((formatted_time_end - formatted_time_begin), 2)


def getTraces(data):
    begin_traces = "[["
    end_traces = "]]"
    allTraces = []
    for line in data:
        if (line is not None):
            if ("QuickChecking" in line):
                samples = line.split("QuickChecking")
                #print(samples)
                for s in samples:
                    if (begin_traces in s):
                        begin = s.find(begin_traces)
                        #print(begin)
                        end = s.find(end_traces)
                        #print(end)
                        traces = s[begin: end+2]
                        allTraces.append(traces)
    #print(allTraces)
    print(len(allTraces))
    finalTraces = []
    for traces in allTraces:
        count = 0
        begin = 0
        end = 0
        ts_aux = traces[1: len(traces)-1]
        first = True
        i = 0
        while i < len(ts_aux):
            if first:
                begin = i
            if count != 0 or first:
                first = False
                if ts_aux[i] == "[":
                    count = count + 1
                if ts_aux[i] == "]":
                    count = count - 1
            if count == 0:
                end = i
                finalTraces.append(ts_aux[begin:end+1])
                i = i+2
                first = True
            i = i+1
    #print((finalTraces))
    return finalTraces


def is_valid_end(trace):
    sub_str = trace[-9:-1]
    if ("REQ" not in sub_str) and (trace != "") and (trace != "[") and (trace != "[]"):
        return True
    else:
        return False


def getValidTraces(traces):
    t = ""
    validated = []
    for trace in traces:
        if trace == traces[-1]:
            t = trace[0: len(trace)-1]
        else:
            t = trace[0: len(trace)]
        if is_valid_end(t):
            validated.append(t)
    print("Traces : %d" % (len(traces)))
    print("Validos: %d" % (len(validated)))
    rate = (float(len(validated)) / float(len(traces))) * 100.00
    print("Rate: %.2f" % (rate))
    return (validated, round(rate, 2))


def compile_samples(exampleName, file_name, rep, samplesNumber):
    pathDotV = "../src/examples/%s/" % (exampleName)
    pathOutputs = "../src/examples/%s/Outputs/" % (exampleName)

    write_samples_file(exampleName, file_name, samplesNumber)
    cmd = "coqc -R ../../ dfrs %s_samples.v" % (exampleName)
    response = Popen(cmd, cwd=pathDotV, shell=True, stdout=PIPE)

    data = response.communicate()
    traces = getTraces(data)
    validTraces = getValidTraces(traces)

    text = ""
    for vt in validTraces[0]:
        text = text + vt + " END-TRACE \n\n"
    outputName = "%s_%d_samples_output_%d.txt" % (exampleName, samplesNumber, rep)
    cmd = "touch " + outputName
    call(cmd, cwd=pathOutputs, shell=True)
    file = open(pathOutputs + outputName, 'w')
    file.write(text)

    return validTraces[1]


def create_file(exampleName):
    pathDotV = "../src/examples/%s/" % (exampleName)
    fileName = exampleName + "_" + "samples.v"
    cmd = "touch " + fileName
    call(cmd, cwd=pathDotV, shell=True)

    return fileName


def runSamples(exampleName, samplesNumber, replicationNumber):
    fileName = create_file(exampleName)
    analyses = []

    for rep in range(1, replicationNumber + 1):
        print("Start %s with %d samples - Rep.: %d") % (exampleName, samplesNumber, rep)
        begin = datetime.datetime.now().time()
        rate = compile_samples(exampleName, fileName, rep, samplesNumber)
        end = datetime.datetime.now().time()
        time = getTime(begin, end)
        print("Time: %f \n------------------------" % (time))
        analyses.append([exampleName, samplesNumber, rep, time, rate])
    
    return analyses
