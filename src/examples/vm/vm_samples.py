from subprocess import call, Popen, PIPE
import datetime


def write_test(file_name, nSamples):
    path = "" + file_name
    file = open(path, 'w')
    file.write(
        "Require Import vm_tests.\n" +
        "Require Import qc_instances.\n\n"
    )

    text = ""
    for i in range(0, nSamples):
        text = text + \
            "Sample (genValidTrace initial_state vm_s_dfrs vm_possibilities 100).\n"
    file.write(text)


def getTime(begin, end):
    formatted_time_begin = float(begin.strftime('%S.%f'))
    formatted_time_end = float(end.strftime('%S.%f'))
    formatted_time_begin = formatted_time_begin + (begin.minute * 60.00)
    formatted_time_end = formatted_time_end + (end.minute * 60.00)
    return (formatted_time_end - formatted_time_begin)

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
        ts_aux = traces[1 : len(traces)-1]
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
    if ("REQ" not in sub_str) and (trace != "") and (trace != "["):
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
    return validated

def compile_test(file_name, eName, samplesNumber):
    write_test(file_name, samplesNumber)
    response = Popen("coqc -R ../../ dfrs vm_samples.v",
                     shell=True, stdout=PIPE)

    data = response.communicate()
    traces = getTraces(data)
    validTraces = getValidTraces(traces)

    text = ""
    for vt in validTraces:
        text = text + vt + " END-TRACE \n\n"
    outputName = eName + "_" + "samples_output.txt"
    cmd = "touch " + outputName
    call(cmd, shell=True)
    path = outputName
    file = open(path, 'w')
    file.write(text)

def create_file(eName):
    fileName = eName + "_" + "samples.v"
    cmd = "touch " + fileName
    call(cmd, shell=True)

    return fileName


exampleName = "vm"
samplesNumber = 10
fileName = create_file(exampleName)

begin = datetime.datetime.now().time()
print(begin)
compile_test(fileName, exampleName, samplesNumber)
end = datetime.datetime.now().time()
print(end)
print("Time: %f" % (getTime(begin, end)))
