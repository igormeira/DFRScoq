from subprocess import call, Popen, PIPE
import csv
import glob
import vmCSV
import nppCSV
import tisCSV

def create_table(eName, ce, csvData, folder, exampleName):
    fileName = eName + "_" + "table_CE00%d.csv" % (ce)

    with open("../src/examples/%s/CSV/%s/%s" % (exampleName, folder, fileName), 'w') as csvFile:
        writer = csv.writer(csvFile)
        writer.writerows(csvData)
    csvFile.close()

def get_traces(filePath):
    text = ""
    file = open(filePath, 'r')
    for line in file:
        text = text + line
    file.close()

    traces = text.split(" END-TRACE \n\n")
    return traces[:-1]

def mkdir(fileName, exampleName):
    begin = fileName.find("%s_" % exampleName)
    end = -4
    name = fileName[begin: end]

    call("mkdir %s" % (name), cwd="../src/examples/%s/CSV/" %
         (exampleName), shell=True)

    return name


def runCSV(exampleName):
    dir_path = "../src/examples/%s/Outputs/*.txt" % (exampleName)
    files = glob.glob(dir_path)
    csvData = ""

    for f in files:
        traces = get_traces(f)
        print(f)
        folder = mkdir(f, exampleName)
        ce = 1
        for t in traces:
            if exampleName == "vm":
                csvData = vmCSV.generate_table_data(t)
            elif exampleName == "npp":
                csvData = nppCSV.generate_table_data(t)
            elif exampleName == "tis":
                csvData = tisCSV.generate_table_data(t)
            create_table(exampleName, ce, csvData, folder, exampleName)
            #print(exampleName + "_" + "table_CE00%d.csv" % (ce))
            ce = ce + 1
