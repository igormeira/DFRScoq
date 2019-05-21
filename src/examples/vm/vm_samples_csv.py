from subprocess import call, Popen, PIPE
import csv


def create_table(eName, ce, csvData):
    fileName = eName + "_" + "table_CE00%d.csv" % (ce)

    with open("CSV/" + fileName, 'w') as csvFile:
        writer = csv.writer(csvFile)
        writer.writerows(csvData)
    csvFile.close()

def generate_table_data(trace):
    table = [["Time", "The_Coin_Sensor", "The_Coffee_Request_Button", "The_System_Mode", "The_Coffee_Machine_Output", "The_Request_Timer"],
             ["0", "false", "false", "1", "0", "0"]]
    trs = trace.split("[(")
    time = 0
    tcsValue = "false"
    tcrValue = "false"
    tsmValue = "1"
    tcmoValue = "0"
    trtValue = "0"
    for index, t in enumerate(trs):
        if "the_coin_sensor" in t:
            time = time + 1
            tcsBegin = t.find("the_coin_sensor, b ")
            tcsEnd = t.find(");")
            tcsValue = t[tcsBegin+19:tcsEnd]
            if "the_coffee_request_button" in t:
                tcrbBegin = t.find("the_coffee_request_button, b ")
                tcrbEnd = t.find(")]),")
                tcrValue = t[tcrbBegin+29:tcrbEnd]
            if (index+1 < len(trs)) and ("the_system_mode" not in trs[index+1]) and ("the_request_timer" not in trs[index+1]) and ("the_coffee_machine_output" not in trs[index+1]):
                item = ["%d" % (time), tcsValue, tcsValue,
                        tsmValue, tcmoValue, trtValue]
                table.append(item)
        elif ("the_system_mode" in t) or ("the_request_timer" in t) or ("the_coffee_machine_output" in t):
            if "the_system_mode" in t:
                tsmBegin = t.find("the_system_mode, i ")
                tsmEnd = t.find(")],")
                tsmValue = t[tsmBegin+19:tsmEnd]
                if len(tsmValue) > 5:
                    tsmEnd = t.find(");")
                    tsmValue = t[tsmBegin+19:tsmEnd]
            if "the_request_timer" in t:
                trtBegin = t.find("the_request_timer, n ")
                trtEnd = t.find(")],")
                trtValue = t[trtBegin+21:trtEnd]
                if len(trtValue) > 5:
                    trtEnd = t.find(");")
                    trtValue = t[trtBegin+21:trtEnd]
            if "the_coffee_machine_output" in t:
                tcmoBegin = t.find("the_coffee_machine_output, i ")
                tcmoEnd = t.find(")],")
                tcmoValue = t[tcmoBegin+29:tcmoEnd]
                if len(tcmoValue) > 5:
                    tcmoEnd = t.find(");")
                    tcmoValue = t[tcmoBegin+29:tcmoEnd]
            if (index+1 < len(trs)) and ("the_system_mode" not in trs[index+1]) and ("the_request_timer" not in trs[index+1]) and ("the_coffee_machine_output" not in trs[index+1]):
                item = ["%d" % (time), tcsValue, tcrValue,
                        tsmValue, tcmoValue, trtValue]
                table.append(item)
    return table

def get_traces():
    text = ""
    file = open('vm_samples_output.txt', 'r')
    for line in file:
        text = text + line
    file.close()

    traces = text.split(" END-TRACE \n\n")
    return traces[:-1]


def compile_test(example_name):
    traces = get_traces()
    #print(traces)
    ce = 1
    for t in traces:
        csvData = generate_table_data(t)
        create_table(example_name, ce, csvData)
        print(example_name + "_" + "table_CE00%d.csv" % (ce))
        ce = ce + 1


exampleName = "vm"
compile_test(exampleName)
