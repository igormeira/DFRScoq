#!/usr/bin/env python
# -*- coding: utf-8 -*-

def generate_table_data(trace):
    table = [["Time", "I: The_Coin_Sensor", "I: The_Coffee_Request_Button", "O: The_System_Mode", "O: The_Coffee_Machine_Output", "T: The_Request_Timer"],
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
                tcrbEnd = t.find(")])")
                tcrValue = t[tcrbBegin+29:tcrbEnd]
            if (index+1 < len(trs)) and ("the_system_mode" not in trs[index+1]) and ("the_request_timer" not in trs[index+1]) and ("the_coffee_machine_output" not in trs[index+1]):
                item = ["%d" % (time), tcsValue, tcrValue,
                        tsmValue, tcmoValue, trtValue]
                table.append(item)
	    #elif (index+1 == len(trs)):
		#item = ["%d" % (time), tcsValue, tcrValue,
                 #       tsmValue, tcmoValue, trtValue]
                #table.append(item)
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
