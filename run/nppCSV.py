#!/usr/bin/env python
# -*- coding: utf-8 -*-

def generate_table_data(trace):
    table = [["Time", "I: the_reset_button", "I: the_blockage_button", "I: the_water_pressure", "O: the_safety_injection_mode", "O: the_overridden_mode", "O: the_pressure_mode"],
             ["0", "false", "false", "0", "1", "false", "1"]]
    trs = trace.split("[(")
    time = 0
    trbValue = "false"
    tbbValue = "false"
    twpValue = "0"
    tsimValue = "1"
    tomValue = "false"
    tpmValue = "1"
    for index, t in enumerate(trs):
        if "the_reset_button" in t:
            time = time + 1
            trbBegin = t.find("the_reset_button, b ")
            trbEnd = t.find("); (the_blockage_button")
            trbValue = t[trbBegin+20:trbEnd]
            if "the_blockage_button" in t:
                tbbBegin = t.find("the_blockage_button, b ")
                tbbEnd = t.find("); (the_water_pressure")
                tbbValue = t[tbbBegin+23:tbbEnd]
            if "the_water_pressure" in t:
                twpBegin = t.find("the_water_pressure, i ")
                twpEnd = t.find(")])")
                twpValue = t[twpBegin+22:twpEnd]
            if (index+1 < len(trs)) and ("the_safety_injection_mode" not in trs[index+1]) and ("the_overridden_mode" not in trs[index+1]) and ("the_pressure_mode" not in trs[index+1]):
                item = ["%d" % (time), trbValue, tbbValue,
                        twpValue, tsimValue, tomValue, tpmValue]
                table.append(item)
	    #elif (index+1 == len(trs)):
		#item = ["%d" % (time), trbValue, tbbValue,
                 #       twpValue, tsimValue, tomValue, tpmValue]
                #table.append(item)
        elif ("the_safety_injection_mode" in t) or ("the_overridden_mode" in t) or ("the_pressure_mode" in t):
            if "the_safety_injection_mode" in t:
                tsimBegin = t.find("the_safety_injection_mode, i ")
                tsimEnd = t.find(")],")
                tsimValue = t[tsimBegin+29:tsimEnd]
                if len(tsimValue) > 5:
                    tsimEnd = t.find(");")
                    tsimValue = t[tsimBegin+29:tsimEnd]
            if "the_overridden_mode" in t:
                tomBegin = t.find("the_overridden_mode, b ")
                tomEnd = t.find(")],")
                tomValue = t[tomBegin+23:tomEnd]
                if len(tomValue) > 5:
                    tomEnd = t.find(");")
                    tomValue = t[tomBegin+23:tomEnd]
            if "the_pressure_mode" in t:
                tpmBegin = t.find("the_pressure_mode, i ")
                tpmEnd = t.find(")],")
                tpmValue = t[tpmBegin+21:tpmEnd]
                if len(tpmValue) > 5:
                    tpmEnd = t.find(");")
                    tpmValue = t[tpmBegin+21:tpmEnd]
            if (index+1 < len(trs)) and ("the_safety_injection_mode" not in trs[index+1]) and ("the_overridden_mode" not in trs[index+1]) and ("the_pressure_mode" not in trs[index+1]):
                item = ["%d" % (time), trbValue, tbbValue,
                        twpValue, tsimValue, tomValue, tpmValue]
                table.append(item)
    return table
