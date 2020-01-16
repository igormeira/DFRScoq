#!/usr/bin/env python
# -*- coding: utf-8 -*-

def generate_table_data(trace):
    table = [["Time", "I: the_voltage", "I: the_turn_indicator_lever", "I: the_emergency_flashing", "O: the_indication_lights", "O: the_flashing_mode", "O: the_flashing_timer"],
             ["0", "0", "0", "0", "2", "2", "0"]]
    trs = trace.split("[(")
    time = 0
    tvoValue = "0"
    ttilValue = "0"
    tefValue = "0"
    tilValue = "2"
    tfmValue = "2"
    tftValue = "0"
    for index, t in enumerate(trs):
        if "the_voltage" in t:
            time = time + 1
            trbBegin = t.find("the_voltage, i ")
            trbEnd = t.find("); (the_turn_indicator_lever")
            tvoValue = t[trbBegin+15:trbEnd]
            if "the_turn_indicator_lever" in t:
                tbbBegin = t.find("the_turn_indicator_lever, i ")
                tbbEnd = t.find("); (the_emergency_flashing")
                ttilValue = t[tbbBegin+28:tbbEnd]
            if "the_emergency_flashing" in t:
                twpBegin = t.find("the_emergency_flashing, i ")
                twpEnd = t.find(")])")
                tefValue = t[twpBegin+26:twpEnd]
            if (index+1 < len(trs)) and ("the_indication_lights" not in trs[index+1]) and ("the_flashing_mode" not in trs[index+1]) and ("the_flashing_timer" not in trs[index+1]):
                item = ["%d" % (time), tvoValue, ttilValue,
                        tefValue, tilValue, tfmValue, tftValue]
                table.append(item)
	    #elif (index+1 == len(trs)):
		#item = ["%d" % (time), tvoValue, ttilValue,
                 #       tefValue, tilValue, tfmValue, tftValue]
                #table.append(item)
        elif ("the_indication_lights" in t) or ("the_flashing_mode" in t) or ("the_flashing_timer" in t):
            if "the_indication_lights" in t:
                tsimBegin = t.find("the_indication_lights, i ")
                tsimEnd = t.find(")],")
                tilValue = t[tsimBegin+25:tsimEnd]
                if len(tilValue) > 5:
                    tsimEnd = t.find(");")
                    tilValue = t[tsimBegin+25:tsimEnd]
            if "the_flashing_mode" in t:
                tomBegin = t.find("the_flashing_mode, i ")
                tomEnd = t.find(")],")
                tfmValue = t[tomBegin+21:tomEnd]
                if len(tfmValue) > 5:
                    tomEnd = t.find(");")
                    tfmValue = t[tomBegin+21:tomEnd]
            if "the_flashing_timer" in t:
                tpmBegin = t.find("the_flashing_timer, n ")
                tpmEnd = t.find(")],")
                tftValue = t[tpmBegin+22:tpmEnd]
                if len(tftValue) > 5:
                    tpmEnd = t.find(");")
                    tftValue = t[tpmBegin+22:tpmEnd]
            if (index+1 < len(trs)) and ("the_indication_lights" not in trs[index+1]) and ("the_flashing_mode" not in trs[index+1]) and ("the_flashing_timer" not in trs[index+1]):
                item = ["%d" % (time), tvoValue, ttilValue,
                        tefValue, tilValue, tfmValue, tftValue]
                table.append(item)
    return table
