import sys

var_map={}
var_num = 1

clause_num = 0

toConvert = sys.argv[1]
boolFile = sys.argv[2]

with open(toConvert) as f:
        lines = f.read().splitlines()

if lines[0].find("(goal") == 0:
    lines = lines[1:]

lines[-1] = lines[-1][:lines[-1].rfind(")")]

line_ct = 0
while line_ct < len(lines):
    lines[line_ct] = lines[line_ct][2:]
    line_ct += 1

largestVarNum = 0
line_ct = 0
while line_ct < len(lines):
    char_ct = 0
    while char_ct < len(lines[line_ct]) and ((char_ct + 1) < len(lines[line_ct])):
        if lines[line_ct][char_ct] == "k" and lines[line_ct][char_ct + 1] == "!":
            currNum = ""
            startsAt = char_ct + 2
            while startsAt < len(lines[line_ct]) and lines[line_ct][startsAt] != " " and lines[line_ct][startsAt] != ")":
                currNum += lines[line_ct][startsAt]
                startsAt += 1
            if int(currNum) > largestVarNum:
                largestVarNum = int(currNum)
        char_ct += 1
    line_ct += 1

largestVarNum += 1

bools = []
with open(boolFile) as f:
        bools = f.read().splitlines()

for b in bools:
    line_ct = 0
    replaced = False
    while line_ct < len(lines):
        lines[line_ct] = lines[line_ct].replace(b, "k!" + str(largestVarNum))
        line_ct += 1
        replaced = True
    if replaced:
        largestVarNum += 1

line_ct = 0
while line_ct < len(lines):
    if lines[line_ct].find("(or") == 0:
        paren_ct = 0
        for c in lines[line_ct]:
            if c == "(":
                paren_ct += 1
            elif c == ")":
                paren_ct -= 1
        if paren_ct != 0:
            lines[line_ct] += ","
    if lines[line_ct][0] == " ":
        if line_ct < (len(lines) - 1):
            if lines[line_ct + 1].find(" ") == 0:
                lines[line_ct] += ","
    line_ct += 1

line_ct = 0
while line_ct < len(lines):
    lines[line_ct] = lines[line_ct].replace("(not ", "Not(")
    lines[line_ct] = lines[line_ct].replace("(or ", "Or(")
    if lines[line_ct].find(" ") != 0:
        lines[line_ct] = lines[line_ct].replace(" ", ", ")
    line_ct += 1

line_ct = 0
while line_ct < len(lines):
    if lines[line_ct].find("Or") == 0:
        if lines[line_ct][-1] == ',':
            local_ct = line_ct + 1 
            to_add = ""
            while lines[local_ct][-1] == ",":
                to_add += lines[local_ct][3:]
                local_ct += 1
            to_add += lines[local_ct][3:]
            lines[line_ct] += to_add
            lines = lines[:(line_ct) + 1] + lines[(local_ct + 1):]
    line_ct += 1

clauses = ""
for line in lines:

    clause = "" 

    if line.find("Or") == 0:
        idx = 0
        while idx < len(line):
            first_Not = line[idx:].find("Not")
            first_variable = line[idx:].find("k")


            if first_Not != -1:
                if first_variable != -1:  
                    if first_Not < first_variable:
                        var_name = line[idx:][first_Not + 6]
                        var_idx = first_Not + 7
                        while line[idx:][var_idx] != ")":
                            var_name += line[idx:][var_idx]
                            var_idx += 1
                        if var_name in var_map:
                            var_name = var_map[var_name]
                        else:
                            var_map[var_name] = var_num
                            var_name = var_num
                            var_num += 1
                        
                        clause = clause + "-" + (str(var_name) + " ")
                        if line[idx:].find(",") == -1:
                            clause = clause + "0" + "\n"
                            idx = len(line)
                            clauses += clause
                            clause_num += 1
                        else:
                            idx = idx + line[idx:].find(",") + 2
                    else:
                        var_name = line[idx:][first_variable + 2]
                        var_idx = first_variable + 3
                        while line[idx:][var_idx] != ")" and line[idx:][var_idx] != ",":
                            var_name += line[idx:][var_idx]
                            var_idx += 1
                        
                        if var_name in var_map:
                            var_name = var_map[var_name]
                        else:
                            var_map[var_name] = var_num
                            var_name = var_num
                            var_num += 1
                        
                        clause = clause + (str(var_name) + " ")
                        
                        if line[idx:].find(",") == -1:
                            clause = clause + "0" + "\n"
                            idx = len(line)
                            clauses += clause
                            clause_num += 1
                        else:
                            idx = idx + line[idx:].find(",") + 2
                else:
                    var_name = line[idx:][first_Not + 6]
                    var_idx = first_Not + 7
                    while line[idx:][var_idx] != ")":
                        var_name += line[idx:][var_idx]
                        var_idx += 1
                    if var_name in var_map:
                        var_name = var_map[var_name]
                    else:
                        var_map[var_name] = var_num
                        var_name = var_num
                        var_num += 1
                    
                    clause = clause + "-" + (str(var_name) + " ")
                    if line[idx:].find(",") == -1:
                        clause = clause + "0" + "\n"
                        idx = len(line)
                        clauses += clause
                        clause_num += 1
                    else:
                        idx = idx + line[idx:].find(",") + 2

            else:
                if first_variable != 1:
                        var_name = line[idx:][first_variable + 2]
                        var_idx = first_variable + 3
                        while line[idx:][var_idx] != ")" and line[idx:][var_idx] != ",":
                            var_name += line[idx:][var_idx]
                            var_idx += 1
                        if var_name in var_map:
                            var_name = var_map[var_name]
                        else:
                            var_map[var_name] = var_num
                            var_name = var_num
                            var_num += 1
                        
                        clause = clause + (str(var_name) + " ")
                        
                        if line[idx:].find(",") == -1:
                            clause = clause + "0" + "\n"
                            idx = len(line)
                            clauses += clause
                            clause_num += 1
                        else:
                            idx = idx + line[idx:].find(",") + 2
    
    elif line.find("Not") == 0:
        var_name = line[6]
        var_idx = 7
        while line[var_idx] != ")":
            var_name += line[var_idx]
            var_idx += 1
        if var_name in var_map:
            var_name = var_map[var_name]
        else:
            var_map[var_name] = var_num
            var_name = var_num
            var_num += 1
        clauses += ("-" + str(var_name) + " 0" + "\n")
        clause_num += 1
    elif line.find("k!") == 0:
        var_name = line[2]
        var_idx = 3
        while var_idx < len(line):
            var_name += line[var_idx]
            var_idx += 1
        if var_name in var_map:
            var_name = var_map[var_name]
        else:
            var_map[var_name] = var_num
            var_name = var_num
            var_num += 1
        clauses += str(var_name) + " 0" + "\n"
        clause_num += 1
    else:
        print "UNKNOWN"
        print line

print ("p cnf " + str((var_num - 1)) + " " +  str(clause_num))
print clauses                        
