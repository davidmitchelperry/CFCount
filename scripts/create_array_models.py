import sys

filename = sys.argv[1]
array_bound = sys.argv[2]
f = open(filename, 'a')


def create_calloc(f, array_bound):
    f.write('def calloc(name, num, size):\n')
    f.write("\tarray = [ BitVec(name + '_%s' % i, size) for i in range(" + str(array_bound) + ") ]\n")
    cons_string = "\tcons = And(";
    for i in range(int(array_bound)):
        cons_string += "array[" + str(i) + "] == 0, "
    cons_string += ")\n\n"
    f.write(cons_string)
    f.write('\treturn (cons, array)\n')


def create_array_store(f, array_bound):
    f.write('def array_store(orig_array, name, idx, val, size):\n')
    f.write("\tarray = [ BitVec(name + '_%s' % i, size) for i in range(" + str(array_bound) + ") ]\n")
    cons_string = ""
    for i in range(int(array_bound)):
        cons_string += "\tcons_" + str(i) + " = "
        cons_string += "If(idx == " + str(i) + ", And("
        for j in range(int(array_bound)):
            if i != j:
                cons_string += "array[" + str(j) + "] == orig_array[" + str(j) + "], "
            else:
                cons_string += "array[" + str(j) + "] == val, "

        if i == 0:
            cons_string += "), False)\n"
        else:
            cons_string += "), cons_" + str(i - 1) + ")\n"

    cons_string += "\tcons = cons_" + str(int(array_bound) - 1) + "\n"
    cons_string += "\n";
    f.write(cons_string)
    f.write("\treturn (cons, array)\n")

def create_array_read(f, array_bound):
    f.write('def array_read(array, idx, result):\n')
    cons_string = ""
    for i in range(int(array_bound)):
        cons_string += "\tcons_" + str(i) + " = "
        cons_string += "If(idx == " + str(i) + ", result == array[" + str(i) + "], "
        if i == 0:
            cons_string += "False)\n"
        else:
            cons_string += "cons_" + str(i - 1) + ")\n"
    cons_string += "\n";
    cons_string += "\tcons = cons_" + str(int(array_bound) - 1) + "\n"
    f.write(cons_string)
    f.write("\treturn cons\n")


def create_multi_dim_array_read(f, array_bound):
    f.write('def multi_dim_array_read(array, idx, result):\n')
    cons_string = ""
    for i in range(int(array_bound)):
        cons_string += "\tcons_" + str(i) + " = "
        cons_string += "If(idx == " + str(i) + ", And("
        for j in range(int(array_bound)):
            cons_string += "result[" + str(j) + "] == array[" + str(i) + "][" + str(j) + "], "
        cons_string += "), "
        if i == 0:
            cons_string += "False)\n"
        else:
            cons_string += "cons_" + str(i - 1) + ")\n"

    f.write(cons_string)
    f.write("\tcons = cons_" + str(int(array_bound) - 1) + "\n")
    f.write("\treturn cons\n");


def create_create_argv(f, array_bound):
    f.write('argv_0 = []')
    f.write('def create_argv():\n')

    for i in range(int(array_bound)):
        f.write('\targv' + str(i) + " = calloc('argv_" + str(i) + "', 5, 8)\n")
        f.write('\targv_0.append(argv' + str(i) + '[1])\n')

    f.write('\n')
    cons_string = "\tcons = And("
    for i in range(int(array_bound)):
        cons_string += "argv" + str(i) + "[0], "
    cons_string += ")\n"
    f.write(cons_string)
    f.write('\treturn cons')



def create_memset(f, array_bound):

    f.write('def memset(orig_array, name, offset, val, num, size):\n')
    f.write("\tarray = [ BitVec(name + '_%s' % i, size) for i in range(" + str(array_bound) + ") ]\n")

    cons_string = ""
    case_ct = 0

    for off in range(int(array_bound)):
        for n in range(int(array_bound) + 1):
            if (off + n) <= int(array_bound):
                case_ct += 1
                cons_string += "\tcons_" + str(case_ct - 1) + " = "
                cons_string += "If(And(offset == " + str(off) + ", num == " + str(n) + "), And("
                for i in range(int(array_bound)):
                    if (i >= off) and (i < off + n):
                        cons_string += "array[" + str(i) + "] == val, "
                    else:
                        cons_string += "array[" + str(i) + "] == orig_array[" + str(i) + "], "
                cons_string += "), "
                if off == 0 and n == 0:
                    cons_string += "False)\n"
                else:
                    cons_string += "cons_" + str(case_ct - 2) + ")\n"

    cons_string += "\n"
    cons_string += "\tcons = cons_" + str(case_ct - 1) + "\n"
    f.write(cons_string)
    f.write('\treturn (cons, array)\n')

f.write('from z3 import *\n')
f.write('\n')

create_calloc(f, array_bound)
f.write('\n')

create_array_store(f, array_bound)
f.write('\n')

create_array_read(f, array_bound)
f.write('\n')





