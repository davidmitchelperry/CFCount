import sys

# Open trace file and read into list
traceFile = open(sys.argv[1], 'r')
trace = traceFile.readlines()

# Remove new line strings from list
trace = [x for x in trace if x != "\n"]

# If trace is not formatted correctly
if trace[0] != "trace_start\n" or trace[-1] != "trace_end\n":
    print "Broken Trace!"
    exit(0)

# Remove "trace_start" and "trace_end" from the trace
trace = trace[1:-1]

# Only include printed lines that start with "trace:"
trace = [x[6:] for x in trace if x[:6] == "trace:"]

# Write clean trace to file
with open(sys.argv[2] , "w") as clean_trace:
    for t in trace:
        clean_trace.write(t)



