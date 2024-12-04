import json
import argparse
from statistics import median

parser = argparse.ArgumentParser(prog=__file__)
parser.add_argument('filename')

args = parser.parse_args()

with open(args.filename, "r") as file:
    report = json.load(file)

params = report["params"]
results = report["results"]

def summarize(runtimes):
    time = 0.0
    alloc = 0
    promote = 0
    for run in runtimes:
        if run["bmark"] == "hamlet2":
            continue
        time += median(run["runs"])
        alloc += run["alloc"]["nbAlloc"]
        promote += run["alloc"]["nbPromote"]
    return time, alloc, promote

summary = {}
for k, v in results.items():
    try:
        s = summarize(v)
    except Exception as e:
        print(e)
        print(f"Skipping {k}")
        continue
    summary[k] = s

time_winner = min(summary.keys(), key=lambda k: summary[k][0])
alloc_winner = min(summary.keys(), key=lambda k: summary[k][1])
promote_winner = min(summary.keys(), key=lambda k: summary[k][2])

print(f"Time winner: {params[time_winner]}")
print(f"Alloc winner: {params[alloc_winner]}")
print(f"Promote winner: {params[promote_winner]}")
