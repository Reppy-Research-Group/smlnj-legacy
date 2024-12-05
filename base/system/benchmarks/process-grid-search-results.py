import json
import argparse
from statistics import median
from rich.table import Table
from rich import print
from collections import defaultdict

parser = argparse.ArgumentParser(prog=__file__)
parser.add_argument('gridsearch')
parser.add_argument('benchmark')

args = parser.parse_args()

with open(args.gridsearch, "r") as file:
    report = json.load(file)

runtime_table = defaultdict(dict)
alloc_table = defaultdict(dict)
promote_table = defaultdict(dict)
gc_table = defaultdict(dict)
instr_table = defaultdict(dict)
load_table = defaultdict(dict)
store_table = defaultdict(dict)

with open(args.benchmark, "r") as file:
    results = json.load(file)
    for program, result in results.items():
        runtimes = result["runtimes"]
        profiles = result["profiles"]

        for runtime in runtimes:
            tag = runtime["tag"]
            runtime_med = median(runtime["runs"])
            runtime_table[program][tag] = runtime_med

            alloc = runtime["alloc"]
            alloc_table[program][tag] = alloc["nbAlloc"]
            promote_table[program][tag] = alloc["nbPromote"]
            gc_table[program][tag] = alloc["nGCs"]

        for profile in profiles:
            tag = profile["tag"]
            instr_table[program][tag] = profile["instructions:u"]
            load_table[program][tag] = profile["mem_inst_retired.all_loads:u"]
            store_table[program][tag] = profile["mem_inst_retired.all_stores:u"]

params = report["params"]
results = report["results"]

def roc(new, old):
    return (new - old) / old

def summarize(runtimes):
    time = 0.0
    alloc = 0
    promote = 0
    gc = 0
    def get0(lst):
        if len(lst) < 1:
            return 0
        else:
            return lst[0]
    for run in runtimes:
        program = run["bmark"]
        # time += 0 if median(run["runs"]) > runtime_table[program]["old"] else -1
        alloc += 0 if run["alloc"]["nbAlloc"] > alloc_table[program]["old"] else -1
        promote += 0 if run["alloc"]["nbPromote"] > promote_table[program]["old"] else -1
        # time += median(run["runs"]) - runtime_table[program]["old"]
        # alloc += run["alloc"]["nbAlloc"] - alloc_table[program]["old"]
        # promote += run["alloc"]["nbPromote"] - promote_table[program]["old"]
        time += roc(median(run["runs"]), runtime_table[program]["old"])
        # alloc += roc(run["alloc"]["nbAlloc"], alloc_table[program]["old"])
        # promote += roc(run["alloc"]["nbPromote"], promote_table[program]["old"])
        gc += 0 if get0(run["alloc"]["nGCs"]) > get0(gc_table[program]["old"]) else -1
        # time += median(run["runs"])
        # alloc += run["alloc"]["nbAlloc"]
        # promote += run["alloc"]["nbPromote"]
    return time, alloc, promote, gc

summary = {}
for k, v in results.items():
    try:
        s = summarize(v)
    except Exception as e:
        print(e)
        print(f"Skipping {k}")
        continue
    summary[k] = s

detailed = True
if not detailed:
    time_winner = min(summary.keys(), key=lambda k: summary[k][0])
    alloc_winner = min(summary.keys(), key=lambda k: summary[k][1])
    promote_winner = min(summary.keys(), key=lambda k: summary[k][2])
    gc_winner = min(summary.keys(), key=lambda k: summary[k][3])

    print(f"Time winner: {params[time_winner]}")
    print(f"Alloc winner: {params[alloc_winner]}")
    print(f"Promote winner: {params[promote_winner]}")
else:
    def time(k): return summary[k][0]
    def alloc(k): return summary[k][1]
    def promote(k): return summary[k][2]
    def gc(k): return summary[k][3]
    time_winners = sorted(summary.keys(), key=time)
    alloc_winners = sorted(summary.keys(), key=alloc)
    promote_winners = sorted(summary.keys(), key=promote)
    gc_winners = sorted(summary.keys(), key=gc)

    def gentable(title, winners, n):
        table = Table(show_header=True, title=title)
        table.add_column("")
        for k in params["0"].keys():
            table.add_column(k)
        table.add_column("Time")
        table.add_column("Alloc")
        table.add_column("Promote")
        table.add_column("GC")

        for i, param_id in enumerate(winners[:n]):
            row = [i] \
                + list(params[param_id].values()) \
                + [time(param_id), alloc(param_id), promote(param_id), gc(param_id)]
            row = map(str, row)
            table.add_row(*row)
        print(table)

    gentable("Time", time_winners, 10)
    gentable("Alloc", alloc_winners, 10)
    gentable("Promote", promote_winners, 30)
    gentable("GC", gc_winners, 10)



