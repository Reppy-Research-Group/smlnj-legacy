#!/usr/bin/env python3

import argparse
import json
import statistics
from collections import defaultdict
from rich.table import Table
from rich.console import Console

parser = argparse.ArgumentParser(prog="gentable.py")
parser.add_argument('benchmark')
parser.add_argument('instrument')

args = parser.parse_args()

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
            runtime_med = statistics.median(runtime["runs"])
            runtime_stdev = statistics.stdev(runtime["runs"])
            runtime_table[program][tag] = (runtime_med, runtime_stdev)

            alloc = runtime["alloc"]
            alloc_table[program][tag] = alloc["nbAlloc"]
            promote_table[program][tag] = alloc["nbPromote"]
            gc_table[program][tag] = alloc["nGCs"]

        for profile in profiles:
            tag = profile["tag"]
            instr_table[program][tag] = profile["instructions:u"]
            load_table[program][tag] = profile["mem_inst_retired.all_loads:u"]
            store_table[program][tag] = profile["mem_inst_retired.all_stores:u"]

instrument_table = defaultdict(dict)
with open(args.instrument, "r") as file:
    results = json.load(file)
    for result in results:
        tag = result["flags"].replace('--', '')
        program = result["bmark"]
        instrument_table[program][tag] = result
# print(instrument_table)

def readable(size):
    units = ('K', 'M', 'G', 'T')
    size_list = [f'{int(size):,} '] + [f'{int(size) / 1000 ** (i + 1):.1f} {u}' for i, u in enumerate(units)]
    return [size for size in size_list if not size.startswith('0.')][-1]

# print(runtime_table)
programs = [
    "hamlet2",
    "vliw",
    "nucleic",
    "lexgen",
    "barnes-hut",
    "mc-ray",
    "life",
    "mandelbrot-int",
    "mandelbrot"
]

columns = [
    "flat-closure",
    "no-active-sharing",
    # "no-flatten",
    # "conservative",
    "new",
    "new2",
    # "space",
    "time",
    # "old",
]


table = Table(title='instrumentation')

table.add_column('Name', justify='left', no_wrap=True)
for col in columns:
    table.add_column(col, justify='right', no_wrap=True)

def loads(data):
    return data["compute"] + data["move"] + data["link"] + data["mixed"]

for program in programs:
    # time_row = [program + ' (time)'] + [f"{runtime_table[program][col][0]:.3f}" for col in columns]
    alloc_row = [program + ' (clos allocs)'] + [readable(instrument_table[program][col]["allocs"]) for col in columns]
    data_alloc = [program + ' (data allocs)'] + [readable(instrument_table[program][col]["dataAllocs"]) for col in columns]
    # diff_alloc = [program + ' (diff allocs)'] + [readable(alloc_table[program][col] // 8 - instrument_table[program][col]["allocs"] - instrument_table[program][col]["dataAllocs"]) for col in columns]
    loads_row = [program + ' (clos loads)'] + [readable(loads(instrument_table[program][col])) for col in columns]
    # diff_loads_row = [program + ' (all loads)'] + [readable(load_table[program][col]) for col in columns]
    compute_row = [program + ' (compute)'] + [readable(instrument_table[program][col]["compute"]) for col in columns]
    move_row = [program + ' (move)'] + [readable(instrument_table[program][col]["move"]) for col in columns]
    link_row = [program + ' (link)'] + [readable(instrument_table[program][col]["link"]) for col in columns]
    mixed_row = [program + ' (mixed)'] + [readable(instrument_table[program][col]["mixed"]) for col in columns]

    # table.add_row(*time_row)
    table.add_row(*alloc_row)
    table.add_row(*data_alloc)
    # table.add_row(*diff_alloc)
    table.add_row(*loads_row)
    # table.add_row(*diff_loads_row)
    table.add_row(*compute_row)
    table.add_row(*move_row)
    table.add_row(*link_row)
    table.add_row(*mixed_row)
    table.add_section()

Console().print(table)

