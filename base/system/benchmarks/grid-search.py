#!/usr/bin/env python3

import os
import subprocess
import json
from random import shuffle
from itertools import product
from datetime import datetime
from concurrent.futures import (
    ThreadPoolExecutor,
    as_completed,
)
from collections import defaultdict
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    TextColumn,
    TimeElapsedColumn,
    TimeRemainingColumn,
)

booleans = ["true", "false"]

PARAMETERS = {
    "flatten-selfref": booleans,
    "flatten-liberally": booleans,
    "flatten-reg-limit": booleans,
    # "sharing-no-thinning": booleans,
    "sharing-policy": range(1, 3),
    "flatten-policy": range(2),
    "sharing-dist-cutoff": range(1, 5),
    "sharing-size-cutoff": range(2, 10),
    "sharing-use-cutoff": range(1, 5),
}

PROGRAMS = [
    # 'hamlet2',
    'barnes-hut',
    'boyer',
    # 'delta-blue',
    'dlx',
    'fft',
    # 'hamlet',
    # 'hamlet2',
    'knuth-bendix',
    'lexgen',
    'life',
    'list',
    'logic',
    'mandelbrot-int',
    'mandelbrot',
    'mazefun',
    'mc-ray',
    'nucleic',
    'plclub-ray',
    'profile',
    'simple',
    'smith-nf',
    'timeit',
    'tsp',
    'vliw',
]

def get_grid(parameters):
    keys, values = parameters.keys(), parameters.values()
    combinations = product(*values)
    return enumerate(dict(zip(keys, combo)) for combo in combinations)

def get_program_param(programs, grid):
    return product(programs, grid)

def test_param(program, param):
    param_id, param_dict = param
    param_list = [f"-Cnc.{flag}={value}" for flag, value in param_dict.items()]
    # param_list.append("-Cnc.flatten-reg-limit=false")

    try:
        process = subprocess.run(
            ["./test.sh", program] + param_list,
            check=True,
            capture_output=True,
            text=True,
        )
        result = eval(process.stdout)
    except:
        raise Exception(" ".join(["./test.sh", program] + param_list))
    progress.advance(total)
    return (param_id, result)

grid = list(get_grid(PARAMETERS))
all_tasks = list(get_program_param(PROGRAMS, grid))
shuffle(all_tasks)

progress = Progress(
    TextColumn("[progress.description]{task.description}"),
    BarColumn(),
    MofNCompleteColumn(),
    TimeElapsedColumn(),
    TimeRemainingColumn(),
)

results = defaultdict(list)
with progress, ThreadPoolExecutor(max_workers=1) as pool:
    total = progress.add_task("All", total=len(all_tasks))
    futures = []
    for program, param in all_tasks:
        fut = pool.submit(test_param, program, param)
        futures.append(fut)

    for fut in as_completed(futures):
        param_id, result = fut.result()
        results[param_id].append(result)

report = {
    "params": dict(grid),
    "results": results,
}

result_filename = datetime.now().strftime("gridsearch_%Y%m%d_%H%M%S.json")

try:
    with open(result_filename, "w") as result_file:
        json.dump(report, result_file)
except Exception as e:
    print(json.dumps(results))
    raise

