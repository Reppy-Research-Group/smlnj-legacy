#!/usr/bin/env python3

import os
import subprocess
import json
from datetime import datetime
from concurrent.futures import (
    ThreadPoolExecutor,
    as_completed,
)
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    TextColumn,
    TimeElapsedColumn,
)
PROGRAMS = [
    'hamlet2',
    'vliw',
    'barnes-hut',
    'life',
    'mc-ray',
    'lexgen',
    'mandelbrot',
    'mandelbrot-int'
]

OPTIONS = [
    '--new',
    # '--reg-limit',
    '--no-flatten',
    '--no-active-sharing',
    '--no-sharing',
    '--flat-closure',
    # '--conservative',
    '--old'
]

results = []

progress = Progress(
    TextColumn("[progress.description]{task.description} {task.fields[flag]} {task.fields[step]}"),
    BarColumn(),
    MofNCompleteColumn(),
    TimeElapsedColumn(),
    transient=True
)

def runbench(task_id, program):
    progress.start_task(task_id)
    runtimes = []
    profiles = []
    for option in OPTIONS:
        progress.update(task_id, flag=option, step='measure')
        with open(os.devnull, "wb") as devnull:
            subprocess.check_call(
                ['./run.sh', option, program],
                stdout=devnull,
                stderr=subprocess.STDOUT
            )
        with open(f"{program}-data", "r") as file:
            data = eval(file.read())
        runtimes.append(data)
        progress.console.log(data)

        progress.update(task_id, flag=option, step='profile')
        with open(os.devnull, "wb") as devnull:
            subprocess.check_call(
                ['./profile.sh', option, program],
                stdout=devnull,
                stderr=subprocess.STDOUT
            )
        with open(f"{program}-profile", "r") as file:
            data = eval(file.read())
        profiles.append(data)
        progress.console.log(data)

        progress.advance(task_id)

    progress.advance(overall_task)
    return (program, { 'runtimes': runtimes, 'profiles': profiles })

results = {}
with progress:
    overall_task = progress.add_task("All", flag="", step="", total=len(PROGRAMS))

    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = []
        for program in PROGRAMS:
            program_task = progress.add_task(program, flag="", step="", total=len(OPTIONS))
            fut = pool.submit(runbench, program_task, program)
            futures.append(fut)

        for fut in as_completed(futures):
            program, result = fut.result()
            results[program] = result

result_filename = datetime.now().strftime("benchmark_%Y%m%d_%H%M%S.json")

try:
    with open(result_filename, "w") as result_file:
        json.dump(results, result_file)
except FileNotFoundError as e:
    print(json.dumps(results))
    raise

