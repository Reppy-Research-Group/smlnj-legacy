#!/usr/bin/env python3

import os
import subprocess
import json
from datetime import datetime
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    TextColumn,
    TimeElapsedColumn,
)
PROGRAMS = [
    # 'hamlet2',
    # 'vliw',
    # 'barnes-hut',
    # 'life',
    # 'mc-ray',
    'lexgen',
    # 'mandelbrot',
    # 'mandelbrot-int'
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
    TextColumn("[progress.description]{task.description} {task.fields[curr]}"),
    BarColumn(),
    MofNCompleteColumn(),
    TimeElapsedColumn()
)

with progress:
    program_task = progress.add_task("Programs", curr="", total=len(PROGRAMS))
    options_task = progress.add_task("Options", curr="", total=len(OPTIONS))

    for program in PROGRAMS:
        progress.update(program_task, curr=program)
        for option in OPTIONS:
            progress.update(options_task, curr=option)
            with open(os.devnull, "wb") as devnull:
                subprocess.check_call(
                    ['./run.sh', option, program],
                    stdout=devnull,
                    stderr=subprocess.STDOUT
                )
            with open(f"{program}-data", "r") as file:
                result = eval(file.read())
                results.append(result)
                print(result)
            progress.advance(options_task)
        progress.reset(options_task)
        progress.advance(program_task)

result_filename = datetime.now().strftime("benchmark_%Y%m%d_%H%M%S.json")

try:
    with open(result_filename, "w") as result_file:
        json.dump(results, result_file)
except FileNotFoundError as e:
    print(json.dumps(results))
    raise

