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
    TimeRemainingColumn,
)

PROGRAMS = [
    'hamlet2',
    'vliw',
    'barnes-hut',
    'life',
    'mc-ray',
    'lexgen',
    'mandelbrot',
    'mandelbrot-int',
    'nucleic',
]

OPTIONS = [
    '--new',
    '--new2',
    # '--space',
    # '--time',
    # '--reg-limit',
    # '--no-flatten',
    # '--no-active-sharing',
    # '--no-sharing',
    # '--flat-closure',
    # '--conservative',
    # '--old'
]

progress = Progress(
    TextColumn("[progress.description]{task.description}"),
    BarColumn(),
    MofNCompleteColumn(),
    TimeElapsedColumn(),
    TimeRemainingColumn(),
)

total = progress.add_task("All", total=len(PROGRAMS) * len(OPTIONS))

results = []
with progress:
    for program in PROGRAMS:
        for option in OPTIONS:
            process = subprocess.run(
                ["./instrument.sh", program, option],
                check=True,
                capture_output=True,
                text=True,
            )
            result = eval(process.stdout)
            progress.advance(total)
            results.append(result)

result_filename = datetime.now().strftime("instrument_%Y%m%d_%H%M%S.json")

try:
    with open(result_filename, "w") as result_file:
        json.dump(results, result_file)
except Exception as e:
    print(json.dumps(results))
    raise

