#!/usr/bin/env python3

from resource import getrusage, RUSAGE_CHILDREN
from subprocess import run, DEVNULL
from glob import glob
import os
import json

def benchmark(program, input=None):
    start_usage = getrusage(RUSAGE_CHILDREN)
    run(program, input=input, stdout=DEVNULL, stderr=DEVNULL, check=True)
    end_usage = getrusage(RUSAGE_CHILDREN)
    user_time = end_usage.ru_utime - start_usage.ru_utime
    system_time = end_usage.ru_stime - start_usage.ru_stime
    total_cpu_time = user_time + system_time
    return total_cpu_time

def main():
    results = []

    for path in glob("target/native/release/build/*/*.exe"):
        name = os.path.splitext(os.path.basename(path))[0]
        elf = os.path.join("/tmp/mmb/", f"{name}.elf")
        with open(os.path.join("test", f"{name}.in"), "rb") as f:
            input = f.read()

        mb = benchmark(path, input)
        mmb = benchmark(elf, input)
        results.append(
            {"name": name,
             "unit": "Percent",
             "value": mb/mmb*100}
        )

    with open("output.txt", "w") as f:
        json.dump(results, f)


if __name__ == '__main__':
    main()
