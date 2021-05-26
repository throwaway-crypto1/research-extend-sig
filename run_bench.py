import re
import os
import sys
import json
import fractions
import subprocess

def bench(op, algo, keys=1, exts=1, iters=10):
    env = os.environ
    env['RUSTFLAGS'] = '-C target-cpu=native'
    env['BENCH_KEYS'] = str(keys)
    env['BENCH_EXTS'] = str(exts)
    env['BENCH_ITERS'] = str(iters)
    env['BENCH_OP'] = op
    env['BENCH_ALGO'] = algo
    cmd = ['cargo', 'run', '--release']
    done = subprocess.run(
        cmd,
        capture_output=True,
        env=env
    )

    stdout = done.stdout.decode('utf-8')

    assert 'num_extend: %d' % exts in stdout, stdout
    assert 'num_extend: %d' % exts in stdout, stdout
    assert 'iters: %d' % iters in stdout, stdout

    time = None
    size = None
    variance = None

    lines = {}

    for line in stdout.split('\n'):
        line = line.strip()
        if ':' in line:
            k, v = line.split(':')
            k = k.strip()
            v = v.strip()
            lines[k] = v

    avg_nano = fractions.Fraction(
        int(lines['duration']),
        iters
    )

    avg_mili = avg_nano / 10**6

    size = int(lines['size']) if 'size' in lines else None

    res = {
        'time': float(avg_mili),
        'size': size
    }

    return res


def run_bench(group, op, keys, exts):
    assert op in ('sign', 'verify')
    assert group in ('class', 'rsa')
    return bench(op, algo=group, keys=keys, exts=exts)

if __name__ == '__main__':

    import math

    group = sys.argv[1]
    op = sys.argv[2]

    val_exts = [1, 2, 4, 8]
    val_keys = [1 << i for i in range(12)]

    for exts in val_exts:

        results = {}

        for keys in val_keys:
            keys_per_ext = math.ceil(keys / exts)
            if keys_per_ext * exts > keys:
                continue
            out = run_bench(group, op, keys_per_ext, exts)
            print(group, op, 'exts:', exts, 'keys:', keys_per_ext * exts, 'res:', out)
            results[keys] = out

        with open('%s-%s-%s.json' % (group, op, exts), 'w') as f:
            json.dump(results, f)
