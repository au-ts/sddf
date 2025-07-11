#!/usr/bin/env python

'''
Watch a given path and re-run a command when you see changes. This script is
useful for watching for changes to your TEX sources and rebuilding your paper
automatically. Many PDF viewers, e.g. Evince, will notice changes to your PDF
and automatically reload it, so you can work on your paper and naturally see
changes whenever you save without having to restart your PDF viewer.
'''

import argparse, os, subprocess, sys

def main(argv):
    parent_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))

    # Command-line argument parsing.
    parser = argparse.ArgumentParser(
        description='watch a path and re-run a command when you see changes')
    parser.add_argument('--path', '-p', default=parent_dir,
        help='path to watch')
    parser.add_argument('--command', '-c', default='make',
        help='command to run')
    parser.add_argument('--cwd', default=parent_dir,
        help='working directory to run command in')
    opts = parser.parse_args(argv[1:])

    # Check we have inotifywait. There are Python bindings for inotify, but
    # they're pretty verbose and slow.
    with open(os.devnull, 'w') as devnull:
        if subprocess.call(['which', 'inotifywait'], stdout=devnull,
                stderr=devnull) != 0:
            print >>sys.stderr, 'inotifywait not found'
            return -1

    # Now just keep watching the path and re-running the command.
    while True:
        if subprocess.call(['inotifywait', '-e', 'close_write', opts.path]) \
                != 0:
            return -1

        ret = subprocess.call(opts.command, cwd=opts.cwd, shell=True)
        if ret != 0:
            print >>sys.stderr, 'warning: %s returned %d' % (opts.command, ret)

    assert False, 'unreachable'

    return 0

if __name__ == '__main__':
    try:
        sys.exit(main(sys.argv))
    except KeyboardInterrupt: # Ctrl+C
        sys.exit(-1)
