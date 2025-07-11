#!/usr/bin/env python

'''
LaTeX error locator.

This tool is designed for locating syntax errors in LaTeX source code.
Generally this can be a pretty arduous task thanks to pdflatex's confusing and
verbose output. This program works by repeatedly running pdflatex with
incremental amounts of your source file; effectively truncating your source by
slightly less each time. Following this it shows you a two column display with
your source document on the right and the number of errors that pdflatex
yielded when your document was truncated at this point. By scanning through
this table for points where the error count goes from 0 to non-zero you can
usually locate your problem.

This is not bulletproof and it is not really a bisection; the tool is simply
named thus as bisection is closer to what a human would do. The code has not
been thoroughly exercised and it is strongly recommended that you read and
understand the source code below before running this program. I take no
responsibility if it eats your source document.
'''

import argparse, subprocess, re, os, sys, tempfile

class LogLine(object):
    '''A status line designated for the final output report.'''
    def __init__(self, text, errors):
        self.text = text
        self.errors = errors

    def __repr__(self):
        if self.errors is None:
            return '  |%s' % self.text
        elif self.errors == 0:
            # Show 0 error count in green
            return '\033[32;1m00\033[0m|%s' % self.text
        # Show non-0 error count in red
        return '\033[31;1m%02d\033[0m|%s' % (self.errors, self.text)

def overwrite(fd, lines):
    '''Overwrite a file with given contents.'''
    fd.truncate(0)
    fd.seek(0)
    fd.write('\n'.join(lines))
    fd.flush()

def main(argv):
    parser = argparse.ArgumentParser(
        description='latex error locator')
    parser.add_argument('--output', '-o', type=argparse.FileType('w'),
        help='write output log to file instead of displaying it')
    parser.add_argument('file', type=argparse.FileType('r+'),
        help='source file to check')
    opts = parser.parse_args(argv[1:])

    # Eagerly read in the file contents as we're going to overwrite it.
    content = opts.file.read().split('\n')

    # LaTeX errors always start with '!'
    latex_error = re.compile(r'^!', flags=re.MULTILINE)

    # Lines that will appear in the final output report.
    log = []

    begun = False
    for i in xrange(len(content)):
        if begun:
            # We're inside the 'document' section itself.

            # Write a truncated version of the source up to this point.
            overwrite(opts.file, content[:i] + ['\\end{document}'])

            # Run pdflatex, which returns its errors on stdout.
            pdflatex = subprocess.Popen(
                ['pdflatex', '-interaction=nonstopmode', opts.file.name],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdout, _ = pdflatex.communicate()

            # Did we get any errors?
            if pdflatex.returncode == 0:
                log.append(LogLine(content[i], 0))
            else:
                log.append(LogLine(content[i],
                    len(latex_error.findall(stdout))))
        else:
            # We're just in the header. No point exploring.
            log.append(LogLine(content[i], None))
            if '\\begin{document}' in content[i]:
                begun = True

    # Reset the original contents of the source.
    overwrite(opts.file, content)

    output = '\n'.join(map(str, log))

    if opts.output is not None:
        # Write the output log to a file.
        opts.output.write(output)
    else:
        # Show the user the output log via `less`.
        _, tmp = tempfile.mkstemp()
        with open(tmp, 'w') as f:
            f.write(output)
        subprocess.call(['less', '-R', tmp])
        os.remove(tmp)

    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))
