#!/bin/bash

# Return how many pages a PDF has. For fun times, construct a commit hook from
# this that updates a 'underlimit' tag to point at the latest changeset under
# your page limit.

if [ $# -ne 1 ]; then
    echo "Usage: $0 file" >&2
    exit 1
fi

PAGES=

which pdftk &>/dev/null
if [ $? -eq 0 ]; then
    PAGES=$(pdftk "$1" dump_data | grep '^NumberOfPages' | cut -d ' ' -f 2)
else
    which pdfinfo &>/dev/null
    if [ $? -eq 0 ]; then
        PAGES=$(pdfinfo "$1" | grep '^Pages:' | sed 's/Pages.*\([0-9]\+\)/\1/g')
    fi
fi

if [ -z "${PAGES}" ]; then
    echo "No tool found to count pages" >&2
    exit 1
else
    echo "${PAGES}"
fi
