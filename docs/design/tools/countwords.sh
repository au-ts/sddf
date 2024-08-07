#!/bin/sh

echo "word count: `cat sections/*.tex | python removecomments.py | detex | tr -d '&' | wc -w`"
for f in sections/*.tex; do
	echo "- $f: `cat "$f" | python removecomments.py | detex | tr -d '&' | wc -w`"
done
