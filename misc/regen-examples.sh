#!/bin/bash

# Re-generate the example output.
# Run from the project root folder:
#   $ ./misc/regen-examples.sh
# Then commit the results.

set -e

stack build

for f in examples/*.tla; do
    stack exec -- ezpsl "$f"
done
