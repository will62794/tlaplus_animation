#
# Run TLC to produce error trace and then run trace explorer on the trace.
#

source aliases.sh

SPEC=$1

# Run the TLC model checker to produce an error trace and save the output.
echo "Running model checking to produce error trace."
tlc -simulate -depth 85 -tool $SPEC | tee $SPEC.out