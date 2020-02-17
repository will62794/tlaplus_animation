#
# Run TLC to produce error trace and then run trace explorer on the trace.
#

source aliases.sh

SPEC=$1

# Generate a trace with specified trace expressions evaluated.
echo "Running trace explorer."
trace -traceExpressions -expressionsFile=traceExp.txt -overwrite $SPEC

# Filter for the trace expression we evaluated.
grep "traceExpression" TE.out | sed -E "s/.*_traceExpression_1 = //" | sed -E "s/\"//" > viewExps.txt

# This is a crude way to replace a template string with the SVG output, but it works. We basically take everything
# in the template file before the magic string ('@SVG_TEXT@'), add it to the output file, then append the animation SVG elements, 
# and then append everything in the template file after the magic string. Can probably also do this with 'sed' but this works for now.
animfile="animation.html"
grep -B 10000 "@SVG_TEXT@" template.html > $animfile
cat viewExps.txt >> $animfile
grep -A 10000 "@SVG_TEXT@" template.html >> $animfile
