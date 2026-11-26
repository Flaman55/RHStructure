# The lever experiment (Section "Where 1/2 is set" of the paper)

`python3 -I patch_theta_v3.py <copy of grh-compact> <num> <den>` changes the number of lifts from
m ~ x^(1/2) to m ~ x^(num/den) in a copy of grh-compact (never in the original), together with
every exponent derived from it. Building the patched copy with `lake build` shows which
inequalities reject the new exponent; the paper reports theta = 2/5 and 3/5.
