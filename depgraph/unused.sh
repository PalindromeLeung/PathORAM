#!/usr/bin/env sh

# Generate graph.dpd
coqc -R ../_build/default/theory POram DepGraph.v
# Generate graph.dot
dpd2dot graph.dpd
# Generate graph.png
# dot -Tpng graph.dot > graph.png
# Generate unused.txt
dpdusage graph.dpd > unused.txt
