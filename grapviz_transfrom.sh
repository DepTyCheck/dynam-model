#! /bin/bash

data="Dynam.Model.Primitives.Casts.IsCastable[0, 1(from), 2(to)] MakeCast - determ: {#0 (from) -> <=[] ->[], #1 (to) -> <=[] ->[], #2 (tos) -> <=[] ->[], #3 -> <=[] ->[#1 (to), #2 (tos)]}"

output="out.dot"

name="[A-Za-z.]"
args="[0-9A-Za-z(), ]"
format="($name)*\[$args*\].*{(.*)}"



echo "digraph {" > $output



echo "}" >> $output
