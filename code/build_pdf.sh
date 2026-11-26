#!/bin/bash
# paper/counterexample.md -> paper/counterexample.pdf  (pandoc + tectonic)
set -e
cd "$(dirname "$0")/../paper"
hdr=$(mktemp --suffix=.tex)
trap 'rm -f "$hdr" counterexample.tex' EXIT
cat > "$hdr" <<'H'
\usepackage{amsmath,amssymb}
\usepackage[margin=2.5cm]{geometry}
\usepackage{microtype}
\usepackage{xurl}
H
pandoc counterexample.md -o counterexample.tex --standalone -H "$hdr" -V fontsize=11pt -V colorlinks=true -V monofont="DejaVu Sans Mono" -V monofontoptions="Scale=0.85"
tectonic -X compile counterexample.tex
