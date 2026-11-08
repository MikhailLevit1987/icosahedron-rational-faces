#!/bin/sh
# Build the 48 kernel certificates one at a time, then the whole library.
#
# Each complex certificate (Icosahedron.CertC.P*) needs 8-13 GB of memory while the Lean kernel
# checks it, each real one (Icosahedron.CertR.R*) up to about 7 GB. A plain `lake build` checks
# as many of them in parallel as there are CPU threads and can exhaust the memory of the machine.
#
# Usage (from the repository root or from lean/):  sh tools/build-certs.sh
set -e
cd "$(dirname "$0")/../lean"

for ch in 0 1 2 3 4 5; do
  for sg in f t; do
    echo "== Icosahedron.CertR.R$ch$sg"
    lake build "Icosahedron.CertR.R$ch$sg"
  done
done
for i in 0 1 2 3 4 5; do
  for j in 0 1 2 3 4 5; do
    echo "== Icosahedron.CertC.P$i$j"
    lake build "Icosahedron.CertC.P$i$j"
  done
done
echo "== Icosahedron (all certificates are built; the rest is light)"
lake build
