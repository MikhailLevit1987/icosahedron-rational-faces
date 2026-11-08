# No regular icosahedron has a rational point on every face

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24059256.svg)](https://doi.org/10.5281/zenodo.24059256)

**Theorem.** For every regular icosahedron in $\mathbb R^3$ (any position, size and orientation,
mirror images included) at least one of its twenty closed triangular faces contains no point with
rational coordinates.

This answers a question of Ilya Bogdanov on MathOverflow,
[*Can a regular icosahedron contain a rational point on each face?*](https://mathoverflow.net/questions/452847)
(2023). The proof is computer-assisted and is completely formalized in Lean 4 / Mathlib: the
48 certificates of the computational part are checked by the Lean kernel itself
(`decide +kernel`, no `native_decide`), and the main theorem depends only on the standard axioms.

## Idea of the proof

Let $\varphi=(1+\sqrt5)/2$. The planes of the faces of the canonical icosahedron are defined over
$\mathbb Q(\sqrt5)$. Applying a field automorphism $\tau$ of $\mathbb C$ with
$\tau(\sqrt5)=-\sqrt5$ to the face equations and the rational points turns a hypothetical solution
$t+sRI$ into a complex orthogonal matrix $T=(R^\tau)^{\mathsf T}R$ such that, for **every** real
$\alpha,\beta$, ten intervals built from $A=\alpha\,\mathrm{Re}\,T+\beta\,\mathrm{Im}\,T$ and the ten
pairs of opposite faces have a common point. The separation theorem shows that for every
$T\in SO(3,\mathbb C)$ some such $A$ separates the intervals:

* $\mathrm{Im}\,T=0$: $\mathrm{Re}\,T$ is a positive multiple of $\mathrm{Fr}_c(u,v)\,M_r(\sigma,t)$,
  a rational chart frame times a rotation about the third axis in half-angle form;
* $\mathrm{Im}\,T\ne0$: in two chart frames $T$ becomes $\mu\mu'\,\mathrm{diag}(pI+rJ,1)$ with
  $p^2+r^2=1$, and for every Pythagorean phase $(X,Y,D)$ the span of $\mathrm{Re}\,T$,
  $\mathrm{Im}\,T$ contains a positive multiple of $\mathrm{Fr}_{c_1}\,\mathrm{diag}(XI+YJ,Dz)\,
  \mathrm{Fr}_{c_2}^{\mathsf T}$ with $|z|\le1$.

The remaining statements over compact parameter boxes are checked cell by cell with exact
polynomial bounds over $\mathbb Z[\varphi]$, without floating point and without Lipschitz estimates.
Details are in the paper.

## Contents

| Path | What |
|---|---|
| [`paper/icosahedron-rational-faces-en.pdf`](paper/icosahedron-rational-faces-en.pdf) | The paper, LaTeX source alongside |
| [`lean/`](lean/) | Lean 4 formalization; main theorem `Icosahedron.no_rational_point_on_every_face` in `lean/Icosahedron/Main.lean` |
| [`lean/Icosahedron/Defs.lean`](lean/Icosahedron/Defs.lean) | The statement: the canonical icosahedron, its faces, rational points (58 lines) |
| [`lean/Icosahedron/CertR/`](lean/Icosahedron/CertR/), [`lean/Icosahedron/CertC/`](lean/Icosahedron/CertC/) | The 48 kernel certificates |
| [`lean/Gen.lean`](lean/Gen.lean) | Generator of the certificate trees (not part of the proof) |
| [`tools/build-certs.sh`](tools/build-certs.sh), [`tools/build-certs.ps1`](tools/build-certs.ps1) | Build the certificates one at a time (see the warning below) |
| [`tools/check_faces.py`](tools/check_faces.py) | Independent check that `faceIdx` lists exactly the 20 faces |
| [`verification/`](verification/) | A self-contained prompt for independent checking that the Lean statement matches the theorem |

## Checking the formal proof

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). Lean 4
v4.34.0-rc2, Mathlib v4.34.0-rc2.

> **Memory warning.** While the Lean kernel checks a certificate it needs up to about 7 GB (real
> case) or 8–13 GB (complex case) of memory. A plain `lake build` checks as many certificates in
> parallel as there are CPU threads and can make a 32 GB machine unresponsive. Build the
> certificates one at a time with the script below.

```sh
cd lean
lake exe cache get              # download prebuilt Mathlib (several GB)
cd ..
sh tools/build-certs.sh         # the 48 certificates one at a time, then the library; about 1.5 h
cd lean
lake env lean CheckAxioms.lean
```

On Windows use `powershell -NoProfile -ExecutionPolicy Bypass -File tools\build-certs.ps1` instead
of the `sh` line. Expected output of the last command:

```
'Icosahedron.no_rational_point_on_every_face' depends on axioms: [propext, Classical.choice, Quot.sound]
'Icosahedron.separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Icosahedron.reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Icosahedron.K.real_all' depends on axioms: [propext, Quot.sound]
'Icosahedron.K.complex_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. no `sorryAx` and no `Lean.ofReduceBool` (no `native_decide`). The meaning of the theorem
depends only on the definitions in `lean/Icosahedron/Defs.lean`.

| File | Content |
|---|---|
| `Defs.lean` | The statement: vertices, faces (closed triangles), rational points, `HasRatPoint` |
| `Geometry.lean` | Face planes $n_j\cdot x=\varphi^2$, opposite faces, conjugate normals |
| `Embedding.lean` | An automorphism of $\mathbb C$ with $\sqrt5\mapsto-\sqrt5$ |
| `Reduction.lean` | Centering and the reduction to $SO(3,\mathbb C)$; `Separated` |
| `KCheck.lean` | The kernel-evaluable checker: $\mathbb Z[\varphi]$, polynomials, the two searches, phases |
| `KSound.lean` | Soundness of the arithmetic and of the cell bound |
| `KGeom.lean` | Chart frames; soundness of both searches |
| `Frames.lean` | Six charts cover the sphere; frame decomposition; the real and the complex case |
| `CertR/*`, `CertC/*`, `CertAll.lean` | The certificates and their collection |
| `Separation.lean` | The separation theorem |
| `Main.lean` | The main theorem |

To regenerate the complex certificate trees: `cd lean && lake exe gen` (writes
`Icosahedron/CertC/P*.lean`); `lake exe gen real` writes the real certificates and `CertAll.lean`.

## Use of AI tools

The author posed the problem, directed the work and checked the results. The mathematical argument
was developed by OpenAI Codex, and the Lean formalization, including the kernel-checkable
certificates and their generator, by Anthropic Claude, both under the direction of the author; the
paper was drafted with Anthropic Claude. The correctness of the theorem does not depend on trust in
these systems: the proof is checked by the Lean kernel, and what must be trusted is the kernel and
the definitions in `Defs.lean`.

## Citation

Mikhail Levit, *No regular icosahedron has a rational point on every face: a proof checked in
Lean*, 2026. Zenodo, [doi:10.5281/zenodo.24059256](https://doi.org/10.5281/zenodo.24059256) (all
versions, resolves to the latest one).

| Version | DOI |
|---|---|
| 1.0 | [10.5281/zenodo.24059257](https://doi.org/10.5281/zenodo.24059257) |

## License

Code (`lean/`, `tools/`, `verification/`): [Apache License 2.0](LICENSE), the same as Mathlib.
Paper (`paper/`): [Creative Commons Attribution 4.0 International](paper/LICENSE).
