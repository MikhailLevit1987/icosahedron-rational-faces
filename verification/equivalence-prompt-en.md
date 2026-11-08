# Task: check that a Lean 4 statement says exactly what a mathematical theorem says

You are reviewing a formalization. Your only job is to decide whether the **Lean statement** below
is logically equivalent to the **mathematical theorem** below. Do **not** try to prove or disprove the
theorem, and do not assess the proof: the Lean proof has been machine-checked (no `sorry`, only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`). The only remaining
risk is that the formal statement does not mean what the mathematical statement means. Be skeptical
and precise.

## 1. The mathematical theorem

**Theorem.** Let `I ⊂ ℝ³` be a regular icosahedron (any position, any size, any orientation,
including mirror images). Then at least one of the twenty closed triangular faces of `I` contains no
point with all three coordinates rational.

A face is the closed triangle (the convex hull of its three vertices), so points on edges and at
vertices count.

## 2. The Lean 4 statement (code verbatim; Lean 4 + Mathlib)

```lean
namespace Icosahedron

open Matrix

/-- The golden ratio. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- Vertex coordinates encoded as `a + b φ` with `(a, b) : ℤ × ℤ`. -/
def vtxCode : Fin 12 → Fin 3 → ℤ × ℤ := ![
  ![(0, 0), (1, 0), (0, 1)],    -- 0: (0, 1, φ)
  ![(1, 0), (0, 1), (0, 0)],    -- 1: (1, φ, 0)
  ![(0, 1), (0, 0), (1, 0)],    -- 2: (φ, 0, 1)
  ![(0, 0), (1, 0), (0, -1)],   -- 3: (0, 1, -φ)
  ![(1, 0), (0, -1), (0, 0)],   -- 4: (1, -φ, 0)
  ![(0, 1), (0, 0), (-1, 0)],   -- 5: (φ, 0, -1)
  ![(0, 0), (-1, 0), (0, 1)],   -- 6: (0, -1, φ)
  ![(-1, 0), (0, 1), (0, 0)],   -- 7: (-1, φ, 0)
  ![(0, -1), (0, 0), (1, 0)],   -- 8: (-φ, 0, 1)
  ![(0, 0), (-1, 0), (0, -1)],  -- 9: (0, -1, -φ)
  ![(-1, 0), (0, -1), (0, 0)],  -- 10: (-1, -φ, 0)
  ![(0, -1), (0, 0), (-1, 0)]]  -- 11: (-φ, 0, -1)

/-- Value of a code `a + b φ`. -/
noncomputable def ev (x : ℤ × ℤ) : ℝ := x.1 + x.2 * φ

/-- The twelve vertices of the canonical icosahedron. -/
noncomputable def vertex (i : Fin 12) : Fin 3 → ℝ := fun c => ev (vtxCode i c)

/-- The twenty faces as vertex index triples. -/
def faceIdx : Fin 20 → Fin 3 → Fin 12 := ![
  ![0, 1, 2], ![0, 1, 7], ![0, 2, 6], ![0, 6, 8], ![0, 7, 8],
  ![1, 2, 5], ![1, 3, 5], ![1, 3, 7], ![2, 4, 5], ![2, 4, 6],
  ![3, 5, 9], ![3, 7, 11], ![3, 9, 11], ![4, 5, 9], ![4, 6, 10],
  ![4, 9, 10], ![6, 8, 10], ![7, 8, 11], ![8, 10, 11], ![9, 10, 11]]

/-- The closed triangular face `j` of the canonical icosahedron. -/
noncomputable def face (j : Fin 20) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (Set.range fun k => vertex (faceIdx j k))

/-- A point of `ℝ³` with rational coordinates. -/
def IsRat (x : Fin 3 → ℝ) : Prop := ∃ q : Fin 3 → ℚ, ∀ c, x c = q c

/-- Face `j` of the placed icosahedron `t + s R I` contains a rational point. -/
def HasRatPoint (t : Fin 3 → ℝ) (s : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 20) : Prop :=
  ∃ x ∈ face j, IsRat (t + s • (R *ᵥ x))

theorem no_rational_point_on_every_face (t : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ¬ ∀ j : Fin 20, HasRatPoint t s R j

end Icosahedron
```

Notes on Lean/Mathlib notation, for reference:
* `Fin n` is `{0, …, n−1}`; `Fin 3 → ℝ` is `ℝ³`, `x c` is the coordinate `c`.
* `![a, b, c]` is the vector (or list of rows) `(a, b, c)`.
* `convexHull ℝ S` is the convex hull of the set `S`; `Set.range f` is the image of `f`.
* `R *ᵥ x` is the matrix–vector product, `s • y` is scalar multiplication.
* `Matrix.orthogonalGroup (Fin 3) ℝ` is the set of real `3 × 3` matrices with `Rᵀ R = R Rᵀ = 1`
  (determinant `±1`, so reflections are included).
* `(q c : ℝ)` in `IsRat` is the coercion of a rational number to a real number.

## 3. What to check (answer every item)

1. Are the twelve points `vertex i` the vertices of a regular icosahedron (cyclic permutations of
   `(0, ±1, ±φ)`, edge length 2)?
2. Does `faceIdx` list exactly the twenty faces of this icosahedron (each face once, each triple
   consisting of three pairwise adjacent vertices)?
3. Is `face j` the closed triangle with these three vertices (edges and vertices included)?
4. Is every regular icosahedron in `ℝ³` of the form `{t + s R x : x ∈ I₀}` for the canonical
   icosahedron `I₀`, with `s > 0` and `R` orthogonal, and do its faces correspond to `face j` under
   this map? Is anything lost or added by allowing `det R = −1`?
5. Does `HasRatPoint t s R j` mean "face `j` of the placed icosahedron contains a point with
   rational coordinates"? Does `IsRat` correctly express "all three coordinates are rational"?
6. Does `¬ ∀ j, HasRatPoint t s R j` mean "some face contains no rational point", and do the
   hypotheses `hs`, `hR` match the theorem, with nothing added or missing and without making the
   statement vacuous?
7. Is there any other way in which the Lean statement is weaker, stronger, or vacuous compared with
   the mathematical theorem (e.g. a wrong value of `φ`, an implicit coercion, an off-by-one index,
   a definition that is trivially true or false)?

## 4. Required answer format

```
VERDICT: EQUIVALENT | NOT EQUIVALENT | UNSURE
1: OK | PROBLEM — <one or two sentences>
2: OK | PROBLEM — ...
3: OK | PROBLEM — ...
4: OK | PROBLEM — ...
5: OK | PROBLEM — ...
6: OK | PROBLEM — ...
7: OK | PROBLEM — ...
DETAILS: <any explanation; for every PROBLEM give a concrete counterexample or a precise logical
reason, or say explicitly that you could not find one>
```

Do not answer `NOT EQUIVALENT` without a concrete distinguishing example or a precise logical reason.
If you are not sure about a Lean/Mathlib detail, say so and answer `UNSURE` rather than guessing.
