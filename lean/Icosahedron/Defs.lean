import Mathlib

/-!
# Rational points on the faces of a regular icosahedron: definitions

Canonical icosahedron: vertices `(0,±1,±φ)`, `(±1,±φ,0)`, `(±φ,0,±1)`, edge length 2.
A regular icosahedron in `ℝ³` is an image `x ↦ t + s • R x` of the canonical one with
`s > 0` and `R` orthogonal (reflections allowed).
-/

namespace Icosahedron

open Matrix

/-- The golden ratio. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- Vertex coordinates encoded as `a + b φ` with `(a, b) : ℤ × ℤ`. Order matches
`claude/ico_common.py`. -/
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

end Icosahedron
