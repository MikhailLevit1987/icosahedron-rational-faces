import Icosahedron.Separation

/-!
# Main theorem

No regular icosahedron in `ℝ³` has a rational point on each of its 20 closed faces.
-/

namespace Icosahedron

open Matrix

theorem no_rational_point_on_every_face (t : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ¬ ∀ j : Fin 20, HasRatPoint t s R j := by
  intro h
  obtain ⟨T, hT, hdet, hns⟩ := reduction t s hs R hR h
  obtain ⟨α, β, hsep⟩ := separation T hT hdet
  exact hns α β hsep

end Icosahedron
