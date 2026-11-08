import Icosahedron.Frames
import Icosahedron.CertAll

/-!
# Separation for every complex orthogonal matrix

For every `T ∈ SO(3, ℂ)` some real combination `α Re T + β Im T` separates the ten
conjugate face intervals (`complex_rotation_proof.md`, sections 2–5):
* `Im T = 0`: `Re T` is a positive multiple of `Fr ch u v * Mr σ t` (`K.real_frame`);
  take `α = 1, β = 0`; certificates `K.real_all` via `K.rsearch_sound`.
* `Im T ≠ 0`: chart frames for the axes `Re T · b`, `b` (`K.complex_frame`); the complex
  search (`K.complex_all`, `K.csearchD_sound`) gives a phase `(X, Y, D)`, `X² + Y² = D²`,
  that separates for every `z ∈ [-1, 1]`, and the span of `Re T`, `Im T` contains a positive
  multiple of the corresponding matrix.
-/

namespace Icosahedron

open Matrix Complex

theorem separation (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) (hdet : T.det = 1) :
    ∃ α β : ℝ, Separated (α • T.map re + β • T.map im) := by
  by_cases hY : T.map im = 0
  · obtain ⟨ch, hch, u, v, t, hu, hv, ht, sg, c, hc, hX⟩ := K.real_frame T hT hdet hY
    refine ⟨1, 0, ?_⟩
    rw [one_smul, zero_smul, add_zero, hX]
    exact K.sep_smul (K.rsearch_sound ch hch sg 40 ⟨0, 0, 0, 0, 0⟩ (K.real_all ch hch sg) u v t
      (K.inSq_zero hu) (K.inSq_zero hv) (K.inT_zero ht)) hc
  · obtain ⟨ch1, h1, ch2, h2, u, v, u', v', hu, hv, hu', hv', hall⟩ :=
      K.complex_frame T hT hdet hY
    obtain ⟨s, s', hs⟩ := K.complex_all ch1 ch2 h1 h2
    obtain ⟨n, hn⟩ := K.csearchD_sound ch1 ch2 h1 h2 40 _ s s' hs u v u' v'
      (K.inSq_zero hu) (K.inSq_zero hv) (K.inSq_zero hu') (K.inSq_zero hv')
    obtain ⟨α, β, c, z, hc, hz, hA⟩ :=
      hall (K.phX n) (K.phY n) (K.phD n) (K.phD_pos' n) (K.phase_norm n)
    exact ⟨α, β, by rw [hA]; exact K.sep_smul (hn z hz) hc⟩

end Icosahedron
