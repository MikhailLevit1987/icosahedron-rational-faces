import Icosahedron.Geometry
import Icosahedron.Embedding

/-!
# Reduction to ten triangles in `ℂ`

If every face of `t + s R I` contains a rational point, then for the automorphism `τ` of `ℂ`
with `τ φ = 1 - φ` the complex orthogonal matrix `T = (R^τ)ᵀ R` has the property that for
all real `α, β` the ten conjugate face intervals of `A = α Re T + β Im T` share a point.
-/

namespace Icosahedron

open Matrix Complex

/-- Conjugate face functional at the vertices of the ten representative faces. -/
noncomputable def fval (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 10) (k : Fin 3) : ℝ :=
  normalConj (rep i) ⬝ᵥ (A *ᵥ vertex (faceIdx (rep i) k))

/-- The ten intervals `[min_k fval A i k, max_k fval A i k]` have no common point. -/
def Separated (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ c : ℝ, ∃ i : Fin 10, (∀ k, c < fval A i k) ∨ (∀ k, fval A i k < c)

/-- Centering: rational points on opposite faces give a rational point on the centered face. -/
theorem centered_point (t : Fin 3 → ℝ) (s : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ j, HasRatPoint t s R j) (i : Fin 10) :
    ∃ m ∈ face (rep i), ∃ p : Fin 3 → ℚ, ∀ c, s * (R *ᵥ m) c = p c := by
  obtain ⟨x, hx, q, hq⟩ := h (rep i)
  obtain ⟨x', hx', q', hq'⟩ := h (opp i)
  refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x'), ?_, fun c => (q c - q' c) / 2, ?_⟩
  · exact convex_face _ hx (neg_mem_face_of_mem_opp i hx') (by norm_num) (by norm_num)
      (by norm_num)
  · intro c
    have e1 := hq c
    have e2 := hq' c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    simp only [mulVec_add, mulVec_smul, mulVec_neg, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    push_cast
    linarith

theorem orth_transpose_mul {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : Rᵀ * R = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR
  simpa [Matrix.star_eq_conjTranspose] using this

theorem orth_mul_transpose {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : R * Rᵀ = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).1 hR
  simpa [Matrix.star_eq_conjTranspose] using this

theorem dot_rot_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) (u v : Fin 3 → ℝ) :
    (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hR, vecMul_one]

theorem ofReal_φ : ((φ : ℝ) : ℂ) = φc := rfl

theorem τ_ev (τ : ℂ ≃+* ℂ) (hτ : τ φc = 1 - φc) (x : ℤ × ℤ) :
    τ ((ev x : ℝ) : ℂ) = ((evc x : ℝ) : ℂ) := by
  simp only [ev, evc, ofReal_add, ofReal_mul, ofReal_intCast, ofReal_sub, ofReal_one,
    map_add, map_mul, map_intCast]
  rw [show ((φ : ℝ) : ℂ) = φc from rfl, hτ]

/-- Splitting a real bilinear expression in a complex matrix into real and imaginary parts. -/
theorem split_re_im (T : Matrix (Fin 3) (Fin 3) ℂ) (u v : Fin 3 → ℝ) :
    (∑ d, (u d : ℂ) * ∑ e, T d e * (v e : ℂ)) =
      ((u ⬝ᵥ (T.map re *ᵥ v) : ℝ) : ℂ) + ((u ⬝ᵥ (T.map im *ᵥ v) : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp [dotProduct, mulVec, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]

theorem reduction (t : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (h : ∀ j, HasRatPoint t s R j) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℂ, Tᵀ * T = 1 ∧ T.det = 1 ∧
      ∀ α β : ℝ, ¬ Separated (α • T.map re + β • T.map im) := by
  obtain ⟨τ, hτ, -⟩ := exists_aut_sqrt5
  have hRR := orth_transpose_mul hR
  have hRR' := orth_mul_transpose hR
  let Rc : Matrix (Fin 3) (Fin 3) ℂ := R.map ofRealHom
  let Rt : Matrix (Fin 3) (Fin 3) ℂ := Rc.map τ.toRingHom
  let T := Rtᵀ * Rc
  -- the key identity on each representative face
  have key : ∀ i : Fin 10, ∃ m ∈ face (rep i),
      (s : ℂ) * (∑ d, (normalConj (rep i) d : ℂ) * ∑ e, T d e * (m e : ℂ)) =
        τ (s : ℂ) * (1 - φc) ^ 2 := by
    intro i
    obtain ⟨m, hm, p, hp⟩ := centered_point t s R h i
    refine ⟨m, hm, ?_⟩
    have hplane := normal_dot_of_mem (rep i) hm
    have hreal : (∑ c, ((p c : ℚ) : ℝ) * ∑ d, R c d * normal (rep i) d) = s * φ ^ 2 := by
      have e : (fun c => ((p c : ℚ) : ℝ)) = s • (R *ᵥ m) := by
        funext c; simp [← hp c]
      have : (∑ c, ((p c : ℚ) : ℝ) * ∑ d, R c d * normal (rep i) d) =
          (fun c => ((p c : ℚ) : ℝ)) ⬝ᵥ (R *ᵥ normal (rep i)) := by
        simp [dotProduct, mulVec]
      rw [this, e, smul_dotProduct, dot_rot_rot hRR, dotProduct_comm, hplane, smul_eq_mul]
    have hC : (∑ c, ((p c : ℚ) : ℂ) * ∑ d, (R c d : ℂ) * (normal (rep i) d : ℂ)) =
        (s : ℂ) * φc ^ 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hreal
      simpa [ofReal_sum, ofReal_mul, ofReal_φ] using this
    have hτC := congrArg τ hC
    simp only [map_sum, map_mul, map_ratCast, map_pow, hτ] at hτC
    have hn : ∀ d, τ ((normal (rep i) d : ℝ) : ℂ) = ((normalConj (rep i) d : ℝ) : ℂ) :=
      fun d => τ_ev τ hτ _
    simp only [hn] at hτC
    have hpC : ∀ c, ((p c : ℚ) : ℂ) = (s : ℂ) * ∑ e, (R c e : ℂ) * (m e : ℂ) := by
      intro c
      have := congrArg (fun x : ℝ => (x : ℂ)) (hp c)
      simpa [mulVec, dotProduct, ofReal_sum, ofReal_mul] using this.symm
    simp only [hpC] at hτC
    rw [← hτC]
    simp only [T, Rt, Rc, mul_apply, transpose_apply, map_apply, ofRealHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Fin.sum_univ_three]
    ring
  refine ⟨T, ?_, ?_, ?_⟩
  · -- orthogonality
    have h1 : Rcᵀ * Rc = 1 := by
      simp only [Rc, ← transpose_map, ← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero _)
        (map_one _)]
    have h2 : Rt * Rtᵀ = 1 := by
      have : Rc * Rcᵀ = 1 := by
        simp only [Rc, ← transpose_map, ← Matrix.map_mul, hRR', Matrix.map_one _ (map_zero _)
          (map_one _)]
      simp only [Rt, ← transpose_map, ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _)
        (map_one _)]
    calc Tᵀ * T = Rcᵀ * (Rt * Rtᵀ) * Rc := by
          simp only [T, transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, h1]
  · -- determinant
    have hdet : R.det = 1 ∨ R.det = -1 := by
      have : R.det * R.det = 1 := by
        have := congrArg Matrix.det hRR
        rwa [det_mul, det_transpose, det_one] at this
      rcases mul_self_eq_one_iff.1 this with h | h <;> simp [h]
    have hc : Rc.det = (R.det : ℂ) := by
      simp only [Rc]; rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have ht : Rt.det = τ (R.det : ℂ) := by
      simp only [Rt]; rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hc]; rfl
    simp only [T, det_mul, det_transpose, ht, hc]
    rcases hdet with h | h <;> simp [h]
  · -- no separation
    intro α β hsep
    let κ : ℂ := τ (s : ℂ) * (1 - φc) ^ 2 / s
    obtain ⟨i, hi⟩ := hsep (α * κ.re + β * κ.im)
    obtain ⟨m, hm, hk⟩ := key i
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hval : (∑ d, (normalConj (rep i) d : ℂ) * ∑ e, T d e * (m e : ℂ)) = κ := by
      rw [eq_div_iff hsC, mul_comm, hk]
    rw [split_re_im] at hval
    have hre := congrArg Complex.re hval
    have him := congrArg Complex.im hval
    simp at hre him
    have hA : normalConj (rep i) ⬝ᵥ ((α • T.map re + β • T.map im) *ᵥ m) =
        α * κ.re + β * κ.im := by
      rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        dotProduct_smul, hre, him, smul_eq_mul, smul_eq_mul]
    rw [dotProduct_mulVec] at hA
    rcases hi with hi | hi
    · have := gt_on_face (rep i) _ _ (fun k => by
        have := hi k; rwa [fval, dotProduct_mulVec] at this) hm
      linarith
    · have := lt_on_face (rep i) _ _ (fun k => by
        have := hi k; rwa [fval, dotProduct_mulVec] at this) hm
      linarith

end Icosahedron
