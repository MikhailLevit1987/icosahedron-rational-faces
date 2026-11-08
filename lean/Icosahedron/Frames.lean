import Icosahedron.KGeom

/-!
# Chart frames and the decomposition of a complex orthogonal matrix

* `Fr_tt`, `Fr_tt'`, `Fr_det`: `Fr ch u v` is `μ = 1 + u² + v²` times a rotation.
* `cover`: every unit vector is the (scaled) third column of some chart frame with
  `|u|, |v| ≤ 1/2`.
* `frame_decomp`: if `Tᵀ T = 1`, `det T = 1`, `Im T · b = 0` and the chart frames
  `Fr ch1 u v`, `Fr ch2 u' v'` have third columns `μ · Re T · b` and `μ' · b`, then
  `(Fr ch1 u v)ᵀ T (Fr ch2 u' v') = μ μ' · diag(p I + r J, 1)` with `p² + r² = 1`.
-/

namespace Icosahedron.K

open Icosahedron Matrix Complex

noncomputable def mu (u v : ℝ) : ℝ := 1 + u ^ 2 + v ^ 2

theorem mu_pos (u v : ℝ) : 0 < mu u v := by unfold mu; positivity

def e3 : Fin 3 → ℝ := ![0, 0, 1]

theorem Rq_tt (u v : ℝ) : (Rq u v)ᵀ * Rq u v = (mu u v) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rq, mu, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem Rq_tt' (u v : ℝ) : Rq u v * (Rq u v)ᵀ = (mu u v) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rq, mu, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem Rq_det (u v : ℝ) : (Rq u v).det = (mu u v) ^ 3 := by
  simp [Rq, mu, Matrix.det_fin_three]; ring

theorem chartM_props (ch : ℕ) (h : ch < 6) :
    (chartM ch)ᵀ * chartM ch = 1 ∧ chartM ch * (chartM ch)ᵀ = 1 ∧ (chartM ch).det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    interval_cases ch <;> fin_cases i <;> fin_cases j <;>
      simp [chartM, Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    interval_cases ch <;> fin_cases i <;> fin_cases j <;>
      simp [chartM, Matrix.mul_apply, Fin.sum_univ_three]
  · interval_cases ch <;> simp [chartM, Matrix.det_fin_three]

theorem Fr_tt (ch : ℕ) (h : ch < 6) (u v : ℝ) :
    (Fr ch u v)ᵀ * Fr ch u v = (mu u v) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨h1, -, -⟩ := chartM_props ch h
  rw [Fr, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (chartM ch)ᵀ, h1,
    Matrix.one_mul, Rq_tt]

theorem Fr_tt' (ch : ℕ) (h : ch < 6) (u v : ℝ) :
    Fr ch u v * (Fr ch u v)ᵀ = (mu u v) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨-, h2, -⟩ := chartM_props ch h
  rw [Fr, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Rq u v), Rq_tt',
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, h2]

theorem Fr_det (ch : ℕ) (h : ch < 6) (u v : ℝ) : (Fr ch u v).det = (mu u v) ^ 3 := by
  obtain ⟨-, -, h3⟩ := chartM_props ch h
  rw [Fr, det_mul, h3, Rq_det, one_mul]

theorem Fr_zero : Fr 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fr, chartM, Rq, Matrix.mul_apply, Fin.sum_univ_three]

theorem mu_zero : mu 0 0 = 1 := by simp [mu]

/-! ## Covering the sphere by six charts -/

/-- One chart: local axis `(a₁, a₂, a₃)` with `a₃ ≥ |a₁|, |a₂|`, `a₁² + a₂² + a₃² = 1`. -/
theorem local_axis (a1 a2 a3 : ℝ) (h : a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1) (h1 : |a1| ≤ a3)
    (h2 : |a2| ≤ a3) :
    let u := -a2 / (1 + a3)
    let v := a1 / (1 + a3)
    |u| ≤ 1 / 2 ∧ |v| ≤ 1 / 2 ∧
      2 * v = mu u v * a1 ∧ -(2 * u) = mu u v * a2 ∧ 1 - u ^ 2 - v ^ 2 = mu u v * a3 := by
  intro u v
  have ha3 : 0 ≤ a3 := le_trans (abs_nonneg _) h1
  have ha3' : a3 ≤ 1 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
  have hw : 0 < 1 + a3 := by linarith
  have key : a1 ^ 2 + a2 ^ 2 = (1 - a3) * (1 + a3) := by linear_combination h
  have hmu : mu u v = 2 / (1 + a3) := by
    simp only [mu, u, v]
    rw [div_pow, div_pow, neg_sq]
    field_simp
    linear_combination key
  have half : a3 / (1 + a3) ≤ 1 / 2 := by
    rw [div_le_iff₀ hw]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [u, abs_div, abs_neg, abs_of_pos hw]
    exact le_trans (div_le_div_of_nonneg_right h2 hw.le) half
  · simp only [v, abs_div, abs_of_pos hw]
    exact le_trans (div_le_div_of_nonneg_right h1 hw.le) half
  · rw [hmu]; simp only [v]; field_simp
  · rw [hmu]; simp only [u]; field_simp
  · rw [hmu]; simp only [u, v]
    rw [div_pow, div_pow, neg_sq]
    field_simp
    linear_combination -h

/-- `local_axis` with the chart coordinates as opaque witnesses, so that later `linarith`
calls see `u`, `v` as atoms instead of differently simplified quotients. -/
theorem local_axis_ex (a1 a2 a3 : ℝ) (h : a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1) (h1 : |a1| ≤ a3)
    (h2 : |a2| ≤ a3) :
    ∃ u v : ℝ, |u| ≤ 1 / 2 ∧ |v| ≤ 1 / 2 ∧
      2 * v = mu u v * a1 ∧ -(2 * u) = mu u v * a2 ∧ 1 - u ^ 2 - v ^ 2 = mu u v * a3 :=
  ⟨-a2 / (1 + a3), a1 / (1 + a3), local_axis a1 a2 a3 h h1 h2⟩

theorem Fr_e3 (ch : ℕ) (u v : ℝ) : Fr ch u v *ᵥ e3 = chartM ch *ᵥ ![2 * v, -(2 * u), 1 - u ^ 2 - v ^ 2] := by
  rw [Fr, ← mulVec_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [Rq, e3, mulVec, dotProduct, Fin.sum_univ_three]

theorem cover (d : Fin 3 → ℝ) (hd : d ⬝ᵥ d = 1) :
    ∃ ch, ch < 6 ∧ ∃ u v : ℝ, |u| ≤ 1 / 2 ∧ |v| ≤ 1 / 2 ∧ Fr ch u v *ᵥ e3 = mu u v • d := by
  have hd' : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 = 1 := by
    simp [dotProduct, Fin.sum_univ_three] at hd; linear_combination hd
  -- choose the largest coordinate in absolute value
  rcases le_total |d 0| |d 2| with h02 | h02 <;> rcases le_total |d 1| |d 2| with h12 | h12 <;>
    rcases le_total |d 0| |d 1| with h01 | h01
  all_goals first
    | -- pole ±e₂
      (have hm0 : |d 0| ≤ |d 2| := by linarith
       have hm1 : |d 1| ≤ |d 2| := by linarith
       rcases le_total 0 (d 2) with hs | hs
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 0) (d 1) (d 2) hd'
           (by rwa [abs_of_nonneg hs] at hm0) (by rwa [abs_of_nonneg hs] at hm1)
         refine ⟨0, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 0) (-d 1) (-d 2) (by linear_combination hd')
           (by rwa [abs_of_nonpos hs] at hm0) (by rw [abs_neg]; rwa [abs_of_nonpos hs] at hm1)
         refine ⟨1, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith)
    | -- pole ±e₀: local axis (d 1, σ d 2, σ d 0)
      (have hm1 : |d 1| ≤ |d 0| := by linarith
       have hm2 : |d 2| ≤ |d 0| := by linarith
       rcases le_total 0 (d 0) with hs | hs
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 1) (d 2) (d 0) (by linear_combination hd')
           (by rwa [abs_of_nonneg hs] at hm1) (by rwa [abs_of_nonneg hs] at hm2)
         refine ⟨2, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 1) (-d 2) (-d 0) (by linear_combination hd')
           (by rwa [abs_of_nonpos hs] at hm1) (by rw [abs_neg]; rwa [abs_of_nonpos hs] at hm2)
         refine ⟨3, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith)
    | -- pole ±e₁: local axis (d 2, σ d 0, σ d 1)
      (have hm0 : |d 0| ≤ |d 1| := by linarith
       have hm2 : |d 2| ≤ |d 1| := by linarith
       rcases le_total 0 (d 1) with hs | hs
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 2) (d 0) (d 1) (by linear_combination hd')
           (by rwa [abs_of_nonneg hs] at hm2) (by rwa [abs_of_nonneg hs] at hm0)
         refine ⟨4, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
       · obtain ⟨u, v, hu, hv, e1, e2, e3'⟩ := local_axis_ex (d 2) (-d 0) (-d 1) (by linear_combination hd')
           (by rwa [abs_of_nonpos hs] at hm2) (by rw [abs_neg]; rwa [abs_of_nonpos hs] at hm0)
         refine ⟨5, by norm_num, u, v, hu, hv, ?_⟩
         rw [Fr_e3]; funext i
         fin_cases i <;> simp [chartM, mulVec, dotProduct, Fin.sum_univ_three] <;> linarith)

/-! ## A complex orthogonal matrix in chart frames -/

/-- A real matrix as a complex one. -/
noncomputable def cM (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  A.map (fun x : ℝ => (x : ℂ))

@[simp] theorem cM_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    cM A i j = (A i j : ℂ) := rfl

theorem cM_det (A : Matrix (Fin 3) (Fin 3) ℝ) : (cM A).det = (A.det : ℂ) := by
  simp [Matrix.det_fin_three]

theorem cM_mul_transpose {A : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (h : A * Aᵀ = c • 1) :
    cM A * (cM A)ᵀ = (c : ℂ) • 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, cM_apply] at e ⊢
  split_ifs at e ⊢ <;> simp only [mul_one, mul_zero] at e ⊢ <;> exact_mod_cast e

theorem cM_transpose_mul {A : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (h : Aᵀ * A = c • 1) :
    (cM A)ᵀ * cM A = (c : ℂ) • 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, cM_apply] at e ⊢
  split_ifs at e ⊢ <;> simp only [mul_one, mul_zero] at e ⊢ <;> exact_mod_cast e

/-- If `Tᵀ T = 1`, `det T = 1`, `Im T · b = 0` and the chart frames have third columns
`μ · Re T · b` and `μ' · b`, then in these frames `T` is `μ μ' · diag(p I + r J, 1)` with
`p² + r² = 1`. -/
theorem frame_decomp (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) (hdet : T.det = 1)
    (b : Fin 3 → ℝ) (hY : T.map Complex.im *ᵥ b = 0) {ch1 ch2 : ℕ} (h1 : ch1 < 6)
    (h2 : ch2 < 6) {u v u' v' : ℝ}
    (hF1 : Fr ch1 u v *ᵥ e3 = mu u v • (T.map Complex.re *ᵥ b))
    (hF2 : Fr ch2 u' v' *ᵥ e3 = mu u' v' • b) :
    ∃ p r : ℂ, p ^ 2 + r ^ 2 = 1 ∧
      (cM (Fr ch1 u v))ᵀ * T * cM (Fr ch2 u' v') =
        ((mu u v : ℂ) * mu u' v') • !![p, -r, 0; r, p, 0; 0, 0, 1] := by
  have hμ := mu_pos u v
  have hμ' := mu_pos u' v'
  have hk0 : (mu u v : ℂ) * mu u' v' ≠ 0 := by
    have : (mu u v : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    have : (mu u' v' : ℂ) ≠ 0 := by exact_mod_cast hμ'.ne'
    positivity
  have hm1 : (mu u v : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hm2 : (mu u' v' : ℂ) ≠ 0 := by exact_mod_cast hμ'.ne'
  -- real third columns
  have hc1 : ∀ l, Fr ch1 u v l 2 = mu u v * (T.map Complex.re *ᵥ b) l := by
    intro l
    have := congrFun hF1 l
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e3] using this
  have he3 : ∀ i, (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 = e3 i := by
    intro i; fin_cases i <;> rfl
  have hwE : ∀ i, Fr ch1 u v 0 i * (T.map Complex.re *ᵥ b) 0 +
      Fr ch1 u v 1 i * (T.map Complex.re *ᵥ b) 1 + Fr ch1 u v 2 i * (T.map Complex.re *ᵥ b) 2 =
        mu u v * e3 i := by
    intro i
    have tt := congrFun (congrFun (Fr_tt ch1 h1 u v) i) 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hc1,
      Matrix.smul_apply, smul_eq_mul, he3] at tt
    have : mu u v * (Fr ch1 u v 0 i * (T.map Complex.re *ᵥ b) 0 +
        Fr ch1 u v 1 i * (T.map Complex.re *ᵥ b) 1 + Fr ch1 u v 2 i * (T.map Complex.re *ᵥ b) 2 -
          mu u v * e3 i) = 0 := by linear_combination tt
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hμ.ne')
  have hcol : ∀ m, Fr ch2 u' v' m 2 = mu u' v' * b m := by
    intro m
    have := congrFun hF2 m
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e3] using this
  have hTb : ∀ l, T l 0 * (b 0 : ℂ) + T l 1 * (b 1 : ℂ) + T l 2 * (b 2 : ℂ) =
      ((T.map Complex.re *ᵥ b) l : ℂ) := by
    intro l
    have hy := congrFun hY l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fin.sum_univ_three,
      Pi.zero_apply] at hy ⊢
    apply Complex.ext
    · simp
    · simp; linarith
  obtain ⟨M, hM⟩ : ∃ M, M = (cM (Fr ch1 u v))ᵀ * T * cM (Fr ch2 u' v') := ⟨_, rfl⟩
  rw [← hM]
  -- `Mᵀ M = k² I`
  have hMM : Mᵀ * M = ((mu u v : ℂ) * mu u' v') ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    have hA1 := cM_mul_transpose (Fr_tt' ch1 h1 u v)
    have hA2 := cM_transpose_mul (Fr_tt ch2 h2 u' v')
    have e : Mᵀ * M = (cM (Fr ch2 u' v'))ᵀ * (Tᵀ * ((cM (Fr ch1 u v) * (cM (Fr ch1 u v))ᵀ) *
        (T * cM (Fr ch2 u' v')))) := by
      simp only [hM, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [e, hA1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc Tᵀ, hT,
      Matrix.one_mul, Matrix.mul_smul, hA2, smul_smul]
    congr 1
    push_cast
    ring
  -- third column: `M e₃ = k e₃`
  have hM2 : ∀ i, M i 2 = (mu u v : ℂ) * mu u' v' * (e3 i : ℂ) := by
    intro i
    have t0 := hTb 0
    have t1 := hTb 1
    have t2 := hTb 2
    have hwc : (Fr ch1 u v 0 i : ℂ) * ((T.map Complex.re *ᵥ b) 0 : ℂ) +
        (Fr ch1 u v 1 i : ℂ) * ((T.map Complex.re *ᵥ b) 1 : ℂ) +
        (Fr ch1 u v 2 i : ℂ) * ((T.map Complex.re *ᵥ b) 2 : ℂ) = (mu u v : ℂ) * (e3 i : ℂ) := by
      exact_mod_cast hwE i
    simp only [hM, Matrix.mul_apply, Matrix.transpose_apply, cM_apply, Fin.sum_univ_three, hcol]
    push_cast
    linear_combination (mu u' v' : ℂ) * ((Fr ch1 u v 0 i : ℂ) * t0 + (Fr ch1 u v 1 i : ℂ) * t1 +
      (Fr ch1 u v 2 i : ℂ) * t2 + hwc)
  have hz02 : M 0 2 = 0 := by simpa [e3] using hM2 0
  have hz12 : M 1 2 = 0 := by simpa [e3] using hM2 1
  have hz22 : M 2 2 = (mu u v : ℂ) * mu u' v' := by simpa [e3] using hM2 2
  -- entries of `Mᵀ M`
  have E : ∀ i j, M 0 i * M 0 j + M 1 i * M 1 j + M 2 i * M 2 j =
      ((mu u v : ℂ) * mu u' v') ^ 2 * (if i = j then 1 else 0) := by
    intro i j
    have := congrFun (congrFun hMM i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using this
  have e20 : M 0 2 * M 0 0 + M 1 2 * M 1 0 + M 2 2 * M 2 0 = 0 := by simpa using E 2 0
  have e21 : M 0 2 * M 0 1 + M 1 2 * M 1 1 + M 2 2 * M 2 1 = 0 := by simpa using E 2 1
  have hz20 : M 2 0 = 0 := by
    have : (mu u v : ℂ) * mu u' v' * M 2 0 = 0 := by
      rw [hz02, hz12, hz22] at e20; linear_combination e20
    exact (mul_eq_zero.1 this).resolve_left hk0
  have hz21 : M 2 1 = 0 := by
    have : (mu u v : ℂ) * mu u' v' * M 2 1 = 0 := by
      rw [hz02, hz12, hz22] at e21; linear_combination e21
    exact (mul_eq_zero.1 this).resolve_left hk0
  have e00 : M 0 0 ^ 2 + M 1 0 ^ 2 = ((mu u v : ℂ) * mu u' v') ^ 2 := by
    have := E 0 0; rw [hz20] at this; simp at this; linear_combination this
  have e01 : M 0 0 * M 0 1 + M 1 0 * M 1 1 = 0 := by
    have := E 0 1; rw [hz20, hz21] at this; simp at this; linear_combination this
  -- determinant
  have hdM : M.det = ((mu u v : ℂ) * mu u' v') ^ 3 := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, cM_det, cM_det, Fr_det ch1 h1,
      Fr_det ch2 h2, hdet]
    push_cast
    ring
  rw [Matrix.det_fin_three, hz02, hz12, hz22, hz20, hz21] at hdM
  have edet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = ((mu u v : ℂ) * mu u' v') ^ 2 := by
    have : (mu u v : ℂ) * mu u' v' * (M 0 0 * M 1 1 - M 0 1 * M 1 0 -
        ((mu u v : ℂ) * mu u' v') ^ 2) = 0 := by linear_combination hdM
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hk0
    · linear_combination h
  have hk2 : ((mu u v : ℂ) * mu u' v') ^ 2 ≠ 0 := pow_ne_zero 2 hk0
  have hd : M 1 1 = M 0 0 := by
    have : (M 1 1 - M 0 0) * ((mu u v : ℂ) * mu u' v') ^ 2 = 0 := by
      linear_combination M 0 0 * edet + M 1 0 * e01 - M 1 1 * e00
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hk2
  have hb : M 0 1 = -M 1 0 := by
    have : (M 0 1 + M 1 0) * ((mu u v : ℂ) * mu u' v') ^ 2 = 0 := by
      linear_combination M 0 0 * e01 - M 0 1 * e00 - M 1 0 * edet
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hk2
  refine ⟨M 0 0 / ((mu u v : ℂ) * mu u' v'), M 1 0 / ((mu u v : ℂ) * mu u' v'), ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, e00, div_self hk2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hz02, hz12, hz22, hz20, hz21, hd, hb] <;> field_simp

/-! ## Assembly helpers -/

theorem fval_smul (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 10) (k : Fin 3) :
    fval (c • A) i k = c * fval A i k := by
  simp only [fval, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  ring

theorem sep_smul {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Separated A) {c : ℝ} (hc : 0 < c) :
    Separated (c • A) := by
  intro x
  obtain ⟨i, hi⟩ := h (x / c)
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · left
    intro k
    have := hi k
    rw [div_lt_iff₀ hc] at this
    rw [fval_smul]; linarith
  · right
    intro k
    have := hi k
    rw [lt_div_iff₀ hc] at this
    rw [fval_smul]; linarith

theorem phase_norm (n : ℕ) : phX n ^ 2 + (phY n : ℝ) ^ 2 = (phD n : ℝ) ^ 2 := by
  unfold phX phY phD sgnR phase
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp <;>
    norm_num

theorem phD_pos' (n : ℕ) : (0 : ℝ) < phD n := by exact_mod_cast phD_pos n

theorem inSq_zero {u : ℝ} (h : |u| ≤ 1 / 2) : inSq 0 0 u := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold inSq; norm_num; constructor <;> linarith

theorem inT_zero {t : ℝ} (h : |t| ≤ 1) : inT 0 0 t := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold inT; norm_num; constructor <;> linarith

theorem dot_mulVec_self (A : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ ((Aᵀ * A) *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Aᵀ, Matrix.vecMul_transpose]

theorem dot_self_nonneg (x : Fin 3 → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct, Fin.sum_univ_three]
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- `F (Fᵀ A G) Gᵀ = a b A` for frames with `F Fᵀ = a I`, `G Gᵀ = b I`. -/
theorem sandwich {F G : Matrix (Fin 3) (Fin 3) ℝ} {a b : ℝ} (hF : F * Fᵀ = a • 1)
    (hG : G * Gᵀ = b • 1) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    F * (Fᵀ * A * G) * Gᵀ = (a * b) • A := by
  have e : F * (Fᵀ * A * G) * Gᵀ = (F * Fᵀ) * A * (G * Gᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [e, hF, hG, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_comm]

/-- Real and imaginary parts of `T = Re T + i Im T` with `Tᵀ T = 1`. -/
theorem orth_parts (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) :
    (T.map Complex.re)ᵀ * T.map Complex.re = 1 + (T.map Complex.im)ᵀ * T.map Complex.im ∧
      (T.map Complex.re)ᵀ * T.map Complex.im + (T.map Complex.im)ᵀ * T.map Complex.re = 0 := by
  have e : ∀ i j, (Tᵀ * T) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    intro i j; rw [hT]
  constructor
  · ext i j
    have := congrArg Complex.re (e i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.map_apply,
      Matrix.add_apply, Matrix.one_apply] at this ⊢
    split_ifs at this ⊢ <;> simp at this ⊢ <;> linarith
  · ext i j
    have := congrArg Complex.im (e i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.map_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply] at this ⊢
    split_ifs at this <;> simp at this ⊢ <;> linarith

/-- A unit vector `b` with `Im T · b = 0`; then also `|Re T · b| = 1`. -/
theorem exists_ker (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) :
    ∃ b : Fin 3 → ℝ, T.map Complex.im *ᵥ b = 0 ∧ b ⬝ᵥ b = 1 ∧
      (T.map Complex.re *ᵥ b) ⬝ᵥ (T.map Complex.re *ᵥ b) = 1 := by
  obtain ⟨h1, h2⟩ := orth_parts T hT
  have key : ∀ w, (T.map Complex.re *ᵥ w) ⬝ᵥ (T.map Complex.re *ᵥ w) =
      w ⬝ᵥ w + (T.map Complex.im *ᵥ w) ⬝ᵥ (T.map Complex.im *ᵥ w) := by
    intro w
    rw [dot_mulVec_self, h1, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
      ← dot_mulVec_self]
  have hX : (T.map Complex.re).det ≠ 0 := by
    intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have e := key w
    rw [hw, zero_dotProduct] at e
    have hww : w ⬝ᵥ w = 0 := by
      linarith [dot_self_nonneg w, dot_self_nonneg (T.map Complex.im *ᵥ w)]
    exact hw0 (dotProduct_self_eq_zero.1 hww)
  have hY : (T.map Complex.im).det = 0 := by
    have e : (T.map Complex.re)ᵀ * T.map Complex.im = -((T.map Complex.im)ᵀ * T.map Complex.re) :=
      eq_neg_of_add_eq_zero_left h2
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose, Fintype.card_fin] at this
    have h3 : (T.map Complex.re).det * (T.map Complex.im).det = 0 := by
      linear_combination (1 / 2 : ℝ) * this
    exact (mul_eq_zero.1 h3).resolve_left hX
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hY
  have hpos : 0 < w ⬝ᵥ w :=
    lt_of_le_of_ne (dot_self_nonneg w) (fun h => hw0 (dotProduct_self_eq_zero.1 h.symm))
  have hYb : T.map Complex.im *ᵥ ((Real.sqrt (w ⬝ᵥ w))⁻¹ • w) = 0 := by
    rw [Matrix.mulVec_smul, hw, smul_zero]
  have hbb : ((Real.sqrt (w ⬝ᵥ w))⁻¹ • w) ⬝ᵥ ((Real.sqrt (w ⬝ᵥ w))⁻¹ • w) = 1 := by
    rw [smul_dot_smul, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  refine ⟨_, hYb, hbb, ?_⟩
  rw [key, hbb, hYb, zero_dotProduct, add_zero]

/-- Real and imaginary parts of the decomposition of `frame_decomp`. -/
theorem map_re_decomp {F G : Matrix (Fin 3) (Fin 3) ℝ} {T : Matrix (Fin 3) (Fin 3) ℂ} {a b : ℝ}
    {p r : ℂ} (h : (cM F)ᵀ * T * cM G = ((a : ℂ) * b) • !![p, -r, 0; r, p, 0; 0, 0, 1]) :
    Fᵀ * T.map Complex.re * G = (a * b) • Mc p.re r.re 1 ∧
      Fᵀ * T.map Complex.im * G = (a * b) • Mc p.im r.im 0 := by
  have e : ∀ i j, ((cM F)ᵀ * T * cM G) i j =
      (((a : ℂ) * b) • !![p, -r, 0; r, p, 0; 0, 0, 1]) i j := by
    intro i j; rw [h]
  constructor
  · ext i j
    have := congrArg Complex.re (e i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cM_apply, Fin.sum_univ_three,
      Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    fin_cases i <;> fin_cases j <;> simp [Mc] at this ⊢ <;> linarith
  · ext i j
    have := congrArg Complex.im (e i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cM_apply, Fin.sum_univ_three,
      Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    fin_cases i <;> fin_cases j <;> simp [Mc] at this ⊢ <;> linarith

/-- A rotation of the plane by the half-angle parametrization: `diag(p I + r J, 1)` is a
positive multiple of `Mr σ t` with `|t| ≤ 1`. -/
theorem Mc_rot {p r : ℝ} (h : p ^ 2 + r ^ 2 = 1) :
    ∃ sg : Bool, ∃ t : ℝ, |t| ≤ 1 ∧ Mr (if sg then -1 else 1) t = (1 + t ^ 2) • Mc p r 1 := by
  by_cases hp : 0 ≤ p
  · have hq : 0 < 1 + p := by linarith
    refine ⟨false, r / (1 + p), ?_, ?_⟩
    · rw [abs_div, abs_of_pos hq, div_le_one hq, ← abs_of_pos hq, abs_le_iff_mul_self_le]
      nlinarith
    · have ht : r / (1 + p) * (1 + p) = r := div_mul_cancel₀ r hq.ne'
      have e1 : 1 - (r / (1 + p)) ^ 2 = (1 + (r / (1 + p)) ^ 2) * p := by
        have : (1 + p) * (1 - (r / (1 + p)) ^ 2 - (1 + (r / (1 + p)) ^ 2) * p) = 0 := by
          linear_combination (-1 : ℝ) * h - (r / (1 + p) * (1 + p) + r) * ht
        have := (mul_eq_zero.1 this).resolve_left hq.ne'
        linear_combination this
      have e2 : 2 * (r / (1 + p)) = (1 + (r / (1 + p)) ^ 2) * r := by
        have : (1 + p) ^ 2 * (2 * (r / (1 + p)) - (1 + (r / (1 + p)) ^ 2) * r) = 0 := by
          linear_combination (-r) * h + (2 * (1 + p) - r / (1 + p) * (1 + p) * r - r * r) * ht
        have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hq.ne')
        linear_combination this
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Mr, Mc] <;>
        first | linear_combination e1 | linear_combination e2
  · replace hp := not_le.1 hp
    have hq : 0 < 1 - p := by linarith
    refine ⟨true, r / (p - 1), ?_, ?_⟩
    · rw [abs_div, abs_of_neg (by linarith : p - 1 < 0), neg_sub, div_le_one hq,
        ← abs_of_pos hq, abs_le_iff_mul_self_le]
      nlinarith
    · have hq' : p - 1 ≠ 0 := by linarith
      have ht : r / (p - 1) * (p - 1) = r := div_mul_cancel₀ r hq'
      have e1 : -(1 - (r / (p - 1)) ^ 2) = (1 + (r / (p - 1)) ^ 2) * p := by
        have : (p - 1) * (-(1 - (r / (p - 1)) ^ 2) - (1 + (r / (p - 1)) ^ 2) * p) = 0 := by
          linear_combination (-1 : ℝ) * h - (r / (p - 1) * (p - 1) + r) * ht
        have := (mul_eq_zero.1 this).resolve_left hq'
        linear_combination this
      have e2 : -(2 * (r / (p - 1))) = (1 + (r / (p - 1)) ^ 2) * r := by
        have : (p - 1) ^ 2 * (-(2 * (r / (p - 1))) - (1 + (r / (p - 1)) ^ 2) * r) = 0 := by
          linear_combination (-r) * h + (-2 * (p - 1) - r / (p - 1) * (p - 1) * r - r * r) * ht
        have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hq')
        linear_combination this
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Mr, Mc] <;>
        first | linear_combination e1 | linear_combination e2 | linear_combination -e2

/-- Real case: `Re T` is a positive multiple of a chart frame times `Mr σ t`. -/
theorem real_frame (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) (hdet : T.det = 1)
    (hY : T.map Complex.im = 0) :
    ∃ ch, ch < 6 ∧ ∃ u v t : ℝ, |u| ≤ 1 / 2 ∧ |v| ≤ 1 / 2 ∧ |t| ≤ 1 ∧ ∃ sg : Bool, ∃ c : ℝ,
      0 < c ∧ T.map Complex.re = c • (Fr ch u v * Mr (if sg then -1 else 1) t) := by
  obtain ⟨hXX, -⟩ := orth_parts T hT
  rw [hY, Matrix.transpose_zero, Matrix.zero_mul, add_zero] at hXX
  have hd : (T.map Complex.re *ᵥ e3) ⬝ᵥ (T.map Complex.re *ᵥ e3) = 1 := by
    rw [dot_mulVec_self, hXX, Matrix.one_mulVec]
    simp [e3, dotProduct, Fin.sum_univ_three]
  obtain ⟨ch, hch, u, v, hu, hv, hF⟩ := cover _ hd
  obtain ⟨p, r, hpr, hM⟩ := frame_decomp (ch2 := 0) (u' := 0) (v' := 0) T hT hdet e3
    (by rw [hY, Matrix.zero_mulVec]) hch (by norm_num) hF
    (by rw [Fr_zero, mu_zero, Matrix.one_mulVec, one_smul])
  obtain ⟨hRe, hIm⟩ := map_re_decomp hM
  rw [Fr_zero, Matrix.mul_one, mu_zero, mul_one] at hRe hIm
  rw [hY, Matrix.mul_zero] at hIm
  have hμ := mu_pos u v
  have hpi : p.im = 0 := by
    have e : mu u v * p.im = 0 := by
      have e := congrFun (congrFun hIm 0) 0
      simpa [Mc] using e.symm
    exact (mul_eq_zero.1 e).resolve_left hμ.ne'
  have hri : r.im = 0 := by
    have e : mu u v * r.im = 0 := by
      have e := congrFun (congrFun hIm 1) 0
      simpa [Mc] using e.symm
    exact (mul_eq_zero.1 e).resolve_left hμ.ne'
  have hc : p.re ^ 2 + r.re ^ 2 = 1 := by
    have e := congrArg Complex.re hpr
    simp [sq, hpi, hri] at e
    linarith
  obtain ⟨sg, t, ht, hMr⟩ := Mc_rot hc
  have hrec : Fr ch u v * ((Fr ch u v)ᵀ * T.map Complex.re) =
      mu u v ^ 2 • T.map Complex.re := by
    rw [← Matrix.mul_assoc, Fr_tt' ch hch u v, Matrix.smul_mul, Matrix.one_mul]
  rw [hRe, Matrix.mul_smul] at hrec
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hMc : Mc p.re r.re 1 = (1 + t ^ 2)⁻¹ • Mr (if sg then -1 else 1) t := by
    rw [hMr, smul_smul, inv_mul_cancel₀ h1t.ne', one_smul]
  refine ⟨ch, hch, u, v, t, hu, hv, ht, sg, (mu u v)⁻¹ * (1 + t ^ 2)⁻¹, by positivity, ?_⟩
  rw [hMc, Matrix.mul_smul, smul_smul] at hrec
  calc T.map Complex.re = (mu u v ^ 2)⁻¹ • (mu u v ^ 2 • T.map Complex.re) := by
        rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hμ.ne'), one_smul]
    _ = _ := by
        rw [← hrec, smul_smul]
        congr 1
        field_simp

/-- Complex case: for every phase `(x, y, D)` with `x² + y² = D²` some real combination of
`Re T`, `Im T` is a positive multiple of `Fr ch1 u v * Mc x y (D z) * (Fr ch2 u' v')ᵀ`,
`|z| ≤ 1`, with chart frames independent of the phase. -/
theorem complex_frame (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : Tᵀ * T = 1) (hdet : T.det = 1)
    (hY : T.map Complex.im ≠ 0) :
    ∃ ch1, ch1 < 6 ∧ ∃ ch2, ch2 < 6 ∧ ∃ u v u' v' : ℝ, |u| ≤ 1 / 2 ∧ |v| ≤ 1 / 2 ∧
      |u'| ≤ 1 / 2 ∧ |v'| ≤ 1 / 2 ∧
      ∀ x y D : ℝ, 0 < D → x ^ 2 + y ^ 2 = D ^ 2 → ∃ α β c z : ℝ, 0 < c ∧ |z| ≤ 1 ∧
        α • T.map Complex.re + β • T.map Complex.im =
          c • (Fr ch1 u v * Mc x y (D * z) * (Fr ch2 u' v')ᵀ) := by
  obtain ⟨b, hYb, hbb, hXb⟩ := exists_ker T hT
  obtain ⟨ch1, h1, u, v, hu, hv, hF1⟩ := cover _ hXb
  obtain ⟨ch2, h2, u', v', hu', hv', hF2⟩ := cover _ hbb
  obtain ⟨p, r, hpr, hM⟩ := frame_decomp T hT hdet b hYb h1 h2 hF1 hF2
  obtain ⟨hRe, hIm⟩ := map_re_decomp hM
  refine ⟨ch1, h1, ch2, h2, u, v, u', v', hu, hv, hu', hv', ?_⟩
  intro x y D hD hxy
  have hμ := mu_pos u v
  have hμ' := mu_pos u' v'
  have hre : p.re ^ 2 - p.im ^ 2 + (r.re ^ 2 - r.im ^ 2) = 1 := by
    have e := congrArg Complex.re hpr
    simp [sq] at e
    linarith
  have him : p.re * p.im + r.re * r.im = 0 := by
    have e := congrArg Complex.im hpr
    simp [sq] at e
    linarith
  have hnb : 0 < p.im ^ 2 + r.im ^ 2 := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have hp2 : p.im = 0 := by nlinarith [sq_nonneg p.im, sq_nonneg r.im]
    have hr2 : r.im = 0 := by nlinarith [sq_nonneg p.im, sq_nonneg r.im]
    apply hY
    have h0 : Mc p.im r.im 0 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Mc, hp2, hr2]
    rw [h0, smul_zero] at hIm
    have hrec := sandwich (Fr_tt' ch1 h1 u v) (Fr_tt' ch2 h2 u' v') (T.map Complex.im)
    rw [hIm, Matrix.mul_zero, Matrix.zero_mul] at hrec
    have hc : mu u v ^ 2 * mu u' v' ^ 2 ≠ 0 := by positivity
    exact ((smul_eq_zero.1 hrec.symm).resolve_left hc)
  have hna1 : 1 ≤ p.re ^ 2 + r.re ^ 2 := by linarith
  have hna : 0 < p.re ^ 2 + r.re ^ 2 := by linarith
  -- the combination
  have hl : 0 < (p.re ^ 2 + r.re ^ 2) * (p.im ^ 2 + r.im ^ 2) := mul_pos hna hnb
  have hx : (x * p.re + y * r.re) * (p.im ^ 2 + r.im ^ 2) * p.re +
      (x * p.im + y * r.im) * (p.re ^ 2 + r.re ^ 2) * p.im =
        (p.re ^ 2 + r.re ^ 2) * (p.im ^ 2 + r.im ^ 2) * x := by
    linear_combination (x * (p.re * p.im - r.re * r.im) + y * (p.re * r.im + p.im * r.re)) * him
  have hy : (x * p.re + y * r.re) * (p.im ^ 2 + r.im ^ 2) * r.re +
      (x * p.im + y * r.im) * (p.re ^ 2 + r.re ^ 2) * r.im =
        (p.re ^ 2 + r.re ^ 2) * (p.im ^ 2 + r.im ^ 2) * y := by
    linear_combination (y * (r.re * r.im - p.re * p.im) + x * (r.re * p.im + r.im * p.re)) * him
  -- `|x p₁ + y r₁| ≤ D |a|²`
  have hs : |x * p.re + y * r.re| ≤ D * (p.re ^ 2 + r.re ^ 2) := by
    have hDn : 0 ≤ D * (p.re ^ 2 + r.re ^ 2) := by positivity
    rw [← abs_of_nonneg hDn, abs_le_iff_mul_self_le]
    nlinarith [sq_nonneg (x * r.re - y * p.re), mul_nonneg (mul_nonneg (sq_nonneg D) hna.le)
      (sub_nonneg.2 hna1)]
  set α := (x * p.re + y * r.re) * (p.im ^ 2 + r.im ^ 2) with hα
  set β := (x * p.im + y * r.im) * (p.re ^ 2 + r.re ^ 2) with hβ
  set l := (p.re ^ 2 + r.re ^ 2) * (p.im ^ 2 + r.im ^ 2) with hl_def
  have hlD : 0 < l * D := mul_pos hl hD
  have hz : l * (D * (α / (l * D))) = α := by field_simp
  refine ⟨α, β, (mu u v ^ 2 * mu u' v' ^ 2)⁻¹ * (mu u v * mu u' v' * l), α / (l * D),
    by positivity, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hlD, div_le_one hlD, hα, abs_mul, abs_of_pos hnb, hl_def]
    calc |x * p.re + y * r.re| * (p.im ^ 2 + r.im ^ 2)
        ≤ D * (p.re ^ 2 + r.re ^ 2) * (p.im ^ 2 + r.im ^ 2) :=
          mul_le_mul_of_nonneg_right hs hnb.le
      _ = _ := by ring
  · have hA : (Fr ch1 u v)ᵀ * (α • T.map Complex.re + β • T.map Complex.im) * Fr ch2 u' v' =
        (mu u v * mu u' v' * l) • Mc x y (D * (α / (l * D))) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, hRe, hIm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Mc] <;>
        first
        | linear_combination (mu u v * mu u' v') * hx
        | linear_combination (mu u v * mu u' v') * hy
        | linear_combination (-(mu u v * mu u' v')) * hy
        | linear_combination (-(mu u v * mu u' v')) * hz
    have hrec := sandwich (Fr_tt' ch1 h1 u v) (Fr_tt' ch2 h2 u' v')
      (α • T.map Complex.re + β • T.map Complex.im)
    rw [hA, Matrix.mul_smul, Matrix.smul_mul] at hrec
    have hc : mu u v ^ 2 * mu u' v' ^ 2 ≠ 0 := by positivity
    calc α • T.map Complex.re + β • T.map Complex.im
        = (mu u v ^ 2 * mu u' v' ^ 2)⁻¹ •
            ((mu u v ^ 2 * mu u' v' ^ 2) • (α • T.map Complex.re + β • T.map Complex.im)) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = _ := by rw [← hrec, smul_smul]

end Icosahedron.K
