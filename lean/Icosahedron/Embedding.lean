import Mathlib

/-!
# A field automorphism of `ℂ` sending `√5` to `-√5`

`K₀ = QuadraticAlgebra ℚ 1 1 = ℚ(ω)`, `ω² = 1 + ω`, embeds into `ℂ` by `ω ↦ φ`.
Choose a transcendence basis `B` of `ℂ` over `K₀`; then `ℂ` is an algebraic closure of
`S = K₀[B] ≅ MvPolynomial B K₀`.  Galois conjugation on coefficients is a ring automorphism
of `S`, and `IsAlgClosure.equivOfEquiv` extends it to `ℂ`.
-/

namespace Icosahedron

noncomputable section

/-- `ℚ(φ)` as an abstract quadratic field. -/
abbrev K₀ := QuadraticAlgebra ℚ 1 1

theorem no_rat_golden (r : ℚ) : r ^ 2 ≠ 1 + 1 * r := by
  intro hr
  have h5 : ((2 * r - 1 : ℚ) : ℝ) ^ 2 = 5 := by
    have : (2 * r - 1) ^ 2 = (5 : ℚ) := by linear_combination 4 * hr
    exact_mod_cast this
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  have hsq : Real.sqrt 5 = |((2 * r - 1 : ℚ) : ℝ)| := by
    rw [← h5, Real.sqrt_sq_eq_abs]
  exact hirr ⟨|2 * r - 1|, by rw [hsq]; push_cast; rfl⟩

instance : Fact (∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r) := ⟨no_rat_golden⟩

/-- The golden ratio in `ℂ`. -/
def φc : ℂ := ((1 + Real.sqrt 5) / 2 : ℝ)

theorem φc_sq : φc * φc = (1 : ℚ) • (1 : ℂ) + (1 : ℚ) • φc := by
  have h : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h' : (Real.sqrt 5 : ℂ) * Real.sqrt 5 = 5 := by exact_mod_cast h
  simp only [φc, one_smul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  linear_combination (1 / 4 : ℂ) * h'

/-- Embedding `K₀ → ℂ`, `ω ↦ φ`. -/
def ι : K₀ →ₐ[ℚ] ℂ := QuadraticAlgebra.lift ⟨φc, φc_sq⟩

theorem ι_apply (z : K₀) : ι z = (z.re : ℂ) + (z.im : ℂ) * φc := by
  change z.re • (1 : ℂ) + z.im • φc = _
  rw [Rat.smul_def, Rat.smul_def, mul_one]

/-- There is a field automorphism of `ℂ` exchanging `φ` with its conjugate `1 - φ`. -/
theorem exists_conj_aut : ∃ τ : ℂ ≃+* ℂ, τ φc = 1 - φc := by
  let _ : Algebra K₀ ℂ := ι.toRingHom.toAlgebra
  have : FaithfulSMul K₀ ℂ :=
    (faithfulSMul_iff_algebraMap_injective K₀ ℂ).mpr ι.toRingHom.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K₀ ℂ
  let S := Algebra.adjoin K₀ (Set.range ((↑) : s → ℂ))
  have : IsAlgClosure S ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let aev := hs.1.aevalEquiv
  let hSR : S ≃+* S := aev.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s (starRingAut : K₀ ≃+* K₀)).trans aev.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ hSR, ?_⟩
  have hω : φc = algebraMap S ℂ (algebraMap K₀ S QuadraticAlgebra.omega) := by
    change φc = ι QuadraticAlgebra.omega
    simp [ι_apply]
  have hS : hSR (algebraMap K₀ S QuadraticAlgebra.omega) =
      algebraMap K₀ S (star QuadraticAlgebra.omega) := by
    simp only [hSR, RingEquiv.trans_apply,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, MvPolynomial.mapEquiv_apply]
    rw [← MvPolynomial.C_eq_algebraMap (R := K₀), MvPolynomial.map_C]
    exact aev.commutes _
  rw [hω, IsAlgClosure.equivOfEquiv_algebraMap, hS]
  change ι (star QuadraticAlgebra.omega) = 1 - ι QuadraticAlgebra.omega
  simp [ι_apply, QuadraticAlgebra.omega]
  ring

/-- The same automorphism sends `√5` to `-√5`. -/
theorem exists_aut_sqrt5 : ∃ τ : ℂ ≃+* ℂ, τ φc = 1 - φc ∧ τ (Real.sqrt 5 : ℂ) = -Real.sqrt 5 := by
  obtain ⟨τ, hτ⟩ := exists_conj_aut
  refine ⟨τ, hτ, ?_⟩
  have h5 : (Real.sqrt 5 : ℂ) = 2 * φc - 1 := by
    simp only [φc, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  rw [h5, map_sub, map_mul, map_one, hτ, map_ofNat]
  ring

end

end Icosahedron
