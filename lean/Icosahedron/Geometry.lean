import Icosahedron.Defs

/-!
# Face planes of the canonical icosahedron

Every face `j` lies in the plane `n_j · x = φ²`; faces `i` and `opp i` (`i < 10`) are
opposite: `-face (opp i) ⊆ face i`.  The conjugate normals `n_j'` replace `φ` by `1 - φ`.
-/

namespace Icosahedron

open Matrix

/-- Outward normals, coded as `a + b φ`, normalized so that `n_j · v = φ²` on face `j`. -/
def nCode : Fin 20 → Fin 3 → ℤ × ℤ := ![
  ![(1, 0), (1, 0), (1, 0)],       -- 0
  ![(0, 0), (0, 1), (-1, 1)],      -- 1: (0, φ, φ-1)
  ![(-1, 1), (0, 0), (0, 1)],      -- 2: (φ-1, 0, φ)
  ![(1, -1), (0, 0), (0, 1)],      -- 3: (1-φ, 0, φ)
  ![(-1, 0), (1, 0), (1, 0)],      -- 4
  ![(0, 1), (-1, 1), (0, 0)],      -- 5: (φ, φ-1, 0)
  ![(1, 0), (1, 0), (-1, 0)],      -- 6
  ![(0, 0), (0, 1), (1, -1)],      -- 7: (0, φ, 1-φ)
  ![(0, 1), (1, -1), (0, 0)],      -- 8: (φ, 1-φ, 0)
  ![(1, 0), (-1, 0), (1, 0)],      -- 9
  ![(-1, 1), (0, 0), (0, -1)],     -- 10: (φ-1, 0, -φ)
  ![(-1, 0), (1, 0), (-1, 0)],     -- 11
  ![(1, -1), (0, 0), (0, -1)],     -- 12: (1-φ, 0, -φ)
  ![(1, 0), (-1, 0), (-1, 0)],     -- 13
  ![(0, 0), (0, -1), (-1, 1)],     -- 14: (0, -φ, φ-1)
  ![(0, 0), (0, -1), (1, -1)],     -- 15: (0, -φ, 1-φ)
  ![(-1, 0), (-1, 0), (1, 0)],     -- 16
  ![(0, -1), (-1, 1), (0, 0)],     -- 17: (-φ, φ-1, 0)
  ![(0, -1), (1, -1), (0, 0)],     -- 18: (-φ, 1-φ, 0)
  ![(-1, 0), (-1, 0), (-1, 0)]]    -- 19

/-- The face opposite to face `i`, for the representatives `i = 0, …, 9`. -/
def opp : Fin 10 → Fin 20 := ![19, 15, 12, 10, 13, 18, 16, 14, 17, 11]

/-- Representative `i : Fin 10` as a face index. -/
def rep (i : Fin 10) : Fin 20 := ⟨i.1, by omega⟩

noncomputable def normal (j : Fin 20) : Fin 3 → ℝ := fun c => ev (nCode j c)

/-- Conjugate value `a + b (1 - φ)`. -/
noncomputable def evc (x : ℤ × ℤ) : ℝ := x.1 + x.2 * (1 - φ)

noncomputable def normalConj (j : Fin 20) : Fin 3 → ℝ := fun c => evc (nCode j c)

theorem φ_sq : φ ^ 2 = φ + 1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold φ
  linear_combination (1 / 4 : ℝ) * h

theorem normal_dot_vertex (j : Fin 20) (k : Fin 3) :
    normal j ⬝ᵥ vertex (faceIdx j k) = φ ^ 2 := by
  have h := φ_sq
  fin_cases j <;> fin_cases k <;>
    simp [normal, vertex, ev, nCode, vtxCode, faceIdx, dotProduct, Fin.sum_univ_three] <;>
    linarith

theorem convex_hyperplane (w : Fin 3 → ℝ) (c : ℝ) : Convex ℝ {x : Fin 3 → ℝ | w ⬝ᵥ x = c} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hx, hy, smul_eq_mul, smul_eq_mul]
  linear_combination c * hab

theorem convex_gt (w : Fin 3 → ℝ) (c : ℝ) : Convex ℝ {x : Fin 3 → ℝ | c < w ⬝ᵥ x} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at *
  rcases ha.lt_or_eq with ha | ha
  · have h1 := mul_pos ha (sub_pos.2 hx)
    have h2 := mul_nonneg hb (sub_pos.2 hy).le
    have h3 : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    rw [h3]
    nlinarith
  · subst ha; simp at hab; subst hab; simpa using hy

theorem convex_lt (w : Fin 3 → ℝ) (c : ℝ) : Convex ℝ {x : Fin 3 → ℝ | w ⬝ᵥ x < c} := by
  have := convex_gt (-w) (-c)
  simpa [neg_dotProduct, neg_lt_neg_iff] using this

theorem normal_dot_of_mem (j : Fin 20) {x : Fin 3 → ℝ} (hx : x ∈ face j) :
    normal j ⬝ᵥ x = φ ^ 2 := by
  have hsub : face j ⊆ {x | normal j ⬝ᵥ x = φ ^ 2} := by
    apply convexHull_min _ (convex_hyperplane _ _)
    rintro _ ⟨k, rfl⟩
    exact normal_dot_vertex j k
  exact hsub hx

theorem convex_face (j : Fin 20) : Convex ℝ (face j) := convex_convexHull ℝ _

theorem ev_neg (x : ℤ × ℤ) : ev (-x) = -ev x := by
  simp [ev]; ring

theorem opp_vertex (i : Fin 10) (k : Fin 3) :
    ∃ k' : Fin 3, vtxCode (faceIdx (opp i) k) = -vtxCode (faceIdx (rep i) k') := by
  revert i k; decide

theorem neg_mem_face_of_mem_opp (i : Fin 10) {x : Fin 3 → ℝ} (hx : x ∈ face (opp i)) :
    -x ∈ face (rep i) := by
  have hsub : face (opp i) ⊆ -face (rep i) := by
    apply convexHull_min _ ((convex_face _).neg)
    rintro _ ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := opp_vertex i k
    show -vertex (faceIdx (opp i) k) ∈ face (rep i)
    have : -vertex (faceIdx (opp i) k) = vertex (faceIdx (rep i) k') := by
      funext c
      simp only [vertex, Pi.neg_apply, hk', ev_neg, neg_neg]
    rw [this]
    exact subset_convexHull ℝ _ ⟨k', rfl⟩
  exact hsub hx

/-- A linear functional strictly above (or below) `c` on all three vertices stays so on the
whole face. -/
theorem gt_on_face (j : Fin 20) (w : Fin 3 → ℝ) (c : ℝ)
    (h : ∀ k, c < w ⬝ᵥ vertex (faceIdx j k)) {x : Fin 3 → ℝ} (hx : x ∈ face j) : c < w ⬝ᵥ x := by
  have hsub : face j ⊆ {x | c < w ⬝ᵥ x} := by
    apply convexHull_min _ (convex_gt _ _)
    rintro _ ⟨k, rfl⟩
    exact h k
  exact hsub hx

theorem lt_on_face (j : Fin 20) (w : Fin 3 → ℝ) (c : ℝ)
    (h : ∀ k, w ⬝ᵥ vertex (faceIdx j k) < c) {x : Fin 3 → ℝ} (hx : x ∈ face j) : w ⬝ᵥ x < c := by
  have hsub : face j ⊆ {x | w ⬝ᵥ x < c} := by
    apply convexHull_min _ (convex_lt _ _)
    rintro _ ⟨k, rfl⟩
    exact h k
  exact hsub hx

end Icosahedron
