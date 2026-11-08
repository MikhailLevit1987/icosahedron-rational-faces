import Icosahedron.KSound
import Icosahedron.Reduction

/-!
# From the kernel checker to separation

Real semantics of the chart frames and of the two searches:

* `rsearch_sound`: a successful real search gives `Separated (Fr ch u v * Mr σ t)` on the
  whole chart square times `t ∈ [-1, 1]`;
* `csearchD_sound`: a successful complex search gives, for every pair of chart points, a
  phase `n` with `Separated (Fr ch1 u v * Mc X Y (D z) * (Fr ch2 u' v')ᵀ)` for all
  `z ∈ [-1, 1]`.
-/

namespace Icosahedron.K

open Icosahedron Matrix

/-- `Rq(1,u,v,0)`: the unnormalized rotation of the quaternion `1 + u i + v j`. -/
def Rq (u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + u ^ 2 - v ^ 2, 2 * u * v, 2 * v; 2 * u * v, 1 - u ^ 2 + v ^ 2, -(2 * u);
     -(2 * v), 2 * u, 1 - u ^ 2 - v ^ 2]

/-- The six chart matrices (columns `e_i, σ e_j, σ e_k`). -/
def chartM : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 2 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  | 3 => !![0, 0, -1; 1, 0, 0; 0, -1, 0]
  | 4 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | _ => !![0, -1, 0; 0, 0, -1; 1, 0, 0]

/-- Chart frame. -/
def Fr (ch : ℕ) (u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := chartM ch * Rq u v

/-- Real-case middle matrix `diag(σ((1-t²) I + 2t J), 1 + t²)`. -/
def Mr (σ t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![σ * (1 - t ^ 2), -(σ * (2 * t)), 0; σ * (2 * t), σ * (1 - t ^ 2), 0; 0, 0, 1 + t ^ 2]

/-- Complex-case middle matrix `diag(x I + y J, z)`. -/
def Mc (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![x, -y, 0; y, x, 0; 0, 0, z]

/-- Signed natural number. -/
def sgnR (b : Bool) (x : ℕ) : ℝ := if b then -(x : ℝ) else x

/-! ## Data tables -/

def dz : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | _ => -1

theorem dv_eq (t : ℕ) : dv t = (dz t : ℝ) := by
  rcases t with _ | _ | t <;> simp [dv, dz]

theorem nSC_code : ∀ i : Fin 10, ∀ c : Fin 3,
    dz (nSC i c).a = (nCode (rep i) c).1 + (nCode (rep i) c).2 ∧
      dz (nSC i c).b = -(nCode (rep i) c).2 := by decide

theorem vSC_code : ∀ i : Fin 10, ∀ k : Fin 3, ∀ c : Fin 3,
    dz (vSC (fIdx i k) c).a = (vtxCode (faceIdx (rep i) k) c).1 ∧
      dz (vSC (fIdx i k) c).b = (vtxCode (faceIdx (rep i) k) c).2 := by decide

theorem nSC_val (i : Fin 10) (c : Fin 3) : (nSC i c).val = normalConj (rep i) c := by
  obtain ⟨ha, hb⟩ := nSC_code i c
  simp only [SC.val, dv_eq, ha, hb, normalConj, evc]
  push_cast; ring

theorem vSC_val (i : Fin 10) (k c : Fin 3) :
    (vSC (fIdx i k) c).val = vertex (faceIdx (rep i) k) c := by
  obtain ⟨ha, hb⟩ := vSC_code i k c
  simp only [SC.val, dv_eq, ha, hb, vertex, ev]

/-- Values of a vector of small constants. -/
noncomputable def scv (κ : V3 SC) : Fin 3 → ℝ := ![κ.x.val, κ.y.val, κ.z.val]

theorem chartT_scv (ch : ℕ) (hch : ch < 6) (κ : ℕ → SC) :
    scv (chartT ch κ) = (chartM ch)ᵀ *ᵥ fun r => (κ r).val := by
  funext c
  interval_cases ch <;> fin_cases c <;>
    simp [scv, chartT, chartM, mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Frame polynomials -/

theorem rq_eval (N up un vp vn : ℕ) (hN : (N : ℝ) ≠ 0) (r c : Fin 3) (s t : ℝ) :
    (rq N up un vp vn r c).eval s t =
      (N : ℝ) ^ 2 * Rq (((up : ℝ) - un + s) / N) (((vp : ℝ) - vn + t) / N) r c := by
  fin_cases r <;> fin_cases c <;>
    simp [rq, P6.eval, ZP.ev, zI, Rq, Nat.add_eq, Nat.mul_eq] <;> field_simp <;> ring

theorem rqT_ev (N up un vp vn : ℕ) (hN : (N : ℝ) ≠ 0) (κ : V3 SC) (s t : ℝ) :
    (rqT N up un vp vn κ).ev s t = (N : ℝ) ^ 2 •
      ((Rq (((up : ℝ) - un + s) / N) (((vp : ℝ) - vn + t) / N))ᵀ *ᵥ scv κ) := by
  have h00 := rq_eval N up un vp vn hN 0 0 s t
  have h01 := rq_eval N up un vp vn hN 0 1 s t
  have h02 := rq_eval N up un vp vn hN 0 2 s t
  have h10 := rq_eval N up un vp vn hN 1 0 s t
  have h11 := rq_eval N up un vp vn hN 1 1 s t
  have h12 := rq_eval N up un vp vn hN 1 2 s t
  have h20 := rq_eval N up un vp vn hN 2 0 s t
  have h21 := rq_eval N up un vp vn hN 2 1 s t
  have h22 := rq_eval N up un vp vn hN 2 2 s t
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  funext c
  fin_cases c <;>
    simp only [rqT, V3.ev, scv, P6.eval_add, P6.eval_smulSC, h00, h01, h02, h10, h11, h12, h20,
      h21, h22, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Fin.sum_univ_three, transpose_apply] <;>
    ring

/-! ## Blocks -/

/-- Chart coordinate of a square cell: `u = (2j + 1 - 2^m + s) / 2^(m+1)`. -/
noncomputable def cco (j m : ℕ) (s : ℝ) : ℝ := ((2 * j + 1 : ℝ) - 2 ^ m + s) / 2 ^ (m + 1)

/-- Coordinate of a `t`-cell: `t = (2j + 1 - 2^m + s) / 2^m`. -/
noncomputable def tco (j m : ℕ) (s : ℝ) : ℝ := ((2 * j + 1 : ℝ) - 2 ^ m + s) / 2 ^ m

theorem cast_cco (j m : ℕ) (s : ℝ) :
    (((Nat.add (Nat.add j j) 1 : ℕ) : ℝ) - ((Nat.pow 2 m : ℕ) : ℝ) + s) /
      ((Nat.add (Nat.pow 2 m) (Nat.pow 2 m) : ℕ) : ℝ) = cco j m s := by
  simp only [cco, Nat.add_eq, Nat.pow_eq]; push_cast; ring

theorem cast_N (m : ℕ) : ((Nat.add (Nat.pow 2 m) (Nat.pow 2 m) : ℕ) : ℝ) = 2 ^ (m + 1) := by
  simp only [Nat.add_eq, Nat.pow_eq]; push_cast; ring

theorem nC_fun (i : Fin 10) : (fun r : Fin 3 => (nSC i r).val) = normalConj (rep i) := by
  funext r; exact nSC_val i r

theorem vC_fun (i : Fin 10) (k : Fin 3) :
    (fun r : Fin 3 => (vSC (fIdx i k) r).val) = vertex (faceIdx (rep i) k) := by
  funext r; exact vSC_val i k r

theorem blockA_ev (ch ju jv m : ℕ) (hch : ch < 6) (i : Fin 10) (s t : ℝ) :
    (blockA ch ju jv m i).ev s t = ((2 : ℝ) ^ (m + 1)) ^ 2 •
      ((Fr ch (cco ju m s) (cco jv m t))ᵀ *ᵥ normalConj (rep i)) := by
  unfold blockA
  rw [rqT_ev _ _ _ _ _ (by rw [cast_N]; positivity), chartT_scv ch hch, nC_fun, cast_cco,
    cast_cco, cast_N, Fr, transpose_mul, ← mulVec_mulVec]

theorem blockB_ev (ch ju jv m : ℕ) (hch : ch < 6) (i : Fin 10) (k : Fin 3) (s t : ℝ) :
    (blockB ch ju jv m i k).ev s t = ((2 : ℝ) ^ (m + 1)) ^ 2 •
      ((Fr ch (cco ju m s) (cco jv m t))ᵀ *ᵥ vertex (faceIdx (rep i) k)) := by
  unfold blockB
  rw [rqT_ev _ _ _ _ _ (by rw [cast_N]; positivity), chartT_scv ch hch, vC_fun, cast_cco,
    cast_cco, cast_N, Fr, transpose_mul, ← mulVec_mulVec]

theorem eval_cond_neg (b : Bool) (p : P6) (s t : ℝ) :
    (cond b (P6.neg p) p).eval s t = (if b then -1 else 1) * p.eval s t := by
  cases b <;> simp

theorem zI_ev (p n : ℕ) : (zI p n).ev = (p : ℝ) - n := by simp [zI, ZP.ev]

theorem tpoly_eval (a b c : ZP) (s : ℝ) :
    (tpoly a b c).eval s 0 = a.ev + b.ev * s + c.ev * s ^ 2 := by
  simp [tpoly, P6.eval]

theorem blockWr_ev (sg : Bool) (jt m : ℕ) (i : Fin 10) (k : Fin 3) (s : ℝ) :
    (blockWr sg jt m i k).ev s 0 = ((2 : ℝ) ^ m) ^ 2 •
      (Mr (if sg then -1 else 1) (tco jt m s) *ᵥ vertex (faceIdx (rep i) k)) := by
  have e0 := vSC_val i k 0
  have e1 := vSC_val i k 1
  have e2 := vSC_val i k 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  funext c
  fin_cases c <;>
    simp only [blockWr, V3.ev, P6.eval_sub, P6.eval_add, P6.eval_smulSC, eval_cond_neg,
      tpoly_eval, zI_ev, ZP.ev_zero, e0, e1, e2, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Fin.sum_univ_three, Mr,
      Matrix.of_apply, tco, Nat.add_eq, Nat.mul_eq, Nat.pow_eq] <;>
    push_cast <;> cases sg <;> (try simp only [Bool.false_eq_true, ite_false, ite_true]) <;>
    field_simp <;> ring

theorem applyPh_ev (p : Ph) (b : V3 P6) (s t : ℝ) :
    (applyPh p b).ev s t = Mc (sgnR p.xs p.x) (sgnR p.ys p.y) (sgnR p.zs p.z) *ᵥ b.ev s t := by
  obtain ⟨xs, x, ys, y, zs, z⟩ := p
  funext c
  fin_cases c <;>
    simp only [applyPh, V3.ev, P6.eval_sub, P6.eval_add, P6.eval_smulS, Mc, sgnR, mulVec,
      dotProduct, Fin.sum_univ_three, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply] <;> ring

/-! ## Face values -/

theorem fval_FM (F M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 10) (k : Fin 3) :
    fval (F * M) i k = (Fᵀ *ᵥ normalConj (rep i)) ⬝ᵥ (M *ᵥ vertex (faceIdx (rep i) k)) := by
  unfold fval
  rw [← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

theorem fval_FMG (F M G : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 10) (k : Fin 3) :
    fval (F * M * Gᵀ) i k =
      (Fᵀ *ᵥ normalConj (rep i)) ⬝ᵥ (M *ᵥ (Gᵀ *ᵥ vertex (faceIdx (rep i) k))) := by
  unfold fval
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [mulVec_transpose]

theorem sep_of_pair (A : Matrix (Fin 3) (Fin 3) ℝ) (i1 i2 : Fin 10)
    (h : ∀ k k' : Fin 3, fval A i2 k' < fval A i1 k) : Separated A := by
  intro c
  by_cases hc : ∀ k, c < fval A i1 k
  · exact ⟨i1, Or.inl hc⟩
  · push_neg at hc
    obtain ⟨k0, hk0⟩ := hc
    exact ⟨i2, Or.inr fun k' => lt_of_lt_of_le (h k0 k') hk0⟩

/-! ## Cells -/

def inSq (j m : ℕ) (u : ℝ) : Prop :=
  (j : ℝ) / 2 ^ m - 1 / 2 ≤ u ∧ u ≤ ((j : ℝ) + 1) / 2 ^ m - 1 / 2

def inT (j m : ℕ) (t : ℝ) : Prop :=
  2 * (j : ℝ) / 2 ^ m - 1 ≤ t ∧ t ≤ 2 * ((j : ℝ) + 1) / 2 ^ m - 1

theorem inSq_coord {j m : ℕ} {u : ℝ} (h : inSq j m u) : ∃ s, |s| ≤ 1 ∧ u = cco j m s := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨h1, h2⟩ := h
  rw [sub_le_iff_le_add, div_le_iff₀ hp] at h1
  rw [le_sub_iff_add_le, le_div_iff₀ hp] at h2
  refine ⟨2 * 2 ^ m * u - (2 * j + 1 - 2 ^ m), abs_le.2 ⟨by nlinarith, by nlinarith⟩, ?_⟩
  unfold cco
  rw [pow_succ]
  field_simp
  ring

theorem inT_coord {j m : ℕ} {t : ℝ} (h : inT j m t) : ∃ s, |s| ≤ 1 ∧ t = tco j m s := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨h1, h2⟩ := h
  rw [sub_le_iff_le_add, div_le_iff₀ hp] at h1
  rw [le_sub_iff_add_le, le_div_iff₀ hp] at h2
  refine ⟨2 ^ m * t - (2 * j + 1 - 2 ^ m), abs_le.2 ⟨by nlinarith, by nlinarith⟩, ?_⟩
  unfold tco
  field_simp
  ring

theorem inSq_split {j m : ℕ} {u : ℝ} (h : inSq j m u) :
    inSq (j + j) (m + 1) u ∨ inSq (j + j + 1) (m + 1) u := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨h1, h2⟩ := h
  have e1 : ((j + j : ℕ) : ℝ) / 2 ^ (m + 1) = (j : ℝ) / 2 ^ m := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e2 : (((j + j + 1 : ℕ) : ℝ) + 1) / 2 ^ (m + 1) = ((j : ℝ) + 1) / 2 ^ m := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e3 : ((j + j : ℕ) : ℝ) + 1 = ((j + j + 1 : ℕ) : ℝ) := by push_cast; ring
  by_cases hc : u ≤ (((j + j : ℕ) : ℝ) + 1) / 2 ^ (m + 1) - 1 / 2
  · exact Or.inl ⟨by rw [e1]; exact h1, hc⟩
  · push_neg at hc
    refine Or.inr ⟨?_, by rw [e2]; exact h2⟩
    rw [← e3]; exact hc.le

theorem inT_split {j m : ℕ} {t : ℝ} (h : inT j m t) :
    inT (j + j) (m + 1) t ∨ inT (j + j + 1) (m + 1) t := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨h1, h2⟩ := h
  have e1 : 2 * ((j + j : ℕ) : ℝ) / 2 ^ (m + 1) = 2 * (j : ℝ) / 2 ^ m := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e2 : 2 * (((j + j + 1 : ℕ) : ℝ) + 1) / 2 ^ (m + 1) = 2 * ((j : ℝ) + 1) / 2 ^ m := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e3 : ((j + j : ℕ) : ℝ) + 1 = ((j + j + 1 : ℕ) : ℝ) := by push_cast; ring
  by_cases hc : t ≤ 2 * (((j + j : ℕ) : ℝ) + 1) / 2 ^ (m + 1) - 1
  · exact Or.inl ⟨by rw [e1]; exact h1, hc⟩
  · push_neg at hc
    refine Or.inr ⟨?_, by rw [e2]; exact h2⟩
    rw [← e3]; exact hc.le

/-! ## Real search -/

theorem cellOK_sound {A : Nat → V3 P6} {W : Nat → Nat → V3 P6} (h : cellOK A W = true) :
    ∃ i1 i2, i1 < 10 ∧ i2 < 10 ∧ pairOK A W i1 i2 = true := by
  unfold cellOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨_, _, h.1.1, h.1.2, h.2⟩

theorem smul_dot_smul (a b : ℝ) (x y : Fin 3 → ℝ) : (a • x) ⬝ᵥ (b • y) = a * b * (x ⬝ᵥ y) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

theorem rcell_sound (ch : ℕ) (hch : ch < 6) (sg : Bool) (c : RCell)
    (h : rcellOK ch sg c = true) (u v t : ℝ) (hu : inSq c.ju c.m1 u) (hv : inSq c.jv c.m1 v)
    (ht : inT c.jt c.m2 t) : Separated (Fr ch u v * Mr (if sg then -1 else 1) t) := by
  obtain ⟨s1, hs1, rfl⟩ := inSq_coord hu
  obtain ⟨s2, hs2, rfl⟩ := inSq_coord hv
  obtain ⟨s3, hs3, rfl⟩ := inT_coord ht
  obtain ⟨i1, i2, hi1, hi2, hp⟩ := cellOK_sound h
  refine sep_of_pair _ ⟨i1, hi1⟩ ⟨i2, hi2⟩ fun k k' => ?_
  have key := pairOK_sound hp hs1 hs2 hs3 (by simp : |(0 : ℝ)| ≤ 1) k.isLt k'.isLt
  have a1 := blockA_ev ch c.ju c.jv c.m1 hch ⟨i1, hi1⟩ s1 s2
  have a2 := blockA_ev ch c.ju c.jv c.m1 hch ⟨i2, hi2⟩ s1 s2
  have w1 := blockWr_ev sg c.jt c.m2 ⟨i1, hi1⟩ k s3
  have w2 := blockWr_ev sg c.jt c.m2 ⟨i2, hi2⟩ k' s3
  simp only [Fin.val_mk] at a1 a2 w1 w2
  rw [a1, a2, w1, w2, smul_dot_smul, smul_dot_smul] at key
  rw [fval_FM, fval_FM]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (c.m1 + 1)) ^ 2 * ((2 : ℝ) ^ c.m2) ^ 2 := by positivity
  exact lt_of_mul_lt_mul_left key hpos.le

theorem rsearch_succ (ch : ℕ) (sg : Bool) (n : ℕ) (c : RCell) :
    rsearch ch sg (n + 1) c = (rcellOK ch sg c ||
      cond (Nat.ble c.m1 c.m2)
        (rsearch ch sg n ⟨c.ju + c.ju, c.jv + c.jv, c.m1 + 1, c.jt, c.m2⟩ &&
          rsearch ch sg n ⟨c.ju + c.ju + 1, c.jv + c.jv, c.m1 + 1, c.jt, c.m2⟩ &&
          rsearch ch sg n ⟨c.ju + c.ju, c.jv + c.jv + 1, c.m1 + 1, c.jt, c.m2⟩ &&
          rsearch ch sg n ⟨c.ju + c.ju + 1, c.jv + c.jv + 1, c.m1 + 1, c.jt, c.m2⟩)
        (rsearch ch sg n ⟨c.ju, c.jv, c.m1, c.jt + c.jt, c.m2 + 1⟩ &&
          rsearch ch sg n ⟨c.ju, c.jv, c.m1, c.jt + c.jt + 1, c.m2 + 1⟩)) := rfl

theorem rsearch_sound (ch : ℕ) (hch : ch < 6) (sg : Bool) (fuel : ℕ) :
    ∀ c : RCell, rsearch ch sg fuel c = true → ∀ u v t, inSq c.ju c.m1 u → inSq c.jv c.m1 v →
      inT c.jt c.m2 t → Separated (Fr ch u v * Mr (if sg then -1 else 1) t) := by
  induction fuel with
  | zero => intro c h; exact rcell_sound ch hch sg c h
  | succ n ih =>
    intro c h u v t hu hv ht
    rw [rsearch_succ, Bool.or_eq_true] at h
    rcases h with h | h
    · exact rcell_sound ch hch sg c h u v t hu hv ht
    · cases hm : Nat.ble c.m1 c.m2
      · rw [hm, Bool.cond_false, Bool.and_eq_true] at h
        rcases inT_split ht with ht' | ht'
        · exact ih _ h.1 u v t hu hv ht'
        · exact ih _ h.2 u v t hu hv ht'
      · rw [hm, Bool.cond_true] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rcases inSq_split hu with hu' | hu' <;> rcases inSq_split hv with hv' | hv'
        · exact ih _ h1 u v t hu' hv' ht
        · exact ih _ h3 u v t hu' hv' ht
        · exact ih _ h2 u v t hu' hv' ht
        · exact ih _ h4 u v t hu' hv' ht

/-! ## Complex search -/

theorem wAt_ev (B : Nat → Nat → V3 P6) (xs : Bool) (x y : ℕ) (zs : Bool) (zv : ℕ) (i k : ℕ)
    (s t : ℝ) : (wAt B xs x y zs zv i k).ev s t =
      Mc (sgnR xs x) y (sgnR zs zv) *ᵥ (B i k).ev s t := by
  rw [wAt, applyPh_ev]; simp [sgnR]

/-- The difference of two face values is affine in `z`. -/
theorem gap_affine (a1 b1 a2 b2 : Fin 3 → ℝ) (X Y Z : ℝ) :
    a1 ⬝ᵥ (Mc X Y Z *ᵥ b1) - a2 ⬝ᵥ (Mc X Y Z *ᵥ b2) =
      (a1 ⬝ᵥ (Mc X Y 0 *ᵥ b1) - a2 ⬝ᵥ (Mc X Y 0 *ᵥ b2)) + Z * (a1 2 * b1 2 - a2 2 * b2 2) := by
  simp [Mc, mulVec, dotProduct, Fin.sum_univ_three]; ring

theorem gap_interp (a1 b1 a2 b2 : Fin 3 → ℝ) (X Y za zb Z : ℝ) (hz : za ≤ Z ∧ Z ≤ zb)
    (ha : a2 ⬝ᵥ (Mc X Y za *ᵥ b2) < a1 ⬝ᵥ (Mc X Y za *ᵥ b1))
    (hb : a2 ⬝ᵥ (Mc X Y zb *ᵥ b2) < a1 ⬝ᵥ (Mc X Y zb *ᵥ b1)) :
    a2 ⬝ᵥ (Mc X Y Z *ᵥ b2) < a1 ⬝ᵥ (Mc X Y Z *ᵥ b1) := by
  have ea := gap_affine a1 b1 a2 b2 X Y za
  have eb := gap_affine a1 b1 a2 b2 X Y zb
  have ez := gap_affine a1 b1 a2 b2 X Y Z
  set g := a1 ⬝ᵥ (Mc X Y 0 *ᵥ b1) - a2 ⬝ᵥ (Mc X Y 0 *ᵥ b2)
  set e := a1 2 * b1 2 - a2 2 * b2 2
  rcases le_total 0 e with he | he
  · nlinarith [mul_le_mul_of_nonneg_right hz.1 he]
  · nlinarith [mul_le_mul_of_nonpos_right hz.2 he]

/-- Semantic content of a leaf for the pair `(i1, i2)` on `Z ∈ [Za, Zb]`. -/
theorem zpair_sound {ch1 ch2 : ℕ} (h1 : ch1 < 6) (h2 : ch2 < 6) (c : CCell) {xs : Bool}
    {x y : ℕ} {zas : Bool} {za : ℕ} {zbs : Bool} {zb : ℕ} {i1 i2 : ℕ}
    (h : zpairOK (blockA ch1 c.ju c.jv c.m1) (blockB ch2 c.ku c.kv c.m2) xs x y zas za zbs zb
      i1 i2 = true) {s1 s2 s3 s4 : ℝ} (hs1 : |s1| ≤ 1) (hs2 : |s2| ≤ 1) (hs3 : |s3| ≤ 1)
    (hs4 : |s4| ≤ 1) (Z : ℝ) (hZ : sgnR zas za ≤ Z ∧ Z ≤ sgnR zbs zb) :
    Separated (Fr ch1 (cco c.ju c.m1 s1) (cco c.jv c.m1 s2) * Mc (sgnR xs x) y Z *
      (Fr ch2 (cco c.ku c.m2 s3) (cco c.kv c.m2 s4))ᵀ) := by
  simp only [zpairOK, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hi1, hi2⟩, hpa⟩, hpb⟩ := h
  refine sep_of_pair _ ⟨i1, hi1⟩ ⟨i2, hi2⟩ fun k k' => ?_
  rw [fval_FMG, fval_FMG]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (c.m1 + 1)) ^ 2 * ((2 : ℝ) ^ (c.m2 + 1)) ^ 2 := by positivity
  have conv : ∀ (zs' : Bool) (zv : ℕ),
      pairOK (blockA ch1 c.ju c.jv c.m1) (wAt (blockB ch2 c.ku c.kv c.m2) xs x y zs' zv) i1 i2 =
        true →
      (Fr ch1 (cco c.ju c.m1 s1) (cco c.jv c.m1 s2))ᵀ *ᵥ normalConj (rep ⟨i2, hi2⟩) ⬝ᵥ
          (Mc (sgnR xs x) y (sgnR zs' zv) *ᵥ
            ((Fr ch2 (cco c.ku c.m2 s3) (cco c.kv c.m2 s4))ᵀ *ᵥ
              vertex (faceIdx (rep ⟨i2, hi2⟩) k'))) <
        (Fr ch1 (cco c.ju c.m1 s1) (cco c.jv c.m1 s2))ᵀ *ᵥ normalConj (rep ⟨i1, hi1⟩) ⬝ᵥ
          (Mc (sgnR xs x) y (sgnR zs' zv) *ᵥ
            ((Fr ch2 (cco c.ku c.m2 s3) (cco c.kv c.m2 s4))ᵀ *ᵥ
              vertex (faceIdx (rep ⟨i1, hi1⟩) k))) := by
    intro zs' zv hp
    have key := pairOK_sound hp hs1 hs2 hs3 hs4 k.isLt k'.isLt
    rw [wAt_ev, wAt_ev] at key
    have a1 := blockA_ev ch1 c.ju c.jv c.m1 h1 ⟨i1, hi1⟩ s1 s2
    have a2 := blockA_ev ch1 c.ju c.jv c.m1 h1 ⟨i2, hi2⟩ s1 s2
    have b1 := blockB_ev ch2 c.ku c.kv c.m2 h2 ⟨i1, hi1⟩ k s3 s4
    have b2 := blockB_ev ch2 c.ku c.kv c.m2 h2 ⟨i2, hi2⟩ k' s3 s4
    rw [a1, a2, b1, b2, mulVec_smul, mulVec_smul, smul_dot_smul, smul_dot_smul] at key
    exact lt_of_mul_lt_mul_left key hpos.le
  exact gap_interp _ _ _ _ _ _ _ _ Z hZ (conv zas za hpa) (conv zbs zb hpb)

theorem cond2 {b : Bool} {x y : Option ℕ} {z : ℕ} (h : cond b x y = some z) :
    (b = true ∧ x = some z) ∨ (b = false ∧ y = some z) := by
  cases b <;> simp_all

theorem cond_some {b : Bool} {x : ℕ} {z : ℕ} (h : cond b (some x) none = some z) :
    b = true := by
  cases b <;> simp_all

/-- Phase data as reals: `X = ±x`, `Y = y`, `D = d`. -/
noncomputable def phX (n : ℕ) : ℝ := sgnR (phase n).1 (phase n).2.1
def phY (n : ℕ) : ℕ := (phase n).2.2.1
def phD (n : ℕ) : ℕ := (phase n).2.2.2

theorem phD_pos (n : ℕ) : 0 < phD n := by
  unfold phD phase
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp

theorem cleaf_sound {ch1 ch2 : ℕ} (h1 : ch1 < 6) (h2 : ch2 < 6) (c : CCell) {s s' : ℕ}
    (h : cleaf ch1 ch2 c s = some s') {s1 s2 s3 s4 : ℝ} (hs1 : |s1| ≤ 1) (hs2 : |s2| ≤ 1)
    (hs3 : |s3| ≤ 1) (hs4 : |s4| ≤ 1) : ∃ n : ℕ, ∀ z : ℝ, |z| ≤ 1 →
      Separated (Fr ch1 (cco c.ju c.m1 s1) (cco c.jv c.m1 s2) *
        Mc (phX n) (phY n) (phD n * z) * (Fr ch2 (cco c.ku c.m2 s3) (cco c.kv c.m2 s4))ᵀ) := by
  dsimp only [cleaf] at h
  rcases cond2 h with ⟨_, h⟩ | ⟨_, h⟩
  · -- leaf of type 1
    have hl := cond_some h
    refine ⟨dg (dr s), fun z hz => ?_⟩
    unfold leaf1OK at hl
    have hD : (0 : ℝ) ≤ phD (dg (dr s)) := by exact_mod_cast (phD_pos _).le
    refine zpair_sound h1 h2 c hl hs1 hs2 hs3 hs4 _ ⟨?_, ?_⟩
    · have := (abs_le.1 hz).1
      simp only [sgnR, ite_true]
      unfold phD at hD ⊢
      nlinarith
    · have := (abs_le.1 hz).2
      simp only [sgnR, Bool.false_eq_true, ite_false]
      unfold phD at hD ⊢
      nlinarith
  · rcases cond2 h with ⟨_, h⟩ | ⟨_, h⟩
    · -- leaf of type 2
      have hl := cond_some h
      refine ⟨dg (dr s), fun z hz => ?_⟩
      unfold leaf2OK at hl
      rw [Bool.and_eq_true] at hl
      have hD : (0 : ℝ) ≤ phD (dg (dr s)) := by exact_mod_cast (phD_pos _).le
      rcases le_total z 0 with hz0 | hz0
      · refine zpair_sound h1 h2 c hl.1 hs1 hs2 hs3 hs4 _ ⟨?_, ?_⟩
        · have := (abs_le.1 hz).1
          simp only [sgnR, ite_true]
          unfold phD at hD ⊢
          nlinarith
        · simp only [sgnR, Bool.false_eq_true, ite_false, Nat.cast_zero]
          unfold phD at hD ⊢
          nlinarith
      · refine zpair_sound h1 h2 c hl.2 hs1 hs2 hs3 hs4 _ ⟨?_, ?_⟩
        · simp only [sgnR, Bool.false_eq_true, ite_false, Nat.cast_zero]
          unfold phD at hD ⊢
          nlinarith
        · have := (abs_le.1 hz).2
          simp only [sgnR, Bool.false_eq_true, ite_false]
          unfold phD at hD ⊢
          nlinarith
    · cases h

theorem obind_some {o : Option ℕ} {f : ℕ → Option ℕ} {z : ℕ} (h : obind o f = some z) :
    ∃ y, o = some y ∧ f y = some z := by
  cases o with
  | none => cases h
  | some y => exact ⟨y, rfl, h⟩

theorem csearchD_succ (ch1 ch2 n : ℕ) (c : CCell) (s : ℕ) :
    csearchD ch1 ch2 (n + 1) c s =
      cond (Nat.beq (dg s) 0)
        (cond (Nat.ble c.m1 c.m2)
          (obind (csearchD ch1 ch2 n ⟨c.ju + c.ju, c.jv + c.jv, c.m1 + 1, c.ku, c.kv, c.m2⟩ (dr s))
            fun s => obind (csearchD ch1 ch2 n
              ⟨c.ju + c.ju + 1, c.jv + c.jv, c.m1 + 1, c.ku, c.kv, c.m2⟩ s)
            fun s => obind (csearchD ch1 ch2 n
              ⟨c.ju + c.ju, c.jv + c.jv + 1, c.m1 + 1, c.ku, c.kv, c.m2⟩ s)
            fun s => csearchD ch1 ch2 n
              ⟨c.ju + c.ju + 1, c.jv + c.jv + 1, c.m1 + 1, c.ku, c.kv, c.m2⟩ s)
          (obind (csearchD ch1 ch2 n ⟨c.ju, c.jv, c.m1, c.ku + c.ku, c.kv + c.kv, c.m2 + 1⟩ (dr s))
            fun s => obind (csearchD ch1 ch2 n
              ⟨c.ju, c.jv, c.m1, c.ku + c.ku + 1, c.kv + c.kv, c.m2 + 1⟩ s)
            fun s => obind (csearchD ch1 ch2 n
              ⟨c.ju, c.jv, c.m1, c.ku + c.ku, c.kv + c.kv + 1, c.m2 + 1⟩ s)
            fun s => csearchD ch1 ch2 n
              ⟨c.ju, c.jv, c.m1, c.ku + c.ku + 1, c.kv + c.kv + 1, c.m2 + 1⟩ s))
        (cleaf ch1 ch2 c s) := rfl

/-- Conclusion of a successful complex search on a cell. -/
def CConcl (ch1 ch2 : ℕ) (c : CCell) : Prop :=
  ∀ u v u' v', inSq c.ju c.m1 u → inSq c.jv c.m1 v → inSq c.ku c.m2 u' → inSq c.kv c.m2 v' →
    ∃ n : ℕ, ∀ z : ℝ, |z| ≤ 1 →
      Separated (Fr ch1 u v * Mc (phX n) (phY n) (phD n * z) * (Fr ch2 u' v')ᵀ)

theorem csearchD_sound (ch1 ch2 : ℕ) (h1 : ch1 < 6) (h2 : ch2 < 6) (fuel : ℕ) :
    ∀ c s s', csearchD ch1 ch2 fuel c s = some s' → CConcl ch1 ch2 c := by
  have leaf : ∀ c s s', cleaf ch1 ch2 c s = some s' → CConcl ch1 ch2 c := by
    intro c s s' h u v u' v' hu hv hu' hv'
    obtain ⟨s1, hs1, rfl⟩ := inSq_coord hu
    obtain ⟨s2, hs2, rfl⟩ := inSq_coord hv
    obtain ⟨s3, hs3, rfl⟩ := inSq_coord hu'
    obtain ⟨s4, hs4, rfl⟩ := inSq_coord hv'
    exact cleaf_sound h1 h2 c h hs1 hs2 hs3 hs4
  induction fuel with
  | zero => exact leaf
  | succ n ih =>
    intro c s s' h
    rw [csearchD_succ] at h
    rcases cond2 h with ⟨_, h⟩ | ⟨_, h⟩
    · rcases cond2 h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨y1, e1, h⟩ := obind_some h
        obtain ⟨y2, e2, h⟩ := obind_some h
        obtain ⟨y3, e3, e4⟩ := obind_some h
        have c1 := ih _ _ _ e1
        have c2 := ih _ _ _ e2
        have c3 := ih _ _ _ e3
        have c4 := ih _ _ _ e4
        intro u v u' v' hu hv hu' hv'
        rcases inSq_split hu with hx | hx <;> rcases inSq_split hv with hy | hy
        · exact c1 u v u' v' hx hy hu' hv'
        · exact c3 u v u' v' hx hy hu' hv'
        · exact c2 u v u' v' hx hy hu' hv'
        · exact c4 u v u' v' hx hy hu' hv'
      · obtain ⟨y1, e1, h⟩ := obind_some h
        obtain ⟨y2, e2, h⟩ := obind_some h
        obtain ⟨y3, e3, e4⟩ := obind_some h
        have c1 := ih _ _ _ e1
        have c2 := ih _ _ _ e2
        have c3 := ih _ _ _ e3
        have c4 := ih _ _ _ e4
        intro u v u' v' hu hv hu' hv'
        rcases inSq_split hu' with hx | hx <;> rcases inSq_split hv' with hy | hy
        · exact c1 u v u' v' hu hv hx hy
        · exact c3 u v u' v' hu hv hx hy
        · exact c2 u v u' v' hu hv hx hy
        · exact c4 u v u' v' hu hv hx hy
    · exact leaf c s s' h

end Icosahedron.K
