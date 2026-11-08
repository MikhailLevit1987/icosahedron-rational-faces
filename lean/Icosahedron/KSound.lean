import Icosahedron.KCheck
import Icosahedron.Geometry

/-!
# Soundness of the kernel arithmetic

`ZP.ev` interprets `ZP` in `ℝ` (with `φ = (1 + √5)/2`); `P6.eval` interprets polynomials.
The main result is `pairOK_sound`: if `pairOK A W i1 i2 = true`, then on the whole cell
`[-1,1]⁴` every value `a_{i1}·w_{i1,k}` exceeds every value `a_{i2}·w_{i2,k'}`.
-/

namespace Icosahedron.K

open Icosahedron Matrix

noncomputable def ZP.ev (x : ZP) : ℝ := ((x.ap : ℝ) - x.an) + ((x.bp : ℝ) - x.bn) * φ

namespace ZP

@[simp] theorem ev_zero : zero.ev = 0 := by simp [ev, zero]

@[simp] theorem ev_add (x y : ZP) : (add x y).ev = x.ev + y.ev := by
  simp only [ev, add, Nat.add_eq, Nat.cast_add]; ring

@[simp] theorem ev_neg (x : ZP) : (neg x).ev = -x.ev := by simp only [ev, neg]; ring

@[simp] theorem ev_sub (x y : ZP) : (sub x y).ev = x.ev - y.ev := by
  simp only [ev, sub, Nat.add_eq, Nat.cast_add]; ring

@[simp] theorem ev_mulPhi (x : ZP) : (mulPhi x).ev = x.ev * φ := by
  simp only [ev, mulPhi, Nat.add_eq, Nat.cast_add]
  linear_combination (-((x.bp : ℝ) - x.bn)) * φ_sq

@[simp] theorem ev_smulN (k : Nat) (x : ZP) : (smulN k x).ev = k * x.ev := by
  simp only [ev, smulN, Nat.mul_eq, Nat.cast_mul]; ring

@[simp] theorem ev_mul (x y : ZP) : (mul x y).ev = x.ev * y.ev := by
  simp only [ev, mul, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul]
  linear_combination (-(((x.bp : ℝ) - x.bn) * ((y.bp : ℝ) - y.bn))) * φ_sq

theorem sqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem aux1 {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β) :
    5 * (β * β) ≤ u * u ↔ β * Real.sqrt 5 ≤ u := by
  have hr2 := sqrt5_sq
  rw [← sq_le_sq₀ (mul_nonneg hβ sqrt5_nonneg) hu, mul_pow, hr2]
  constructor <;> intro h <;> nlinarith

theorem aux2 {μ b : ℝ} (hμ : 0 ≤ μ) (hb : 0 ≤ b) :
    μ * μ ≤ 5 * (b * b) ↔ μ ≤ b * Real.sqrt 5 := by
  have hr2 := sqrt5_sq
  rw [← sq_le_sq₀ hμ (mul_nonneg hb sqrt5_nonneg), mul_pow, hr2]
  constructor <;> intro h <;> nlinarith

theorem ble_t {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

theorem ble_f {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h

/-- The exact sign test of `u + b √5`, `u = up - un`, `b = bp - bn`. -/
theorem sign_test (up un bp bn : ℕ) :
    (cond (Nat.ble un up)
      (cond (Nat.ble bn bp) true
        (Nat.ble (Nat.mul 5 (Nat.mul (Nat.sub bn bp) (Nat.sub bn bp)))
          (Nat.mul (Nat.sub up un) (Nat.sub up un))))
      (cond (Nat.ble bn bp)
        (Nat.ble (Nat.mul (Nat.sub un up) (Nat.sub un up))
          (Nat.mul 5 (Nat.mul (Nat.sub bp bn) (Nat.sub bp bn))))
        false)) = true ↔
    0 ≤ ((up : ℝ) - un) + ((bp : ℝ) - bn) * Real.sqrt 5 := by
  have hr := sqrt5_nonneg
  simp only [Nat.mul_eq, Nat.sub_eq]
  by_cases h1 : un ≤ up <;> by_cases h2 : bn ≤ bp
  · rw [ble_t h1, ble_t h2]
    simp only [Bool.cond_true, true_iff]
    have : (un : ℝ) ≤ up := by exact_mod_cast h1
    have : (bn : ℝ) ≤ bp := by exact_mod_cast h2
    nlinarith
  · rw [ble_t h1, ble_f h2]
    simp only [Bool.cond_true, Bool.cond_false, Nat.ble_eq]
    have h2' : bp ≤ bn := by omega
    rw [← @Nat.cast_le ℝ]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2']
    rw [aux1 (by linarith [(show (un : ℝ) ≤ up by exact_mod_cast h1)])
      (by linarith [(show (bp : ℝ) ≤ bn by exact_mod_cast h2')])]
    constructor <;> intro h <;> linarith
  · rw [ble_f h1, ble_t h2]
    simp only [Bool.cond_true, Bool.cond_false, Nat.ble_eq]
    have h1' : up ≤ un := by omega
    rw [← @Nat.cast_le ℝ]
    push_cast [Nat.cast_sub h1', Nat.cast_sub h2]
    rw [aux2 (by linarith [(show (up : ℝ) ≤ un by exact_mod_cast h1')])
      (by linarith [(show (bn : ℝ) ≤ bp by exact_mod_cast h2)])]
    constructor <;> intro h <;> linarith
  · rw [ble_f h1, ble_f h2]
    simp only [Bool.cond_false, Bool.false_eq_true, false_iff, not_le]
    have : (up : ℝ) < un := by exact_mod_cast (by omega : up < un)
    have : (bp : ℝ) < bn := by exact_mod_cast (by omega : bp < bn)
    nlinarith

theorem nonneg_iff (x : ZP) : nonneg x = true ↔ 0 ≤ x.ev := by
  have h := sign_test (Nat.add (Nat.add x.ap x.ap) x.bp) (Nat.add (Nat.add x.an x.an) x.bn)
    x.bp x.bn
  refine Iff.trans Iff.rfl (h.trans ?_)
  have e : 2 * x.ev = (((Nat.add (Nat.add x.ap x.ap) x.bp : ℕ) : ℝ) -
      ((Nat.add (Nat.add x.an x.an) x.bn : ℕ) : ℝ)) + ((x.bp : ℝ) - x.bn) * Real.sqrt 5 := by
    simp only [ev, φ, Nat.add_eq]; push_cast; ring
  rw [← e]
  constructor <;> intro h <;> linarith

theorem ev_abs (x : ZP) : (abs x).ev = |x.ev| := by
  unfold abs
  cases h : nonneg x
  · have : ¬ 0 ≤ x.ev := fun h' => by simp [(nonneg_iff x).2 h'] at h
    simp only [Bool.cond_false, ev_neg]
    rw [abs_of_neg (lt_of_not_ge this)]
  · simp only [Bool.cond_true]
    rw [abs_of_nonneg ((nonneg_iff x).1 h)]

theorem ev_min0 (x : ZP) : (min0 x).ev = min x.ev 0 := by
  unfold min0
  cases h : nonneg x
  · have : ¬ 0 ≤ x.ev := fun h' => by simp [(nonneg_iff x).2 h'] at h
    simp only [Bool.cond_false]
    rw [min_eq_left (le_of_lt (lt_of_not_ge this))]
  · simp only [Bool.cond_true, ev_zero]
    rw [min_eq_right ((nonneg_iff x).1 h)]

theorem pos_iff (x : ZP) : pos x = true ↔ 0 < x.ev := by
  unfold pos
  rw [Bool.not_eq_true', ← Bool.not_eq_true, nonneg_iff, ev_neg]
  constructor
  · intro h; by_contra h'; exact h (by linarith)
  · intro h h'; linarith

end ZP

/-! ## Small constants -/

def dv : Nat → ℝ
  | 0 => 0
  | 1 => 1
  | _ => -1

noncomputable def SC.val (k : SC) : ℝ := dv k.a + dv k.b * φ

theorem ev_dig (t : Nat) (x : ZP) : (dig t x).ev = dv t * x.ev := by
  rcases t with _ | _ | t
  · show ZP.zero.ev = _; simp [dv]
  · show x.ev = _; simp [dv]
  · show (ZP.neg x).ev = _; simp [dv]

@[simp] theorem SC.ev_mul (k : SC) (x : ZP) : (k.mul x).ev = k.val * x.ev := by
  simp only [SC.mul, ZP.ev_add, ev_dig, ZP.ev_mulPhi, SC.val]; ring

theorem dv_ndig (t : Nat) : dv (ndig t) = -dv t := by
  rcases t with _ | _ | t
  · show dv 0 = _; simp [dv]
  · show dv 2 = _; simp [dv]
  · show dv 1 = _; simp [dv]

@[simp] theorem SC.val_neg (k : SC) : k.neg.val = -k.val := by
  simp only [SC.neg, SC.val, dv_ndig]; ring

/-! ## Polynomials -/

noncomputable def P6.eval (p : P6) (s t : ℝ) : ℝ :=
  p.c0.ev + p.c1.ev * s + p.c2.ev * t + p.c3.ev * s ^ 2 + p.c4.ev * (s * t) + p.c5.ev * t ^ 2

namespace P6

@[simp] theorem eval_zero (s t : ℝ) : zero.eval s t = 0 := by simp [eval, zero]

@[simp] theorem eval_add (p q : P6) (s t : ℝ) : (add p q).eval s t = p.eval s t + q.eval s t := by
  simp only [eval, add, ZP.ev_add]; ring

@[simp] theorem eval_sub (p q : P6) (s t : ℝ) : (sub p q).eval s t = p.eval s t - q.eval s t := by
  simp only [eval, sub, ZP.ev_sub]; ring

@[simp] theorem eval_neg (p : P6) (s t : ℝ) : (neg p).eval s t = -p.eval s t := by
  simp only [eval, neg, ZP.ev_neg]; ring

@[simp] theorem eval_smul (k : ZP) (p : P6) (s t : ℝ) :
    (smul k p).eval s t = k.ev * p.eval s t := by
  simp only [eval, smul, ZP.ev_mul]; ring

@[simp] theorem eval_smulTail (k : ZP) (p : P6) (s t : ℝ) :
    (smulTail k p).eval s t = k.ev * (p.eval s t - p.c0.ev) := by
  simp only [eval, smulTail, ZP.ev_mul, ZP.ev_zero]; ring

@[simp] theorem c0_smulTail (k : ZP) (p : P6) : (smulTail k p).c0 = ZP.zero := rfl

@[simp] theorem eval_smulSC (k : SC) (p : P6) (s t : ℝ) :
    (smulSC k p).eval s t = k.val * p.eval s t := by
  simp only [eval, smulSC, SC.ev_mul]; ring

@[simp] theorem eval_smulS (ng : Bool) (k : Nat) (p : P6) (s t : ℝ) :
    (smulS ng k p).eval s t = (if ng then -(k : ℝ) else k) * p.eval s t := by
  cases ng
  · simp only [smulS, Bool.cond_false, eval, ZP.ev_smulN, Bool.false_eq_true, ite_false]; ring
  · simp only [smulS, Bool.cond_true, eval_neg, ite_true]
    simp only [eval, ZP.ev_smulN]; ring

theorem term_lin (c x : ℝ) (hx : |x| ≤ 1) : -|c| ≤ c * x := by
  have : |c * x| ≤ |c| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg c) hx
  exact neg_le_of_abs_le this

theorem term_sq (c x : ℝ) (hx : |x| ≤ 1) : min c 0 ≤ c * x ^ 2 := by
  have h0 : 0 ≤ x ^ 2 := sq_nonneg x
  have h1 : x ^ 2 ≤ 1 := by
    have := sq_abs x ▸ pow_le_one₀ (abs_nonneg x) hx (n := 2)
    simpa using this
  rcases le_total c 0 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; positivity

theorem abs_st (s t : ℝ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) : |s * t| ≤ 1 := by
  rw [abs_mul]; exact mul_le_one₀ hs (abs_nonneg t) ht

theorem lbRest_le (p : P6) {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    p.c0.ev + (lbRest p).ev ≤ p.eval s t := by
  simp only [lbRest, ZP.ev_sub, ZP.ev_add, ZP.ev_min0, ZP.ev_abs, eval]
  have h1 := term_lin p.c1.ev s hs
  have h2 := term_lin p.c2.ev t ht
  have h3 := term_sq p.c3.ev s hs
  have h4 := term_lin p.c4.ev (s * t) (abs_st s t hs ht)
  have h5 := term_sq p.c5.ev t ht
  linarith

theorem abs_le_l1 (p : P6) {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    |p.eval s t - p.c0.ev| ≤ (l1 p).ev := by
  simp only [l1, ZP.ev_add, ZP.ev_abs, eval]
  have b1 : |p.c1.ev * s| ≤ |p.c1.ev| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs
  have b2 : |p.c2.ev * t| ≤ |p.c2.ev| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ht
  have b3 : |p.c3.ev * s ^ 2| ≤ |p.c3.ev| := by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have b4 : |p.c4.ev * (s * t)| ≤ |p.c4.ev| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_st s t hs ht)
  have b5 : |p.c5.ev * t ^ 2| ≤ |p.c5.ev| := by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg t) ht)
  have e : p.c0.ev + p.c1.ev * s + p.c2.ev * t + p.c3.ev * s ^ 2 + p.c4.ev * (s * t) +
      p.c5.ev * t ^ 2 - p.c0.ev = p.c1.ev * s + p.c2.ev * t + p.c3.ev * s ^ 2 +
      p.c4.ev * (s * t) + p.c5.ev * t ^ 2 := by ring
  rw [e]
  calc _ ≤ |p.c1.ev * s| + |p.c2.ev * t| + |p.c3.ev * s ^ 2| + |p.c4.ev * (s * t)| +
        |p.c5.ev * t ^ 2| := by
        have := abs_add_le (p.c1.ev * s + p.c2.ev * t + p.c3.ev * s ^ 2 + p.c4.ev * (s * t))
          (p.c5.ev * t ^ 2)
        have := abs_add_le (p.c1.ev * s + p.c2.ev * t + p.c3.ev * s ^ 2) (p.c4.ev * (s * t))
        have := abs_add_le (p.c1.ev * s + p.c2.ev * t) (p.c3.ev * s ^ 2)
        have := abs_add_le (p.c1.ev * s) (p.c2.ev * t)
        linarith
    _ ≤ _ := by linarith

theorem l1_nonneg (p : P6) : 0 ≤ (l1 p).ev := by
  simp only [l1, ZP.ev_add, ZP.ev_abs]; positivity

end P6

/-! ## Vectors and the bound for one pair -/

noncomputable def V3.ev (a : V3 P6) (s t : ℝ) : Fin 3 → ℝ :=
  ![a.x.eval s t, a.y.eval s t, a.z.eval s t]

theorem V3.dot_ev (a w : V3 P6) (s1 s2 s3 s4 : ℝ) :
    a.ev s1 s2 ⬝ᵥ w.ev s3 s4 = a.x.eval s1 s2 * w.x.eval s3 s4 +
      a.y.eval s1 s2 * w.y.eval s3 s4 + a.z.eval s1 s2 * w.z.eval s3 s4 := by
  simp [V3.ev, dotProduct, Fin.sum_univ_three]

/-- Exact decomposition: constant + block-1 part + block-2 part + cross part. -/
theorem dot_decomp (a w : V3 P6) (s1 s2 s3 s4 : ℝ) :
    a.ev s1 s2 ⬝ᵥ w.ev s3 s4 = (fconst a w).ev + (fP a w).eval s1 s2 + (fQ a w).eval s3 s4 +
      ((a.x.eval s1 s2 - a.x.c0.ev) * (w.x.eval s3 s4 - w.x.c0.ev) +
       (a.y.eval s1 s2 - a.y.c0.ev) * (w.y.eval s3 s4 - w.y.c0.ev) +
       (a.z.eval s1 s2 - a.z.c0.ev) * (w.z.eval s3 s4 - w.z.c0.ev)) := by
  rw [V3.dot_ev]
  simp only [fconst, fP, fQ, ZP.ev_add, ZP.ev_mul, P6.eval_add, P6.eval_smulTail]
  ring

theorem cross_le (a w : V3 P6) {s1 s2 s3 s4 : ℝ} (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1)
    (h3 : |s3| ≤ 1) (h4 : |s4| ≤ 1) :
    |(a.x.eval s1 s2 - a.x.c0.ev) * (w.x.eval s3 s4 - w.x.c0.ev) +
       (a.y.eval s1 s2 - a.y.c0.ev) * (w.y.eval s3 s4 - w.y.c0.ev) +
       (a.z.eval s1 s2 - a.z.c0.ev) * (w.z.eval s3 s4 - w.z.c0.ev)| ≤ (fX a w).ev := by
  simp only [fX, ZP.ev_add, ZP.ev_mul]
  have m : ∀ p q : P6, |(p.eval s1 s2 - p.c0.ev) * (q.eval s3 s4 - q.c0.ev)| ≤
      (P6.l1 p).ev * (P6.l1 q).ev := fun p q => by
    rw [abs_mul]
    exact mul_le_mul (P6.abs_le_l1 p h1 h2) (P6.abs_le_l1 q h3 h4) (abs_nonneg _)
      (P6.l1_nonneg p)
  have hx := m a.x w.x
  have hy := m a.y w.y
  have hz := m a.z w.z
  have t1 := abs_add_le ((a.x.eval s1 s2 - a.x.c0.ev) * (w.x.eval s3 s4 - w.x.c0.ev) +
       (a.y.eval s1 s2 - a.y.c0.ev) * (w.y.eval s3 s4 - w.y.c0.ev))
       ((a.z.eval s1 s2 - a.z.c0.ev) * (w.z.eval s3 s4 - w.z.c0.ev))
  have t2 := abs_add_le ((a.x.eval s1 s2 - a.x.c0.ev) * (w.x.eval s3 s4 - w.x.c0.ev))
    ((a.y.eval s1 s2 - a.y.c0.ev) * (w.y.eval s3 s4 - w.y.c0.ev))
  linarith

theorem fP_c0 (a w : V3 P6) : (fP a w).c0.ev = 0 := by
  simp [fP, P6.add]

theorem fQ_c0 (a w : V3 P6) : (fQ a w).c0.ev = 0 := by
  simp [fQ, P6.add]

theorem formLB_le (a1 w1 a2 w2 : V3 P6) {s1 s2 s3 s4 : ℝ} (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1)
    (h3 : |s3| ≤ 1) (h4 : |s4| ≤ 1) :
    (formLB a1 w1 a2 w2).ev ≤ a1.ev s1 s2 ⬝ᵥ w1.ev s3 s4 - a2.ev s1 s2 ⬝ᵥ w2.ev s3 s4 := by
  rw [dot_decomp a1 w1, dot_decomp a2 w2]
  have hP := P6.lbRest_le (P6.sub (fP a1 w1) (fP a2 w2)) h1 h2
  have hQ := P6.lbRest_le (P6.sub (fQ a1 w1) (fQ a2 w2)) h3 h4
  rw [P6.eval_sub] at hP hQ
  have eP : (P6.sub (fP a1 w1) (fP a2 w2)).c0.ev = 0 := by
    show (ZP.sub _ _).ev = 0; rw [ZP.ev_sub, fP_c0, fP_c0]; ring
  have eQ : (P6.sub (fQ a1 w1) (fQ a2 w2)).c0.ev = 0 := by
    show (ZP.sub _ _).ev = 0; rw [ZP.ev_sub, fQ_c0, fQ_c0]; ring
  rw [eP, zero_add] at hP
  rw [eQ, zero_add] at hQ
  have c1 := abs_le.1 (cross_le a1 w1 h1 h2 h3 h4)
  have c2 := abs_le.1 (cross_le a2 w2 h1 h2 h3 h4)
  simp only [formLB, ZP.ev_sub, ZP.ev_add]
  linarith [c1.1, c2.2]

theorem pairOK_sound {A : Nat → V3 P6} {W : Nat → Nat → V3 P6} {i1 i2 : Nat}
    (h : pairOK A W i1 i2 = true) {s1 s2 s3 s4 : ℝ} (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1)
    (h3 : |s3| ≤ 1) (h4 : |s4| ≤ 1) {k k' : ℕ} (hk : k < 3) (hk' : k' < 3) :
    (A i2).ev s1 s2 ⬝ᵥ (W i2 k').ev s3 s4 < (A i1).ev s1 s2 ⬝ᵥ (W i1 k).ev s3 s4 := by
  have key : ZP.pos (formLB (A i1) (W i1 k) (A i2) (W i2 k')) = true := by
    simp only [pairOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨g00, g01⟩, g02⟩, g10⟩, g11⟩, g12⟩, g20⟩, g21⟩, g22⟩ := h
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals obtain rfl | rfl | rfl : k' = 0 ∨ k' = 1 ∨ k' = 2 := by omega
    exacts [g00, g01, g02, g10, g11, g12, g20, g21, g22]
  have := (ZP.pos_iff _).1 key
  have := formLB_le (A i1) (W i1 k) (A i2) (W i2 k') h1 h2 h3 h4
  linarith

end Icosahedron.K

