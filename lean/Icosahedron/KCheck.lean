/-!
# Kernel-evaluable separation checker

Everything here is written for `decide +kernel`: only `Nat` arithmetic through `Nat.add`,
`Nat.mul`, `Nat.sub`, `Nat.ble` (accelerated by the kernel), `cond`, structures and explicit
`Nat.rec` (no well-founded or `brecOn` recursion).

* `ZP`: an element `(ap - an) + (bp - bn) φ` of `ℤ[φ]`.
* `SC`: a small constant `d a + d b φ` with digits `d 0 = 0, d 1 = 1, d 2 = -1`.
* `P6`: a polynomial `c0 + c1 s + c2 t + c3 s² + c4 s t + c5 t²` over `ℤ[φ]`.
* A cell of a chart square at level `m` and index `j` is `u = (2j+1-2^m + s)/2^(m+1)`,
  `s ∈ [-1,1]`; a `t`-interval at level `m` is `t = (2j+1-2^m + s)/2^m`.
-/

namespace Icosahedron.K

structure ZP where
  ap : Nat
  an : Nat
  bp : Nat
  bn : Nat

namespace ZP

def zero : ZP := ⟨0, 0, 0, 0⟩

def add (x y : ZP) : ZP :=
  ⟨Nat.add x.ap y.ap, Nat.add x.an y.an, Nat.add x.bp y.bp, Nat.add x.bn y.bn⟩

def neg (x : ZP) : ZP := ⟨x.an, x.ap, x.bn, x.bp⟩

def sub (x y : ZP) : ZP :=
  ⟨Nat.add x.ap y.an, Nat.add x.an y.ap, Nat.add x.bp y.bn, Nat.add x.bn y.bp⟩

/-- `(a + b φ) φ = b + (a + b) φ`. -/
def mulPhi (x : ZP) : ZP := ⟨x.bp, x.bn, Nat.add x.ap x.bp, Nat.add x.an x.bn⟩

def smulN (k : Nat) (x : ZP) : ZP :=
  ⟨Nat.mul k x.ap, Nat.mul k x.an, Nat.mul k x.bp, Nat.mul k x.bn⟩

def mul (x y : ZP) : ZP :=
  let acp := Nat.add (Nat.mul x.ap y.ap) (Nat.mul x.an y.an)
  let acn := Nat.add (Nat.mul x.ap y.an) (Nat.mul x.an y.ap)
  let bdp := Nat.add (Nat.mul x.bp y.bp) (Nat.mul x.bn y.bn)
  let bdn := Nat.add (Nat.mul x.bp y.bn) (Nat.mul x.bn y.bp)
  let adp := Nat.add (Nat.mul x.ap y.bp) (Nat.mul x.an y.bn)
  let adn := Nat.add (Nat.mul x.ap y.bn) (Nat.mul x.an y.bp)
  let bcp := Nat.add (Nat.mul x.bp y.ap) (Nat.mul x.bn y.an)
  let bcn := Nat.add (Nat.mul x.bp y.an) (Nat.mul x.bn y.ap)
  ⟨Nat.add acp bdp, Nat.add acn bdn, Nat.add (Nat.add adp bcp) bdp,
    Nat.add (Nat.add adn bcn) bdn⟩

/-- Exact test `0 ≤ a + b φ`, i.e. `0 ≤ u + b √5` with `u = 2a + b`. -/
def nonneg (x : ZP) : Bool :=
  let up := Nat.add (Nat.add x.ap x.ap) x.bp
  let un := Nat.add (Nat.add x.an x.an) x.bn
  cond (Nat.ble un up)
    (cond (Nat.ble x.bn x.bp) true
      (Nat.ble (Nat.mul 5 (Nat.mul (Nat.sub x.bn x.bp) (Nat.sub x.bn x.bp)))
        (Nat.mul (Nat.sub up un) (Nat.sub up un))))
    (cond (Nat.ble x.bn x.bp)
      (Nat.ble (Nat.mul (Nat.sub un up) (Nat.sub un up))
        (Nat.mul 5 (Nat.mul (Nat.sub x.bp x.bn) (Nat.sub x.bp x.bn))))
      false)

def pos (x : ZP) : Bool := !(nonneg (neg x))

def abs (x : ZP) : ZP := cond (nonneg x) x (neg x)

def min0 (x : ZP) : ZP := cond (nonneg x) zero x

/-- `x ≤ y`. -/
def le (x y : ZP) : Bool := nonneg (sub y x)

end ZP

/-- Small constant `d a + d b φ`, digits `0 ↦ 0`, `1 ↦ 1`, otherwise `-1`. -/
structure SC where
  a : Nat
  b : Nat

def dig (t : Nat) (x : ZP) : ZP :=
  Nat.casesOn (motive := fun _ => ZP) t ZP.zero
    (fun t' => Nat.casesOn (motive := fun _ => ZP) t' x (fun _ => ZP.neg x))

def SC.mul (k : SC) (x : ZP) : ZP := ZP.add (dig k.a x) (dig k.b (ZP.mulPhi x))

/-- Negated digit. -/
def ndig (t : Nat) : Nat := Nat.casesOn (motive := fun _ => Nat) t 0 (fun t' => Nat.casesOn
  (motive := fun _ => Nat) t' 2 (fun _ => 1))

def SC.neg (k : SC) : SC := ⟨ndig k.a, ndig k.b⟩

structure P6 where
  c0 : ZP
  c1 : ZP
  c2 : ZP
  c3 : ZP
  c4 : ZP
  c5 : ZP

namespace P6

def zero : P6 := ⟨ZP.zero, ZP.zero, ZP.zero, ZP.zero, ZP.zero, ZP.zero⟩

def add (p q : P6) : P6 :=
  ⟨ZP.add p.c0 q.c0, ZP.add p.c1 q.c1, ZP.add p.c2 q.c2, ZP.add p.c3 q.c3,
    ZP.add p.c4 q.c4, ZP.add p.c5 q.c5⟩

def sub (p q : P6) : P6 :=
  ⟨ZP.sub p.c0 q.c0, ZP.sub p.c1 q.c1, ZP.sub p.c2 q.c2, ZP.sub p.c3 q.c3,
    ZP.sub p.c4 q.c4, ZP.sub p.c5 q.c5⟩

def neg (p : P6) : P6 :=
  ⟨ZP.neg p.c0, ZP.neg p.c1, ZP.neg p.c2, ZP.neg p.c3, ZP.neg p.c4, ZP.neg p.c5⟩

/-- Multiply by a `ℤ[φ]` constant. -/
def smul (k : ZP) (p : P6) : P6 :=
  ⟨ZP.mul k p.c0, ZP.mul k p.c1, ZP.mul k p.c2, ZP.mul k p.c3, ZP.mul k p.c4, ZP.mul k p.c5⟩

/-- Multiply the non-constant part by a `ℤ[φ]` constant (constant slot becomes zero). -/
def smulTail (k : ZP) (p : P6) : P6 :=
  ⟨ZP.zero, ZP.mul k p.c1, ZP.mul k p.c2, ZP.mul k p.c3, ZP.mul k p.c4, ZP.mul k p.c5⟩

/-- Multiply by a small constant. -/
def smulSC (k : SC) (p : P6) : P6 :=
  ⟨k.mul p.c0, k.mul p.c1, k.mul p.c2, k.mul p.c3, k.mul p.c4, k.mul p.c5⟩

/-- Multiply by a signed natural number (`true` = negative). -/
def smulS (neg : Bool) (k : Nat) (p : P6) : P6 :=
  let q : P6 := ⟨ZP.smulN k p.c0, ZP.smulN k p.c1, ZP.smulN k p.c2, ZP.smulN k p.c3,
    ZP.smulN k p.c4, ZP.smulN k p.c5⟩
  cond neg (P6.neg q) q

/-- Lower bound of the non-constant part on `[-1,1]²`. -/
def lbRest (p : P6) : ZP :=
  ZP.sub (ZP.add (ZP.min0 p.c3) (ZP.min0 p.c5))
    (ZP.add (ZP.add (ZP.abs p.c1) (ZP.abs p.c2)) (ZP.abs p.c4))

/-- Sum of absolute values of the non-constant coefficients. -/
def l1 (p : P6) : ZP :=
  ZP.add (ZP.add (ZP.add (ZP.abs p.c1) (ZP.abs p.c2)) (ZP.add (ZP.abs p.c3) (ZP.abs p.c4)))
    (ZP.abs p.c5)

end P6

structure V3 (α : Type) where
  x : α
  y : α
  z : α

/-! ## Forms for one pair of faces -/

def fconst (a w : V3 P6) : ZP :=
  ZP.add (ZP.add (ZP.mul a.x.c0 w.x.c0) (ZP.mul a.y.c0 w.y.c0)) (ZP.mul a.z.c0 w.z.c0)

/-- Block-1 part `ã · w⁰`. -/
def fP (a w : V3 P6) : P6 :=
  P6.add (P6.add (P6.smulTail w.x.c0 a.x) (P6.smulTail w.y.c0 a.y)) (P6.smulTail w.z.c0 a.z)

/-- Block-2 part `a⁰ · w̃`. -/
def fQ (a w : V3 P6) : P6 :=
  P6.add (P6.add (P6.smulTail a.x.c0 w.x) (P6.smulTail a.y.c0 w.y)) (P6.smulTail a.z.c0 w.z)

/-- Bound for the cross part `|ã · w̃|`. -/
def fX (a w : V3 P6) : ZP :=
  ZP.add (ZP.add (ZP.mul (P6.l1 a.x) (P6.l1 w.x)) (ZP.mul (P6.l1 a.y) (P6.l1 w.y)))
    (ZP.mul (P6.l1 a.z) (P6.l1 w.z))

/-- Lower bound of `a1 · w1 - a2 · w2` over the cell. -/
def formLB (a1 w1 a2 w2 : V3 P6) : ZP :=
  ZP.sub
    (ZP.add (ZP.add (ZP.sub (fconst a1 w1) (fconst a2 w2))
      (P6.lbRest (P6.sub (fP a1 w1) (fP a2 w2)))) (P6.lbRest (P6.sub (fQ a1 w1) (fQ a2 w2))))
    (ZP.add (fX a1 w1) (fX a2 w2))

/-- All nine forms `f(i1,k) - f(i2,k')` are positive on the cell. -/
def pairOK (A : Nat → V3 P6) (W : Nat → Nat → V3 P6) (i1 i2 : Nat) : Bool :=
  let a1 := A i1
  let a2 := A i2
  let g := fun k k' => ZP.pos (formLB a1 (W i1 k) a2 (W i2 k'))
  g 0 0 && g 0 1 && g 0 2 && g 1 0 && g 1 1 && g 1 2 && g 2 0 && g 2 1 && g 2 2

/-! ## Choice of the pair at the cell centre -/

def cval (A : Nat → V3 P6) (W : Nat → Nat → V3 P6) (i k : Nat) : ZP := fconst (A i) (W i k)

def zmin (x y : ZP) : ZP := cond (ZP.le x y) x y
def zmax (x y : ZP) : ZP := cond (ZP.le x y) y x

def lo (A : Nat → V3 P6) (W : Nat → Nat → V3 P6) (i : Nat) : ZP :=
  zmin (zmin (cval A W i 0) (cval A W i 1)) (cval A W i 2)

def hi (A : Nat → V3 P6) (W : Nat → Nat → V3 P6) (i : Nat) : ZP :=
  zmax (zmax (cval A W i 0) (cval A W i 1)) (cval A W i 2)

/-- Index in `0, …, n` maximizing `f`, scanning downwards. -/
def argmaxUpTo (f : Nat → ZP) (n : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × ZP) (0, f 0)
    (fun k ih => cond (ZP.le ih.2 (f (Nat.succ k))) (Nat.succ k, f (Nat.succ k)) ih) n).1

def argminUpTo (f : Nat → ZP) (n : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × ZP) (0, f 0)
    (fun k ih => cond (ZP.le (f (Nat.succ k)) ih.2) (Nat.succ k, f (Nat.succ k)) ih) n).1

def cellOK (A : Nat → V3 P6) (W : Nat → Nat → V3 P6) : Bool :=
  let i1 := argmaxUpTo (lo A W) 9
  let i2 := argminUpTo (hi A W) 9
  Nat.blt i1 10 && Nat.blt i2 10 && pairOK A W i1 i2

/-! ## Geometry data -/

/-- Conjugate normals `n'_i` of the representative faces `0, …, 9`. -/
def nSC (i c : Nat) : SC :=
  match i, c with
  | 0, _ => ⟨1, 0⟩
  | 1, 0 => ⟨0, 0⟩ | 1, 1 => ⟨1, 2⟩ | 1, 2 => ⟨0, 2⟩
  | 2, 0 => ⟨0, 2⟩ | 2, 1 => ⟨0, 0⟩ | 2, 2 => ⟨1, 2⟩
  | 3, 0 => ⟨0, 1⟩ | 3, 1 => ⟨0, 0⟩ | 3, 2 => ⟨1, 2⟩
  | 4, 0 => ⟨2, 0⟩ | 4, 1 => ⟨1, 0⟩ | 4, 2 => ⟨1, 0⟩
  | 5, 0 => ⟨1, 2⟩ | 5, 1 => ⟨0, 2⟩ | 5, 2 => ⟨0, 0⟩
  | 6, 0 => ⟨1, 0⟩ | 6, 1 => ⟨1, 0⟩ | 6, 2 => ⟨2, 0⟩
  | 7, 0 => ⟨0, 0⟩ | 7, 1 => ⟨1, 2⟩ | 7, 2 => ⟨0, 1⟩
  | 8, 0 => ⟨1, 2⟩ | 8, 1 => ⟨0, 1⟩ | 8, 2 => ⟨0, 0⟩
  | 9, 0 => ⟨1, 0⟩ | 9, 1 => ⟨2, 0⟩ | 9, 2 => ⟨1, 0⟩
  | _, _ => ⟨0, 0⟩

/-- Vertex coordinates. -/
def vSC (j c : Nat) : SC :=
  match j, c with
  | 0, 0 => ⟨0, 0⟩ | 0, 1 => ⟨1, 0⟩ | 0, 2 => ⟨0, 1⟩
  | 1, 0 => ⟨1, 0⟩ | 1, 1 => ⟨0, 1⟩ | 1, 2 => ⟨0, 0⟩
  | 2, 0 => ⟨0, 1⟩ | 2, 1 => ⟨0, 0⟩ | 2, 2 => ⟨1, 0⟩
  | 3, 0 => ⟨0, 0⟩ | 3, 1 => ⟨1, 0⟩ | 3, 2 => ⟨0, 2⟩
  | 4, 0 => ⟨1, 0⟩ | 4, 1 => ⟨0, 2⟩ | 4, 2 => ⟨0, 0⟩
  | 5, 0 => ⟨0, 1⟩ | 5, 1 => ⟨0, 0⟩ | 5, 2 => ⟨2, 0⟩
  | 6, 0 => ⟨0, 0⟩ | 6, 1 => ⟨2, 0⟩ | 6, 2 => ⟨0, 1⟩
  | 7, 0 => ⟨2, 0⟩ | 7, 1 => ⟨0, 1⟩ | 7, 2 => ⟨0, 0⟩
  | 8, 0 => ⟨0, 2⟩ | 8, 1 => ⟨0, 0⟩ | 8, 2 => ⟨1, 0⟩
  | 9, 0 => ⟨0, 0⟩ | 9, 1 => ⟨2, 0⟩ | 9, 2 => ⟨0, 2⟩
  | 10, 0 => ⟨2, 0⟩ | 10, 1 => ⟨0, 2⟩ | 10, 2 => ⟨0, 0⟩
  | 11, 0 => ⟨0, 2⟩ | 11, 1 => ⟨0, 0⟩ | 11, 2 => ⟨2, 0⟩
  | _, _ => ⟨0, 0⟩

/-- Vertex indices of the representative faces. -/
def fIdx (i k : Nat) : Nat :=
  match i, k with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2
  | 1, 0 => 0 | 1, 1 => 1 | 1, 2 => 7
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 6
  | 3, 0 => 0 | 3, 1 => 6 | 3, 2 => 8
  | 4, 0 => 0 | 4, 1 => 7 | 4, 2 => 8
  | 5, 0 => 1 | 5, 1 => 2 | 5, 2 => 5
  | 6, 0 => 1 | 6, 1 => 3 | 6, 2 => 5
  | 7, 0 => 1 | 7, 1 => 3 | 7, 2 => 7
  | 8, 0 => 2 | 8, 1 => 4 | 8, 2 => 5
  | 9, 0 => 2 | 9, 1 => 4 | 9, 2 => 6
  | _, _ => 0

/-! ## Chart frames

Chart `ch = 2 p + e` (`p ∈ {0,1,2}`, `e ∈ {0,1}`): columns `e_i, σ e_j, σ e_k` with
`(i,j,k)` the `p`-th cyclic shift of `(0,1,2)` and `σ = (-1)^e`.  For a vector of constants
`κ` the chart gives `Pᵀ κ = (κ_i, σ κ_j, σ κ_k)`. -/

def chartT (ch : Nat) (κ : Nat → SC) : V3 SC :=
  let p := Nat.div ch 2
  let sgn := fun (k : SC) => cond (Nat.beq (Nat.mod ch 2) 0) k k.neg
  cond (Nat.beq p 0) ⟨κ 0, sgn (κ 1), sgn (κ 2)⟩
    (cond (Nat.beq p 1) ⟨κ 1, sgn (κ 2), sgn (κ 0)⟩ ⟨κ 2, sgn (κ 0), sgn (κ 1)⟩)

/-- Integer constant `p - n` as `ZP`. -/
def zI (p n : Nat) : ZP := ⟨p, n, 0, 0⟩

/-- Entries of `N² Rq(1,u,v,0)` with `u = (U + s)/N`, `v = (V + t)/N`, `U = up - un`,
`V = vp - vn`, as polynomials in `(s, t)`. Row `r`, column `c`. -/
def rq (N up un vp vn : Nat) (r c : Nat) : P6 :=
  let N2 := Nat.mul N N
  let U2p := Nat.add (Nat.mul up up) (Nat.mul un un)
  let U2n := Nat.add (Nat.mul up un) (Nat.mul un up)
  let V2p := Nat.add (Nat.mul vp vp) (Nat.mul vn vn)
  let V2n := Nat.add (Nat.mul vp vn) (Nat.mul vn vp)
  let UVp := Nat.add (Nat.mul up vp) (Nat.mul un vn)
  let UVn := Nat.add (Nat.mul up vn) (Nat.mul un vp)
  let two := fun (x : Nat) => Nat.add x x
  match r, c with
  | 0, 0 => ⟨zI (Nat.add (Nat.add N2 U2p) V2n) (Nat.add U2n V2p), zI (two up) (two un),
      zI (two vn) (two vp), zI 1 0, zI 0 0, zI 0 1⟩
  | 0, 1 => ⟨zI (two UVp) (two UVn), zI (two vp) (two vn), zI (two up) (two un), zI 0 0,
      zI 2 0, zI 0 0⟩
  | 0, 2 => ⟨zI (two (Nat.mul N vp)) (two (Nat.mul N vn)), zI 0 0, zI (two N) 0, zI 0 0,
      zI 0 0, zI 0 0⟩
  | 1, 0 => ⟨zI (two UVp) (two UVn), zI (two vp) (two vn), zI (two up) (two un), zI 0 0,
      zI 2 0, zI 0 0⟩
  | 1, 1 => ⟨zI (Nat.add (Nat.add N2 U2n) V2p) (Nat.add U2p V2n), zI (two un) (two up),
      zI (two vp) (two vn), zI 0 1, zI 0 0, zI 1 0⟩
  | 1, 2 => ⟨zI (two (Nat.mul N un)) (two (Nat.mul N up)), zI 0 (two N), zI 0 0, zI 0 0,
      zI 0 0, zI 0 0⟩
  | 2, 0 => ⟨zI (two (Nat.mul N vn)) (two (Nat.mul N vp)), zI 0 0, zI 0 (two N), zI 0 0,
      zI 0 0, zI 0 0⟩
  | 2, 1 => ⟨zI (two (Nat.mul N up)) (two (Nat.mul N un)), zI (two N) 0, zI 0 0, zI 0 0,
      zI 0 0, zI 0 0⟩
  | _, _ => ⟨zI (Nat.add (Nat.add N2 U2n) V2n) (Nat.add U2p V2p), zI (two un) (two up),
      zI (two vn) (two vp), zI 0 1, zI 0 0, zI 0 1⟩

/-- `(N² Rq)ᵀ κ` for a vector of small constants. -/
def rqT (N up un vp vn : Nat) (κ : V3 SC) : V3 P6 :=
  let col := fun c => P6.add (P6.add (P6.smulSC κ.x (rq N up un vp vn 0 c))
    (P6.smulSC κ.y (rq N up un vp vn 1 c))) (P6.smulSC κ.z (rq N up un vp vn 2 c))
  ⟨col 0, col 1, col 2⟩

/-- Block 1 of a chart square `(ju, jv)` at level `m`: `A i = (N² F)ᵀ n'_i`. -/
def blockA (ch ju jv m : Nat) (i : Nat) : V3 P6 :=
  let M := Nat.pow 2 m
  rqT (Nat.add M M) (Nat.add (Nat.add ju ju) 1) M (Nat.add (Nat.add jv jv) 1) M
    (chartT ch (nSC i))

/-! ## Real case: `A = F · diag(σ((1-t²) I + 2 t J), 1 + t²)` -/

/-- Constant polynomial in slot `c0`, linear in `c1`, quadratic in `c3` (variable `s`). -/
def tpoly (c0 c1 c3 : ZP) : P6 := ⟨c0, c1, ZP.zero, c3, ZP.zero, ZP.zero⟩

/-- `w = Nt² M(t) v` for `t = (T + s)/Nt`, `T = tp - tn`, sign `σ` (`true` = negative). -/
def blockWr (sg : Bool) (jt m : Nat) (i k : Nat) : V3 P6 :=
  let Nt := Nat.pow 2 m
  let tp := Nat.add (Nat.add jt jt) 1
  let tn := Nt
  let N2 := Nat.mul Nt Nt
  let T2p := Nat.add (Nat.mul tp tp) (Nat.mul tn tn)
  let T2n := Nat.add (Nat.mul tp tn) (Nat.mul tn tp)
  -- x = σ (Nt² - (T+s)²), y = σ 2 Nt (T+s), z = Nt² + (T+s)²
  let x0 := tpoly (zI (Nat.add N2 T2n) T2p) (zI (Nat.add tn tn) (Nat.add tp tp)) (zI 0 1)
  let y0 := tpoly (zI (Nat.mul 2 (Nat.mul Nt tp)) (Nat.mul 2 (Nat.mul Nt tn)))
    (zI (Nat.mul 2 Nt) 0) ZP.zero
  let x := cond sg (P6.neg x0) x0
  let y := cond sg (P6.neg y0) y0
  let z := tpoly (zI (Nat.add N2 T2p) T2n) (zI (Nat.add tp tp) (Nat.add tn tn)) (zI 1 0)
  let j := fIdx i k
  let v0 := vSC j 0
  let v1 := vSC j 1
  let v2 := vSC j 2
  ⟨P6.sub (P6.smulSC v0 x) (P6.smulSC v1 y), P6.add (P6.smulSC v0 y) (P6.smulSC v1 x),
    P6.smulSC v2 z⟩

structure RCell where
  ju : Nat
  jv : Nat
  m1 : Nat
  jt : Nat
  m2 : Nat

def rcellOK (ch : Nat) (sg : Bool) (c : RCell) : Bool :=
  cellOK (blockA ch c.ju c.jv c.m1) (blockWr sg c.jt c.m2)

def rsearch (ch : Nat) (sg : Bool) (fuel : Nat) : RCell → Bool :=
  Nat.rec (motive := fun _ => RCell → Bool) (fun c => rcellOK ch sg c)
    (fun _ ih c => rcellOK ch sg c ||
      cond (Nat.ble c.m1 c.m2)
        (let a := Nat.add c.ju c.ju
         let b := Nat.add c.jv c.jv
         let m := Nat.succ c.m1
         ih ⟨a, b, m, c.jt, c.m2⟩ && ih ⟨Nat.succ a, b, m, c.jt, c.m2⟩ &&
           ih ⟨a, Nat.succ b, m, c.jt, c.m2⟩ && ih ⟨Nat.succ a, Nat.succ b, m, c.jt, c.m2⟩)
        (let a := Nat.add c.jt c.jt
         let m := Nat.succ c.m2
         ih ⟨c.ju, c.jv, c.m1, a, m⟩ && ih ⟨c.ju, c.jv, c.m1, Nat.succ a, m⟩))
    fuel

/-! ## Complex case: `A = F₁ diag(x I + y J, z) F₂ᵀ` -/

/-- `b = (N² F₂)ᵀ v_ik`. -/
def blockB (ch ju jv m : Nat) (i k : Nat) : V3 P6 :=
  let M := Nat.pow 2 m
  rqT (Nat.add M M) (Nat.add (Nat.add ju ju) 1) M (Nat.add (Nat.add jv jv) 1) M
    (chartT ch (vSC (fIdx i k)))

/-- Phase `(X, Y)` with signs and the `z` value `Z`, all signed naturals. -/
structure Ph where
  xs : Bool
  x : Nat
  ys : Bool
  y : Nat
  zs : Bool
  z : Nat

/-- `w = diag(X I + Y J, Z) b`. -/
def applyPh (p : Ph) (b : V3 P6) : V3 P6 :=
  ⟨P6.sub (P6.smulS p.xs p.x b.x) (P6.smulS p.ys p.y b.y),
    P6.add (P6.smulS p.ys p.y b.x) (P6.smulS p.xs p.x b.y), P6.smulS p.zs p.z b.z⟩

/-- Pythagorean phases `(±X, Y, D)`, `X² + Y² = D²`, sixteen directions of the upper half
circle (the sign of `X` is the first component, `true` = negative). -/
def phase (n : Nat) : Bool × Nat × Nat × Nat :=
  match n with
  | 0 => (false, 1, 0, 1)
  | 1 => (false, 99, 20, 101)
  | 2 => (false, 12, 5, 13)
  | 3 => (false, 91, 60, 109)
  | 4 => (false, 119, 120, 169)
  | 5 => (false, 161, 240, 289)
  | 6 => (false, 5, 12, 13)
  | 7 => (false, 20, 99, 101)
  | 8 => (false, 0, 1, 1)
  | 9 => (true, 20, 99, 101)
  | 10 => (true, 5, 12, 13)
  | 11 => (true, 161, 240, 289)
  | 12 => (true, 119, 120, 169)
  | 13 => (true, 91, 60, 109)
  | 14 => (true, 12, 5, 13)
  | _ => (true, 99, 20, 101)

/-- Block-2 vectors at the phase `(±x, y)` and `z = ±zv`. -/
def wAt (B : Nat → Nat → V3 P6) (xs : Bool) (x y : Nat) (zs : Bool) (zv : Nat) :
    Nat → Nat → V3 P6 :=
  fun i k => applyPh ⟨xs, x, false, y, zs, zv⟩ (B i k)

/-- The pair `(i1, i2)` separates at both ends `Za, Zb` of a `z`-interval. -/
def zpairOK (A : Nat → V3 P6) (B : Nat → Nat → V3 P6) (xs : Bool) (x y : Nat)
    (zas : Bool) (za : Nat) (zbs : Bool) (zb : Nat) (i1 i2 : Nat) : Bool :=
  Nat.blt i1 10 && Nat.blt i2 10 && pairOK A (wAt B xs x y zas za) i1 i2 &&
    pairOK A (wAt B xs x y zbs zb) i1 i2

/-- Leaf of type 1: phase `n`, one pair for all of `z ∈ [-D, D]`. -/
def leaf1OK (A : Nat → V3 P6) (B : Nat → Nat → V3 P6) (n i1 i2 : Nat) : Bool :=
  let p := phase n
  zpairOK A B p.1 p.2.1 p.2.2.1 true p.2.2.2 false p.2.2.2 i1 i2

/-- Leaf of type 2: phase `n`, pair `(i1,i2)` on `[-D, 0]` and `(j1,j2)` on `[0, D]`. -/
def leaf2OK (A : Nat → V3 P6) (B : Nat → Nat → V3 P6) (n i1 i2 j1 j2 : Nat) : Bool :=
  let p := phase n
  zpairOK A B p.1 p.2.1 p.2.2.1 true p.2.2.2 false 0 i1 i2 &&
    zpairOK A B p.1 p.2.1 p.2.2.1 false 0 false p.2.2.2 j1 j2

structure CCell where
  ju : Nat
  jv : Nat
  m1 : Nat
  ku : Nat
  kv : Nat
  m2 : Nat

/-! The certificate tree is a stream of hexadecimal digits (least significant first):
`0` = split, `1 n i1 i2` = leaf of type 1, `2 n i1 i2 j1 j2` = leaf of type 2. -/

def dg (s : Nat) : Nat := Nat.mod s 16
def dr (s : Nat) : Nat := Nat.div s 16

def obind (o : Option Nat) (f : Nat → Option Nat) : Option Nat :=
  Option.casesOn (motive := fun _ => Option Nat) o none f

def cleaf (ch1 ch2 : Nat) (c : CCell) (s : Nat) : Option Nat :=
  let A := blockA ch1 c.ju c.jv c.m1
  let B := blockB ch2 c.ku c.kv c.m2
  let s1 := dr s
  let s2 := dr s1
  let s3 := dr s2
  let s4 := dr s3
  cond (Nat.beq (dg s) 1) (cond (leaf1OK A B (dg s1) (dg s2) (dg s3)) (some s4) none)
    (cond (Nat.beq (dg s) 2)
      (let s5 := dr s4
       cond (leaf2OK A B (dg s1) (dg s2) (dg s3) (dg s4) (dg s5)) (some (dr s5)) none)
      none)

def csearchD (ch1 ch2 : Nat) (fuel : Nat) : CCell → Nat → Option Nat :=
  Nat.rec (motive := fun _ => CCell → Nat → Option Nat) (fun c s => cleaf ch1 ch2 c s)
    (fun _ ih c s =>
      cond (Nat.beq (dg s) 0)
        (let s := dr s
         cond (Nat.ble c.m1 c.m2)
          (let a := Nat.add c.ju c.ju
           let b := Nat.add c.jv c.jv
           let m := Nat.succ c.m1
           obind (ih ⟨a, b, m, c.ku, c.kv, c.m2⟩ s) fun s =>
           obind (ih ⟨Nat.succ a, b, m, c.ku, c.kv, c.m2⟩ s) fun s =>
           obind (ih ⟨a, Nat.succ b, m, c.ku, c.kv, c.m2⟩ s) fun s =>
           ih ⟨Nat.succ a, Nat.succ b, m, c.ku, c.kv, c.m2⟩ s)
          (let a := Nat.add c.ku c.ku
           let b := Nat.add c.kv c.kv
           let m := Nat.succ c.m2
           obind (ih ⟨c.ju, c.jv, c.m1, a, b, m⟩ s) fun s =>
           obind (ih ⟨c.ju, c.jv, c.m1, Nat.succ a, b, m⟩ s) fun s =>
           obind (ih ⟨c.ju, c.jv, c.m1, a, Nat.succ b, m⟩ s) fun s =>
           ih ⟨c.ju, c.jv, c.m1, Nat.succ a, Nat.succ b, m⟩ s))
        (cleaf ch1 ch2 c s))
    fuel

end Icosahedron.K
