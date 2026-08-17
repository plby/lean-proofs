/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.Selector

/-!
Modular arithmetic infrastructure for the nontrivial-prime selector step.

The source proof repeatedly localizes from a modulus `d` to one full
prime-power factor `p ^ a`, and then reconstructs residues by the Chinese
remainder theorem.  `PrimaryComponent` records exactly the factorization
data those operations need.  Keeping the coprimality witness in the
structure avoids introducing a separate valuation API into the selector
proof.
-/

namespace Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- A root of `-1` modulo an arbitrary modulus.  This is an abbreviation of
a subtype so its coercion to `ZMod d` remains transparent to elaboration. -/
abbrev Root (d : ℕ) := {x : ZMod d // x ^ 2 = -1}

/-- A full primary component `p ^ a` of `d`, with its coprime complementary
factor.  The exponent is positive, while the complementary factor may be
one. -/
structure PrimaryComponent (d : ℕ) where
  p : ℕ
  a : ℕ
  D : ℕ
  prime : p.Prime
  exp_pos : 0 < a
  factor : d = p ^ a * D
  coprime : (p ^ a).Coprime D

namespace PrimaryComponent

/-- The prime-power modulus represented by a component. -/
def q {d : ℕ} (c : PrimaryComponent d) : ℕ := c.p ^ c.a

lemma q_pos {d : ℕ} (c : PrimaryComponent d) : 0 < c.q := by
  exact pow_pos c.prime.pos _

lemma q_ne_zero {d : ℕ} (c : PrimaryComponent d) : c.q ≠ 0 :=
  Nat.ne_of_gt c.q_pos

lemma factor_q {d : ℕ} (c : PrimaryComponent d) : d = c.q * c.D := by
  exact c.factor

lemma q_dvd {d : ℕ} (c : PrimaryComponent d) : c.q ∣ d := by
  exact ⟨c.D, c.factor⟩

lemma D_dvd {d : ℕ} (c : PrimaryComponent d) : c.D ∣ d := by
  refine ⟨c.q, ?_⟩
  calc
    d = c.q * c.D := c.factor_q
    _ = c.D * c.q := Nat.mul_comm _ _

/-- Reduction from the global modulus to this prime-power component. -/
def reduce {d : ℕ} (c : PrimaryComponent d) : ZMod d →+* ZMod c.q :=
  ZMod.castHom c.q_dvd (ZMod c.q)

@[simp] lemma reduce_natCast {d : ℕ} (c : PrimaryComponent d) (n : ℕ) :
    c.reduce (n : ZMod d) = (n : ZMod c.q) := by
  simp [reduce]

@[simp] lemma reduce_intCast {d : ℕ} (c : PrimaryComponent d) (z : ℤ) :
    c.reduce (z : ZMod d) = (z : ZMod c.q) := by
  simp [reduce]

@[simp] lemma reduce_neg {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    c.reduce (-x) = -c.reduce x := by
  exact map_neg c.reduce x

@[simp] lemma reduce_sub {d : ℕ} (c : PrimaryComponent d) (x y : ZMod d) :
    c.reduce (x - y) = c.reduce x - c.reduce y := by
  exact map_sub c.reduce x y

@[simp] lemma reduce_pow {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) (n : ℕ) :
    c.reduce (x ^ n) = c.reduce x ^ n := by
  exact map_pow c.reduce x n

/-- Reducing a global root gives a root on every primary component. -/
def reduceRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) : Root c.q :=
  ⟨c.reduce lam.1, by
    rw [← map_pow, lam.property]
    simp⟩

@[simp] lemma coe_reduceRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) :
    (c.reduceRoot lam : ZMod c.q) = c.reduce lam.1 := rfl

lemma isUnit_D {d : ℕ} (c : PrimaryComponent d) : IsUnit (c.D : ZMod c.q) := by
  rw [ZMod.isUnit_iff_coprime]
  exact c.coprime.symm

/-- The source's localized quotient `[z/d]_(p^a)`, specialized to a primary
component `d = p^a D`. -/
def localQuotient {d : ℕ} (c : PrimaryComponent d) (z : ℤ) : ZMod c.q :=
  localizedQuotient c.q (c.D : ZMod c.q)⁻¹ z

/-- Clearing the complementary denominator recovers the ordinary quotient.
This lemma is the cancellation step behind equations (4.6) and (4.13). -/
lemma localQuotient_mul_D {d : ℕ} (c : PrimaryComponent d) (z : ℤ) :
    c.localQuotient z * (c.D : ZMod c.q) = (z / (c.q : ℤ) : ℤ) := by
  simp only [localQuotient, localizedQuotient, mul_assoc]
  rw [ZMod.inv_mul_of_unit _ c.isUnit_D]
  simp

lemma D_mul_localQuotient {d : ℕ} (c : PrimaryComponent d) (z : ℤ) :
    (c.D : ZMod c.q) * c.localQuotient z = (z / (c.q : ℤ) : ℤ) := by
  rw [mul_comm, c.localQuotient_mul_D]

/-- CRT splitting for the factorization stored by a primary component. -/
def split {d : ℕ} (c : PrimaryComponent d) :
    ZMod d ≃+* ZMod c.q × ZMod c.D :=
  (ZMod.ringEquivCongr c.factor_q).trans (ZMod.chineseRemainder c.coprime)

/-- CRT reconstruction for the factorization stored by a primary component. -/
def combine {d : ℕ} (c : PrimaryComponent d) (x : ZMod c.q) (y : ZMod c.D) :
    ZMod d :=
  c.split.symm (x, y)

@[simp] lemma split_combine {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : c.split (c.combine x y) = (x, y) := by
  exact c.split.apply_symm_apply (x, y)

@[simp] lemma combine_split {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    c.combine (c.split x).1 (c.split x).2 = x := by
  exact c.split.symm_apply_apply x

@[simp] lemma split_combine_fst {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : (c.split (c.combine x y)).1 = x := by
  simp

@[simp] lemma split_combine_snd {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : (c.split (c.combine x y)).2 = y := by
  simp

/-- Reconstruct a global root from roots on one primary component and its
coprime complement. -/
def combineRoot {d : ℕ} (c : PrimaryComponent d)
    (x : Root c.q) (y : Root c.D) : Root d :=
  ⟨c.combine x.1 y.1, by
    apply c.split.injective
    simp only [map_pow, split_combine, map_neg, map_one]
    change (x.1 ^ 2, y.1 ^ 2) = ((-1 : ZMod c.q), (-1 : ZMod c.D))
    exact Prod.ext x.property y.property⟩

@[simp] lemma split_combineRoot {d : ℕ} (c : PrimaryComponent d)
    (x : Root c.q) (y : Root c.D) :
    c.split (c.combineRoot x y) = ((x : ZMod c.q), (y : ZMod c.D)) := by
  exact c.split_combine x.1 y.1

end PrimaryComponent

/-- Pairwise CRT in the construction direction. -/
def crt {m n : ℕ} (h : m.Coprime n) (x : ZMod m) (y : ZMod n) :
    ZMod (m * n) :=
  (ZMod.chineseRemainder h).symm (x, y)

@[simp] lemma chineseRemainder_crt {m n : ℕ} (h : m.Coprime n)
    (x : ZMod m) (y : ZMod n) :
    (ZMod.chineseRemainder h) (crt h x y) = (x, y) := by
  exact (ZMod.chineseRemainder h).apply_symm_apply (x, y)

/-- Pairwise CRT preserves the equation `x² = -1`. -/
def crtRoot {m n : ℕ} (h : m.Coprime n) (x : Root m) (y : Root n) :
    Root (m * n) :=
  ⟨crt h x.1 y.1, by
    apply (ZMod.chineseRemainder h).injective
    simp only [map_pow, chineseRemainder_crt, map_neg, map_one]
    change (x.1 ^ 2, y.1 ^ 2) = ((-1 : ZMod m), (-1 : ZMod n))
    exact Prod.ext x.property y.property⟩

@[simp] lemma chineseRemainder_crtRoot {m n : ℕ} (h : m.Coprime n)
    (x : Root m) (y : Root n) :
    (ZMod.chineseRemainder h) (crtRoot h x y) =
      ((x : ZMod m), (y : ZMod n)) := by
  exact chineseRemainder_crt h x.1 y.1

/-- The canonical numerator `(1 + λ.val²) / d` attached to a root. -/
def rootQuotient {d : ℕ} (lam : Root d) : ℕ :=
  (1 + ZMod.val lam.1 ^ 2) / d

lemma root_dvd_one_add_val_sq {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    d ∣ 1 + ZMod.val lam.1 ^ 2 := by
  let _ : NeZero d := ⟨hd⟩
  apply (ZMod.natCast_eq_zero_iff (1 + ZMod.val lam.1 ^ 2) d).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [lam.property]
  simp

lemma mul_rootQuotient {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    d * rootQuotient lam = 1 + ZMod.val lam.1 ^ 2 := by
  exact Nat.mul_div_cancel' (root_dvd_one_add_val_sq hd lam)

/-- The modular half of `(1 + λ.val²) / d` occurring in (4.4). -/
def rootPhase {d : ℕ} (lam : Root d) : ZMod d :=
  (2 : ZMod d)⁻¹ * (rootQuotient lam : ZMod d)

lemma two_mul_rootPhase {d : ℕ} (h2 : Nat.Coprime 2 d) (lam : Root d) :
    (2 : ZMod d) * rootPhase lam = (rootQuotient lam : ZMod d) := by
  have hinv : (2 : ZMod d) * (2 : ZMod d)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 h2
  simp only [rootPhase, ← mul_assoc, hinv, one_mul]

/-- Every root of `-1` is a unit, over an arbitrary commutative residue
ring (no primality assumption is required). -/
lemma root_isUnit {d : ℕ} (lam : Root d) : IsUnit (lam : ZMod d) := by
  refine ⟨⟨lam.1, -lam.1, ?_, ?_⟩, rfl⟩
  · change lam.1 * -lam.1 = 1
    rw [mul_neg, ← pow_two, lam.property]
    simp
  · change -lam.1 * lam.1 = 1
    rw [neg_mul, ← pow_two, lam.property]
    simp

end

end Erdos215.Selector.Modular
