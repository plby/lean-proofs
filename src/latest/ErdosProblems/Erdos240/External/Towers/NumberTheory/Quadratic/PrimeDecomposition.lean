import ErdosProblems.Erdos240.External.Towers.NumberTheory.Quadratic.IntegralElements

namespace Towers.NumberTheory

open Ideal
open scoped QuadraticAlgebra

/-- The quadratic order with basis `1, ω` and relation `ω² = A + Bω`.  The two
normal forms for quadratic rings of integers are `QOrd m 0` and
`QOrd ((m - 1) / 4) 1`. -/
abbrev QOrd (A B : ℤ) := QuadraticAlgebra ℤ A B

namespace QOrd

/-- Evaluation at a root of the defining quadratic polynomial modulo `p`. -/
def evalMod (A B : ℤ) (p : ℕ) (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p)) :
    QOrd A B →+* ZMod p :=
  (QuadraticAlgebra.lift
    (R := ℤ) (A := ZMod p)
    ⟨(r : ZMod p), by simpa [pow_two] using hr⟩).toRingHom

@[simp]
theorem evalMod_apply (A B : ℤ) (p : ℕ) (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p))
    (z : QOrd A B) :
    evalMod A B p r hr z = (z.re : ZMod p) + (z.im : ZMod p) * (r : ZMod p) := by
  simp [evalMod]

/-- The ideal `(p, ω - r)` attached to a root `r` modulo `p`. -/
def rootIdeal (A B : ℤ) (p : ℕ) (r : ℤ) : Ideal (QOrd A B) :=
  span {(p : QOrd A B), ω - (r : QOrd A B)}

private theorem root_ideal_ker (A B : ℤ) (p : ℕ) (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p)) :
    rootIdeal A B p r = RingHom.ker (evalMod A B p r hr) := by
  apply le_antisymm
  · rw [rootIdeal, span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simp [evalMod]
    · simp [evalMod]
  · intro z hz
    rw [RingHom.mem_ker, evalMod_apply] at hz
    have hdiv : (p : ℤ) ∣ z.re + z.im * r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [Int.cast_add, Int.cast_mul] using hz
    obtain ⟨q, hq⟩ := hdiv
    rw [rootIdeal, mem_span_pair]
    refine ⟨(⟨q, 0⟩ : QOrd A B),
      (⟨z.im, 0⟩ : QOrd A B), ?_⟩
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_sub,
        QuadraticAlgebra.omega_re]
      dsimp
      nlinarith [hq]
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.omega_im]
      dsimp
      ring

private theorem evalMod_surjective (A B : ℤ) (p : ℕ) (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p)) :
    Function.Surjective (evalMod A B p r hr) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) x
  refine ⟨(z : QOrd A B), ?_⟩
  simp [evalMod]

/-- Every root of the defining polynomial modulo a rational prime gives the
explicit maximal (hence prime) ideal `(p, ω - r)`. -/
theorem root_ideal_maximal (A B : ℤ) (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p)) :
    (rootIdeal A B p r).IsMaximal := by
  rw [root_ideal_ker A B p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (evalMod_surjective A B p r hr)

theorem root_ideal_prime (A B : ℤ) (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p)) :
    (rootIdeal A B p r).IsPrime :=
  (root_ideal_maximal A B p r hr).isPrime

private theorem root_mul_conjugate (A B r : ℤ) :
    (ω - (r : QOrd A B)) *
        (ω - ((B - r : ℤ) : QOrd A B)) =
      ((A + r * (B - r) : ℤ) : QOrd A B) := by
  apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

/-- If the defining quadratic has two distinct roots modulo `p`, the two root
ideals multiply to `(p)`.  The Bezout hypothesis says exactly that the roots
`r` and `B - r` remain distinct modulo `p`. -/
theorem root_ideal_conjugate (A B : ℤ) (p : ℕ) (r : ℤ)
    (hroot : ∃ q : ℤ, r ^ 2 - B * r - A = (p : ℤ) * q)
    (hbezout : ∃ u v : ℤ, u * (p : ℤ) + v * (2 * r - B) = 1) :
    rootIdeal A B p r * rootIdeal A B p (B - r) =
      span {(p : QOrd A B)} := by
  obtain ⟨q, hq⟩ := hroot
  obtain ⟨u, v, huv⟩ := hbezout
  apply le_antisymm
  · rw [rootIdeal, rootIdeal, span_pair_mul_span_pair, span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (span {(p : QOrd A B)}).mul_mem_left _
        (mem_span_singleton_self (p : QOrd A B))
    · exact (span {(p : QOrd A B)}).mul_mem_right _
        (mem_span_singleton_self (p : QOrd A B))
    · exact (span {(p : QOrd A B)}).mul_mem_left _
        (mem_span_singleton_self (p : QOrd A B))
    · rw [root_mul_conjugate]
      apply mem_span_singleton.mpr
      refine ⟨((-q : ℤ) : QOrd A B), ?_⟩
      apply QuadraticAlgebra.ext <;> simp
      nlinarith [hq]
  · rw [span_singleton_le_iff_mem]
    let P := rootIdeal A B p r * rootIdeal A B p (B - r)
    have hp_left : (p : QOrd A B) ∈ rootIdeal A B p r := by
      exact subset_span (Set.mem_insert _ _)
    have hp_right : (p : QOrd A B) ∈ rootIdeal A B p (B - r) := by
      exact subset_span (Set.mem_insert _ _)
    have hr_left : ω - (r : QOrd A B) ∈ rootIdeal A B p r := by
      exact subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
    have hs_right :
        ω - ((B - r : ℤ) : QOrd A B) ∈ rootIdeal A B p (B - r) := by
      exact subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
    have hpp :
        (p : QOrd A B) * (p : QOrd A B) ∈ P :=
      mul_mem_mul hp_left hp_right
    have hpr :
        (ω - (r : QOrd A B)) * (p : QOrd A B) ∈ P :=
      mul_mem_mul hr_left hp_right
    have hps :
        (p : QOrd A B) *
          (ω - ((B - r : ℤ) : QOrd A B)) ∈ P :=
      mul_mem_mul hp_left hs_right
    have hpdiff :
        (p : QOrd A B) *
          ((2 * r - B : ℤ) : QOrd A B) ∈ P := by
      convert P.sub_mem hps hpr using 1
      apply QuadraticAlgebra.ext
      · simp
        ring
      · simp
    have hcomb := P.add_mem (P.mul_mem_left (u : QOrd A B) hpp)
      (P.mul_mem_left (v : QOrd A B) hpdiff)
    convert hcomb using 1
    apply QuadraticAlgebra.ext <;> simp
    nlinarith [huv]

private theorem root_mod_mul (A B : ℤ) (p : ℕ) (r q : ℤ)
    (hq : r ^ 2 - B * r - A = (p : ℤ) * q) :
    (r : ZMod p) ^ 2 = (A : ZMod p) + (B : ZMod p) * (r : ZMod p) := by
  have hqmod := congrArg (fun z : ℤ ↦ (z : ZMod p)) hq
  push_cast at hqmod
  simpa only [Nat.cast_eq_zero, mul_zero] using
    (sub_eq_zero.mp <| by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hqmod)

/-- The split case of Theorems 93 and 94 in a quadratic-order normal form. -/
theorem splits_at_root (A B : ℤ) (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hroot : ∃ q : ℤ, r ^ 2 - B * r - A = (p : ℤ) * q)
    (hbezout : ∃ u v : ℤ, u * (p : ℤ) + v * (2 * r - B) = 1) :
    (rootIdeal A B p r).IsPrime ∧
      (rootIdeal A B p (B - r)).IsPrime ∧
      rootIdeal A B p r ≠ rootIdeal A B p (B - r) ∧
      rootIdeal A B p r * rootIdeal A B p (B - r) =
        span {(p : QOrd A B)} := by
  obtain ⟨q, hq⟩ := hroot
  have hr := root_mod_mul A B p r q hq
  have hs :
      ((B - r : ℤ) : ZMod p) ^ 2 =
        (A : ZMod p) + (B : ZMod p) * ((B - r : ℤ) : ZMod p) := by
    push_cast
    linear_combination hr
  have hprimeR := root_ideal_prime A B p r hr
  have hprimeS := root_ideal_prime A B p (B - r) hs
  refine ⟨hprimeR, hprimeS, ?_, root_ideal_conjugate A B p r ⟨q, hq⟩ hbezout⟩
  intro heq
  obtain ⟨u, v, huv⟩ := hbezout
  have hp : (p : QOrd A B) ∈ rootIdeal A B p r :=
    subset_span (Set.mem_insert _ _)
  have hrmem : ω - (r : QOrd A B) ∈ rootIdeal A B p r :=
    subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
  have hsmem :
      ω - ((B - r : ℤ) : QOrd A B) ∈ rootIdeal A B p r := by
    rw [heq]
    exact subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
  have hdiff :
      ((2 * r - B : ℤ) : QOrd A B) ∈ rootIdeal A B p r := by
    convert (rootIdeal A B p r).sub_mem hsmem hrmem using 1
    apply QuadraticAlgebra.ext
    · simp
      ring
    · simp
  have hone := (rootIdeal A B p r).add_mem
    ((rootIdeal A B p r).mul_mem_left (u : QOrd A B) hp)
    ((rootIdeal A B p r).mul_mem_left (v : QOrd A B) hdiff)
  have : (1 : QOrd A B) ∈ rootIdeal A B p r := by
    convert hone using 1
    apply QuadraticAlgebra.ext <;> simp
    nlinarith [huv]
  exact hprimeR.ne_top ((rootIdeal A B p r).eq_top_iff_one.mpr this)

/-- Coordinatewise reduction of a quadratic order modulo `p`. -/
def reduceMod (A B : ℤ) (p : ℕ) :
    QOrd A B →+*
      QuadraticAlgebra (ZMod p) (A : ZMod p) (B : ZMod p) where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

@[simp]
theorem reduceMod_re (A B : ℤ) (p : ℕ) (z : QOrd A B) :
    (reduceMod A B p z).re = (z.re : ZMod p) := rfl

@[simp]
theorem reduceMod_im (A B : ℤ) (p : ℕ) (z : QOrd A B) :
    (reduceMod A B p z).im = (z.im : ZMod p) := rfl

private theorem reduceMod_surjective (A B : ℤ) (p : ℕ) :
    Function.Surjective (reduceMod A B p) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) x
  obtain ⟨b, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) y
  exact ⟨(⟨a, b⟩ : QOrd A B), rfl⟩

private theorem span_reduce_ker (A B : ℤ) (p : ℕ) :
    span {(p : QOrd A B)} = RingHom.ker (reduceMod A B p) := by
  apply le_antisymm
  · rw [span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    apply QuadraticAlgebra.ext
    · simpa only [reduceMod_re, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.re_zero, Int.cast_natCast] using ZMod.natCast_self p
    · simp only [reduceMod_im, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.im_zero, Int.cast_zero]
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hre0 : (z.re : ZMod p) = 0 := by
      simpa using congrArg QuadraticAlgebra.re hz
    have him0 : (z.im : ZMod p) = 0 := by
      simpa using congrArg QuadraticAlgebra.im hz
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre0
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him0
    apply mem_span_singleton.mpr
    refine ⟨(⟨a, b⟩ : QOrd A B), ?_⟩
    apply QuadraticAlgebra.ext
    · simpa [mul_comm] using ha
    · simpa [mul_comm] using hb

/-- If the defining quadratic has no root modulo `p`, then `(p)` is maximal
(and therefore prime), which is the inert case of Theorems 93 and 94. -/
theorem inert_no_root (A B : ℤ) (p : ℕ) [Fact p.Prime]
    (hroot : ∀ r : ZMod p,
      r ^ 2 ≠ (A : ZMod p) + (B : ZMod p) * r) :
    (span {(p : QOrd A B)}).IsPrime := by
  letI : Fact (∀ r : ZMod p,
      r ^ 2 ≠ (A : ZMod p) + (B : ZMod p) * r) := ⟨hroot⟩
  have hmax : (RingHom.ker (reduceMod A B p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (reduceMod_surjective A B p)
  rw [← span_reduce_ker A B p] at hmax
  exact hmax.isPrime

private theorem root_sub_mul (A B : ℤ) (p : ℕ) (r s t : ℤ)
    (hst : s - r = (p : ℤ) * t) :
    rootIdeal A B p r = rootIdeal A B p s := by
  rw [rootIdeal, rootIdeal]
  apply le_antisymm
  · rw [span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact subset_span (Set.mem_insert _ _)
    · apply mem_span_pair.mpr
      refine ⟨(t : QOrd A B), 1, ?_⟩
      apply QuadraticAlgebra.ext <;> simp
      nlinarith [hst]
  · rw [span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact subset_span (Set.mem_insert _ _)
    · apply mem_span_pair.mpr
      refine ⟨((-t : ℤ) : QOrd A B), 1, ?_⟩
      apply QuadraticAlgebra.ext <;> simp
      nlinarith [hst]

private theorem root_conjugate_coprime
    (A B : ℤ) (p : ℕ) (r q u v : ℤ)
    (hq : A + r * (B - r) = (p : ℤ) * q)
    (huv : u * (p : ℤ) + v * q = 1) :
    rootIdeal A B p r * rootIdeal A B p (B - r) =
      span {(p : QOrd A B)} := by
  apply le_antisymm
  · rw [rootIdeal, rootIdeal, span_pair_mul_span_pair, span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (span {(p : QOrd A B)}).mul_mem_left _
        (mem_span_singleton_self (p : QOrd A B))
    · exact (span {(p : QOrd A B)}).mul_mem_right _
        (mem_span_singleton_self (p : QOrd A B))
    · exact (span {(p : QOrd A B)}).mul_mem_left _
        (mem_span_singleton_self (p : QOrd A B))
    · rw [root_mul_conjugate]
      apply mem_span_singleton.mpr
      refine ⟨(q : QOrd A B), ?_⟩
      apply QuadraticAlgebra.ext <;> simp
      nlinarith [hq]
  · rw [span_singleton_le_iff_mem]
    let P := rootIdeal A B p r * rootIdeal A B p (B - r)
    have hp_left : (p : QOrd A B) ∈ rootIdeal A B p r :=
      subset_span (Set.mem_insert _ _)
    have hp_right : (p : QOrd A B) ∈ rootIdeal A B p (B - r) :=
      subset_span (Set.mem_insert _ _)
    have hr_left : ω - (r : QOrd A B) ∈ rootIdeal A B p r :=
      subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
    have hs_right :
        ω - ((B - r : ℤ) : QOrd A B) ∈ rootIdeal A B p (B - r) :=
      subset_span (Set.mem_insert_iff.mpr <| Or.inr <| Set.mem_singleton _)
    have hpp :
        (p : QOrd A B) * (p : QOrd A B) ∈ P :=
      mul_mem_mul hp_left hp_right
    have hroots :
        (ω - (r : QOrd A B)) *
          (ω - ((B - r : ℤ) : QOrd A B)) ∈ P :=
      mul_mem_mul hr_left hs_right
    have hpq :
        (p : QOrd A B) * (q : QOrd A B) ∈ P := by
      rw [root_mul_conjugate] at hroots
      convert hroots using 1
      apply QuadraticAlgebra.ext <;> simp
      nlinarith [hq]
    have hcomb := P.add_mem (P.mul_mem_left (u : QOrd A B) hpp)
      (P.mul_mem_left (v : QOrd A B) hpq)
    convert hcomb using 1
    apply QuadraticAlgebra.ext <;> simp
    nlinarith [huv]

/-- The repeated-root case: the root ideal is prime and its square is `(p)`. -/
theorem ramifies_at_root (A B : ℤ) (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hquot : ∃ q : ℤ, A + r * (B - r) = (p : ℤ) * q)
    (hsame : ∃ t : ℤ, B - 2 * r = (p : ℤ) * t)
    (hcoprime : ∀ q : ℤ, A + r * (B - r) = (p : ℤ) * q →
      ∃ u v : ℤ, u * (p : ℤ) + v * q = 1) :
    (rootIdeal A B p r).IsPrime ∧
      rootIdeal A B p r * rootIdeal A B p r =
        span {(p : QOrd A B)} := by
  obtain ⟨q, hq⟩ := hquot
  obtain ⟨t, ht⟩ := hsame
  obtain ⟨u, v, huv⟩ := hcoprime q hq
  have hroot : r ^ 2 - B * r - A = (p : ℤ) * (-q) := by
    nlinarith [hq]
  have hr := root_mod_mul A B p r (-q) hroot
  have heq : rootIdeal A B p (B - r) = rootIdeal A B p r := by
    symm
    apply root_sub_mul A B p r (B - r) t
    nlinarith [ht]
  refine ⟨root_ideal_prime A B p r hr, ?_⟩
  calc
    rootIdeal A B p r * rootIdeal A B p r =
        rootIdeal A B p r * rootIdeal A B p (B - r) := by rw [heq]
    _ = span {(p : QOrd A B)} :=
      root_conjugate_coprime A B p r q u v hq huv

/-- Theorem 94(i), in the half-integral normal form for `m = 8k + 1`. -/
theorem two_splits_eight (k : ℤ) :
    (rootIdeal (2 * k) 1 2 0).IsPrime ∧
      (rootIdeal (2 * k) 1 2 1).IsPrime ∧
      rootIdeal (2 * k) 1 2 0 ≠ rootIdeal (2 * k) 1 2 1 ∧
      rootIdeal (2 * k) 1 2 0 * rootIdeal (2 * k) 1 2 1 =
        span {(2 : QOrd (2 * k) 1)} := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  simpa using splits_at_root (2 * k) 1 2 0
    ⟨-k, by ring⟩ ⟨0, -1, by ring⟩

/-- Theorem 94(ii), in the half-integral normal form for `m = 8k + 5`. -/
theorem two_inert_eight (k : ℤ) :
    (span {(2 : QOrd (2 * k + 1) 1)}).IsPrime := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply inert_no_root (2 * k + 1) 1 2
  intro r
  have htwo : (2 : ZMod 2) = 0 := by decide
  fin_cases r
  · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_one, htwo, zero_mul, zero_add,
      one_mul, ne_eq]
    decide
  · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_one, htwo, zero_mul, zero_add,
      one_mul, ne_eq]
    decide

/-- Theorem 94(iii), first case, for `m = 4k + 2`. -/
theorem ramifies_four_add (k : ℤ) :
    (rootIdeal (4 * k + 2) 0 2 0).IsPrime ∧
      rootIdeal (4 * k + 2) 0 2 0 * rootIdeal (4 * k + 2) 0 2 0 =
        span {(2 : QOrd (4 * k + 2) 0)} := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply ramifies_at_root (4 * k + 2) 0 2 0
  · exact ⟨2 * k + 1, by ring⟩
  · exact ⟨0, by ring⟩
  · intro q hq
    refine ⟨-k, 1, ?_⟩
    norm_num at hq ⊢
    nlinarith [hq]

/-- Theorem 94(iii), second case, for `m = 4k + 3`. -/
theorem ramifies_four_three (k : ℤ) :
    (rootIdeal (4 * k + 3) 0 2 (-1)).IsPrime ∧
      rootIdeal (4 * k + 3) 0 2 (-1) * rootIdeal (4 * k + 3) 0 2 (-1) =
        span {(2 : QOrd (4 * k + 3) 0)} := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply ramifies_at_root (4 * k + 3) 0 2 (-1)
  · exact ⟨2 * k + 1, by ring⟩
  · exact ⟨1, by ring⟩
  · intro q hq
    refine ⟨-k, 1, ?_⟩
    norm_num at hq ⊢
    nlinarith [hq]

/-- Theorem 93(i) for the integral-coordinate quadratic order. -/
theorem odd_splits_order
    (m a : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬(p : ℤ) ∣ m) (hroot : (p : ℤ) ∣ a ^ 2 - m) :
    (rootIdeal m 0 p a).IsPrime ∧
      (rootIdeal m 0 p (-a)).IsPrime ∧
      rootIdeal m 0 p a ≠ rootIdeal m 0 p (-a) ∧
      rootIdeal m 0 p a * rootIdeal m 0 p (-a) =
        span {(p : QOrd m 0)} := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hnot : ¬(p : ℤ) ∣ 2 * a := by
    intro hpa2
    rcases hpZ.dvd_mul.mp hpa2 with hp_two | hp_a
    · have hp_two_nat : p ∣ 2 := by
        exact Int.natCast_dvd_natCast.mp (by simpa using hp_two)
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp_two_nat with hp_one | hp_eq
      · exact (Fact.out : Nat.Prime p).ne_one hp_one
      · exact hp2 hp_eq
    · have hp_asq : (p : ℤ) ∣ a ^ 2 := by
        obtain ⟨c, hc⟩ := hp_a
        refine ⟨(p : ℤ) * c ^ 2, ?_⟩
        rw [hc]
        ring
      have hp_m : (p : ℤ) ∣ m := by
        have := dvd_sub hp_asq hroot
        simpa using this
      exact hpm hp_m
  have hcop : IsCoprime (p : ℤ) (2 * a) :=
    hpZ.irreducible.coprime_iff_not_dvd.mpr hnot
  change ∃ u v : ℤ, u * (p : ℤ) + v * (2 * a) = 1 at hcop
  obtain ⟨q, hq⟩ := hroot
  simpa using splits_at_root m 0 p a
    ⟨q, by simpa using hq⟩ (by simpa using hcop)

/-- Theorem 93(ii) for the integral-coordinate quadratic order. -/
theorem odd_inert_order
    (m : ℤ) (p : ℕ) [Fact p.Prime]
    (hnonsquare : ∀ a : ℤ, ¬(p : ℤ) ∣ a ^ 2 - m) :
    (span {(p : QOrd m 0)}).IsPrime := by
  apply inert_no_root m 0 p
  intro r hr
  obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) r
  apply hnonsquare a
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hr' : (a : ZMod p) ^ 2 = (m : ZMod p) := by simpa using hr
  simpa [Int.cast_sub, Int.cast_pow] using sub_eq_zero.mpr hr'

/-- Theorem 93(iii) for the integral-coordinate quadratic order. -/
theorem odd_ramifies_order
    (m : ℤ) (hm : Squarefree m) (p : ℕ) [Fact p.Prime]
    (hpm : (p : ℤ) ∣ m) :
    (rootIdeal m 0 p 0).IsPrime ∧
      rootIdeal m 0 p 0 * rootIdeal m 0 p 0 =
        span {(p : QOrd m 0)} := by
  obtain ⟨q, hq⟩ := hpm
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hnot : ¬(p : ℤ) ∣ q := by
    intro hpq
    obtain ⟨t, ht⟩ := hpq
    have hsq : (p : ℤ) ^ 2 ∣ m := by
      refine ⟨t, ?_⟩
      rw [hq]
      rw [ht]
      ring
    exact hpZ.not_unit (hm (p : ℤ) <| by simpa [pow_two] using hsq)
  have hcop : IsCoprime (p : ℤ) q :=
    hpZ.irreducible.coprime_iff_not_dvd.mpr hnot
  change ∃ u v : ℤ, u * (p : ℤ) + v * q = 1 at hcop
  apply ramifies_at_root m 0 p 0
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨0, by ring⟩
  · intro q' hq'
    have hqq : q' = q := by
      apply mul_left_cancel₀ hp0
      have hq'' : m = (p : ℤ) * q' := by simpa using hq'
      exact hq''.symm.trans hq
    simpa [hqq] using hcop

end QOrd

end Towers.NumberTheory
