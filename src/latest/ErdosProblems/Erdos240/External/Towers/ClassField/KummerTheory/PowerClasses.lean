import ErdosProblems.Erdos240.External.Towers.ClassField.KummerNormIndex.PowerIndex
import ErdosProblems.Erdos240.External.Towers.ClassField.NormLimitation.FiniteQuotients
import ErdosProblems.Erdos240.External.Towers.NumberTheory.Locals.MultiquadraticDegree
import Mathlib.GroupTheory.OrderOfElement

/-!
# Chapter VII, Appendix A: power classes

The Kummer correspondence of Theorem A.3 is formulated using
`K^x / K^{x n}`.  This file records that quotient and the elementary facts
used in Propositions A.2--A.3.  `KummerCorrespondence.lean` gives the full
statement with intermediate fields in a fixed algebraic closure; its proof is
not yet available as a packaged Mathlib theorem.

The two small examples from A.4 are represented by the exact size of the real
square-class group and by Milne's independence theorem for rational prime
square classes.
-/

namespace Towers.CField.KTheory

noncomputable section

/-- The multiplicative power-class group `K^x / K^{x n}`. -/
abbrev PowerClassGroup (K : Type*) [Field K] (n : ℕ) :=
  Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

variable {K : Type*} [Field K]

/-- The quotient map sending a nonzero field element to its power class. -/
def powerClass (n : ℕ) : Kˣ →* PowerClassGroup K n :=
  QuotientGroup.mk' _

/-- Every class in `K^x / K^{x n}` is killed by `n`. -/
theorem power_class_pow (n : ℕ) (x : PowerClassGroup K n) :
    x ^ n = 1 :=
  NLimita.quotient_exponent_pow
    ((powMonoidHom n : Kˣ →* Kˣ).range) n (fun u ↦ ⟨u, rfl⟩) x

/-- Raising a class to an exponent coprime to its order does not change the
cyclic subgroup it generates.  This is the group-theoretic core of the
criterion in Proposition A.2. -/
theorem zpowers_coprime_order
    {G : Type*} [Group G] (x : G) (r : ℕ)
    (hr : r.Coprime (orderOf x)) :
    Subgroup.zpowers (x ^ r) = Subgroup.zpowers x := by
  apply le_antisymm
  · exact Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers x r)
  · exact Subgroup.zpowers_le.mpr
      ((mem_zpowers_pow_iff (g := x) (k := r)).2 hr)

/-- Multiplying a representative by an `n`th power does not change its
power class.  More generally, the class of `b ^ r * c ^ n` is the `r`th
power of the class of `b`. -/
theorem power_class_mul
    {n r : ℕ} {a b c : Kˣ} (h : a = b ^ r * c ^ n) :
    powerClass n a = powerClass n b ^ r := by
  rw [h, map_mul, map_pow]
  have hc : powerClass n (c ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨c, rfl⟩
  rw [hc]
  exact @mul_one (PowerClassGroup K n) _ (powerClass n b ^ r)

/-- The directly formalized implication in Proposition A.2: representatives
related by a coprime power and an `n`th power generate the same subgroup of
the power-class group. -/
theorem same_cyclicSubgroup
    {n r : ℕ} {a b c : Kˣ} (h : a = b ^ r * c ^ n)
    (hr : r.Coprime (orderOf (powerClass n b))) :
    Subgroup.zpowers (powerClass n a) =
      Subgroup.zpowers (powerClass n b) := by
  rw [power_class_mul h]
  exact zpowers_coprime_order _ r hr

/-- **Example A.4(a).** The real square-class group has exactly two elements. -/
theorem real_square_card :
    Nat.card (PowerClassGroup ℝ 2) = 2 := by
  rw [← Subgroup.index_eq_card]
  exact KNIndex.real_even_index (by norm_num) (by norm_num)

/-- **Example A.4(b), independence input.** A nonempty product of distinct
rational primes is not a square.  Consequently the prime square classes are
independent in `ℚ^x / ℚ^{x 2}`. -/
theorem rational_square_independence
    {ι : Type*} (p : ι → ℕ) (s : Finset ι) (hs : s.Nonempty)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) (hinj : Set.InjOn p s) :
    ¬IsSquare ((∏ i ∈ s, p i : ℕ) : ℚ) :=
  Towers.NumberTheory.Milne.distinct_primes_square
    p s hs hp hinj

/-- The finite-level degree consequence of Example A.4(b): adjoining square
roots of `m` distinct rational primes gives degree `2 ^ m`. -/
theorem rational_multiquadratic_degree
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (p : ℕ → ℕ) (alpha : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hinj : Set.InjOn p (Set.Iio m))
    (hsq : ∀ i < m, alpha i ^ 2 = algebraMap ℚ E (p i : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (alpha '' Set.Iio m)) = 2 ^ m :=
  Towers.NumberTheory.Milne.distinct_square_roots
    m p alpha hp hinj hsq

end

end Towers.CField.KTheory
