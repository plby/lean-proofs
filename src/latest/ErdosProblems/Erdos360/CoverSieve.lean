import ErdosProblems.Erdos360.Core

/-!
# The progression-cover / beta-sieve bridge for Erdős 360

The progressions produced by the inverse theorem need not have differences
coprime to the original missing-prime product.  For a progression of step
`b`, the correct application of the already formalized beta sieve uses the
auxiliary target `n * b`.  Then every sieving prime dividing `b` has been
removed and the step is automatically coprime to the resulting product.

This file packages that argument, sums it over an overlapping progression
cover, and records both the upper bound for useful (coprime) representatives
and the corresponding lower bound for non-coprime representatives.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Removing the additional prime divisors of `b` from the sieve target can
only decrease the missing-prime product. -/
lemma missingPrimeProduct_mul_dvd (n b y : ℕ) :
    missingPrimeProduct (n * b) y ∣ missingPrimeProduct n y := by
  unfold missingPrimeProduct
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  apply mem_missingPrimesUpTo.mpr
  obtain ⟨hp2, hpy, hpprime, hpnb⟩ := mem_missingPrimesUpTo.mp hp
  exact ⟨hp2, hpy, hpprime, fun hpn ↦ hpnb (hpn.trans (dvd_mul_right n b))⟩

/-- An element surviving the original missing-prime sieve also survives the
weaker sieve in which primes dividing a progression step have been removed. -/
lemma coprime_missingPrimeProduct_mul_of_coprime
    {n b y x : ℕ} (hx : Nat.Coprime (missingPrimeProduct n y) x) :
    Nat.Coprime (missingPrimeProduct (n * b) y) x :=
  Nat.Coprime.of_dvd_left (missingPrimeProduct_mul_dvd n b y) hx

/-- The original coprime part of a set covered by progressions is bounded by
the sum of the *step-adjusted* sifted occurrence counts.  Overlaps are allowed. -/
lemma card_coprimePart_le_sum_stepAdjusted_cover
    {X : Finset ℕ} {m n y : ℕ} (P : Fin m → NatProgressionSpec)
    (hcover : ∀ x ∈ X, ∃ i, x ∈ (P i).carrier) :
    (coprimePart X (missingPrimeProduct n y)).card ≤
      ∑ i, (progressionCoprimeIndices
        (P i).start (P i).step (P i).length
        (missingPrimeProduct (n * (P i).step) y)).card := by
  let U := Finset.univ.biUnion fun i : Fin m ↦
    coprimePart (P i).carrier
      (missingPrimeProduct (n * (P i).step) y)
  have hsub : coprimePart X (missingPrimeProduct n y) ⊆ U := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
    have hxcop : Nat.Coprime (missingPrimeProduct n y) x :=
      (Finset.mem_filter.mp hx).2
    obtain ⟨i, hi⟩ := hcover x hxX
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hi, coprime_missingPrimeProduct_mul_of_coprime hxcop⟩
  calc
    (coprimePart X (missingPrimeProduct n y)).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.univ,
        (coprimePart (P i).carrier
          (missingPrimeProduct (n * (P i).step) y)).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact progression_coprimePart_card (P i)
        (missingPrimeProduct (n * (P i).step) y)

/-- The Euler product over missing primes is at most one. -/
lemma missingEulerProduct_le_one (n y : ℕ) :
    missingEulerProduct n y ≤ 1 := by
  unfold missingEulerProduct
  apply Finset.prod_le_one
  · intro p hp
    exact (Erdos851.oneShift_localFactor_pos
      (mem_missingPrimesUpTo.mp hp).2.2.1).le
  · intro p hp
    have hnonneg := (Erdos851.oneShiftDensity_pos
      (mem_missingPrimesUpTo.mp hp).2.2.1).le
    linarith

/-- Exact beta-sieve bound for a progression cover with arbitrary positive
steps.  The caller supplies a uniform bound `K` for the step-adjusted Euler
products; this is where the elementary `log log` loss in CFP Lemma 5.9 enters.

The error term is paid once per progression. -/
theorem exists_stepAdjusted_progressionCover_coprimePart_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass m : ℕ, ∀ P : Fin m → NatProgressionSpec,
        ∀ K : ℝ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        0 ≤ K →
        (∀ i, missingEulerProduct (n * (P i).step) y ≤ K) →
        (∑ i, (P i).length) ≤ mass →
        ∀ X : Finset ℕ,
          (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) →
          let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
          let D := y ^ S
          ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
            (mass : ℝ) * ((1 + eta) * K) +
              (m : ℝ) * (D : ℝ) ^ 2 := by
  obtain ⟨A, hA, hsieve⟩ := exists_progressionCoprimeIndices_card_bound
  refine ⟨A, hA, ?_⟩
  intro n y S mass m P K hy hS hlog hKnonneg hK hmass X hcover
  dsimp only
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℕ := y ^ S
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hpiece (i : Fin m) :
      ((progressionCoprimeIndices
        (P i).start (P i).step (P i).length
        (missingPrimeProduct (n * (P i).step) y)).card : ℝ) ≤
          ((P i).length : ℝ) * ((1 + eta) * K) + (D : ℝ) ^ 2 := by
    have hi := hsieve (n * (P i).step) (P i).start (P i).step
      (P i).length y S hy hS hlog
      (progression_step_coprime_missingPrimeProduct_mul n (P i).step y)
    dsimp only at hi
    have hlen : 0 ≤ ((P i).length : ℝ) := by positivity
    have hfactor : 0 ≤ 1 + eta := by positivity
    calc
      ((progressionCoprimeIndices
        (P i).start (P i).step (P i).length
        (missingPrimeProduct (n * (P i).step) y)).card : ℝ) ≤
          ((P i).length : ℝ) *
            ((1 + eta) * missingEulerProduct (n * (P i).step) y) +
              (D : ℝ) ^ 2 := by simpa [eta, D] using hi
      _ ≤ ((P i).length : ℝ) * ((1 + eta) * K) +
              (D : ℝ) ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hK i) hfactor) hlen) le_rfl
  have hcount := card_coprimePart_le_sum_stepAdjusted_cover
    (n := n) (y := y) P hcover
  have hcountR :
      ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct (n * (P i).step) y)).card : ℝ) := by
    exact_mod_cast hcount
  have hmassR : (((∑ i, (P i).length : ℕ) : ℝ)) ≤ mass := by
    exact_mod_cast hmass
  calc
    ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct (n * (P i).step) y)).card : ℝ) := hcountR
    _ ≤ ∑ i, (((P i).length : ℝ) * ((1 + eta) * K) +
          (D : ℝ) ^ 2) := Finset.sum_le_sum fun i _ ↦ hpiece i
    _ = (((∑ i, (P i).length : ℕ) : ℝ)) * ((1 + eta) * K) +
          (m : ℝ) * (D : ℝ) ^ 2 := by
      push_cast
      simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (mass : ℝ) * ((1 + eta) * K) +
          (m : ℝ) * (D : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hmassR (mul_nonneg (by positivity) hKnonneg))
        le_rfl
    _ = _ := rfl

/-- A direct consequence for the existing `HasLongProgressionCover`
interface.  It uses the universal crude Euler-product bound `V ≤ 1`; the
sharper theorem above is the interface needed for CFP's `log log / log`
estimate.  Nonemptiness implies that every displayed progression has positive
length, and hence that their number is at most the parameter mass. -/
theorem exists_longProgressionCover_coprimePart_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass : ℕ, ∀ X : Finset ℕ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty → HasLongProgressionCover X mass →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
          (mass : ℝ) * ((1 + eta) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hcoverSieve⟩ :=
    exists_stepAdjusted_progressionCover_coprimePart_bound
  refine ⟨A, hA, ?_⟩
  intro n y S mass X hy hS hlog hX hlong
  dsimp only
  obtain ⟨m, P, hcover, hmass, hlength⟩ := hlong
  have hXcard : 0 < X.card := Finset.card_pos.mpr hX
  have hlengthPos : ∀ i, 1 ≤ (P i).length := by
    intro i
    have hi := hlength i
    by_contra hnot
    have hz : (P i).length = 0 := by omega
    have hi0 : X.card ≤ 0 := by simpa [hz] using hi
    omega
  have hm : m ≤ mass := by
    calc
      m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, (P i).length :=
        Finset.sum_le_sum fun i _ ↦ hlengthPos i
      _ ≤ mass := hmass
  have hraw := hcoverSieve n y S mass m P 1 hy hS hlog
    (by norm_num) (fun i ↦ missingEulerProduct_le_one _ _) hmass X hcover
  dsimp only at hraw
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℕ := y ^ S
  have hmR : (m : ℝ) ≤ mass := by exact_mod_cast hm
  have hD : 0 ≤ (D : ℝ) ^ 2 := sq_nonneg _
  calc
    ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
        (mass : ℝ) * ((1 + eta) * 1) +
          (m : ℝ) * (D : ℝ) ^ 2 := by simpa [eta, D] using hraw
    _ ≤ (mass : ℝ) * ((1 + eta) * 1) +
          (mass : ℝ) * (D : ℝ) ^ 2 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hmR hD)
    _ = (mass : ℝ) * ((1 + eta) + (D : ℝ) ^ 2) := by ring

/-- The non-coprime part, i.e. the representatives divisible by at least one
missing prime. -/
def nonCoprimePart (X : Finset ℕ) (M : ℕ) : Finset ℕ :=
  X.filter fun x ↦ ¬Nat.Coprime M x

lemma card_coprimePart_add_card_nonCoprimePart (X : Finset ℕ) (M : ℕ) :
    (coprimePart X M).card + (nonCoprimePart X M).card = X.card := by
  classical
  have hunion : coprimePart X M ∪ nonCoprimePart X M = X := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      by_cases h : Nat.Coprime M x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hdisj : Disjoint (coprimePart X M) (nonCoprimePart X M) := by
    rw [Finset.disjoint_left]
    intro x hxc hxn
    exact (Finset.mem_filter.mp hxn).2 (Finset.mem_filter.mp hxc).2
  calc
    (coprimePart X M).card + (nonCoprimePart X M).card =
        (coprimePart X M ∪ nonCoprimePart X M).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = X.card := congrArg Finset.card hunion

lemma mem_nonCoprimePart_missingPrimeProduct_iff
    {X : Finset ℕ} {n y x : ℕ} :
    x ∈ nonCoprimePart X (missingPrimeProduct n y) ↔
      x ∈ X ∧ ∃ p ∈ missingPrimesUpTo n y, p ∣ x := by
  constructor
  · intro hx
    obtain ⟨hxX, hxcop⟩ := Finset.mem_filter.mp hx
    obtain ⟨p, hpprime, hpM, hpx⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hxcop
    refine ⟨hxX, p, ?_, hpx⟩
    rw [← primeFactors_missingPrimeProduct]
    exact Nat.mem_primeFactors.mpr
      ⟨hpprime, hpM, (missingPrimeProduct_pos n y).ne'⟩
  · rintro ⟨hxX, p, hp, hpx⟩
    apply Finset.mem_filter.mpr
    refine ⟨hxX, ?_⟩
    apply Nat.Prime.not_coprime_iff_dvd.mpr
    refine ⟨p, (mem_missingPrimesUpTo.mp hp).2.2.1, ?_, hpx⟩
    exact Finset.dvd_prod_of_mem (fun q ↦ q) hp

/-- Subtracting the coprime upper bound gives the exact number of
representatives which must be divisible by a missing prime. -/
lemma nonCoprimePart_cast_lower_of_coprimePart_cast_upper
    {X : Finset ℕ} {M : ℕ} {B : ℝ}
    (hB : ((coprimePart X M).card : ℝ) ≤ B) :
    (X.card : ℝ) - B ≤ (nonCoprimePart X M).card := by
  have hcard := card_coprimePart_add_card_nonCoprimePart X M
  have hcardR := congrArg (fun z : ℕ ↦ (z : ℝ)) hcard
  norm_num only [Nat.cast_add] at hcardR
  linarith

/-- If a covered set is larger than the step-adjusted beta-sieve upper
bound, it contains an element divisible by a missing prime.  Contrapositively,
an all-useful (all-coprime) diverse remainder cannot fit in such a cover. -/
lemma exists_missingPrime_dvd_of_coprimePart_cast_lt_card
    {X : Finset ℕ} {n y : ℕ} {B : ℝ}
    (hupper : ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤ B)
    (hlarge : B < X.card) :
    ∃ x ∈ X, ∃ p ∈ missingPrimesUpTo n y, p ∣ x := by
  by_contra hnot
  push Not at hnot
  have hall : coprimePart X (missingPrimeProduct n y) = X := by
    ext x
    constructor
    · exact fun hx ↦ (Finset.mem_filter.mp hx).1
    · intro hx
      apply Finset.mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra hcop
      obtain ⟨p, hpprime, hpM, hpx⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpMissing : p ∈ missingPrimesUpTo n y := by
        rw [← primeFactors_missingPrimeProduct]
        exact Nat.mem_primeFactors.mpr
          ⟨hpprime, hpM, (missingPrimeProduct_pos n y).ne'⟩
      exact hnot x hx p hpMissing hpx
  rw [hall] at hupper
  exact (not_lt_of_ge hupper) hlarge

/-- Algebraic last step of the cover/sieve contradiction.  Once a cover
whose mass is proportional to `growth` gives
`|X| ≤ K * growth * sieveFactor`, the translation increment `growth` is
at least the displayed quotient.  Instantiating `|X| ≈ z` and the CFP
sieve factor gives the required order `y / z`. -/
lemma cast_growth_lower_of_card_le_mul
    {X : Finset ℕ} {K growth : ℕ} {sieveFactor : ℝ}
    (hK : 0 < K) (hfactor : 0 < sieveFactor)
    (hbound : (X.card : ℝ) ≤
      ((K : ℝ) * growth) * sieveFactor) :
    (X.card : ℝ) / ((K : ℝ) * sieveFactor) ≤ growth := by
  have hden : 0 < (K : ℝ) * sieveFactor := by
    exact mul_pos (by exact_mod_cast hK) hfactor
  rw [div_le_iff₀ hden]
  calc
    (X.card : ℝ) ≤ ((K : ℝ) * growth) * sieveFactor := hbound
    _ = (growth : ℝ) * ((K : ℝ) * sieveFactor) := by ring

end Erdos360
