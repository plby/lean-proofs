import ErdosProblems.Erdos444.FewPrimeFactors
import ErdosProblems.Erdos444.MomentComparison
import ErdosProblems.Erdos444.SupportBound
import ErdosProblems.Erdos444.SupportSplit

/-!
# A coarse finite Erdős--Sárközy large-value lemma

This module assembles the exact tuple moment, the few-large-prime estimate,
and the support split.  All asymptotic choices have been reduced to two
simple hypotheses: the discarded reciprocal mass is at most half of the
full prefix mass, and the reciprocal mass of the prime window is at most the
integer parameter `m`.
-/

open scoped BigOperators

namespace Erdos444

noncomputable section

open Erdos697.Factorization

/-- Prefix members having at least `t` distinct prime factors above `y`. -/
def richPrefix (A : Set ℕ) (X y t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun a ↦
    a ∈ A ∧ t ≤ (roughPrimes y a).card

@[simp] theorem mem_richPrefix_iff {A : Set ℕ} {X y t a : ℕ} :
    a ∈ richPrefix A X y t ↔
      1 ≤ a ∧ a ≤ X ∧ a ∈ A ∧ t ≤ (roughPrimes y a).card := by
  simp [richPrefix, and_assoc]

theorem largePrimeDistinctCount_eq_card_roughPrimes
    {n y : ℕ} :
    largePrimeDistinctCount n y = (roughPrimes y n).card := by
  unfold largePrimeDistinctCount largePrimeSupport roughPrimes
  rw [Nat.support_factorization]

/-- The strict prefix at `X+1` splits into the rich part and the discarded
few-large-prime part. -/
theorem reciprocalMassNat_succ_eq_rich_add_few
    (A : Set ℕ) (X y t : ℕ) :
    reciprocalMassNat A (X + 1) =
      (∑ a ∈ richPrefix A X y t, (a : ℝ)⁻¹) +
      ∑ a ∈ fewRoughFactorsUpTo A X y t, (a : ℝ)⁻¹ := by
  classical
  let P := (positiveBelowNat (X + 1)).filter (fun a ↦ a ∈ A)
  have hP : P = richPrefix A X y t ∪ fewRoughFactorsUpTo A X y t := by
    ext a
    simp only [P, Finset.mem_filter, mem_positiveBelowNat_iff,
      Finset.mem_union, mem_richPrefix_iff, mem_fewRoughFactorsUpTo]
    constructor
    · rintro ⟨⟨ha1, haX⟩, haA⟩
      by_cases hrich : t ≤ (roughPrimes y a).card
      · exact Or.inl ⟨ha1, by omega, haA, hrich⟩
      · exact Or.inr ⟨ha1, by omega, haA, by omega⟩
    · rintro (⟨ha1, haX, haA, _⟩ | ⟨ha1, haX, haA, _⟩)
      · exact ⟨⟨ha1, by omega⟩, haA⟩
      · exact ⟨⟨ha1, by omega⟩, haA⟩
  have hdisj : Disjoint (richPrefix A X y t)
      (fewRoughFactorsUpTo A X y t) := by
    rw [Finset.disjoint_left]
    intro a har haf
    have hr := mem_richPrefix_iff.mp har
    have hf := mem_fewRoughFactorsUpTo.mp haf
    omega
  unfold reciprocalMassNat
  change (∑ a ∈ P, (a : ℝ)⁻¹) = _
  rw [hP, Finset.sum_union hdisj]

/-- Coarse finite large-value theorem with fully explicit discrete
parameters.  The moment order and prime cutoff are both `m²`; the richness
threshold is `8*b`, while the two support thresholds are `m²*b` and
`4*m²*b`. -/
theorem finite_large_value
    (A : Set ℕ) (X m b q : ℕ)
    (hm : 2 ≤ m) (hmX : m ^ 2 ≤ X) (hb : q + 2 ≤ b)
    (hwindow : Erdos697.PrimeWindow.reciprocalMass (m ^ 2) X ≤ m)
    (hretain :
      (∑ a ∈ fewRoughFactorsUpTo A X (m ^ 2) (8 * b), (a : ℝ)⁻¹) ≤
        reciprocalMassNat A (X + 1) / 2)
    (hmass : 0 < reciprocalMassNat A (X + 1)) :
    (((m ^ 2 : ℕ) : ℝ) ^ q) * reciprocalMassNat A (X + 1) ≤
      (maxDivisorCountNat A (X ^ (m ^ 2) + 1) : ℝ) := by
  let r : ℕ := m ^ 2
  let y : ℕ := m ^ 2
  let t : ℕ := 8 * b
  let B : ℕ := r * b
  let K : ℕ := 4 * r * b
  let Astar : Finset ℕ := richPrefix A X y t
  let N : ℕ := X ^ r
  let P : Finset ℕ := Erdos697.PrimeWindow.primes y X
  let μ : ℝ := Erdos697.PrimeWindow.reciprocalMass y X
  have hr : 0 < r := by dsimp [r]; positivity
  have hX : 0 < X := by omega
  have hy : 1 < y := by dsimp [y]; nlinarith
  have hpos : ∀ a ∈ Astar, 0 < a := by
    intro a ha
    exact (mem_richPrefix_iff.mp ha).1
  have hle : ∀ a ∈ Astar, a ≤ X := by
    intro a ha
    exact (mem_richPrefix_iff.mp ha).2.1
  have hsub : ∀ a ∈ Astar, a ∈ A := by
    intro a ha
    exact (mem_richPrefix_iff.mp ha).2.2.1
  have hrich : ∀ a ∈ Astar, t ≤ largePrimeDistinctCount a y := by
    intro a ha
    have ha' := mem_richPrefix_iff.mp ha
    rw [largePrimeDistinctCount_eq_card_roughPrimes]
    exact ha'.2.2.2
  have hBK : 2 * B + K ≤ r * t := by
    dsimp [B, K, t]
    nlinarith
  have hsupportSub : representationSupport Astar r N ⊆
      repeatedPrimeExceptionalUpTo y B N ∪ manyPrimeDivisorsUpTo P K N := by
    simpa [N, P] using
      (representationSupport_subset_repeatedPrime_union_manyPrime
        hpos hle hrich hBK)
  have hsupportCardNat : (representationSupport Astar r N).card ≤
      (repeatedPrimeExceptionalUpTo y B N).card +
        (manyPrimeDivisorsUpTo P K N).card := by
    exact (Finset.card_le_card hsupportSub).trans
      (Finset.card_union_le _ _)
  have hsupportCard : ((representationSupport Astar r N).card : ℝ) ≤
      ((repeatedPrimeExceptionalUpTo y B N).card : ℝ) +
        (manyPrimeDivisorsUpTo P K N).card := by
    exact_mod_cast hsupportCardNat
  have hrepeat : ((repeatedPrimeExceptionalUpTo y B N).card : ℝ) ≤
      (N : ℝ) / y ^ B := card_repeatedPrimeExceptionalUpTo_le_div hy
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos697.PrimeWindow.mem_primes.mp hp).2.2
  have hmanych : ((manyPrimeDivisorsUpTo P K N).card : ℝ) ≤
      (N : ℝ) * (μ ^ K / (K.factorial : ℝ)) := by
    simpa [P, μ, Erdos697.PrimeWindow.reciprocalMass] using
      card_manyPrimeDivisorsUpTo_le hPprime K N
  have hsupportBound : ((representationSupport Astar r N).card : ℝ) ≤
      (N : ℝ) / y ^ B + (N : ℝ) * (μ ^ K / (K.factorial : ℝ)) :=
    hsupportCard.trans (add_le_add hrepeat hmanych)
  have hμ0 : 0 ≤ μ := by
    dsimp [μ, Erdos697.PrimeWindow.reciprocalMass]
    positivity
  have hμm : μ ≤ m := by simpa [μ, y] using hwindow
  have hscale : 2 * ((representationSupport Astar r N).card : ℝ) *
      (2 * (((m ^ 2 : ℕ) : ℝ) ^ q)) ^ r ≤ (N : ℝ) := by
    have := support_scale_bound (N : ℝ)
      ((representationSupport Astar r N).card : ℝ) μ m b q
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hμ0 hμm hm hb
    simpa [r, y, B, K] using this hsupportBound
  have hmassSplit := reciprocalMassNat_succ_eq_rich_add_few A X y t
  have hnonnegFew : 0 ≤
      ∑ a ∈ fewRoughFactorsUpTo A X y t, (a : ℝ)⁻¹ := by positivity
  have hretain' : reciprocalMassNat A (X + 1) ≤
      2 * ∑ a ∈ Astar, (a : ℝ)⁻¹ := by
    have hret : (∑ a ∈ fewRoughFactorsUpTo A X y t, (a : ℝ)⁻¹) ≤
        reciprocalMassNat A (X + 1) / 2 := by
      simpa [y, t] using hretain
    dsimp [Astar]
    rw [hmassSplit]
    nlinarith
  have hstar : 0 < ∑ a ∈ Astar, (a : ℝ)⁻¹ := by
    nlinarith [hmass]
  have hlarge := large_maxDivisorCountNat_of_support_bound
    (A := A) (Astar := Astar) (r := r) (U := X)
    (F := reciprocalMassNat A (X + 1))
    (Z := (((m ^ 2 : ℕ) : ℝ) ^ q)) hr hX hpos hle hsub
    (reciprocalMassNat_nonneg A (X + 1)) hretain' hstar (by positivity) ?_
  · simpa [r, N] using hlarge
  · simpa [r, N] using hscale

end

end Erdos444
