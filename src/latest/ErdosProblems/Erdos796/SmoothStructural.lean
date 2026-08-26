import ErdosProblems.Erdos796.SmoothFiberCross
import ErdosProblems.Erdos796.BucketCompression
import ErdosProblems.Erdos796.Lift

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The smooth-fibre contribution to the structural reduction

This module combines cross-compatibility, collision cleaning, and quotient
bucket compression.  It proves that all cofactors at most `R` attached to
large primes are bounded by the finite cofactor model, with the exact cleaning
loss `R^4`.
-/

namespace Erdos796

open scoped BigOperators

namespace SmoothStructural

open SmoothFiberCross BucketCompression

theorem cofactorFiber_subset_quotient
    {n R q : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hq : q ∈ largePrimes n) :
    cofactorFiber A R q ⊆ positiveIcc (n / q) := by
  intro u hu
  have hu' := mem_cofactorFiber.mp hu
  have hqu := mem_positiveIcc.mp (hA.1 hu'.2)
  have hqpos := (mem_largePrimes.mp hq).2.2.pos
  apply mem_positiveIcc.mpr
  constructor
  · exact (mem_positiveIcc.mp hu'.1).1
  · apply (Nat.le_div_iff_mul_le hqpos).mpr
    simpa [Nat.mul_comm] using! hqu.2

theorem largePrime_gt_cofactorRange
    {n R q : ℕ} (hR : R ≤ n.sqrt) (hq : q ∈ largePrimes n) :
    R < q :=
  hR.trans_lt (mem_largePrimes.mp hq).1

theorem largePrimes_are_prime {n q : ℕ} (hq : q ∈ largePrimes n) :
    q.Prime :=
  (mem_largePrimes.mp hq).2.2

/-- The bucket-compressed cleaned fibres are compatible and dominate the
sum of cleaned fibre sizes by their finite-model score. -/
theorem exists_compatible_model_for_cleaned
    {n : ℕ} {S : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ largePrimes n, S q ⊆ positiveIcc (n / q))
    (hcompat : ∀ q ∈ largePrimes n, ∀ r ∈ largePrimes n, ∀ m : ℕ,
      productRepCount (S q) (S r) m ≤ 2) :
    ∃ U : ℕ → Finset ℕ,
      Compatible U ∧
      (∑ q ∈ largePrimes n, (S q).card) ≤ modelScore n U := by
  let U := compressedFamily (largePrimes n) (fun q => n / q) S
  have hU : Compatible U :=
    compatible_compressedFamily hrange hcompat
  refine ⟨U, hU, ?_⟩
  calc
    ∑ q ∈ largePrimes n, (S q).card ≤
        ∑ q ∈ largePrimes n, (U (n / q)).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hj : n / q ∈
          bucketIndices (largePrimes n) (fun r => n / r) := by
        exact mem_bucketIndices.mpr ⟨q, hq, rfl⟩
      rw [show U (n / q) =
          S (representative (largePrimes n) (fun r => n / r) S (n / q)) by
        exact compressedFamily_eq_of_mem hj]
      exact card_le_representative hj hq rfl
    _ = modelScore n U := sum_primes_eq_modelScore n U

/-- Exact smooth-fibre structural estimate: after at most `R⁴` deletions,
bucket compression embeds all remaining cofactors into one compatible model
family. -/
theorem smooth_fibres_le_model_add_cleaning
    {n R : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hR : R ≤ n.sqrt) :
    ∃ U : ℕ → Finset ℕ,
      Compatible U ∧
      (∑ q ∈ largePrimes n, (cofactorFiber A R q).card) ≤
        modelScore n U + R ^ 4 := by
  obtain ⟨S, hSsub, hScompat, hcost⟩ :=
    exists_cleaned_cofactorFibers hA
      (fun q hq => largePrimes_are_prime hq)
      (fun q hq => largePrime_gt_cofactorRange hR hq)
  have hSrange : ∀ q ∈ largePrimes n,
      S q ⊆ positiveIcc (n / q) := by
    intro q hq
    exact (hSsub q hq).trans (cofactorFiber_subset_quotient hA hq)
  obtain ⟨U, hU, hSmodel⟩ :=
    exists_compatible_model_for_cleaned hSrange hScompat
  refine ⟨U, hU, ?_⟩
  have hsplit :
      ∑ q ∈ largePrimes n, (cofactorFiber A R q).card =
        (∑ q ∈ largePrimes n,
          ((cofactorFiber A R q).card - (S q).card)) +
        ∑ q ∈ largePrimes n, (S q).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hcard := Finset.card_le_card (hSsub q hq)
    omega
  omega

/-- Taking the model maximum removes the witness family. -/
theorem smooth_fibres_le_G_add_cleaning
    {n R : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hR : R ≤ n.sqrt) :
    (∑ q ∈ largePrimes n, (cofactorFiber A R q).card) ≤
      G n + R ^ 4 := by
  obtain ⟨U, hU, hbound⟩ :=
    smooth_fibres_le_model_add_cleaning hA hR
  exact hbound.trans (Nat.add_le_add_right (modelScore_le_G hU n) _)

end SmoothStructural

end Erdos796
