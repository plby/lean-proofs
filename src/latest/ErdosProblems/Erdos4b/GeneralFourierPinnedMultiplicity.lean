/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedResidues
import ErdosProblems.Erdos4b.GeneralFourierPinnedAsymptotic

/-!
# The pinned Fourier singular factor counts the actual forbidden roots

An edge corresponds bijectively to an intersection of the two root
families. The resulting count retains both collision primes and primes
dividing the companion slope. No separation hypothesis is imposed.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem card_pinnedIndexFourierEdges_eq_intersection
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p ∣ p₀) (hpm : ¬p ∣ m)
    (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    (pinnedIndexFourierEdges h m p₀ p).card =
      (pinnedFirstLocalResidues h w p₀ p ∩ pinnedCompanionLocalResidues h w m p₀ p).card := by
  classical
  have hF := pinnedFirstRoot_injective h hp hKw hwp hpp₀
  have hE := pinnedCompanionRoot_injective h hp hKw hwp hpm hnum
  apply Finset.card_bij (fun ij _ ↦ pinnedFirstRoot h w p₀ p ij.1)
  · intro ij hij
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨ij.1, Finset.mem_univ _, rfl⟩
    · rw [pinnedCompanionLocalResidues, if_neg hpm]
      exact Finset.mem_image.mpr ⟨ij.2, Finset.mem_univ _,
        ((pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp hpm ij.1 ij.2).mp hij).symm⟩
  · intro a ha b hb hab
    have hea := (pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp hpm a.1 a.2).mp ha
    have heb := (pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp hpm b.1 b.2).mp hb
    exact Prod.ext (hF hab) (hE (hea.symm.trans (hab.trans heb)))
  · intro z hz
    obtain ⟨hzF, hzE⟩ := Finset.mem_inter.mp hz
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hzF
    rw [pinnedCompanionLocalResidues, if_neg hpm] at hzE
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hzE
    exact ⟨(i, j), (pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp hpm i j).mpr
      (hiz.trans hjz.symm), hiz⟩

theorem pinnedLocalMultiplicity_add_edge_card
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p.val ∣ p₀) (hpm : ¬p.val ∣ m)
    (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalMultiplicity h w m p₀ p + (pinnedIndexFourierEdges h m p₀ p).card =
      2 * Fintype.card (PinnedShiftIndex h) := by
  rw [card_pinnedIndexFourierEdges_eq_intersection h p.property hKw hwp hpp₀ hpm hnum,
    pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_union h p hKw hwp hpp₀ hnum,
    Finset.card_union_add_card_inter, card_pinnedFirstLocalResidues h p.property hKw hwp hpp₀,
    card_pinnedCompanionLocalResidues h p.property hKw hwp hpm hnum]
  omega

theorem pinnedLocalMultiplicity_add_FourierExceptionalCount
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalMultiplicity h w m p₀ p +
      doubledFourierExceptionalCount Finset.univ (pinnedIndexFourierEdges h m p₀ p)
        (affineFourierCompanionSwitch m p) = 2 * Fintype.card (PinnedShiftIndex h) := by
  by_cases hpm : p.val ∣ m
  · have hmult : pinnedLocalMultiplicity h w m p₀ p = Fintype.card (PinnedShiftIndex h) := by
      rw [pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_union h p hKw hwp hpp₀ hnum,
        pinnedCompanionLocalResidues, if_pos hpm, Finset.union_empty]
      exact card_pinnedFirstLocalResidues h p.property hKw hwp hpp₀
    rw [hmult, pinnedIndexFourierEdges_eq_empty_of_dvd_m h (hKw.trans hwp.le) hpm]
    simp [doubledFourierExceptionalCount, affineFourierCompanionSwitch, hpm, two_mul]
  · simpa [doubledFourierExceptionalCount, affineFourierCompanionSwitch, hpm] using
      pinnedLocalMultiplicity_add_edge_card h p hKw hwp hpp₀ hpm hnum

def pinnedLocalFactor {K : ℕ} (h : Fin K) (w m p₀ : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - (pinnedLocalMultiplicity h w m p₀ p : ℝ) / p) *
    (1 - (1 : ℝ) / p)⁻¹ ^ (2 * Fintype.card (PinnedShiftIndex h))

theorem doubledFourierSingularFactor_eq_pinnedLocalFactor
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    doubledFourierSingularFactor (pinnedIndexFourierEdges h m p₀)
      (affineFourierCompanionSwitch m) p = (pinnedLocalFactor h w m p₀ p : ℂ) := by
  have hcount := pinnedLocalMultiplicity_add_FourierExceptionalCount h p hKw hwp hpp₀ hnum
  have hcast : (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℂ) -
      doubledFourierExceptionalCount Finset.univ (pinnedIndexFourierEdges h m p₀ p)
        (affineFourierCompanionSwitch m p) = pinnedLocalMultiplicity h w m p₀ p := by
    have hc : (pinnedLocalMultiplicity h w m p₀ p : ℂ) +
        doubledFourierExceptionalCount Finset.univ (pinnedIndexFourierEdges h m p₀ p)
          (affineFourierCompanionSwitch m p) =
        2 * (Fintype.card (PinnedShiftIndex h) : ℂ) := by exact_mod_cast hcount
    simp only [Fintype.card_sum, Nat.cast_add]
    linear_combination -hc
  unfold doubledFourierSingularFactor
  rw [hcast]
  unfold pinnedLocalFactor
  push_cast
  rw [div_eq_mul_inv, inv_pow]
  simp only [Fintype.card_sum, two_mul]

theorem roughPinnedFourierSingularFactor_eq_pinnedLocalFactor
    {K w m p₀ Y : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w)
    (hwp : w < p) (hpY : p.val ≤ Y) (hpp₀ : ¬p.val ∣ p₀)
    (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    doubledFourierSingularFactor (roughPinnedFourierEdges h w m p₀ Y)
      (truncatedPinnedFourierCompanion m Y) p = (pinnedLocalFactor h w m p₀ p : ℂ) := by
  have heq := doubledFourierSingularFactor_eq_pinnedLocalFactor h p hKw hwp hpp₀ hnum
  simpa only [doubledFourierSingularFactor, roughPinnedFourierEdges, if_pos hwp,
    truncatedPinnedFourierEdges, truncatedPinnedFourierCompanion, if_pos hpY] using heq

end

end Erdos4b
