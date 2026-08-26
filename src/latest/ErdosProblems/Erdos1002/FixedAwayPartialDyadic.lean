import ErdosProblems.Erdos1002.FixedAwayCarrierAggregation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Partial terminal dyadic blocks in the fixed-away range

The natural cutoff `p ≤ N` need not end at a power of two.  This file
proves that an arbitrary subset of one dyadic denominator block obeys the
same one-block energy bound.  Thus the final partial block is not silently
replaced by a full block, an operation that would be invalid in `L²` because
of cancellation.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

def fixedAwayShiftedPartialDyadicBlock
    (P : Finset ℕ) (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock P
    (fixedAwayShiftedProfile t δ N ell) n

theorem summable_fixedAwayShiftedPartialDyadicBlock_norm_sq
    {P : Finset ℕ} {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hP : P ⊆ fixedAwayDyadicDenominators Q) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedPartialDyadicBlock P t δ N ell n‖ ^ 2 := by
  unfold fixedAwayShiftedPartialDyadicBlock
  apply summable_fixedAwayRamanujanProfileBlock_norm_sq
  intro p hp p' hp'
  have hpFull := hP hp
  have hp'Full := hP hp'
  have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hpFull).1
  have hp'Pos : 0 < p' := hQ.trans (Finset.mem_Ioc.mp hp'Full).1
  exact summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    (N := N) (ell := ell) hδ hδt hpPos hp'Pos

private theorem sum_partial_diagonal_le_full
    {P : Finset ℕ} {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hP : P ⊆ fixedAwayDyadicDenominators Q) :
    (∑ p ∈ P,
      ‖fixedAwayProfilePairTsum
        (fixedAwayShiftedProfile t δ N ell) p p‖) ≤
      2 * fixedAwayShiftedDiagonalConstant t δ := by
  calc
    (∑ p ∈ P,
      ‖fixedAwayProfilePairTsum
        (fixedAwayShiftedProfile t δ N ell) p p‖) ≤
        ∑ p ∈ fixedAwayDyadicDenominators Q,
          ‖fixedAwayProfilePairTsum
            (fixedAwayShiftedProfile t δ N ell) p p‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hP
      intro p _hpFull _hpNot
      exact norm_nonneg _
    _ ≤ 2 * fixedAwayShiftedDiagonalConstant t δ :=
      sum_norm_fixedAwayProfilePairTsum_shifted_diagonal_le
        hδ hδt hQ

private theorem erase_subset_full_erase
    {P S : Finset ℕ} (hP : P ⊆ S) (p : ℕ) :
    P.erase p ⊆ S.erase p := by
  intro q hq
  have hqParts := Finset.mem_erase.mp hq
  exact Finset.mem_erase.mpr ⟨hqParts.1, hP hqParts.2⟩

private theorem sum_partial_offDiagonal_le_full
    {P : Finset ℕ} {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hP : P ⊆ fixedAwayDyadicDenominators Q) :
    (∑ p ∈ P, ∑ p' ∈ P.erase p,
      ‖fixedAwayProfilePairTsum
        (fixedAwayShiftedProfile t δ N ell) p p'‖) ≤
      ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
          ‖fixedAwayProfilePairTsum
            (fixedAwayShiftedProfile t δ N ell) p p'‖ := by
  calc
    (∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum
          (fixedAwayShiftedProfile t δ N ell) p p'‖) ≤
        ∑ p ∈ P,
          ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
            ‖fixedAwayProfilePairTsum
              (fixedAwayShiftedProfile t δ N ell) p p'‖ := by
      gcongr with p hp
    _ ≤ ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
          ‖fixedAwayProfilePairTsum
            (fixedAwayShiftedProfile t δ N ell) p p'‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hP
      intro p _hpFull _hpNot
      exact Finset.sum_nonneg fun p' _hp' ↦ norm_nonneg _

/-- Arbitrary subsets of `(Q,2Q]` have the same explicit one-block bound
as the complete block. -/
theorem tsum_fixedAwayShiftedPartialDyadicBlock_norm_sq_le
    {P : Finset ℕ} {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hP : P ⊆ fixedAwayDyadicDenominators Q)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedPartialDyadicBlock P t δ N ell n‖ ^ 2) ≤
      fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let R := fixedAwayShiftedProfile t δ N ell
  let D : ℂ := ∑ p ∈ P, fixedAwayProfilePairTsum R p p
  let O : ℂ := ∑ p ∈ P, ∑ p' ∈ P.erase p,
    fixedAwayProfilePairTsum R p p'
  let E : ℝ := ∑' n : ℤ,
    ‖fixedAwayShiftedPartialDyadicBlock P t δ N ell n‖ ^ 2
  have hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦
        hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair R p p') p p' n := by
    intro p hp p' hp'
    have hpFull := hP hp
    have hp'Full := hP hp'
    have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hpFull).1
    have hp'Pos : 0 < p' := hQ.trans (Finset.mem_Ioc.mp hp'Full).1
    simpa only [R] using!
      (summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
        (N := N) (ell := ell) hδ hδt hpPos hp'Pos)
  have hparseval :=
    tsum_fixedAwayRamanujanProfileBlock_norm_sq_diagonal_offDiagonal
      P R hpair
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact tsum_nonneg fun n ↦ sq_nonneg _
  have hDnorm : ‖D‖ ≤
      ∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖ := by
    dsimp only [D]
    exact norm_sum_le P fun p ↦ fixedAwayProfilePairTsum R p p
  have hOnorm : ‖O‖ ≤
      ∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖ := by
    dsimp only [O]
    calc
      ‖∑ p ∈ P, ∑ p' ∈ P.erase p,
          fixedAwayProfilePairTsum R p p'‖ ≤
          ∑ p ∈ P,
            ‖∑ p' ∈ P.erase p,
              fixedAwayProfilePairTsum R p p'‖ :=
        norm_sum_le P fun p ↦
          ∑ p' ∈ P.erase p, fixedAwayProfilePairTsum R p p'
      _ ≤ ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ := by
        gcongr with p hp
        exact norm_sum_le (P.erase p) fun p' ↦
          fixedAwayProfilePairTsum R p p'
  have hDbound :
      (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) ≤
        2 * fixedAwayShiftedDiagonalConstant t δ := by
    simpa only [R] using!
      (sum_partial_diagonal_le_full hδ hδt hQ hP)
  have hObound :
      (∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖) ≤
        32 * fixedAwayHermitianRapidBVConstant t δ J := by
    calc
      (∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖) ≤
          ∑ p ∈ fixedAwayDyadicDenominators Q,
            ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
              ‖fixedAwayProfilePairTsum R p p'‖ := by
        simpa only [R] using! sum_partial_offDiagonal_le_full
          (t := t) (δ := δ) (N := N) (Q := Q) (ell := ell) hP
      _ ≤ 32 * fixedAwayHermitianRapidBVConstant t δ J := by
        simpa only [R] using!
          (sum_norm_fixedAwayProfilePairTsum_shifted_offDiagonal_le
            (N := N) (ell := ell) hδ hδt hQ hJ)
  change E ≤ fixedAwayShiftedDyadicEnergyConstant t δ J
  calc
    E = ‖((E : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hE]
    _ = ‖D + O‖ := by
      congr 1
    _ ≤ ‖D‖ + ‖O‖ := norm_add_le D O
    _ ≤ (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) +
        ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ :=
      add_le_add hDnorm hOnorm
    _ ≤ 2 * fixedAwayShiftedDiagonalConstant t δ +
        32 * fixedAwayHermitianRapidBVConstant t δ J :=
      add_le_add hDbound hObound
    _ = fixedAwayShiftedDyadicEnergyConstant t δ J := rfl

theorem tsum_fixedAwayShiftedPartialDyadicBlock_norm_sq_le_uniform
    {P : Finset ℕ} {t δ T : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hQ : 0 < Q) (hP : P ⊆ fixedAwayDyadicDenominators Q)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedPartialDyadicBlock P t δ N ell n‖ ^ 2) ≤
      fixedAwayShiftedDyadicEnergyUniformConstant T δ J := by
  exact (tsum_fixedAwayShiftedPartialDyadicBlock_norm_sq_le
    hδ hδt hQ hP hJ).trans
      (fixedAwayShiftedDyadicEnergyConstant_le_uniform
        hδ hδt.le htT J)

/-- The actual terminal denominator set `(Q,N]`, under `Q < N ≤ 2Q`,
is a valid partial dyadic block. -/
theorem Ioc_subset_fixedAwayDyadicDenominators
    {Q N : ℕ} (hN : N ≤ 2 * Q) :
    Finset.Ioc Q N ⊆ fixedAwayDyadicDenominators Q := by
  intro p hp
  exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hp).1,
    (Finset.mem_Ioc.mp hp).2.trans hN⟩

end

end Erdos1002
