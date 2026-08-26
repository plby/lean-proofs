import ErdosProblems.Erdos1002.PrimitiveShotL2
import ErdosProblems.Erdos1002.ResonanceCellMeasure
import ErdosProblems.Erdos1002.PVPeriodization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite cell expansion of a primitive shot

For `p ≥ 2`, every primitive nearest-cell shot on `(0,1)` is exactly the
sum over reduced residues of one half-open affine cell.  The half-open
interval is the one dictated by the manuscript's tie convention.  This is
the finite pointwise identity needed before any Fourier integration or
principal-value passage.
-/

open Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The reduced-residue nearest-cell expansion for one denominator. -/
def nearestPrimitiveCellExpansion (N p : ℕ) (alpha : ℝ) : ℂ :=
  ∑ q ∈ reducedResidues p,
    if (p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
      periodizationCell N p (q : ℤ) alpha
    else 0

private theorem primitiveShot_eq_periodizationCell_of_numerator
    {N p : ℕ} {alpha : ℝ} {q : ℤ}
    (hp : 0 < p) (hprim : IsPrimitiveResonance p alpha)
    (hq : resonanceNumerator p alpha = q) :
    (primitiveShot N p alpha : ℂ) =
      periodizationCell N p q alpha := by
  rw [primitiveShot_of_primitive N p alpha hprim]
  have hdelta :
      (p : ℝ) * alpha - (q : ℝ) = resonanceDelta p alpha := by
    unfold resonanceDelta
    rw [hq]
  unfold periodizationCell
  rw [hdelta]
  by_cases hzero : resonanceDelta p alpha = 0
  · simp [hzero, transformKernel, bernoulliMark]
  · rw [transformKernel, if_neg hzero]
    push_cast
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp [hpR, hzero]

/-- Exact cell expansion, with every endpoint convention visible. -/
theorem primitiveShot_eq_nearestPrimitiveCellExpansion
    {N p : ℕ} (hp : 2 ≤ p) {alpha : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    (primitiveShot N p alpha : ℂ) =
      nearestPrimitiveCellExpansion N p alpha := by
  classical
  by_cases hprim : IsPrimitiveResonance p alpha
  · let q : ℕ := (resonanceNumerator p alpha).natAbs
    have hqmem : q ∈ reducedResidues p :=
      resonanceNumerator_nat_mem_reducedResidues hp halpha hprim
    have hqnonneg : 0 ≤ resonanceNumerator p alpha :=
      (resonanceNumerator_bounds_of_mem_unitInterval p halpha).1
    have hqcast : (q : ℤ) = resonanceNumerator p alpha := by
      dsimp [q]
      rw [Int.natCast_natAbs, abs_of_nonneg hqnonneg]
    have hcell :
        (p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
      rw [show (q : ℝ) = (resonanceNumerator p alpha : ℝ) by
        exact_mod_cast hqcast]
      exact resonanceDelta_mem p alpha
    symm
    unfold nearestPrimitiveCellExpansion
    rw [Finset.sum_eq_single q]
    · rw [if_pos hcell]
      exact (primitiveShot_eq_periodizationCell_of_numerator
        (by omega) hprim hqcast.symm).symm
    · intro b hb hne
      have hnotcell :
          ¬ ((p : ℝ) * alpha - (b : ℝ) ∈
            Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
        intro hbcell
        have hnum : resonanceNumerator p alpha = (b : ℤ) :=
          resonanceNumerator_eq_of_delta_mem hbcell
        apply hne
        exact_mod_cast (hqcast.trans hnum).symm
      rw [if_neg hnotcell]
    · intro hqnot
      exact (hqnot hqmem).elim
  · have hzero : primitiveShot N p alpha = 0 :=
      primitiveShot_of_not_primitive N p alpha hprim
    rw [hzero]
    symm
    unfold nearestPrimitiveCellExpansion
    apply Finset.sum_eq_zero
    intro q hqmem
    have hnotcell :
        ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
      intro hcell
      apply hprim
      unfold IsPrimitiveResonance
      have hnum : resonanceNumerator p alpha = (q : ℤ) :=
        resonanceNumerator_eq_of_delta_mem hcell
      rw [hnum]
      have hqcop : Nat.Coprime q p := by
        rw [reducedResidues, Finset.mem_filter] at hqmem
        exact hqmem.2
      simpa using! hqcop
    rw [if_neg hnotcell]

end

end Erdos1002
