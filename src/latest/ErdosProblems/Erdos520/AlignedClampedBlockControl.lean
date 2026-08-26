import ErdosProblems.Erdos520.AlignedBlockControl
import ErdosProblems.Erdos520.ConcreteClampedBlockMaximum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# The repaired aligned block maximum on the clamped schedule

This is the no-shift counterpart of `exists_alignedBlockEnergyMaxGood_of_harper`.
The finite analytic cutoff is absorbed by `max S ell`, which equals the outer
scale `ell` eventually.  Hence the block schedule, test families, and final
energy estimate all use the same scale index.
-/

/-- Complete aligned maximal-block theorem with eventual literal agreement
between the analytic and outer scales. -/
theorem exists_clampedAlignedBlockEnergyMaxGood_of_harper
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, ∃ B : ℝ,
      5 ≤ S ∧
      s.J = clampedAlignedThinBlockCount K S ∧
      s.y = (fun ell j =>
        alignedThinEndpoint K (clampedAlignedScale S ell) j) ∧
      s.I = (fun ell j =>
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (alignedThinEndpoint K (clampedAlignedScale S ell) 0)
          (alignedThinEndpoint K (clampedAlignedScale S ell) j)) ∧
      0 < B ∧
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        blockEnergyMaxGoodAtScale s.J s.toThinBlockData.U B K ell omega := by
  obtain ⟨C, hC, Y, hY, hHarperBound⟩ := hHarper
  obtain ⟨s, S, hS, hJ, hy, hI⟩ :=
    exists_clampedAlignedIntegerConcreteThinBlockSchedule K (by omega)
  let C' : ℝ := alignedHarperMomentConstant C K
  have hC' : 0 ≤ C' := alignedHarperMomentConstant_nonneg hC.le K
  have hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (s.y ell 0) (s.y ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget
          (clampedAlignedScale S ell) K C' := by
    filter_upwards [eventually_ge_atTop Y] with ell hellY
    let L : ℕ := clampedAlignedScale S ell
    have hL5 : 5 ≤ L :=
      hS.trans (le_clampedAlignedScale_left S ell)
    have hYendpoint : Y ≤ alignedThinEndpoint K L 0 := by
      calc
        Y ≤ ell := hellY
        _ ≤ L := le_clampedAlignedScale_right S ell
        _ ≤ alignedThinEndpoint K L 0 :=
          scale_le_alignedThinEndpoint (by omega) (show 4 ≤ L by omega)
    have hm := integral_alignedThinInitialEnergy_twoThird_le_of_harperBound
      hC.le hHarperBound (by omega) hL5 hYendpoint
    simpa only [C', L, hy] using! hm
  have hJpoly : ∀ ell,
      (s.J ell : ℝ) ≤
        ((S ^ (K + 1) : ℕ) : ℝ) * (ell : ℝ) ^ (K + 1) := by
    intro ell
    rw [hJ]
    exact clampedAlignedThinBlockCount_cast_le_all (by omega) ell
  have hIpoint : ∀ ell j,
      s.I ell j = caichNormalizedEnergy (clampedAlignedScale S ell) K
        (s.y ell 0) (s.y ell j) := by
    intro ell j
    rw [hI, hy]
  obtain ⟨B, hB, hmax⟩ :=
    exists_ae_eventually_concreteClampedBlockEnergyMax_le
      s (S := S) (K := K) (Kblocks := K + 1)
        (D := ((S ^ (K + 1) : ℕ) : ℝ))
        (C := C') (by omega) hC' hJpoly hIpoint hmoment
  refine ⟨s, S, B, hS, hJ, hy, hI, hB, ?_⟩
  filter_upwards [hmax] with omega homega
  filter_upwards [homega, eventually_clampedAlignedScale_eq S]
    with ell hell hscale
  unfold blockEnergyMaxGoodAtScale
  calc
    caichBlockEnergyMax s.J s.toThinBlockData.U ell omega ≤
        B * caichMaximalEnergyThreshold
          (clampedAlignedScale S ell) K
          (caichSmallEnergyT1 (clampedAlignedScale S ell)) := hell
    _ = B * caichMaximalEnergyThreshold ell K
          (caichSmallEnergyT1 ell) := by rw [hscale]
    _ = B * alignedCaichBlockLevel K ell := by
      rw [caichMaximalEnergyThreshold_smallEnergyT1]
      rfl
    _ = B * Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2) := by
      unfold alignedCaichBlockLevel
      ring

end Problem520
end Erdos
