import ErdosProblems.Erdos520.AlignedClampedBlockControl
import ErdosProblems.Erdos520.AlignedSmoothConcentrationAssembly
import ErdosProblems.Erdos520.CaichConcreteSmoothingReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Harper block control inserted into aligned concentration

The clamped aligned schedule and its almost-sure block maximum are determined
by Harper's initial low-moment statement.  This file selects that concrete
certificate and inserts its block theorem into the unconditional-smooth
concentration endpoint.  The only remaining analytic inputs are then the
quadratic-variation smoothing inequality and its auxiliary remainder bound
for the selected schedule.
-/

/-- A concrete clamped aligned schedule together with the Harper-derived
almost-sure block maximum used by concentration. -/
structure ClampedAlignedHarperBlockCertificate (K : ℕ) where
  schedule : ConcreteThinBlockSchedule
  clamp : ℕ
  blockConstant : ℝ
  five_le_blockConstant : 5 ≤ blockConstant
  five_le_clamp : 5 ≤ clamp
  J_eq : schedule.J = clampedAlignedThinBlockCount K clamp
  y_eq : schedule.y = fun ell j =>
    alignedThinEndpoint K (clampedAlignedScale clamp ell) j
  I_eq : schedule.I = fun ell j =>
    caichNormalizedEnergy (clampedAlignedScale clamp ell) K
      (alignedThinEndpoint K (clampedAlignedScale clamp ell) 0)
      (alignedThinEndpoint K (clampedAlignedScale clamp ell) j)
  blockConstant_pos : 0 < blockConstant
  block_good : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
    blockEnergyMaxGoodAtScale schedule.J schedule.toThinBlockData.U
      blockConstant K ell omega

/-- Enlarging the numerical block constant preserves the pointwise block
maximum estimate.  This lets the literal constant `5` from the five Caich
auxiliaries share the certificate's single downstream constant. -/
theorem blockEnergyMaxGoodAtScale_mono_constant
    {J : ℕ → ℕ} {U : ℕ → ℕ → Omega → ℝ}
    {B B' : ℝ} {K ell : ℕ} {omega : Omega}
    (hBB' : B ≤ B')
    (hgood : blockEnergyMaxGoodAtScale J U B K ell omega) :
    blockEnergyMaxGoodAtScale J U B' K ell omega := by
  unfold blockEnergyMaxGoodAtScale at hgood ⊢
  exact hgood.trans <| div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBB' (Real.sqrt_nonneg _)) (by positivity)

/-- Harper's statement unconditionally produces the complete clamped block
certificate. -/
theorem nonempty_clampedAlignedHarperBlockCertificate
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) :
    Nonempty (ClampedAlignedHarperBlockCertificate K) := by
  obtain ⟨s, S, B, hS, hJ, hy, hI, hB, hblock⟩ :=
    exists_clampedAlignedBlockEnergyMaxGood_of_harper hK hHarper
  exact ⟨{
    schedule := s
    clamp := S
    blockConstant := max B 5
    five_le_blockConstant := le_max_right B 5
    five_le_clamp := hS
    J_eq := hJ
    y_eq := hy
    I_eq := hI
    blockConstant_pos := hB.trans_le (le_max_left B 5)
    block_good := by
      filter_upwards [hblock] with omega homega
      filter_upwards [homega] with ell hell
      exact blockEnergyMaxGoodAtScale_mono_constant
        (le_max_left B 5) hell }⟩

/-- The canonical selected concrete certificate for downstream assembly. -/
noncomputable def selectedClampedAlignedHarperBlockCertificate
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) :
    ClampedAlignedHarperBlockCertificate K :=
  Classical.choice
    (nonempty_clampedAlignedHarperBlockCertificate hK hHarper)

/-- Complete aligned test-point bound after selecting the Harper schedule.

Besides the scalar exponent conditions, the only premises are Harper's
published initial moment, the smoothing inequality, and the auxiliary
remainder estimate.  The block maximum and smooth contribution are supplied
internally. -/
theorem aeTestPointBound_partialSum_of_alignedHarper_smoothing_auxiliary
    {K m : ℕ} (hK : 9 ≤ K) (hm : 0 < m)
    {D η : ℝ} (hD : 0 < D) (hη : 0 < η)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hHarper : HarperRademacherInitialMomentStatement)
    (E : ℕ → ℕ → Omega → ℝ)
    (hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale
        (alignedRootExpTests K m)
        (fun _ell i => alignedRootExpTestPoint m i)
        (fun ell _i => alignedThinEndpoint K
          (clampedAlignedScale
            (selectedClampedAlignedHarperBlockCertificate hK hHarper).clamp
            ell) 0)
        (fun _ell i => alignedRootExpTestPoint m i)
        (selectedClampedAlignedHarperBlockCertificate hK hHarper).schedule.J
        (ConcreteThinBlockSchedule.toThinBlockData
          (selectedClampedAlignedHarperBlockCertificate hK hHarper).schedule).U
        E D ell omega)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m) E
        (selectedClampedAlignedHarperBlockCertificate hK hHarper).blockConstant
        K ell omega) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  let w : ClampedAlignedHarperBlockCertificate K :=
    selectedClampedAlignedHarperBlockCertificate hK hHarper
  exact aeTestPointBound_partialSum_clampedAligned_of_components
    w.clamp w.schedule.J w.schedule.toThinBlockData.U E
    hD w.blockConstant_pos hη (by omega) hm hgap
    hsmoothing w.block_good haux

/-- The explicit smoothing remainder for the selected Harper schedule. -/
noncomputable def selectedAlignedHarperConcreteSmoothingRemainder
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (m : ℕ) (X : ℕ → ℕ → ℝ) : ℕ → ℕ → Omega → ℝ :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  fun ell i omega =>
    caichConcreteSmoothingRemainder (X ell i)
      w.schedule.J w.schedule.toThinBlockData.U ell omega
      (alignedRootExpTestPoint m i)
      (alignedThinEndpoint K (clampedAlignedScale w.clamp ell) 0)
      (alignedRootExpTestPoint m i)

/-- Fully concrete smoothing endpoint for the selected Harper schedule.

The smoothing parameter `X` is arbitrary and point-dependent, subject only
to positivity.  The deterministic smoothing inequality is instantiated
internally.  Thus the sole remaining probabilistic/analytic premise is the
eventual auxiliary bound for the displayed explicit remainder. -/
theorem aeTestPointBound_partialSum_of_alignedHarper_concreteSmoothing
    {K m : ℕ} (hK : 9 ≤ K) (hm : 0 < m)
    {η : ℝ} (hη : 0 < η)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hHarper : HarperRademacherInitialMomentStatement)
    (X : ℕ → ℕ → ℝ)
    (hX : ∀ ell i, i ∈ alignedRootExpTests K m ell → 0 < X ell i)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m)
        (selectedAlignedHarperConcreteSmoothingRemainder
          hK hHarper m X)
        (selectedClampedAlignedHarperBlockCertificate hK hHarper).blockConstant
        K ell omega) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  let w : ClampedAlignedHarperBlockCertificate K :=
    selectedClampedAlignedHarperBlockCertificate hK hHarper
  let E : ℕ → ℕ → Omega → ℝ :=
    selectedAlignedHarperConcreteSmoothingRemainder hK hHarper m X
  have hx : ∀ ell i, i ∈ alignedRootExpTests K m ell →
      0 < alignedRootExpTestPoint m i := by
    intro ell i hi
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  have hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale
        (alignedRootExpTests K m)
        (fun _ell i => alignedRootExpTestPoint m i)
        (fun ell _i =>
          alignedThinEndpoint K (clampedAlignedScale w.clamp ell) 0)
        (fun _ell i => alignedRootExpTestPoint m i)
        w.schedule.J w.schedule.toThinBlockData.U E 2 ell omega := by
    have h := ae_eventually_qvSmoothingGood_caichConcrete
      (alignedRootExpTests K m)
      (fun _ell i => alignedRootExpTestPoint m i)
      (fun ell _i =>
        alignedThinEndpoint K (clampedAlignedScale w.clamp ell) 0)
      (fun _ell i => alignedRootExpTestPoint m i)
      X w.schedule.J w.schedule.toThinBlockData.U hX hx
    simpa only [E, selectedAlignedHarperConcreteSmoothingRemainder, w]
      using! h
  exact aeTestPointBound_partialSum_of_alignedHarper_smoothing_auxiliary
    hK hm (D := 2) (by norm_num) hη hgap hHarper E hsmoothing haux

end Problem520
end Erdos
