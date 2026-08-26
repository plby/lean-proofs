import ErdosProblems.Erdos520.CaichOvershootMainCleanup
import ErdosProblems.Erdos520.AlignedHarperConcentrationAssembly
import ErdosProblems.Erdos520.CaichWoverX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Literal aligned specialization of the scheduled Caich cleanup

This file selects the Harper schedule, scales its energy family by the honest
fixed near-block constant, and uses the least scheduled endpoint above each
root-exponential test point.  The endpoint is not capped: the overshoot
identity in `CaichOvershootMainCleanup` makes the last Harper block literal.
-/

/-! ## The least scheduled endpoint above a test point -/

noncomputable def caichAlignedFirstReachingBlock
    (K L x : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, x ≤ alignedThinEndpoint K L j then Nat.find h else 0

theorem exists_caichAlignedReachingBlock
    {K L x : ℕ} (hL : 0 < L)
    (hx : x ≤ alignedOuterEndpoint K L) :
    ∃ j, x ≤ alignedThinEndpoint K L j := by
  exact ⟨alignedThinBlockCount K L,
    hx.trans (alignedOuterEndpoint_le_finalThinEndpoint hL)⟩

theorem le_caichAlignedFirstReachingBlock_endpoint
    {K L x : ℕ} (hL : 0 < L)
    (hx : x ≤ alignedOuterEndpoint K L) :
    x ≤ alignedThinEndpoint K L (caichAlignedFirstReachingBlock K L x) := by
  classical
  let h := exists_caichAlignedReachingBlock hL hx
  rw [caichAlignedFirstReachingBlock, dif_pos h]
  exact Nat.find_spec h

theorem caichAlignedFirstReachingBlock_le
    {K L x j : ℕ} (hL : 0 < L)
    (hx : x ≤ alignedOuterEndpoint K L)
    (hj : x ≤ alignedThinEndpoint K L j) :
    caichAlignedFirstReachingBlock K L x ≤ j := by
  classical
  let h := exists_caichAlignedReachingBlock hL hx
  rw [caichAlignedFirstReachingBlock, dif_pos h]
  exact Nat.find_min' h hj

theorem caichAlignedFirstReachingBlock_le_blockCount
    {K L x : ℕ} (hL : 0 < L)
    (hx : x ≤ alignedOuterEndpoint K L) :
    caichAlignedFirstReachingBlock K L x ≤ alignedThinBlockCount K L := by
  exact caichAlignedFirstReachingBlock_le hL hx
    (hx.trans (alignedOuterEndpoint_le_finalThinEndpoint hL))

theorem alignedThinEndpoint_lt_of_lt_firstReachingBlock
    {K L x j : ℕ} (hL : 0 < L)
    (hx : x ≤ alignedOuterEndpoint K L)
    (hj : j < caichAlignedFirstReachingBlock K L x) :
    alignedThinEndpoint K L j < x := by
  classical
  let h := exists_caichAlignedReachingBlock hL hx
  rw [caichAlignedFirstReachingBlock, dif_pos h] at hj
  exact Nat.lt_of_not_ge (Nat.find_min h hj)

/-! ## The paper-compatible near-ratio predicate -/

/-- A block is near when the logarithmic ratio from its left endpoint to the
test point is at most `L^(100 K)`. -/
def caichAlignedNearRatio (K L x j : ℕ) : Prop :=
  Real.log (x : ℝ) / Real.log (alignedThinEndpoint K L j : ℝ) ≤
    (L : ℝ) ^ (100 * K)

/-! ## Selected and scaled Harper data -/

noncomputable def selectedScaledAlignedHarperEnergy
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) (D0 : ℝ) :
    ℕ → ℕ → Omega → ℝ :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  caichScaledBlockEnergy D0 w.schedule.toThinBlockData.U

theorem ae_eventually_selectedScaledAlignedHarper_blockGood
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {D0 : ℝ} (hD0 : 0 ≤ D0) :
    let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale w.schedule.J
        (selectedScaledAlignedHarperEnergy hK hHarper D0)
        (D0 * w.blockConstant) K ell omega := by
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  simpa only [selectedScaledAlignedHarperEnergy, w] using!
    (ae_eventually_blockEnergyMaxGoodAtScale_scaled
      (D0 := D0) hD0 w.block_good)

/-! ## Literal aligned residuals -/

noncomputable def selectedAlignedHarperEndpoint
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (ell j : ℕ) : ℕ :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  alignedThinEndpoint K (clampedAlignedScale w.clamp ell) j

noncomputable def selectedAlignedHarperBlockCount
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (m ell i : ℕ) : ℕ :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  caichAlignedFirstReachingBlock K (clampedAlignedScale w.clamp ell)
    (alignedRootExpTestPoint m i)

def selectedAlignedHarperNear
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (m ell i j : ℕ) : Prop :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  caichAlignedNearRatio K (clampedAlignedScale w.clamp ell)
    (alignedRootExpTestPoint m i) j

noncomputable def selectedAlignedHarperL12
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) (omega : Omega) : ℝ := by
  classical
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  exact caichScheduledL12 (caichWSmoothingParameterNatCast q x) omega x
    (Finset.range N) endpoint (fun j ↦ endpoint (j + 1))
    (selectedAlignedHarperNear hK hHarper m ell i)

noncomputable def selectedAlignedHarperL2
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) (omega : Omega) : ℝ := by
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  exact caichScheduledL2 (caichWSmoothingParameterNatCast q x) omega x
    (Finset.range N) endpoint (fun j ↦ endpoint (j + 1))

noncomputable def selectedAlignedCaichSmoothingParameter
    (q m _ell i : ℕ) : ℝ :=
  caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i)

noncomputable def selectedAlignedTestPoint (m _ell i : ℕ) : ℕ :=
  alignedRootExpTestPoint m i

noncomputable def selectedAlignedHarperInitialCutoff
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (ell _i : ℕ) : ℕ :=
  selectedAlignedHarperEndpoint hK hHarper ell 0

def selectedAlignedZeroAuxiliary (_ell _i : ℕ) (_omega : Omega) : ℝ := 0

noncomputable def selectedAlignedHarperNearBlocks
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (m ell i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range
    (selectedAlignedHarperBlockCount hK hHarper m ell i)).filter
      (selectedAlignedHarperNear hK hHarper m ell i)

/-! ## Pointwise and eventual deterministic main cleanup -/

/-- Literal pointwise aligned cleanup, conditional only on the two scalar
prime-geometry facts supplied by the short-window/count calculation. -/
theorem selectedAlignedHarper_pointwise_main_cleanup
    {K m q ell i : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {C D0 : ℝ} (hC : 0 ≤ C) (hD0 : 0 ≤ D0)
    (hclamp :
      (selectedClampedAlignedHarperBlockCertificate hK hHarper).clamp ≤ ell)
    (hi : i ∈ alignedRootExpTests K m ell)
    (hshort : ∀ j ∈ Finset.range
        (selectedAlignedHarperBlockCount hK hHarper m ell i),
      selectedAlignedHarperNear hK hHarper m ell i j → ∀ z ∈
        Ioc
          ((alignedRootExpTestPoint m i : ℝ) /
            (selectedAlignedHarperEndpoint hK hHarper ell (j + 1) : ℝ))
          ((alignedRootExpTestPoint m i : ℝ) /
            (selectedAlignedHarperEndpoint hK hHarper ell j : ℝ)),
        caichShortWindowReciprocalMass
            (caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i))
            (alignedRootExpTestPoint m i)
            (selectedAlignedHarperEndpoint hK hHarper ell j)
            (selectedAlignedHarperEndpoint hK hHarper ell (j + 1)) z ≤
          C / (caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i) *
            Real.log
              (selectedAlignedHarperEndpoint hK hHarper ell (j + 1) : ℝ)))
    (hbudget :
      ((selectedAlignedHarperNearBlocks hK hHarper m ell i).card : ℝ) * C ≤
        D0 * caichAuxiliaryLogFactor ell)
    (omega : Omega) :
    caichUnaccountedSmoothedMain
        (caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i))
        (selectedClampedAlignedHarperBlockCertificate hK hHarper).schedule.J
        (selectedScaledAlignedHarperEnergy hK hHarper D0)
        ell omega (alignedRootExpTestPoint m i)
        (selectedAlignedHarperEndpoint hK hHarper ell 0)
        (alignedRootExpTestPoint m i) ≤
      selectedAlignedHarperL12 hK hHarper q m ell i omega +
        selectedAlignedHarperL2 hK hHarper q m ell i omega := by
  classical
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  let x := alignedRootExpTestPoint m i
  let L := clampedAlignedScale w.clamp ell
  let endpoint : ℕ → ℕ := alignedThinEndpoint K L
  let N := caichAlignedFirstReachingBlock K L x
  let near : ℕ → Prop := caichAlignedNearRatio K L x
  have hell : 5 ≤ ell := w.five_le_clamp.trans hclamp
  have hL : L = ell := by
    dsimp only [L]
    exact clampedAlignedScale_eq_of_ge hclamp
  have hxUpper : x ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    rw [if_neg (by omega : ¬ell < 5)] at hi
    exact (Finset.mem_filter.mp hi).2.2
  have hxpos : 0 < x := by
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  have hX : 0 < caichWSmoothingParameterNatCast q x :=
    caichWSmoothingParameterNatCast_pos q x
  have hNfinal : x ≤ endpoint N := by
    dsimp only [endpoint, N]
    rw [hL]
    exact le_caichAlignedFirstReachingBlock_endpoint (by omega) hxUpper
  have hNcount : N ≤ alignedThinBlockCount K ell := by
    dsimp only [N]
    rw [hL]
    exact caichAlignedFirstReachingBlock_le_blockCount (by omega) hxUpper
  have hstart : endpoint 0 ≤ x := by
    dsimp only [endpoint]
    rw [hL]
    exact (alignedThinInitial_lt_testPoint_of_mem hi).le
  have hJ : ∀ j ∈ Finset.range N, near j → j + 1 ≤ w.schedule.J ell := by
    intro j hj hjNear
    have hjN : j + 1 ≤ N := Nat.lt_iff_add_one_le.mp (Finset.mem_range.mp hj)
    rw [w.J_eq, clampedAlignedThinBlockCount,
      if_neg (by omega : ell ≠ 0)]
    change j + 1 ≤ alignedThinBlockCount K L
    exact hjN.trans (by simpa only [hL] using! hNcount)
  have hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy (endpoint j) (endpoint (j + 1)) omega ≤
        w.schedule.toThinBlockData.U ell (j + 1) omega := by
    intro j hj hjNear
    rw [ConcreteThinBlockSchedule.toThinBlockData_U]
    change realSmoothBlockEnergy (endpoint j) (endpoint (j + 1)) omega ≤
      realSmoothBlockEnergy (w.schedule.y ell ((j + 1) - 1))
        (w.schedule.y ell (j + 1)) omega
    simp only [Nat.add_sub_cancel]
    rw [w.y_eq]
  have hmax : 0 ≤ caichBlockEnergyMax w.schedule.J
      w.schedule.toThinBlockData.U ell omega := by
    apply caichBlockEnergyMax_nonneg_of_family
    intro j hj
    rw [ConcreteThinBlockSchedule.toThinBlockData_U]
    exact w.schedule.realSmoothBlockEnergy_nonneg ell j omega
  have hmain :=
    caichUnaccountedSmoothedMain_le_scaledScheduledL12_add_L2_of_final_ge
      w.schedule.J w.schedule.toThinBlockData.U endpoint N near
      (fun j ↦ j + 1) hX hxpos hC hD0 omega
      (alignedThinEndpoint_mono K L)
      (fun j hj ↦ by
        change 1 ≤ alignedThinEndpoint K L j
        exact (by norm_num : 1 ≤ 2).trans
          (two_le_alignedThinEndpoint K L j))
      hstart hNfinal hJ
      (fun j hj hjNear ↦ two_le_alignedThinEndpoint K L (j + 1))
      hU (by
        simpa only [selectedAlignedHarperBlockCount,
          selectedAlignedHarperNear, selectedAlignedHarperEndpoint,
          w, x, L, N, near, endpoint] using! hshort)
      hmax (by
        simpa only [selectedAlignedHarperNearBlocks,
          selectedAlignedHarperBlockCount,
          selectedAlignedHarperNear, w, x, L, N, near] using! hbudget)
  simpa only [selectedScaledAlignedHarperEnergy,
    selectedAlignedHarperL12, selectedAlignedHarperL2,
    selectedAlignedHarperEndpoint, selectedAlignedHarperBlockCount,
    selectedAlignedHarperNear, w, x, L, endpoint, N, near] using! hmain

/-- The exact effective short-window statement needed at one aligned test
point. -/
def SelectedAlignedHarperShortWindowBound
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) (C : ℝ) (ell i : ℕ) : Prop :=
  ∀ j ∈ Finset.range
      (selectedAlignedHarperBlockCount hK hHarper m ell i),
    selectedAlignedHarperNear hK hHarper m ell i j → ∀ z ∈
      Ioc
        ((alignedRootExpTestPoint m i : ℝ) /
          (selectedAlignedHarperEndpoint hK hHarper ell (j + 1) : ℝ))
        ((alignedRootExpTestPoint m i : ℝ) /
          (selectedAlignedHarperEndpoint hK hHarper ell j : ℝ)),
      caichShortWindowReciprocalMass
          (caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i))
          (alignedRootExpTestPoint m i)
          (selectedAlignedHarperEndpoint hK hHarper ell j)
          (selectedAlignedHarperEndpoint hK hHarper ell (j + 1)) z ≤
        C / (caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i) *
          Real.log
            (selectedAlignedHarperEndpoint hK hHarper ell (j + 1) : ℝ))

/-- Honest scaled near-cardinality budget at one aligned test point. -/
def SelectedAlignedHarperNearBudget
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (m : ℕ) (C D0 : ℝ) (ell i : ℕ) : Prop :=
  ((selectedAlignedHarperNearBlocks hK hHarper m ell i).card : ℝ) * C ≤
    D0 * caichAuxiliaryLogFactor ell

/-- Both deterministic geometry facts, uniformly over the actual finite
test family at one scale. -/
def SelectedAlignedHarperMainGeometryAtScale
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) (C D0 : ℝ) (ell : ℕ) : Prop :=
  ∀ i ∈ alignedRootExpTests K m ell,
    SelectedAlignedHarperShortWindowBound hK hHarper q m C ell i ∧
      SelectedAlignedHarperNearBudget hK hHarper m C D0 ell i

/-- The selected literal `L12/L2` cleanup in exactly the deterministic
predicate consumed by `CaichConcreteAuxiliaryAssembly`; both lambda terms
are zero. -/
theorem selectedAlignedHarper_mainDominatedAtScale
    {K m q ell : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {C D0 : ℝ} (hC : 0 ≤ C) (hD0 : 0 ≤ D0)
    (hclamp :
      (selectedClampedAlignedHarperBlockCertificate hK hHarper).clamp ≤ ell)
    (hgeometry : SelectedAlignedHarperMainGeometryAtScale
      hK hHarper q m C D0 ell)
    (omega : Omega) :
    caichUnaccountedMainDominatedAtScale
      (alignedRootExpTests K m)
      (selectedAlignedTestPoint m)
      (selectedAlignedHarperInitialCutoff hK hHarper)
      (selectedAlignedTestPoint m)
      (selectedAlignedCaichSmoothingParameter q m)
      (selectedClampedAlignedHarperBlockCertificate hK hHarper).schedule.J
      (selectedScaledAlignedHarperEnergy hK hHarper D0)
      selectedAlignedZeroAuxiliary selectedAlignedZeroAuxiliary
      (selectedAlignedHarperL12 hK hHarper q m)
      (selectedAlignedHarperL2 hK hHarper q m)
      ell omega := by
  intro i hi
  have hpoint := selectedAlignedHarper_pointwise_main_cleanup
    hK hHarper hC hD0 hclamp hi
    (hgeometry i hi).1 (hgeometry i hi).2 omega
  simpa only [selectedAlignedTestPoint,
    selectedAlignedHarperInitialCutoff,
    selectedAlignedCaichSmoothingParameter,
    selectedAlignedZeroAuxiliary, zero_add, mul_zero] using! hpoint

/-- Eventual deterministic main cleanup.  Once the aligned scalar geometry
is proved, this removes the `hmain` premise without any random exceptional
set. -/
theorem ae_eventually_selectedAlignedHarper_mainDominatedAtScale
    {K m q : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {C D0 : ℝ} (hC : 0 ≤ C) (hD0 : 0 ≤ D0)
    (hgeometry : ∀ᶠ ell : ℕ in atTop,
      SelectedAlignedHarperMainGeometryAtScale
        hK hHarper q m C D0 ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      caichUnaccountedMainDominatedAtScale
        (alignedRootExpTests K m)
        (selectedAlignedTestPoint m)
        (selectedAlignedHarperInitialCutoff hK hHarper)
        (selectedAlignedTestPoint m)
        (selectedAlignedCaichSmoothingParameter q m)
        (selectedClampedAlignedHarperBlockCertificate hK hHarper).schedule.J
        (selectedScaledAlignedHarperEnergy hK hHarper D0)
        selectedAlignedZeroAuxiliary selectedAlignedZeroAuxiliary
        (selectedAlignedHarperL12 hK hHarper q m)
        (selectedAlignedHarperL2 hK hHarper q m) ell omega := by
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  filter_upwards with omega
  filter_upwards [hgeometry, eventually_ge_atTop w.clamp]
    with ell hgeom hclamp
  exact selectedAlignedHarper_mainDominatedAtScale
    hK hHarper hC hD0 hclamp hgeom omega

end Problem520
end Erdos
