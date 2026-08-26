import ErdosProblems.Erdos520.CaichAlignedScheduledCleanup
import ErdosProblems.Erdos520.CaichScheduledResidualMoments

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Markov and finite-test tails for the literal aligned residuals

The only inputs left by this file are scalar summability statements for the
displayed deterministic smooth-number integrals.  All measurability,
integrability, expectation, Markov, and finite-union steps are proved here.
-/

noncomputable def selectedAlignedHarperL12FirstMoment
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) : ℝ := by
  classical
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  exact caichScheduledL12FirstMoment
    (caichWSmoothingParameterNatCast q x) x (Finset.range N)
    endpoint (fun j ↦ endpoint (j + 1))
    (selectedAlignedHarperNear hK hHarper m ell i)

noncomputable def selectedAlignedHarperL2FirstMoment
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) : ℝ := by
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  exact caichScheduledL2FirstMoment
    (caichWSmoothingParameterNatCast q x) x (Finset.range N)
    endpoint (fun j ↦ endpoint (j + 1))

theorem integrable_selectedAlignedHarperL12
    {K m q ell i : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hi : i ∈ alignedRootExpTests K m ell) :
    Integrable (selectedAlignedHarperL12 hK hHarper q m ell i) μ := by
  classical
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  have hX : 0 < caichWSmoothingParameterNatCast q x :=
    caichWSmoothingParameterNatCast_pos q x
  have hx : 0 < x := by
    dsimp only [x]
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  unfold selectedAlignedHarperL12
  exact integrable_caichScheduledL12 hX hx (Finset.range N)
    endpoint (fun j ↦ endpoint (j + 1))
    (selectedAlignedHarperNear hK hHarper m ell i)
    (fun j hj ↦ by
      change 1 ≤ selectedAlignedHarperEndpoint hK hHarper ell j
      unfold selectedAlignedHarperEndpoint
      exact (by norm_num : 1 ≤ 2).trans
        (two_le_alignedThinEndpoint K _ j))
    (fun j hj ↦ by
      dsimp only [endpoint, selectedAlignedHarperEndpoint]
      exact alignedThinEndpoint_mono K _ (Nat.le_succ j))

theorem integral_selectedAlignedHarperL12_le_firstMoment
    {K m q ell i : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hi : i ∈ alignedRootExpTests K m ell) :
    (∫ omega, selectedAlignedHarperL12 hK hHarper q m ell i omega ∂μ) ≤
      selectedAlignedHarperL12FirstMoment hK hHarper q m ell i := by
  classical
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  have hX : 0 < caichWSmoothingParameterNatCast q x :=
    caichWSmoothingParameterNatCast_pos q x
  have hx : 0 < x := by
    dsimp only [x]
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  unfold selectedAlignedHarperL12 selectedAlignedHarperL12FirstMoment
  exact integral_caichScheduledL12_le_firstMoment hX hx
    (Finset.range N) endpoint (fun j ↦ endpoint (j + 1))
    (selectedAlignedHarperNear hK hHarper m ell i)
    (fun j hj ↦ by
      change 1 ≤ selectedAlignedHarperEndpoint hK hHarper ell j
      unfold selectedAlignedHarperEndpoint
      exact (by norm_num : 1 ≤ 2).trans
        (two_le_alignedThinEndpoint K _ j))
    (fun j hj ↦ by
      dsimp only [endpoint, selectedAlignedHarperEndpoint]
      exact alignedThinEndpoint_mono K _ (Nat.le_succ j))

theorem integrable_selectedAlignedHarperL2
    {K m q ell i : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hi : i ∈ alignedRootExpTests K m ell) :
    Integrable (selectedAlignedHarperL2 hK hHarper q m ell i) μ := by
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  have hX : 0 < caichWSmoothingParameterNatCast q x :=
    caichWSmoothingParameterNatCast_pos q x
  have hx : 0 < x := by
    dsimp only [x]
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  unfold selectedAlignedHarperL2
  exact integrable_caichScheduledL2 hX hx (Finset.range N)
    endpoint (fun j ↦ endpoint (j + 1)) (fun j hj ↦ by
      change 1 ≤ selectedAlignedHarperEndpoint hK hHarper ell (j + 1)
      unfold selectedAlignedHarperEndpoint
      exact (by norm_num : 1 ≤ 2).trans
        (two_le_alignedThinEndpoint K _ (j + 1)))

theorem integral_selectedAlignedHarperL2_le_firstMoment
    {K m q ell i : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hi : i ∈ alignedRootExpTests K m ell) :
    (∫ omega, selectedAlignedHarperL2 hK hHarper q m ell i omega ∂μ) ≤
      selectedAlignedHarperL2FirstMoment hK hHarper q m ell i := by
  let x := alignedRootExpTestPoint m i
  let endpoint := selectedAlignedHarperEndpoint hK hHarper ell
  let N := selectedAlignedHarperBlockCount hK hHarper m ell i
  have hX : 0 < caichWSmoothingParameterNatCast q x :=
    caichWSmoothingParameterNatCast_pos q x
  have hx : 0 < x := by
    dsimp only [x]
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  unfold selectedAlignedHarperL2 selectedAlignedHarperL2FirstMoment
  exact integral_caichScheduledL2_le_firstMoment hX hx
    (Finset.range N) endpoint (fun j ↦ endpoint (j + 1)) (fun j hj ↦ by
      change 1 ≤ selectedAlignedHarperEndpoint hK hHarper ell (j + 1)
      unfold selectedAlignedHarperEndpoint
      exact (by norm_num : 1 ≤ 2).trans
        (two_le_alignedThinEndpoint K _ (j + 1)))

/-! ## Safe all-scale extensions and scalar budgets -/

noncomputable def selectedAlignedLargeSafeThreshold (K ell : ℕ) : ℝ :=
  if ell < 5 then 1 else caichLargeAuxThreshold K ell

theorem selectedAlignedLargeSafeThreshold_pos (K ell : ℕ) :
    0 < selectedAlignedLargeSafeThreshold K ell := by
  unfold selectedAlignedLargeSafeThreshold
  split_ifs with hell
  · norm_num
  · have hellpos : (0 : ℝ) < ell := by
      exact_mod_cast (show 0 < ell by omega)
    unfold caichLargeAuxThreshold caichAuxiliaryPower
    positivity

noncomputable def selectedAlignedHarperSafeL12
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) (omega : Omega) : ℝ :=
  if i ∈ alignedRootExpTests K m ell then
    selectedAlignedHarperL12 hK hHarper q m ell i omega else 0

noncomputable def selectedAlignedHarperSafeL2
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) (omega : Omega) : ℝ :=
  if i ∈ alignedRootExpTests K m ell then
    selectedAlignedHarperL2 hK hHarper q m ell i omega else 0

noncomputable def selectedAlignedHarperSafeL12Moment
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) : ℝ :=
  if i ∈ alignedRootExpTests K m ell then
    selectedAlignedHarperL12FirstMoment hK hHarper q m ell i else 0

noncomputable def selectedAlignedHarperSafeL2Moment
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) : ℝ :=
  if i ∈ alignedRootExpTests K m ell then
    selectedAlignedHarperL2FirstMoment hK hHarper q m ell i else 0

def SelectedAlignedHarperL12ScalarSummability
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) : Prop :=
  Summable (caichAuxiliaryFiniteUnionMomentBudget
    (alignedRootExpTests K m)
    (selectedAlignedHarperSafeL12Moment hK hHarper q m)
    (selectedAlignedLargeSafeThreshold K) 1)

def SelectedAlignedHarperL2ScalarSummability
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) : Prop :=
  Summable (caichAuxiliaryFiniteUnionMomentBudget
    (alignedRootExpTests K m)
    (selectedAlignedHarperSafeL2Moment hK hHarper q m)
    (selectedAlignedLargeSafeThreshold K) 1)

end Problem520
end Erdos
