/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZHighSpatialTransitionFactor

/-!
# The spatial future factor on every proper HLOZ mesh cell

The high-mesh future factor uses the fixed radius `exp (m^κ₂) / 3`.  On a
low mesh cell `a`, Proposition 4.7 instead uses the lower edge of that cell,
namely `exp (m^(meshExponent (a - 1))) / 3`.  The first cell has no
predecessor; its source-correct normalization is the origin boundary, whose
escape-before-return cost is one.

This file proves only the deterministic future containment.  It does not
assume or state a transition-probability inequality.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZMeshSpatialTransitionFactor

open BoundaryVisitRegeneration HLOZGapStoppedCandidate
open HLOZHighSpatialTransitionFactor HLOZPathEvents
open HLOZSourceCorrectFutureTransition TerminalExcursionPathwise

noncomputable section

/-- The natural boundary radius at the lower edge of a positive mesh cell.
The zero cell is handled by the origin boundary below. -/
def meshLowerSpatialRadius (m : ℕ) (a : GapScale) : ℕ :=
  if a.1 = 0 then 0 else Nat.ceil (meshRadius m (a.1 - 1) / 3)

@[simp] lemma meshLowerSpatialRadius_of_zero
    (m : ℕ) (a : GapScale) (ha : a.1 = 0) :
    meshLowerSpatialRadius m a = 0 := by
  simp [meshLowerSpatialRadius, ha]

lemma meshLowerSpatialRadius_of_pos
    (m : ℕ) (a : GapScale) (ha : 0 < a.1) :
    meshLowerSpatialRadius m a =
      Nat.ceil (meshRadius m (a.1 - 1) / 3) := by
  simp [meshLowerSpatialRadius, ha.ne']

/-- The future boundary for a mesh cell.  At the first cell this is `{0}`:
the complement of return-before-boundary is the whole fresh-walk space and
therefore contributes the intended cost one. -/
def meshSpatialBoundary (m : ℕ) (a : GapScale) : Set Point :=
  if a.1 = 0 then {0}
  else ThickPoint.discBoundary 0 (meshLowerSpatialRadius m a : ℝ)

@[simp] lemma meshSpatialBoundary_of_zero
    (m : ℕ) (a : GapScale) (ha : a.1 = 0) :
    meshSpatialBoundary m a = {0} := by
  simp [meshSpatialBoundary, ha]

lemma meshSpatialBoundary_of_pos
    (m : ℕ) (a : GapScale) (ha : 0 < a.1) :
    meshSpatialBoundary m a =
      ThickPoint.discBoundary 0 (meshLowerSpatialRadius m a : ℝ) := by
  simp [meshSpatialBoundary, ha.ne']

/-- Minimality of `gapScaleOf` supplies the strict lower radial edge of every
positive proper mesh cell. -/
theorem meshRadius_pred_lt_latticeDistance_of_gapScaleOf_eq
    {m : ℕ} {x y : Point} {a : GapScale}
    (ha : a ∈ properGapMesh) (hapos : 0 < a.1)
    (hscale : gapScaleOf m x y = a) :
    meshRadius m (a.1 - 1) < latticeDistance x y := by
  have hproper : HasProperGapScale m x y := by
    by_contra hnot
    have hover := (gapScaleOf_eq_overflow_iff m x y).2 hnot
    have hane : a ≠ overflowScale := by
      simpa only [properGapMesh, Finset.mem_erase, Finset.mem_univ,
        and_true] using ha
    exact hane (hscale.symm.trans hover)
  have hvalue : Nat.find hproper = a.1 := by
    unfold gapScaleOf at hscale
    rw [dif_pos hproper] at hscale
    exact congrArg Fin.val hscale
  have hpredLt : a.1 - 1 < Nat.find hproper := by omega
  have hpredSteps : a.1 - 1 < meshSteps := by
    have hane : a ≠ overflowScale := by
      simpa only [properGapMesh, Finset.mem_erase, Finset.mem_univ,
        and_true] using ha
    have haBound : a.1 < meshSteps := by
      have halt : a.1 < meshSteps + 1 := a.2
      by_contra hnot
      have hval : a.1 = meshSteps := by omega
      apply hane
      apply Fin.ext
      simpa only [overflowScale] using hval
    omega
  have hnot := Nat.find_min hproper hpredLt
  by_contra hle
  apply hnot
  exact ⟨hpredSteps, le_of_not_gt hle⟩

lemma meshLowerSpatialRadius_pos
    {m : ℕ} {a : GapScale} (ha : 0 < a.1) :
    0 < meshLowerSpatialRadius m a := by
  rw [meshLowerSpatialRadius_of_pos m a ha]
  exact Nat.ceil_pos.mpr (by
    unfold meshRadius
    positivity)

/-- The ceiling in the natural lower-edge radius still remains strictly
inside the lower edge of the mesh cell. -/
lemma meshLowerSpatialRadius_cast_lt_meshRadius
    {m : ℕ} {a : GapScale} (hm : 1 ≤ m) (ha : 0 < a.1) :
    (meshLowerSpatialRadius m a : ℝ) < meshRadius m (a.1 - 1) := by
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ meshExponent (a.1 - 1) := by
    apply Real.one_le_rpow
    · exact_mod_cast hm
    · unfold meshExponent ScreeningInstantiation.meshDelta
      positivity
  have hexp : Real.exp 1 ≤ meshRadius m (a.1 - 1) := by
    unfold meshRadius
    exact Real.exp_le_exp.mpr hpow
  have hthree : (3 : ℝ) / 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h ⊢
    linarith
  have hlarge : (3 : ℝ) / 2 < meshRadius m (a.1 - 1) :=
    hthree.trans_le hexp
  rw [meshLowerSpatialRadius_of_pos m a ha]
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ meshRadius m (a.1 - 1) / 3 by
      unfold meshRadius
      positivity)
  exact lt_of_lt_of_le hceil (by linarith)

/-- Starting at a threshold-creation clock, the fresh translated walk must
hit the lower-edge boundary of its proper mesh cell before any positive
return to the old favorite.  The zero cell is normalized by the origin
boundary; positive cells use the literal radial boundary.

This is the deterministic future half of the low-scale factor in HLOZ
Proposition 4.7. -/
theorem postStoppingSteps_not_positiveReturnBeforeBoundary_of_creation
    {omega : StepPath} {m rank nOld nNew : ℕ} {a : GapScale}
    (hm : 1 ≤ m) (hrank : 0 < rank)
    (hold : ThresholdCreation (trajectory omega) m rank nOld)
    (hnew : ThresholdCreation (trajectory omega) m (rank + 1) nNew)
    (hnext : thresholdCount (trajectory omega) nNew (m + 1) = 0)
    (ha : a ∈ properGapMesh)
    (hscale : gapScaleOf m (trajectory omega nOld)
      (trajectory omega nNew) = a) :
    postStoppingSteps (fun _ : StepPath => nOld) omega ∉
      positiveReturnBeforeBoundary (meshSpatialBoundary m a) := by
  classical
  let tail := postStoppingSteps (fun _ : StepPath => nOld) omega
  by_cases hazero : a.1 = 0
  · rw [meshSpatialBoundary_of_zero m a hazero]
    intro hreturn
    obtain ⟨r, hr, havoidBoundary⟩ := Set.mem_iUnion.mp hreturn
    have hrspec := TerminalSequentialVisitLaw.firstPositiveReturnTime_spec hr
    apply havoidBoundary 0 hrspec.1
    simp [postStoppingSteps]
  · have hapos : 0 < a.1 := Nat.pos_of_ne_zero hazero
    rw [meshSpatialBoundary_of_pos m a hapos]
    let d := nNew - nOld
    have hOldNew : nOld < nNew :=
      creation_time_lt hrank (by omega) (by omega) hold hnew
    have hadd : nOld + d = nNew := Nat.add_sub_of_le hOldNew.le
    have htailZero : trajectory tail 0 = 0 := by
      simp [tail, postStoppingSteps]
    have htailEnd : trajectory tail d =
        trajectory omega nNew - trajectory omega nOld := by
      dsimp only [tail, postStoppingSteps]
      rw [← trajectory_add_sub_trajectory, hadd]
    have hdist := meshRadius_pred_lt_latticeDistance_of_gapScaleOf_eq
      ha hapos hscale
    have hout : trajectory tail d ∉
        ThickPoint.disc 0 (meshLowerSpatialRadius m a : ℝ) := by
      intro hmem
      change latticeDistance 0 (trajectory tail d) ≤
        (meshLowerSpatialRadius m a : ℝ) at hmem
      have hradius : latticeDistance 0 (trajectory tail d) =
          latticeDistance (trajectory omega nOld)
            (trajectory omega nNew) := by
        rw [htailEnd]
        unfold latticeDistance
        congr 1
        simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub]
        push_cast
        ring
      rw [hradius] at hmem
      exact (not_lt_of_ge hmem)
        ((meshLowerSpatialRadius_cast_lt_meshRadius hm hapos).trans hdist)
    have hin : trajectory tail 0 ∈
        ThickPoint.disc 0 (meshLowerSpatialRadius m a : ℝ) := by
      rw [htailZero]
      change latticeDistance 0 0 ≤ (meshLowerSpatialRadius m a : ℝ)
      simp [latticeDistance]
    have hhit : ThickPoint.firstHitThrough (trajectory tail)
        (ThickPoint.discBoundary 0
          (meshLowerSpatialRadius m a : ℝ)) 0 d ≤ d := by
      change ThickPoint.firstHitThrough (trajectory tail)
        (ThickPoint.innerBoundary
          (ThickPoint.disc 0 (meshLowerSpatialRadius m a : ℝ))) 0 d ≤ d
      apply firstHitThrough_innerBoundary_le_of_exit (trajectory tail)
        (ThickPoint.disc 0 (meshLowerSpatialRadius m a : ℝ))
        (trajectory_adjacent tail) (Nat.zero_le d) hin hout
    let hit := ThickPoint.firstHitThrough (trajectory tail)
      (ThickPoint.discBoundary 0 (meshLowerSpatialRadius m a : ℝ)) 0 d
    have hhitMem : trajectory tail hit ∈
        ThickPoint.discBoundary 0 (meshLowerSpatialRadius m a : ℝ) :=
      ThickPoint.firstHitThrough_mem_set_of_le _ _ _ _ hhit
    have hnoReturn : ∀ q, 0 < q → q ≤ d → trajectory tail q ≠ 0 := by
      intro q hq hqd hzero
      have hqOld : nOld < nOld + q := by omega
      have hqNew : nOld + q ≤ nNew := by omega
      have havoid := no_oldCreation_visit_of_no_next_level
        hrank hold hnext (nOld + q) hqOld hqNew
      apply havoid
      have hshift := trajectory_add_sub_trajectory omega nOld q
      dsimp only [tail, postStoppingSteps] at hzero
      rw [hzero] at hshift
      simpa using (sub_eq_zero.mp hshift)
    intro hreturn
    obtain ⟨r, hr, havoidBoundary⟩ := Set.mem_iUnion.mp hreturn
    have hrspec := TerminalSequentialVisitLaw.firstPositiveReturnTime_spec hr
    by_cases hrd : r ≤ d
    · exact hnoReturn r hrspec.1 hrd hrspec.2.1
    · have hdlt : d < r := Nat.lt_of_not_ge hrd
      exact havoidBoundary hit (hhit.trans_lt hdlt) hhitMem

end

end Erdos1165.HLOZMeshSpatialTransitionFactor
