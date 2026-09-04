/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.Augmentation
import ErdosProblems.Erdos636.AugmentationGraphFull
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.AugmentationSmallNZ
import ErdosProblems.Erdos636.AugmentationCenterMoments
import ErdosProblems.Erdos636.AugmentationCenterMotion
import ErdosProblems.Erdos636.AugmentationExposureAssembly
import ErdosProblems.Erdos636.AugmentationExposureCrowd
import ErdosProblems.Erdos636.AugmentationExposureCrowdFinal
import ErdosProblems.Erdos636.AugmentationInnerScales
import ErdosProblems.Erdos636.AugmentationInnerScalesFinal
import ErdosProblems.Erdos636.AugmentationOuterConstants
import ErdosProblems.Erdos636.AugmentationScales
import ErdosProblems.Erdos636.CrowdedInstantiation
import ErdosProblems.Erdos636.CrowdScheduleBridge
import ErdosProblems.Erdos636.DegreeBuckets
import ErdosProblems.Erdos636.OuterSwitchingPath
import ErdosProblems.Erdos636.OuterConcentrationPathBridge
import ErdosProblems.Erdos636.StructuralOuterConcentration

/-!
# Integration of the balanced augmentation

This file is the graph-facing composition layer for the two exposure
claims in the Kwan--Sudakov proof.  It keeps one deletion set across the
outer switching path, retains the successful times as a marked set, and
turns the resulting window family into `OuterSwitching.PointwiseWindows`.

The elementary lemmas below isolate two pieces of bookkeeping which are
easy to state incorrectly in an informal proof:

* the variation of the centre errors on a switching path is charged at
  most twice their `L^1` mass; and
* the collision-event counter is literally the cardinality of the marked
  filter.

The final graph theorem is assembled below these deterministic facts from
the concrete partial- and full-exposure endpoints.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationIntegration

noncomputable section

universe w

/-! ## Exact branch ratios -/

/-- The two rounded branches preserve the deletion density exactly: both
the reservoir and the deletion size are doubled in the `true` branch. -/
lemma branchScale_ratio (branch : Bool) (f ell : ℕ) (hell : 0 < ell) :
    ((RoundedParameters.branchScale branch f : ℕ) : ℝ) /
        RoundedParameters.branchScale branch ell =
      (f : ℝ) / ell := by
  cases branch
  · simp [RoundedParameters.branchScale]
  · simp only [RoundedParameters.branchScale_true, Nat.cast_mul,
      Nat.cast_ofNat]
    have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp

/-- Convenient form of `branchScale_ratio` for the canonical centre moment
identity. -/
lemma structuralAlpha_eq_branchDeletionRatio
    {alpha : ℝ} {branch : Bool} {f ell nD : ℕ}
    (hAlpha : alpha = 1 - (f : ℝ) / ell)
    (hell : 0 < ell)
    (hnD : nD = RoundedParameters.branchScale branch f)
    {U0 : Finset w}
    (hU0 : U0.card = RoundedParameters.branchScale branch ell) :
    alpha = 1 - (nD : ℝ) / U0.card := by
  rw [hAlpha, hnD, hU0, branchScale_ratio branch f ell hell]

lemma abs_one_sub_natRatio_le_one {f ell : ℕ}
    (hell : 0 < ell) (hf : f ≤ ell) :
    |(1 : ℝ) - (f : ℝ) / ell| ≤ 1 := by
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  have hf' : (f : ℝ) ≤ ell := by exact_mod_cast hf
  rw [abs_le]
  constructor <;> nlinarith [div_nonneg (by positivity : (0 : ℝ) ≤ f) hell'.le,
    (div_le_one hell').2 hf']

/-- Every one- or two-copy reservoir associated to an outer parameter has
size at most `4 c n`. -/
lemma branchScale_outerParameter_upper
    {c : ℝ} {n ell : ℕ} (hc : 0 ≤ c)
    (hell : ell ∈ RoundedParameters.outerParameterInterval c n)
    (branch : Bool) :
    (RoundedParameters.branchScale branch ell : ℝ) ≤ 4 * c * n := by
  have hellBounds :=
    (RoundedParameters.mem_outerParameterInterval hc).mp hell
  have hellUpper : (ell : ℝ) ≤ 2 * c * n := by
    simpa using hellBounds.2
  have hbranch : RoundedParameters.branchScale branch ell ≤ 2 * ell :=
    RoundedParameters.branchScale_le_two_mul branch ell
  have hbranch' : (RoundedParameters.branchScale branch ell : ℝ) ≤
      2 * ell := by exact_mod_cast hbranch
  nlinarith

lemma StructuralWitness.exists_branch_card_U0
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    ∃ branch : Bool,
      S.U0.card = RoundedParameters.branchScale branch ell := by
  rcases S.card_U0 with h | h
  · exact ⟨false, by simpa using h⟩
  · exact ⟨true, by simpa using h⟩

/-- The two endpoint degrees of a nonempty structural matching lie in the
same interval `[0, K nW]`; hence their difference costs only `K nW`, not
twice that amount. -/
lemma StructuralWitness.abs_dPlus_sub_dMinus_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (hmatching : S.matching.Nonempty) :
    |(S.dPlus : ℝ) - S.dMinus| ≤ K * nW := by
  obtain ⟨x, hx⟩ := hmatching
  have hxcard : x.card ≤ K := (S.matching_uniform x hx).le.trans S.k_le
  have hminusNat : S.dMinus ≤ K * nW := by
    rw [← S.degree_Wminus x hx]
    exact (degreeInto_le_card_mul_card G S.Wminus x).trans (by
      rw [S.card_Wminus]
      exact Nat.mul_le_mul_right nW hxcard)
  have hplusNat : S.dPlus ≤ K * nW := by
    rw [← S.degree_Wplus x hx]
    exact (degreeInto_le_card_mul_card G S.Wplus x).trans (by
      rw [S.card_Wplus]
      exact Nat.mul_le_mul_right nW hxcard)
  have hminus : (0 : ℝ) ≤ S.dMinus := by positivity
  have hplus : (0 : ℝ) ≤ S.dPlus := by positivity
  have hminus' : (S.dMinus : ℝ) ≤ K * nW := by exact_mod_cast hminusNat
  have hplus' : (S.dPlus : ℝ) ≤ K * nW := by exact_mod_cast hplusNat
  rw [abs_le]
  constructor <;> linarith

/-- Coarse linear bound for the deterministic weighted-score cost of one
outer vertex exchange. -/
lemma StructuralWitness.weightedStepBound_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {scale nW ell K n : ℕ}
    {alpha aDisc aDiv b cW uCoeff : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (halpha : |alpha| ≤ 1) (hnW : (nW : ℝ) ≤ cW * n)
    (hU0 : (S.U0.card : ℝ) ≤ uCoeff * n) :
    OuterSwitchingPath.weightedStepBound S ≤ (cW + uCoeff) * n := by
  dsimp only [OuterSwitchingPath.weightedStepBound]
  have hmul := mul_le_mul_of_nonneg_right halpha
    (show (0 : ℝ) ≤ S.U0.card by positivity)
  nlinarith

/-- A structural matching with a positive density coefficient is nonempty at
every positive ambient order. -/
lemma StructuralWitness.matching_nonempty_of_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {n nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G n nW ell K alpha aDisc aDiv b)
    (hb : 0 < b) (hn : 0 < n) :
    S.matching.Nonempty := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hnreal _
  have hcard : (0 : ℝ) < S.matching.card :=
    (mul_pos hb hpow).trans_le S.matching_large
  exact Finset.card_pos.mp (by exact_mod_cast hcard)

lemma StructuralWitness.weightedStepBound_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    0 ≤ OuterSwitchingPath.weightedStepBound S := by
  dsimp only [OuterSwitchingPath.weightedStepBound]
  positivity

/-- Eventually the rounded outer deletion size is positive. -/
theorem exists_deletionSize_pos {cW : ℝ} (hcW : 0 < cW) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < OuterAssembly.deletionSize cW n := by
  obtain ⟨N, hN⟩ :=
    AsymptoticThresholds.exists_const_le_mul_sqrt cW 1 hcW
  refine ⟨N, ?_⟩
  intro n hn
  have hone : (1 : ℝ) ≤ cW * Real.sqrt n := hN n hn
  have hnpos : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    norm_num [hnzero] at hone
  have hsqrt : Real.sqrt n ≤ (n : ℝ) :=
    AsymptoticThresholds.sqrt_nat_le_nat hnpos
  have hlinear : (1 : ℝ) ≤ cW * n :=
    hone.trans (mul_le_mul_of_nonneg_left hsqrt hcW.le)
  dsimp only [OuterAssembly.deletionSize]
  exact Nat.floor_pos.mpr hlinear

/-- The outer `2*nD` reservoir is a uniformly balanced slice of either
rounded branch of `U0`.  This is the exact balance pair consumed by the
partial-exposure theorem. -/
lemma branch_partial_balance
    {c c₀ δ₀ δZ : ℝ} {K n ell k nD : ℕ} {branch : Bool}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hell : ell ∈ RoundedParameters.outerParameterInterval c n)
    (B : AugmentationScales.BranchBounds c c₀ δ₀ δZ K n ell k branch)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    {U0 : Finset w}
    (hU0 : U0.card = RoundedParameters.branchScale branch ell) :
    c₀ / (4 * c) * U0.card ≤ ((2 * nD : ℕ) : ℝ) ∧
      c₀ / (4 * c) * U0.card ≤ ((U0.card - 2 * nD : ℕ) : ℝ) := by
  have hU0upper : (U0.card : ℝ) ≤ 4 * c * n := by
    rw [hU0]
    exact branchScale_outerParameter_upper hc.le hell branch
  have hratioPos : 0 ≤ c₀ / (4 * c) := by positivity
  have hbalanceUpper : c₀ / (4 * c) * U0.card ≤ c₀ * n := by
    calc
      c₀ / (4 * c) * U0.card ≤ c₀ / (4 * c) * (4 * c * n) := by
        gcongr
      _ = c₀ * n := by field_simp
  have hnDlower : c₀ / 2 * n ≤ (nD : ℝ) := by
    simpa only [hnD] using B.order_lower
  have hnDupper : (nD : ℝ) ≤ 2 * c₀ * n := by
    simpa only [hnD] using B.order_upper
  have hselected : c₀ / (4 * c) * U0.card ≤ ((2 * nD : ℕ) : ℝ) := by
    push_cast
    linarith
  have hellBounds := (RoundedParameters.mem_outerParameterInterval hc.le).mp hell
  have hbranchLower : (ell : ℝ) ≤
      RoundedParameters.branchScale branch ell := by
    cases branch
    · simp [RoundedParameters.branchScale]
    · simp [RoundedParameters.branchScale]
      have : (0 : ℝ) ≤ ell := by positivity
      linarith
  have hU0lower : c * n ≤ (U0.card : ℝ) := by
    rw [hU0]
    exact hellBounds.1.trans hbranchLower
  have hfeasible : 2 * nD ≤ U0.card := by
    rw [hU0, hnD]
    exact B.feasible
  have hsubcast : ((U0.card - 2 * nD : ℕ) : ℝ) =
      (U0.card : ℝ) - 2 * nD := by
    rw [Nat.cast_sub hfeasible]
    push_cast
    rfl
  constructor
  · exact hselected
  · rw [hsubcast]
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    have hsmall' : 4 * c₀ + c₀ ≤ c := by linarith
    have hroom : c₀ * n ≤ (U0.card : ℝ) - 2 * nD := by
      calc
        c₀ * n ≤ (c - 4 * c₀) * n := by
          exact mul_le_mul_of_nonneg_right (by linarith) hnnonneg
        _ ≤ (U0.card : ℝ) - 2 * nD := by linarith
    exact hbalanceUpper.trans hroom

/-- A fixed fraction of the structural diversity constant remains valid on
either one- or two-copy outer reservoir. -/
lemma branch_normalized_diversity
    {c aDiv : ℝ} {n ell : ℕ} {branch : Bool}
    (hc : 0 < c) (haDiv : 0 < aDiv)
    (hell : ell ∈ RoundedParameters.outerParameterInterval c n)
    {U0 : Finset w}
    (hU0 : U0.card = RoundedParameters.branchScale branch ell) :
    aDiv / (8 * c) * U0.card ≤ aDiv * n := by
  have hU0upper : (U0.card : ℝ) ≤ 4 * c * n := by
    rw [hU0]
    exact branchScale_outerParameter_upper hc.le hell branch
  have hcoeff : 0 ≤ aDiv / (8 * c) := by positivity
  calc
    aDiv / (8 * c) * U0.card ≤
        aDiv / (8 * c) * (4 * c * n) := by gcongr
    _ = aDiv / 2 * n := by field_simp; ring
    _ ≤ aDiv * n := by
      gcongr
      linarith

/-! ## Compatible inner coefficients -/

/-- The three small coefficients which link the partial Turán selection, the
inner switching endpoint, and the eventual outer crowd window. -/
structure CompatibleInnerScaleCoefficients
    (K : ℕ) (a₀ LH c₀ : ℝ) where
  delta : ℝ
  gap : ℝ
  window : ℝ
  delta_pos : 0 < delta
  delta_le_c₀ : delta ≤ c₀
  gap_pos : 0 < gap
  window_pos : 0 < window
  partial_turan :
    (3 * delta + gap) * (a₀ / 4 + 2 * LH) < (a₀ / 16) ^ 2
  inner_endpoint :
    (K : ℝ) ^ 2 * delta ^ 2 + 2 * delta * window <
      (delta / (4 * K)) * gap / 4

/-- Positive compatible coefficients exist for every positive partial scale.
The augmentation coefficient is additionally capped by the already fixed
outer deletion coefficient, so the final outer endpoint may safely use
`c₀` as its (looser) augmentation upper coefficient. -/
theorem nonempty_compatibleInnerScaleCoefficients
    {K : ℕ} {a₀ LH c₀ : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (hLH : 0 < LH) (hc₀ : 0 < c₀) :
    Nonempty (CompatibleInnerScaleCoefficients K a₀ LH c₀) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let D : ℝ := a₀ / 4 + 2 * LH
  have hD : 0 < D := by dsimp [D]; positivity
  let base : ℝ := (a₀ / 16) ^ 2 / D
  have hbase : 0 < base := by dsimp [base]; positivity
  let gap : ℝ := base / 4
  have hgap : 0 < gap := by dsimp [gap]; positivity
  let delta : ℝ := min c₀
    (min (base / 16) (gap / (128 * (K : ℝ) ^ 3)))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min hc₀ (lt_min (by positivity) (by positivity))
  have hdeltaC : delta ≤ c₀ := by
    dsimp only [delta]
    exact min_le_left _ _
  have hdeltaBase : delta ≤ base / 16 := by
    dsimp only [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaGap : delta ≤ gap / (128 * (K : ℝ) ^ 3) := by
    dsimp only [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let window : ℝ := gap / (256 * K)
  have hwindow : 0 < window := by dsimp [window]; positivity
  have hbaseD : base * D = (a₀ / 16) ^ 2 := by
    dsimp only [base]
    field_simp
  have hturan :
      (3 * delta + gap) * (a₀ / 4 + 2 * LH) < (a₀ / 16) ^ 2 := by
    have hsum : 3 * delta + gap ≤ 7 * base / 16 := by
      dsimp only [gap]
      linarith
    have hseven : 7 * base / 16 < base := by nlinarith
    have hscaled := mul_lt_mul_of_pos_right (hsum.trans_lt hseven) hD
    dsimp only [D] at hscaled
    rw [hbaseD] at hscaled
    exact hscaled
  have hfirst : (K : ℝ) ^ 2 * delta ^ 2 ≤
      delta * gap / (128 * K) := by
    have hscaled := mul_le_mul_of_nonneg_left hdeltaGap hdelta.le
    have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKreal
    calc
      (K : ℝ) ^ 2 * delta ^ 2 =
          delta * delta * (K : ℝ) ^ 2 := by ring
      _ ≤ delta * (gap / (128 * (K : ℝ) ^ 3)) *
          (K : ℝ) ^ 2 := by gcongr
      _ = delta * gap / (128 * K) := by field_simp
  have hsecond : 2 * delta * window = delta * gap / (128 * K) := by
    dsimp only [window]
    field_simp
    ring
  have hendpoint :
      (K : ℝ) ^ 2 * delta ^ 2 + 2 * delta * window <
        (delta / (4 * K)) * gap / 4 := by
    rw [hsecond]
    have htarget : delta * gap / (64 * K) < delta * gap / (16 * K) := by
      have hx : 0 < delta * gap / (K : ℝ) := by positivity
      calc
        delta * gap / (64 * K) = (delta * gap / K) / 64 := by ring
        _ < (delta * gap / K) / 16 := by nlinarith
        _ = delta * gap / (16 * K) := by ring
    have hsum : (K : ℝ) ^ 2 * delta ^ 2 +
        delta * gap / (128 * K) ≤ delta * gap / (64 * K) := by
      calc
        (K : ℝ) ^ 2 * delta ^ 2 + delta * gap / (128 * K) ≤
            delta * gap / (128 * K) + delta * gap / (128 * K) :=
          add_le_add hfirst le_rfl
        _ = delta * gap / (64 * K) := by ring
    calc
      (K : ℝ) ^ 2 * delta ^ 2 + delta * gap / (128 * K) ≤
          delta * gap / (64 * K) := hsum
      _ < delta * gap / (16 * K) := htarget
      _ = (delta / (4 * K)) * gap / 4 := by ring
  exact ⟨{
    delta := delta
    gap := gap
    window := window
    delta_pos := hdelta
    delta_le_c₀ := hdeltaC
    gap_pos := hgap
    window_pos := hwindow
    partial_turan := hturan
    inner_endpoint := hendpoint }⟩

/-! ## Increasing enumeration of one common set of good times -/

/-- The final ordinal in the increasing enumeration of a nonempty marked
set of source times. -/
def markedLast (marked : Finset ℕ) : ℕ := marked.card - 1

lemma markedLast_add_one (marked : Finset ℕ) (hmarked : marked.Nonempty) :
    markedLast marked + 1 = marked.card := by
  exact Nat.sub_add_cancel (Finset.one_le_card.mpr hmarked)

/-- Increasing enumeration of a finite set of natural switching times. -/
def markedTime (marked : Finset ℕ) : Fin marked.card → ℕ :=
  fun i ↦ ((marked.orderIsoOfFin rfl) i).1

@[simp] lemma markedTime_mem (marked : Finset ℕ) (i : Fin marked.card) :
    markedTime marked i ∈ marked :=
  ((marked.orderIsoOfFin rfl) i).2

lemma markedTime_strictMono (marked : Finset ℕ) :
    StrictMono (markedTime marked) := by
  intro i j hij
  have h := (marked.orderIsoOfFin rfl).strictMono hij
  exact_mod_cast h

/-- The same enumeration with the `last + 1` domain required by
`OuterSwitching.SharedAugmentationOutcome`. -/
def markedGoodTime (marked : Finset ℕ) (hmarked : marked.Nonempty) :
    Fin (markedLast marked + 1) → ℕ :=
  fun i ↦ markedTime marked (Fin.cast (markedLast_add_one marked hmarked) i)

@[simp] lemma markedGoodTime_mem (marked : Finset ℕ)
    (hmarked : marked.Nonempty) (i : Fin (markedLast marked + 1)) :
    markedGoodTime marked hmarked i ∈ marked :=
  markedTime_mem marked _

lemma markedGoodTime_strictMono (marked : Finset ℕ)
    (hmarked : marked.Nonempty) :
    StrictMono (markedGoodTime marked hmarked) := by
  intro i j hij
  apply markedTime_strictMono marked
  simpa using hij

/-- Reindex source-time data by the increasing marked-time enumeration.
The fallback is irrelevant on ordinals at most `markedLast`. -/
def markedReindex {α : Type*} (marked : Finset ℕ)
    (f : ℕ → α) (fallback : α) (i : ℕ) : α :=
  if hi : i < marked.card then f (markedTime marked ⟨i, hi⟩) else fallback

@[simp] lemma markedReindex_apply_fin {α : Type*} (marked : Finset ℕ)
    (f : ℕ → α) (fallback : α) (i : Fin marked.card) :
    markedReindex marked f fallback i = f (markedTime marked i) := by
  simp only [markedReindex, i.isLt, ↓reduceDIte]

@[simp] lemma markedReindex_apply_goodTime {α : Type*}
    (marked : Finset ℕ) (hmarked : marked.Nonempty)
    (f : ℕ → α) (fallback : α) (i : Fin (markedLast marked + 1)) :
    markedReindex marked f fallback i =
      f (markedGoodTime marked hmarked i) := by
  let j : Fin marked.card :=
    Fin.cast (markedLast_add_one marked hmarked) i
  have hij : (i : ℕ) = (j : ℕ) := rfl
  rw [hij]
  exact markedReindex_apply_fin marked f fallback j

/-- Package data carried by one shared deletion on a nonempty marked set
into the exact second-switching interface.  The strict source-time map is
the canonical order enumeration, so the constructor cannot silently
choose a different deletion or reorder windows at different times. -/
noncomputable def sharedAugmentationOutcomeOfMarked
    {DState : Type w} {spectrum : Finset ℕ} {n sourceLast : ℕ}
    (sharedDeletion : DState)
    (marked : Finset ℕ) (hmarked : marked.Nonempty)
    (hmarked_le : ∀ t ∈ marked, t ≤ sourceLast)
    (center : ℕ → ℝ)
    (deterministicIncrement randomError : ℕ → ℝ)
    (jumpBound errorBudget : ℝ)
    (hjumpBound_nonneg : 0 ≤ jumpBound)
    (hdeterministicIncrement_bound : ∀ i < markedLast marked,
      |deterministicIncrement i| ≤ jumpBound)
    (hincrement_decomposition : ∀ i < markedLast marked,
      markedReindex marked center 0 (i + 1) -
          markedReindex marked center 0 i =
        deterministicIncrement i + randomError i)
    (hrandomError_l1 :
      ∑ i ∈ Finset.range (markedLast marked), |randomError i| ≤ errorBudget)
    (piece : ℕ → Finset ℕ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hin_window : ∀ t ∈ marked, ∀ e ∈ piece t,
      |(e : ℝ) - center t| ≤ radius)
    (hpiece_subset : ∀ t ∈ marked, piece t ⊆ spectrum) :
    OuterSwitching.SharedAugmentationOutcome
      (DState := DState) spectrum n where
  sharedDeletion := sharedDeletion
  last := markedLast marked
  sourceLast := sourceLast
  goodTime := markedGoodTime marked hmarked
  goodTime_strictMono := markedGoodTime_strictMono marked hmarked
  goodTime_le := fun i ↦ hmarked_le _ (markedGoodTime_mem marked hmarked i)
  center := markedReindex marked center 0
  deterministicIncrement := deterministicIncrement
  randomError := randomError
  jumpBound := jumpBound
  errorBudget := errorBudget
  jumpBound_nonneg := hjumpBound_nonneg
  deterministicIncrement_bound := hdeterministicIncrement_bound
  increment_decomposition := hincrement_decomposition
  randomError_l1 := hrandomError_l1
  piece := markedReindex marked piece ∅
  radius := radius
  radius_nonneg := hradius_nonneg
  in_window := by
    intro i hi e he
    have hiCard : i < marked.card := by
      rw [← markedLast_add_one marked hmarked]
      omega
    rw [markedReindex_apply_fin marked center 0 ⟨i, hiCard⟩]
    rw [markedReindex_apply_fin marked piece ∅ ⟨i, hiCard⟩] at he
    exact hin_window _ (markedTime_mem marked ⟨i, hiCard⟩) e he
  piece_subset := by
    intro i hi
    have hiCard : i < marked.card := by
      rw [← markedLast_add_one marked hmarked]
      omega
    rw [markedReindex_apply_fin marked piece ∅ ⟨i, hiCard⟩]
    exact hpiece_subset _ (markedTime_mem marked ⟨i, hiCard⟩)

theorem nonempty_sharedAugmentationOutcome_of_marked
    {DState : Type w} {spectrum : Finset ℕ} {n sourceLast : ℕ}
    (sharedDeletion : DState)
    (marked : Finset ℕ) (hmarked : marked.Nonempty)
    (hmarked_le : ∀ t ∈ marked, t ≤ sourceLast)
    (center : ℕ → ℝ)
    (deterministicIncrement randomError : ℕ → ℝ)
    (jumpBound errorBudget : ℝ)
    (hjumpBound_nonneg : 0 ≤ jumpBound)
    (hdeterministicIncrement_bound : ∀ i < markedLast marked,
      |deterministicIncrement i| ≤ jumpBound)
    (hincrement_decomposition : ∀ i < markedLast marked,
      markedReindex marked center 0 (i + 1) -
          markedReindex marked center 0 i =
        deterministicIncrement i + randomError i)
    (hrandomError_l1 :
      ∑ i ∈ Finset.range (markedLast marked), |randomError i| ≤ errorBudget)
    (piece : ℕ → Finset ℕ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hin_window : ∀ t ∈ marked, ∀ e ∈ piece t,
      |(e : ℝ) - center t| ≤ radius)
    (hpiece_subset : ∀ t ∈ marked, piece t ⊆ spectrum) :
    Nonempty (OuterSwitching.SharedAugmentationOutcome
      (DState := DState) spectrum n) :=
  ⟨sharedAugmentationOutcomeOfMarked sharedDeletion marked hmarked
    hmarked_le center deterministicIncrement randomError jumpBound
    errorBudget hjumpBound_nonneg hdeterministicIncrement_bound
    hincrement_decomposition hrandomError_l1 piece radius
    hradius_nonneg hin_window hpiece_subset⟩

/-! ## Error variation along a switching path -/

/-- Consecutive differences of a real error sequence cost at most twice
its `L^1` mass.  The two endpoints are included in the right-hand sum;
this is the exact estimate used after one deletion is fixed for all marked
switching times. -/
theorem sum_abs_sub_le_two_sum_abs (e : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.Icc 1 m, |e i - e (i - 1)|) ≤
      2 * ∑ i ∈ Finset.range (m + 1), |e i| := by
  calc
    (∑ i ∈ Finset.Icc 1 m, |e i - e (i - 1)|)
        ≤ ∑ i ∈ Finset.Icc 1 m, (|e i| + |e (i - 1)|) := by
          apply Finset.sum_le_sum
          intro i _hi
          exact abs_sub _ _
    _ = (∑ i ∈ Finset.Icc 1 m, |e i|) +
          ∑ i ∈ Finset.Icc 1 m, |e (i - 1)| := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ Finset.range (m + 1), |e i|) +
          ∑ i ∈ Finset.range (m + 1), |e i| := by
          apply add_le_add
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              rw [Finset.mem_range]
              exact Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2
            · intro i _hi _hnot
              exact abs_nonneg _
          · have hshift :
                (∑ i ∈ Finset.Icc 1 m, |e (i - 1)|) =
                  ∑ j ∈ Finset.range m, |e j| := by
              apply Finset.sum_bij (fun i _hi ↦ i - 1)
              · intro i hi
                rw [Finset.mem_range]
                have hii := Finset.mem_Icc.mp hi
                omega
              · intro i₁ hi₁ i₂ hi₂ heq
                have h₁ := (Finset.mem_Icc.mp hi₁).1
                have h₂ := (Finset.mem_Icc.mp hi₂).1
                omega
              · intro j hj
                refine ⟨j + 1, ?_, ?_⟩
                · rw [Finset.mem_Icc]
                  have hjlt := Finset.mem_range.mp hj
                  omega
                · omega
              · intro i _hi
                rfl
            rw [hshift]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_mono (Nat.le_succ m)
            · intro i _hi _hnot
              exact abs_nonneg _
    _ = 2 * ∑ i ∈ Finset.range (m + 1), |e i| := by ring

/-! ## Marked-time bookkeeping -/

/-- The successful switching times for one fixed outcome. -/
def markedTimes {J Omega : Type*} [DecidableEq J]
    (I : Finset J) (good : J → Omega → Prop) (omega : Omega) : Finset J :=
  I.filter fun j ↦ good j omega

@[simp] lemma card_markedTimes {J Omega : Type*} [DecidableEq J]
    (I : Finset J) (good : J → Omega → Prop) (omega : Omega) :
    (markedTimes I good omega).card =
      CollisionCounting.eventCount I good omega :=
  rfl

lemma markedTimes_subset {J Omega : Type*} [DecidableEq J]
    (I : Finset J) (good : J → Omega → Prop) (omega : Omega) :
    markedTimes I good omega ⊆ I :=
  Finset.filter_subset _ _

@[simp] lemma mem_markedTimes {J Omega : Type*} [DecidableEq J]
    {I : Finset J} {good : J → Omega → Prop} {omega : Omega} {j : J} :
    j ∈ markedTimes I good omega ↔ j ∈ I ∧ good j omega :=
  Finset.mem_filter

/-- Reindexing a nonempty marked set by its increasing enumeration cannot
increase the sum of a nonnegative function relative to a containing source
interval. -/
lemma sum_range_markedReindex_le_sum_range
    (marked : Finset ℕ) (hmarked : marked.Nonempty)
    (sourceLast : ℕ)
    (hmarkedRange : marked ⊆ Finset.range (sourceLast + 1))
    (e : ℕ → ℝ) :
    (∑ i ∈ Finset.range (markedLast marked + 1),
        |markedReindex marked e 0 i|) ≤
      ∑ i ∈ Finset.range (sourceLast + 1), |e i| := by
  rw [markedLast_add_one marked hmarked]
  calc
    (∑ i ∈ Finset.range marked.card, |markedReindex marked e 0 i|) =
        ∑ i : Fin marked.card, |e (markedTime marked i)| := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [markedReindex_apply_fin]
    _ = ∑ x : marked, |e x.1| := by
      exact Equiv.sum_comp (marked.orderIsoOfFin rfl).toEquiv
        (fun x : marked ↦ |e x.1|)
    _ = ∑ x ∈ marked, |e x| := by
      simpa using (Finset.sum_attach marked (fun x : ℕ ↦ |e x|))
    _ ≤ ∑ i ∈ Finset.range (sourceLast + 1), |e i| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hmarkedRange
      intro i _hi _hnot
      exact abs_nonneg _

/-- Monotonicity of uniform-layer probability when the implication only
needs to hold on the sampled layer. -/
lemma layerProbability_mono_on_layer
    {A : Type*} [DecidableEq A]
    (U : Finset A) (d : ℕ) (P Q : Finset A → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ D ∈ NestedUniform.layer U d, P D → Q D) :
    NestedUniform.layerProbability U d P ≤
      NestedUniform.layerProbability U d Q := by
  unfold NestedUniform.layerProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro D hD
      rw [Finset.mem_filter] at hD ⊢
      exact ⟨hD.1, hPQ D hD.1 hD.2⟩)
  · positivity

/-! ## Window event retained by the shared-deletion selector -/

/-- A successful deletion at one outer switching time carries the actual
large subwindow, not merely the cardinality of a larger ambient image. -/
def WindowGood {J DState : Type*} (spectrum : Finset ℕ)
    (center : J → DState → ℝ) (radius L : ℝ)
    (j : J) (D : DState) : Prop :=
  ∃ piece : Finset ℕ,
    piece ⊆ spectrum ∧ L ≤ (piece.card : ℝ) ∧
      ∀ e ∈ piece, |(e : ℝ) - center j D| ≤ radius

/-- Total absolute deviation of the deletion-dependent window centres from
the deterministic outer centre path. -/
def centerL1Error {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    (omega : Erdos88.Fourier.BoolSlice U d) : ℝ :=
  ∑ i ∈ Finset.range (sourceLast + 1),
    |center i (Augmentation.boolSliceDeletion U d omega) - idealCenter i|

lemma centerL1Error_nonneg {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    (omega : Erdos88.Fourier.BoolSlice U d) :
    0 ≤ centerL1Error U d sourceLast center idealCenter omega := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- A per-time first-moment estimate sums to the exact global error budget
used by the common-deletion selector. -/
lemma uniformExpectation_centerL1Error_le
    {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    [Nonempty (Erdos88.Fourier.BoolSlice U d)]
    (moment : ℕ → ℝ)
    (hmoment : ∀ i ≤ sourceLast,
      Erdos88.Concentration.uniformExpectation
        (fun omega : Erdos88.Fourier.BoolSlice U d ↦
          |center i (Augmentation.boolSliceDeletion U d omega) -
            idealCenter i|) ≤ moment i)
    (B : ℝ) (hsum : ∑ i ∈ Finset.range (sourceLast + 1), moment i ≤ B) :
    Erdos88.Concentration.uniformExpectation
      (centerL1Error U d sourceLast center idealCenter) ≤ B := by
  change Erdos88.Concentration.uniformExpectation
      (fun omega ↦ ∑ i ∈ Finset.range (sourceLast + 1),
        |center i (Augmentation.boolSliceDeletion U d omega) -
          idealCenter i|) ≤ B
  rw [AugmentationFull.uniformExpectation_sum]
  exact (Finset.sum_le_sum fun i hi ↦
    hmoment i (by simpa using Finset.mem_range.mp hi)).trans hsum

/-- Error in one *increment* of the deletion-dependent centre relative to
the deterministic outer path.  This is the quantity used in the paper:
for an adjacent one-vertex switch its slice coefficients are uniformly
bounded, whereas the absolute centre at one time need not have small
variance. -/
def rawCenterIncrementError {V : Type*} [Fintype V]
    (U : Finset V) (d : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    (omega : Erdos88.Fourier.BoolSlice U d) (i : ℕ) : ℝ :=
  |(center i (Augmentation.boolSliceDeletion U d omega) -
        center (i - 1) (Augmentation.boolSliceDeletion U d omega)) -
      (idealCenter i - idealCenter (i - 1))|

/-- Total perturbation charged along all adjacent raw outer switches. -/
def rawCenterVariationError {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    (omega : Erdos88.Fourier.BoolSlice U d) : ℝ :=
  ∑ i ∈ Finset.Icc 1 sourceLast,
    rawCenterIncrementError U d center idealCenter omega i

lemma rawCenterVariationError_nonneg {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    (omega : Erdos88.Fourier.BoolSlice U d) :
    0 ≤ rawCenterVariationError U d sourceLast center idealCenter omega := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Per-switch first moments sum to the global raw-variation budget. -/
lemma uniformExpectation_rawCenterVariationError_le
    {V : Type*} [Fintype V]
    (U : Finset V) (d sourceLast : ℕ)
    (center : ℕ → Finset V → ℝ) (idealCenter : ℕ → ℝ)
    [Nonempty (Erdos88.Fourier.BoolSlice U d)]
    (moment : ℕ → ℝ)
    (hmoment : ∀ i ∈ Finset.Icc 1 sourceLast,
      Erdos88.Concentration.uniformExpectation
        (fun omega : Erdos88.Fourier.BoolSlice U d ↦
          rawCenterIncrementError U d center idealCenter omega i) ≤ moment i)
    (B : ℝ) (hsum : ∑ i ∈ Finset.Icc 1 sourceLast, moment i ≤ B) :
    Erdos88.Concentration.uniformExpectation
      (rawCenterVariationError U d sourceLast center idealCenter) ≤ B := by
  change Erdos88.Concentration.uniformExpectation
      (fun omega ↦ ∑ i ∈ Finset.Icc 1 sourceLast,
        rawCenterIncrementError U d center idealCenter omega i) ≤ B
  rw [AugmentationFull.uniformExpectation_sum]
  exact (Finset.sum_le_sum fun i hi ↦ hmoment i hi).trans hsum

/-! ## Concrete partial exposure on a structural crowd -/

/-- The graph-specific partial-exposure theorem, specialized to the crowd
at one time of a structural switching path.  All incidence, uniformity, and
equal-reservoir-degree assumptions are inherited from the structural
witness; only the explicit finite balance and risk inequalities remain.

This is deliberately parameterized by the three exceptional-count
thresholds.  In the eventual application the two degree thresholds are
`s₀ / 2`, while the collision threshold is an independently chosen
multiple of `sqrt nD`. -/
theorem three_fourths_le_layerProbability_partialGood_crowd_thresholds
    {V : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : OuterSwitchingPath.CrowdedPath S mu window)
    (i nD s₀ : ℕ) (c theta divDev degreeDev : ℝ)
    (tS tX tCollision : ℝ)
    (hi : i ≤ nW) (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hfamilies : 2 * s₀ ≤ (Q.crowd i).card)
    (hnormalizedDiversity : theta * S.U0.card ≤ aDiv * scale)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hbudget :
      let pDiv := AugmentationGraphPartial.outerLinearFailure nD K divDev
      let pDegree :=
        AugmentationGraphPartial.outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv +
          s₀ * pDegree / tS +
          s₀ * pDegree / tX +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    3 / 4 ≤ NestedUniform.layerProbability S.U0 (2 * nD)
      (AugmentationGraphPartial.PartialGood G (Q.crowd i) s₀
        ((2 * nD : ℕ) * theta - divDev)
        (((2 * nD : ℕ) : ℝ) / S.U0.card * S.d0)
        degreeDev tS tX tCollision) := by
  apply AugmentationGraphPartial.three_fourths_le_layerProbability_partialGood_thresholds
    G S.U0 (Q.crowd i) K nD s₀ S.d0 c theta divDev degreeDev
      tS tX tCollision hnD (S.k_pos.trans S.k_le)
      hfeasible hfamilies
  · intro x hx
    rw [Q.crowd_uniform hi hx]
    exact S.k_le
  · intro x hx
    exact Q.crowd_degree_U0 hi hx
  · intro x hx y hy hxy
    exact hnormalizedDiversity.trans (Q.crowd_diverse hi hx hy hxy)
  · exact hc₀
  · exact hc₁
  · exact htheta
  · exact hselected
  · exact hunselected
  · exact hdivDev
  · exact hdegreeDev
  · exact htS
  · exact htX
  · exact htCollision
  · exact hbudget

/-- Scheduled-path form of the same statement.  This is the direct target
of `OuterSwitchingPath.exists_scheduledCrowdedPath`; no separately supplied
abstract crowd schedule occurs in its hypotheses. -/
theorem three_fourths_le_layerProbability_partialGood_scheduled_thresholds
    {V : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K blockLength mu window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ} {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : OuterSwitchingPath.ScheduledCrowdedPath S
      blockLength mu window step spread)
    (i nD s₀ : ℕ) (c theta divDev degreeDev : ℝ)
    (tS tX tCollision : ℝ)
    (hi : i ≤ nW) (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hfamilies : 2 * s₀ ≤ (A.crowded.crowd i).card)
    (hnormalizedDiversity : theta * S.U0.card ≤ aDiv * scale)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hbudget :
      let pDiv := AugmentationGraphPartial.outerLinearFailure nD K divDev
      let pDegree :=
        AugmentationGraphPartial.outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv +
          s₀ * pDegree / tS +
          s₀ * pDegree / tX +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    3 / 4 ≤ NestedUniform.layerProbability S.U0 (2 * nD)
      (AugmentationGraphPartial.PartialGood G (A.crowded.crowd i) s₀
        ((2 * nD : ℕ) * theta - divDev)
        (((2 * nD : ℕ) : ℝ) / S.U0.card * S.d0)
        degreeDev tS tX tCollision) := by
  exact three_fourths_le_layerProbability_partialGood_crowd_thresholds
    A.crowded i nD s₀ c theta divDev degreeDev tS tX tCollision
      hi hnD hfeasible hfamilies hnormalizedDiversity hc₀ hc₁ htheta
      hselected hunselected hdivDev hdegreeDev htS htX htCollision hbudget

/-- Build the proof-only partial-exposure certificate directly from one
structural crowd.  All graph fields are inherited; the remaining arguments
are scalar balance and risk inequalities. -/
theorem partialExposureCertificate_of_crowd
    {V : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : OuterSwitchingPath.CrowdedPath S mu window)
    (i nD s₀ : ℕ) (c theta divDev degreeDev tS tX tCollision : ℝ)
    (hi : i ≤ nW) (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hfamilies : 2 * s₀ ≤ (Q.crowd i).card)
    (hnormalizedDiversity : theta * S.U0.card ≤ aDiv * scale)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hbudget :
      let pDiv := AugmentationGraphPartial.outerLinearFailure nD K divDev
      let pDegree := AugmentationGraphPartial.outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv + s₀ * pDegree / tS +
          s₀ * pDegree / tX +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    AugmentationExposureAssembly.PartialExposureCertificate G S.U0
      (Q.crowd i) K nD s₀ S.d0 c theta divDev degreeDev
        tS tX tCollision := by
  refine {
    nD_pos := hnD
    K_pos := S.k_pos.trans S.k_le
    feasible := hfeasible
    families := hfamilies
    cell_card := ?_
    reservoir_degree := ?_
    diverse := ?_
    c_pos := hc₀
    c_le_half := hc₁
    theta_pos := htheta
    selected_balance := hselected
    unselected_balance := hunselected
    divDev_pos := hdivDev
    degreeDev_pos := hdegreeDev
    tS_pos := htS
    tX_pos := htX
    tCollision_pos := htCollision
    risk_budget := hbudget }
  · intro x hx
    rw [Q.crowd_uniform hi hx]
    exact S.k_le
  · intro x hx
    exact Q.crowd_degree_U0 hi hx
  · intro x hx y hy hxy
    exact hnormalizedDiversity.trans (Q.crowd_diverse hi hx hy hxy)

/-- Bounded-`nZ` conditional window theorem specialized to one structural
crowd.  All family, degree, and disjointness hypotheses of the general
one-state theorem are discharged from `Q`; only the explicit finite
anti-concentration and Turán budgets remain. -/
theorem one_third_le_layerProbability_innerWindowGood_smallNZ_crowd
    {V : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i nD nZ s₀ : ℕ) (D₁ : Finset V)
    (diversityThreshold outerCenter outerRadius tS tX tCollision : ℝ)
    (c theta innerDeviation E tDegree L : ℝ)
    (outerBad edgeBudget badDegree piece : ℕ)
    (hi : i ≤ nW)
    (hpartial : AugmentationGraphPartial.PartialGood G (Q.crowd i) s₀
      diversityThreshold outerCenter outerRadius tS tX tCollision D₁)
    (hnD : 0 < nD) (hnZ : 1 ≤ nZ) (hhalf : D₁.card = 2 * nD)
    (hD₁ : D₁ ⊆ S.U0) (hstateSize : nZ - 1 ≤ s₀)
    (hK : 1 ≤ K)
    (hdiversityScale : theta * D₁.card ≤ diversityThreshold)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsmall : 2 * outerRadius < theta / 2 * D₁.card)
    (hselected : c * D₁.card ≤ (nD : ℝ))
    (hunselected : c * D₁.card ≤ ((D₁.card - nD : ℕ) : ℝ))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : ℝ) + 1)
    (hgoodLower : badDegree < s₀ - outerBad)
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (theta ^ 2 / 4) K / Real.sqrt (D₁.card : ℝ)
      let pDegree := AugmentationSmallNZ.innerLinearFailure nD K innerDeviation
      (s₀ : ℝ) ^ 2 * pCollision / E +
          s₀ * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : ℝ) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : ℝ) + 1)
    (hpiece : piece * (s₀ + 2 * edgeBudget) ≤
      (s₀ - outerBad - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece) :
    ∃ state : Finset (Finset V),
      state ⊆ Q.crowd i ∧ state.card = nZ - 1 ∧
        (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D₁ nD
          (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
            (Q.crowd i) nZ L
            (AugmentationSmallNZ.generalSmallNZCenter G (Q.W i) S.U0
              D₁ nD state
              (degreeInto G (Q.W i) (Q.anchor i)) S.d0 outerCenter D)
            (AugmentationSmallNZ.generalSmallNZRadius K nZ nD D₁
              degreeWindow innerDeviation outerRadius) D) := by
  apply AugmentationSmallNZ.one_third_le_layerProbability_innerWindowGood_general_of_partialGood
    G (Q.W i) S.U0 (Q.crowd i) S.k K S.d0 nD nZ s₀ D₁
      diversityThreshold outerCenter outerRadius tS tX tCollision
      (degreeInto G (Q.W i) (Q.anchor i)) degreeWindow c theta
      innerDeviation E tDegree L outerBad edgeBudget badDegree piece
      hpartial hnD hnZ hhalf hD₁ hstateSize (Q.disjoint_W_U0 i)
      (Q.crowd_pairwiseDisjoint hi) (fun x hx ↦ Q.crowd_uniform hi hx)
      S.k_le (fun x hx ↦ Q.crowd_away_W_union_U0 hi hx)
      (fun x hx ↦ Q.crowd_degree_U0 hi hx) ?_ hK
      hdiversityScale hc0 hc1 htheta hsmall hselected hunselected
      hinnerDeviation htXBudget hgoodLower hE htDegree hrisk
      hEbudget htDegreeBudget hpiece hpiecePos hL
  intro x hx
  have h := Q.crowd_degree_window hi hx
  exact_mod_cast h

/-- Composable bounded-`nZ` endpoint at one crowded-path time.  In contrast
to the existential-state convenience theorem above, `state` is fixed before
the intermediate reservoir `D₁` is sampled.  Consequently the displayed
centre is a function of the final deletion alone and can be passed through
the nested-uniform marginal and common-deletion arguments. -/
theorem one_third_le_layerProbability_innerWindowGood_fixedState_smallNZ_crowd
    {V : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i nD nZ s₀ : ℕ) (state : Finset (Finset V)) (D₁ : Finset V)
    (diversityThreshold outerCenter outerRadius tS tX tCollision : ℝ)
    (c theta innerDeviation E tDegree L : ℝ)
    (outerBad edgeBudget badDegree piece : ℕ)
    (hi : i ≤ nW)
    (hpartial : AugmentationGraphPartial.PartialGood G (Q.crowd i) s₀
      diversityThreshold outerCenter outerRadius tS tX tCollision D₁)
    (hnD : 0 < nD) (hnZ : 1 ≤ nZ) (hhalf : D₁.card = 2 * nD)
    (hD₁ : D₁ ⊆ S.U0)
    (hstate : state ⊆ Q.crowd i) (hstateCard : state.card = nZ - 1)
    (hK : 1 ≤ K)
    (hdiversityScale : theta * D₁.card ≤ diversityThreshold)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsmall : 2 * outerRadius < theta / 2 * D₁.card)
    (hselected : c * D₁.card ≤ (nD : ℝ))
    (hunselected : c * D₁.card ≤ ((D₁.card - nD : ℕ) : ℝ))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : ℝ) + 1)
    (hgoodLower : badDegree < s₀ - outerBad - (nZ - 1))
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (theta ^ 2 / 4) K / Real.sqrt (D₁.card : ℝ)
      let pDegree := AugmentationSmallNZ.innerLinearFailure nD K innerDeviation
      (s₀ : ℝ) ^ 2 * pCollision / E +
          s₀ * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : ℝ) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : ℝ) + 1)
    (hpiece : piece * (s₀ + 2 * edgeBudget) ≤
      (s₀ - outerBad - (nZ - 1) - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece) :
    (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D₁ nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
        (Q.crowd i) nZ L
        (AugmentationSmallNZ.fixedStateSmallNZCenter G (Q.W i) S.U0 state
          (degreeInto G (Q.W i) (Q.anchor i)) S.d0 outerCenter D)
        (AugmentationSmallNZ.generalSmallNZRadius K nZ nD D₁
          degreeWindow innerDeviation outerRadius) D) := by
  apply AugmentationSmallNZ.one_third_le_layerProbability_innerWindowGood_fixedState_of_partialGood
    G (Q.W i) S.U0 (Q.crowd i) S.k K S.d0 nD nZ s₀ state D₁
      diversityThreshold outerCenter outerRadius tS tX tCollision
      (degreeInto G (Q.W i) (Q.anchor i)) degreeWindow c theta
      innerDeviation E tDegree L outerBad edgeBudget badDegree piece
      hpartial hnD hnZ hhalf hD₁ (Q.disjoint_W_U0 i)
      (Q.crowd_pairwiseDisjoint hi) (fun x hx ↦ Q.crowd_uniform hi hx)
      S.k_le (fun x hx ↦ Q.crowd_away_W_union_U0 hi hx)
      (fun x hx ↦ Q.crowd_degree_U0 hi hx) ?_ hstate hstateCard hK
      hdiversityScale hc0 hc1 htheta hsmall hselected hunselected
      hinnerDeviation htXBudget hgoodLower hE htDegree hrisk
      hEbudget htDegreeBudget hpiece hpiecePos hL
  intro x hx
  have h := Q.crowd_degree_window hi hx
  exact_mod_cast h

/-! ## Transporting graph windows to one fixed-order spectrum -/

/-- Recenter a witnessed inner window at a canonical centre.  This is used
to eliminate auxiliary `D₁`/state-dependent centres before the nested
sampling marginal is taken. -/
lemma innerWindowGood_recenter
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W U₀ : Finset V}
    {M : Finset (Finset V)} {nZ : ℕ} {L oldCenter oldRadius newCenter newRadius : ℝ}
    {D : Finset V}
    (hgood : AugmentationGraphFull.innerWindowGood G W U₀ M nZ L
      oldCenter oldRadius D)
    (hcenter : |oldCenter - newCenter| + oldRadius ≤ newRadius) :
    AugmentationGraphFull.innerWindowGood G W U₀ M nZ L
      newCenter newRadius D := by
  rcases hgood with ⟨piece, hsub, hcard, hwindow⟩
  refine ⟨piece, hsub, hcard, ?_⟩
  intro e he
  calc
    |(e : ℝ) - newCenter| =
        |((e : ℝ) - oldCenter) + (oldCenter - newCenter)| := by ring_nf
    _ ≤ |(e : ℝ) - oldCenter| + |oldCenter - newCenter| := abs_add_le _ _
    _ ≤ oldRadius + |oldCenter - newCenter| := by
      gcongr
      exact hwindow e he
    _ = |oldCenter - newCenter| + oldRadius := by ring
    _ ≤ newRadius := hcenter

/-- A witnessed augmentation window at one crowded-path time lies in the
literal fixed-order edge spectrum.  Every order hypothesis is discharged
from the structural witness and the layer membership of the deletion. -/
lemma windowGood_of_innerWindowGood_crowd
    {V J : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i nD nZ : ℕ) (hi : i ≤ nW)
    (center : J → Finset V → ℝ) (radius L : ℝ)
    (j : J) (D : Finset V)
    (hD : D ∈ NestedUniform.layer S.U0 nD)
    (hgood : AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
      (Q.crowd i) nZ L (center j D) radius D) :
    WindowGood
      (Augmentation.fixedOrderEdgeValues G
        (Augmentation.augmentationOrder (Q.W i) S.U0 nD nZ S.k))
      center radius L j D := by
  rcases hgood with ⟨piece, hpiece, hlarge, hwindow⟩
  refine ⟨piece, ?_, hlarge, hwindow⟩
  exact hpiece.trans
    (Augmentation.augmentationEdgeValues_subset_fixedOrderEdgeValues
      G (Q.W i) S.U0 D (Q.crowd i) nD nZ S.k
      (NestedUniform.mem_layer.mp hD).1
      (NestedUniform.mem_layer.mp hD).2
      (Q.disjoint_W_U0 i)
      (Q.crowd_pairwiseDisjoint hi)
      (fun x hx ↦ Q.crowd_uniform hi hx)
      (fun x hx ↦ Q.crowd_away_W_union_U0 hi hx))

/-- Probability-level form of `windowGood_of_innerWindowGood_crowd`.
This is the final lossless transport used after the concrete two-stage
graph exposure proves its `1/4` witnessed-window estimate. -/
theorem one_fourth_le_layerProbability_windowGood_of_innerWindowGood_crowd
    {V J : Type*} [Fintype V] [DecidableEq V]
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i nD nZ : ℕ) (hi : i ≤ nW)
    (center : J → Finset V → ℝ) (radius L : ℝ) (j : J)
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
        (Q.crowd i) nZ L (center j D) radius D)) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (WindowGood
        (Augmentation.fixedOrderEdgeValues G
          (Augmentation.augmentationOrder (Q.W i) S.U0 nD nZ S.k))
        center radius L j) := by
  apply hprob.trans
  apply layerProbability_mono_on_layer
  intro D hD hgood
  exact windowGood_of_innerWindowGood_crowd Q i nD nZ hi
    center radius L j D hD hgood

/-! ## Exact rounded order on every crowded-path state -/

lemma selectedOffsetOrder_eq_branchScale_sub_add
    (f nW nZ k ell : ℕ) (branch : Bool) (hf : f ≤ ell) :
    ProfileReduction.selectedOffsetOrder f
        (fun _ ↦ nW + k * nZ) (fun _ ↦ branch) ell =
      RoundedParameters.branchScale branch ell -
        RoundedParameters.branchScale branch f + (nW + k * nZ) := by
  cases branch
  · simp [ProfileReduction.selectedOffsetOrder,
      ProfileReduction.offsetAffineOrder, ProfileReduction.firstAffineOrder,
      RoundedParameters.branchScale]
  · simp [ProfileReduction.selectedOffsetOrder,
      ProfileReduction.offsetAffineOrder, ProfileReduction.secondAffineOrder,
      RoundedParameters.branchScale]
    omega

/-- The augmentation order is independent of the outer switching time.
Thus every window transported above lands in the single rounded affine
order selected for this `ell`, including the one-copy/two-copy branch and
the `k`-dependent bounded offset. -/
lemma augmentationOrder_crowd_eq_selectedAssemblyOrder
    {n scale nW ell K : ℕ} {alpha aDisc aDiv b cW c₀ delta₀ : ℝ}
    {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i : ℕ) (hi : i ≤ nW) (branch : Bool)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (nD nZ : ℕ)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell) :
    Augmentation.augmentationOrder (Q.W i) S.U0 nD nZ S.k =
      ProfileReduction.selectedOffsetOrder
        (OuterAssembly.deletionSize c₀ n)
        (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
        (fun _ ↦ branch) ell := by
  rw [show ProfileReduction.selectedOffsetOrder
      (OuterAssembly.deletionSize c₀ n)
      (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
      (fun _ ↦ branch) ell =
        RoundedParameters.branchScale branch ell -
          RoundedParameters.branchScale branch
            (OuterAssembly.deletionSize c₀ n) +
          (OuterAssembly.deletionSize cW n +
            S.k * OuterAssembly.augmentationSize delta₀
              (OuterAssembly.deletionSize c₀ n) S.k) by
    simpa [OuterAssembly.assemblyOffset, OuterAssembly.deletionSize] using
      selectedOffsetOrder_eq_branchScale_sub_add
        (OuterAssembly.deletionSize c₀ n)
        (OuterAssembly.deletionSize cW n)
        (OuterAssembly.augmentationSize delta₀
          (OuterAssembly.deletionSize c₀ n) S.k)
        S.k ell branch hf]
  rw [Augmentation.augmentationOrder, Q.card_W hi, hU0, hnD, hnZ]
  have hbranch := RoundedParameters.branchScale_mono
    (double := branch) hf
  rw [Nat.mul_comm
    (OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k) S.k]
  omega

/-- Window-probability transport all the way to the selected rounded order
consumed by `PointwiseWindows`. -/
theorem one_fourth_le_layerProbability_selectedWindowGood_of_innerWindowGood_crowd
    {n scale nW ell K nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ : ℝ} {branch : Bool}
    {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (i : ℕ) (hi : i ≤ nW)
    (center : ℕ → Finset (Fin n) → ℝ) (radius L : ℝ)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
        (Q.crowd i) nZ L (center i D) radius D)) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (WindowGood
        (Augmentation.fixedOrderEdgeValues G
          (ProfileReduction.selectedOffsetOrder
            (OuterAssembly.deletionSize c₀ n)
            (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
            (fun _ ↦ branch) ell))
        center radius L i) := by
  have horder := augmentationOrder_crowd_eq_selectedAssemblyOrder
    Q i hi branch hU0 hnW nD nZ hnD hnZ hf
  rw [← horder]
  exact one_fourth_le_layerProbability_windowGood_of_innerWindowGood_crowd
    Q i nD nZ hi center radius L i hprob

/-! ## Selecting actual window witnesses for one shared deletion -/

/-- Output of the common-deletion averaging step, with all existential
window witnesses chosen simultaneously after the one deletion is fixed. -/
structure SharedWindowSelection {V J : Type*} [Fintype V]
    (U : Finset V) (d : ℕ) (I : Finset J)
    (spectrum : Finset ℕ)
    (center : J → Finset V → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice U d → ℝ) (B : ℝ) where
  deletion : Erdos88.Fourier.BoolSlice U d
  marked : Finset J
  marked_subset : marked ⊆ I
  marked_large :
    (1 / 8 : ℝ) * I.card ≤ (marked.card : ℝ)
  error_le : error deletion ≤ 8 * B
  piece : J → Finset ℕ
  piece_subset : ∀ j ∈ marked, piece j ⊆ spectrum
  piece_large : ∀ j ∈ marked, L ≤ ((piece j).card : ℝ)
  in_window : ∀ j ∈ marked, ∀ e ∈ piece j,
    |(e : ℝ) - center j (Augmentation.boolSliceDeletion U d deletion)| ≤
      radius

lemma SharedWindowSelection.marked_nonempty
    {V J : Type*} [Fintype V]
    {U : Finset V} {d : ℕ} {I : Finset J}
    {spectrum : Finset ℕ}
    {center : J → Finset V → ℝ} {radius L : ℝ}
    {error : Erdos88.Fourier.BoolSlice U d → ℝ} {B : ℝ}
    (T : SharedWindowSelection U d I spectrum center radius L error B)
    (hI : I.Nonempty) : T.marked.Nonempty := by
  rw [← Finset.card_pos]
  have hIcard : (0 : ℝ) < I.card := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hpositive : (0 : ℝ) < (1 / 8 : ℝ) * I.card := by positivity
  have hmarkedReal : (0 : ℝ) < T.marked.card :=
    hpositive.trans_le T.marked_large
  exact_mod_cast hmarkedReal

/-- On the full switching-time interval, the common-deletion selector
retains at least one eighth of the `nW` transitions (indeed it retains one
eighth of the `nW + 1` states). -/
lemma SharedWindowSelection.one_eighth_mul_le_marked_of_range
    {V : Type*} [Fintype V]
    {U : Finset V} {d nW : ℕ}
    {spectrum : Finset ℕ}
    {center : ℕ → Finset V → ℝ} {radius L : ℝ}
    {error : Erdos88.Fourier.BoolSlice U d → ℝ} {B : ℝ}
    (T : SharedWindowSelection U d (Finset.range (nW + 1))
      spectrum center radius L error B) :
    (1 / 8 : ℝ) * nW ≤ (T.marked.card : ℝ) := by
  calc
    (1 / 8 : ℝ) * nW ≤ (1 / 8 : ℝ) * (nW + 1) := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast Nat.le_succ nW
      · norm_num
    _ = (1 / 8 : ℝ) * (Finset.range (nW + 1)).card := by simp
    _ ≤ (T.marked.card : ℝ) := T.marked_large

/-- The selector's global `L¹` error bound remains valid after restricting
to, and increasingly enumerating, the marked successful times. -/
lemma SharedWindowSelection.sum_marked_centerError_le
    {V : Type*} [Fintype V]
    {U : Finset V} {d nW : ℕ}
    {spectrum : Finset ℕ}
    {center : ℕ → Finset V → ℝ} {radius L : ℝ}
    {error : Erdos88.Fourier.BoolSlice U d → ℝ} {B : ℝ}
    (T : SharedWindowSelection U d (Finset.range (nW + 1))
      spectrum center radius L error B)
    (idealCenter : ℕ → ℝ)
    (herror_def : ∀ omega,
      error omega =
        ∑ i ∈ Finset.range (nW + 1),
          |center i (Augmentation.boolSliceDeletion U d omega) -
            idealCenter i|) :
    (∑ i ∈ Finset.range (markedLast T.marked + 1),
      |markedReindex T.marked
        (fun t ↦ center t
            (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t)
        0 i|) ≤ 8 * B := by
  have hnonempty : T.marked.Nonempty :=
    T.marked_nonempty ⟨0, by simp⟩
  calc
    (∑ i ∈ Finset.range (markedLast T.marked + 1),
      |markedReindex T.marked
        (fun t ↦ center t
            (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t)
        0 i|) ≤
        ∑ i ∈ Finset.range (nW + 1),
          |center i (Augmentation.boolSliceDeletion U d T.deletion) -
            idealCenter i| :=
      sum_range_markedReindex_le_sum_range T.marked hnonempty nW
        T.marked_subset _
    _ = error T.deletion := (herror_def T.deletion).symm
    _ ≤ 8 * B := T.error_le

/-- Consecutive perturbations along the marked enumeration cost at most
`16 B`.  This is the bridge from the common-outcome first-moment bound to
the error term in the second switching/marked-packing step. -/
lemma SharedWindowSelection.sum_marked_centerError_variation_le
    {V : Type*} [Fintype V]
    {U : Finset V} {d nW : ℕ}
    {spectrum : Finset ℕ}
    {center : ℕ → Finset V → ℝ} {radius L : ℝ}
    {error : Erdos88.Fourier.BoolSlice U d → ℝ} {B : ℝ}
    (T : SharedWindowSelection U d (Finset.range (nW + 1))
      spectrum center radius L error B)
    (idealCenter : ℕ → ℝ)
    (herror_def : ∀ omega,
      error omega =
        ∑ i ∈ Finset.range (nW + 1),
          |center i (Augmentation.boolSliceDeletion U d omega) -
            idealCenter i|) :
    let e : ℕ → ℝ := markedReindex T.marked
      (fun t ↦ center t
          (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t) 0
    (∑ i ∈ Finset.Icc 1 (markedLast T.marked), |e i - e (i - 1)|) ≤
      16 * B := by
  dsimp only
  calc
    (∑ i ∈ Finset.Icc 1 (markedLast T.marked),
      |markedReindex T.marked
          (fun t ↦ center t
              (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t)
          0 i -
        markedReindex T.marked
          (fun t ↦ center t
              (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t)
          0 (i - 1)|) ≤
        2 * ∑ i ∈ Finset.range (markedLast T.marked + 1),
          |markedReindex T.marked
            (fun t ↦ center t
                (Augmentation.boolSliceDeletion U d T.deletion) - idealCenter t)
            0 i| :=
      sum_abs_sub_le_two_sum_abs _ _
    _ ≤ 2 * (8 * B) := by
      gcongr
      exact T.sum_marked_centerError_le idealCenter herror_def
    _ = 16 * B := by ring

/-- Deterministic handoff from the one-deletion selection to the exact
`PointwiseWindows` object.  The centre in this theorem is the *actual*
deletion-dependent centre.  Consequently an `L¹` perturbation estimate can
be charged through `r` before applying marked packing; no pointwise error
bound or change of deletion set is hidden in this constructor. -/
theorem SharedWindowSelection.nonempty_pointwiseWindows_of_markedPacking
    {V : Type*} [Fintype V]
    {U : Finset V} {deletionSize n nW K ell k : ℕ}
    {cW c₀ delta₀ bIndex dPiece : ℝ} {branch : Bool}
    {spectra : ℕ → Finset ℕ}
    {center : ℕ → Finset V → ℝ} {radius L : ℝ}
    {error : Erdos88.Fourier.BoolSlice U deletionSize → ℝ} {B : ℝ}
    (T : SharedWindowSelection U deletionSize (Finset.range (nW + 1))
      (spectra
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c₀ n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n k)
          (fun _ ↦ branch) ell))
      center radius L error B)
    (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (r : ℕ → ℝ) {s R : ℝ}
    (hs : 0 < s) (hR : 0 < R)
    (hr : ∀ u ∈ Finset.Icc 1 nW, 0 ≤ r u)
    (hgrowth : ∀ {j q : ℕ}, j < q → q ≤ nW →
      ((q - j : ℕ) : ℝ) * s -
          ∑ u ∈ Finset.Ioc j q, r u ≤
        center q (Augmentation.boolSliceDeletion U deletionSize T.deletion) -
          center j (Augmentation.boolSliceDeletion U deletionSize T.deletion))
    (herror : ∑ u ∈ Finset.Icc 1 nW, r u ≤
      (1 / 8 : ℝ) / 2 * nW * s)
    (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * nW) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece spectra ell) := by
  obtain ⟨W, hWcard, hWpiece⟩ :=
    OuterSwitching.exists_separatedWindows_of_markedPacking
      (spectra
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c₀ n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n k)
          (fun _ ↦ branch) ell))
      (fun i ↦ center i
        (Augmentation.boolSliceDeletion U deletionSize T.deletion))
      r T.piece nW n hs hR (show (0 : ℝ) < 1 / 8 by norm_num) hr
      (by intro j q hjq hqn; exact hgrowth hjq hqn)
      T.marked T.marked_subset
      T.one_eighth_mul_le_marked_of_range herror hradius hseparate
      (by intro i hi e he; exact T.in_window i hi e he)
      (by intro i hi; exact T.piece_subset i hi)
      (by
        intro i hi
        exact hpieceScale.trans (T.piece_large i hi))
  refine ⟨{
    k := k
    branch := branch
    k_pos := hkpos
    k_le := hkle
    windows := W
    index_large := hindex.trans hWcard
    piece_large := hWpiece }⟩

/-- The common-outcome theorem with its existential window witnesses
retained.  Every hypothesis is a finite probability or expectation fact;
the graph-facing theorem below discharges them using the partial and full
exposure estimates. -/
theorem exists_sharedWindowSelection
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (U : Finset V) (d : ℕ) (I : Finset J)
    (spectrum : Finset ℕ)
    (center : J → Finset V → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice U d → ℝ) (B : ℝ)
    [Nonempty (Erdos88.Fourier.BoolSlice U d)]
    [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint U d)]
    (hB : 0 < B)
    (hgood : ∀ j ∈ I, (1 / 4 : ℝ) ≤
      NestedUniform.layerProbability U d
        (WindowGood spectrum center radius L j))
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    Nonempty (SharedWindowSelection U d I spectrum center radius L error B) := by
  classical
  obtain ⟨omega, hcount, herror⟩ :=
    Augmentation.exists_shared_deletion_one_eighth_good_and_error_le_eight
      U d I (WindowGood spectrum center radius L) error B hB hgood
        herror_nonneg herror_mean
  let D := Augmentation.boolSliceDeletion U d omega
  let good : J → Prop := fun j ↦ WindowGood spectrum center radius L j D
  let marked : Finset J := I.filter good
  let piece : J → Finset ℕ := fun j ↦
    if hj : good j then Classical.choose hj else ∅
  have hpiece (j : J) (hj : good j) :
      piece j ⊆ spectrum ∧ L ≤ ((piece j).card : ℝ) ∧
        ∀ e ∈ piece j, |(e : ℝ) - center j D| ≤ radius := by
    simpa only [piece, hj, ↓reduceDIte] using Classical.choose_spec hj
  refine ⟨{
    deletion := omega
    marked := marked
    marked_subset := Finset.filter_subset _ _
    marked_large := ?_
    error_le := herror
    piece := piece
    piece_subset := ?_
    piece_large := ?_
    in_window := ?_ }⟩
  · rw [show marked.card =
        CollisionCounting.eventCount I
          (fun j omega ↦ WindowGood spectrum center radius L j
            (Augmentation.boolSliceDeletion U d omega)) omega by rfl]
    exact hcount
  · intro j hj
    exact (hpiece j (Finset.mem_filter.mp hj).2).1
  · intro j hj
    exact (hpiece j (Finset.mem_filter.mp hj).2).2.1
  · intro j hj e he
    exact (hpiece j (Finset.mem_filter.mp hj).2).2.2 e he

/-- Concrete graph-facing shared-deletion composition.  A witnessed
`1/4` augmentation-window probability at every state of one crowded path
is converted to one common deletion and simultaneous fixed-order window
witnesses on at least one eighth of the states.  There are no abstract
outer events or independent per-time choices in the conclusion. -/
theorem exists_sharedWindowSelection_of_crowd_innerWindowGood
    {n scale nW ell K nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ : ℝ} {branch : Bool}
    {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (center : ℕ → Finset (Fin n) → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice S.U0 nD → ℝ) (B : ℝ)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hwindowProbability : ∀ i ≤ nW,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
          (Q.crowd i) nZ L (center i D) radius D))
    (hB : 0 < B)
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    Nonempty (SharedWindowSelection S.U0 nD (Finset.range (nW + 1))
      (Augmentation.fixedOrderEdgeValues G
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c₀ n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
          (fun _ ↦ branch) ell))
      center radius L error B) := by
  let : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint S.U0 nD) :=
    SliceMoments.nonempty_booleanSlicePoint S.U0 nD (by omega)
  let E := Augmentation.boolSliceEquivBooleanSlicePoint S.U0 nD
  let : Nonempty (Erdos88.Fourier.BoolSlice S.U0 nD) :=
    E.nonempty_congr.mpr inferInstance
  apply exists_sharedWindowSelection S.U0 nD (Finset.range (nW + 1))
    (Augmentation.fixedOrderEdgeValues G
      (ProfileReduction.selectedOffsetOrder
        (OuterAssembly.deletionSize c₀ n)
        (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
        (fun _ ↦ branch) ell))
    center radius L error B hB
  · intro i hi
    have hi' : i ≤ nW := by simpa using Finset.mem_range.mp hi
    exact one_fourth_le_layerProbability_selectedWindowGood_of_innerWindowGood_crowd
      Q i hi' center radius L hU0 hnW hnD hnZ hf
        (hwindowProbability i hi')
  · exact herror_nonneg
  · exact herror_mean

/-- Correct first-switching form of the shared selector.  The ordinal
`j ≤ m` is sent to a separated original switching time `time j`; hence the
error expectation is summed over only `m + 1` states, not over all `nW + 1`
raw switches. -/
theorem exists_sharedWindowSelection_of_crowd_subsequence_innerWindowGood
    {n scale nW ell K m nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ : ℝ} {branch : Bool}
    {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ → ℕ) (htime : ∀ j ≤ m, time j ≤ nW)
    (center : ℕ → Finset (Fin n) → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice S.U0 nD → ℝ) (B : ℝ)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hwindowProbability : ∀ j ≤ m,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W (time j)) S.U0
          (Q.crowd (time j)) nZ L (center j D) radius D))
    (hB : 0 < B)
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    Nonempty (SharedWindowSelection S.U0 nD (Finset.range (m + 1))
      (Augmentation.fixedOrderEdgeValues G
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c₀ n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
          (fun _ ↦ branch) ell))
      center radius L error B) := by
  let : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint S.U0 nD) :=
    SliceMoments.nonempty_booleanSlicePoint S.U0 nD (by omega)
  let E := Augmentation.boolSliceEquivBooleanSlicePoint S.U0 nD
  let : Nonempty (Erdos88.Fourier.BoolSlice S.U0 nD) :=
    E.nonempty_congr.mpr inferInstance
  apply exists_sharedWindowSelection S.U0 nD (Finset.range (m + 1))
    (Augmentation.fixedOrderEdgeValues G
      (ProfileReduction.selectedOffsetOrder
        (OuterAssembly.deletionSize c₀ n)
        (fun _ ↦ OuterAssembly.assemblyOffset cW c₀ delta₀ n S.k)
        (fun _ ↦ branch) ell))
    center radius L error B hB
  · intro j hj
    have hj' : j ≤ m := by simpa using Finset.mem_range.mp hj
    have ht := htime j hj'
    have hp := one_fourth_le_layerProbability_windowGood_of_innerWindowGood_crowd
      Q (time j) nD nZ ht center radius L j (hwindowProbability j hj')
    have horder := augmentationOrder_crowd_eq_selectedAssemblyOrder
      Q (time j) ht branch hU0 hnW nD nZ hnD hnZ hf
    simpa only [horder] using hp
  · exact herror_nonneg
  · exact herror_mean

/-- End-to-end finite integration on a fixed crowded path.  The only
probabilistic input is the concrete graph window probability that the
large- and bounded-`nZ` exposure theorems supply; the common deletion,
marked-state density, actual window witnesses, and marked packing are all
constructed here. -/
theorem nonempty_pointwiseWindows_of_crowd_innerWindowGood
    {n scale nW ell K k nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ bIndex dPiece : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (center : ℕ → Finset (Fin n) → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice S.U0 nD → ℝ) (B : ℝ)
    (r : Erdos88.Fourier.BoolSlice S.U0 nD → ℕ → ℝ)
    {s R : ℝ}
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hwindowProbability : ∀ i ≤ nW,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W i) S.U0
          (Q.crowd i) nZ L (center i D) radius D))
    (hB : 0 < B)
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B)
    (hs : 0 < s) (hR : 0 < R)
    (hr : ∀ omega, ∀ u ∈ Finset.Icc 1 nW, 0 ≤ r omega u)
    (hgrowth : ∀ omega, ∀ {j q : ℕ}, j < q → q ≤ nW →
      ((q - j : ℕ) : ℝ) * s -
          ∑ u ∈ Finset.Ioc j q, r omega u ≤
        center q (Augmentation.boolSliceDeletion S.U0 nD omega) -
          center j (Augmentation.boolSliceDeletion S.U0 nD omega))
    (hpackingError : ∀ omega, error omega ≤ 8 * B →
      ∑ u ∈ Finset.Icc 1 nW, r omega u ≤
        (1 / 8 : ℝ) / 2 * nW * s)
    (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * nW) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  subst k
  obtain ⟨T⟩ := exists_sharedWindowSelection_of_crowd_innerWindowGood
    Q center radius L error B hfeasible hU0 hnW hnD hnZ hf
      hwindowProbability hB herror_nonneg herror_mean
  exact T.nonempty_pointwiseWindows_of_markedPacking S.k_pos
    S.k_le (r T.deletion) hs hR (hr T.deletion)
      (by intro j q hjq hqn; exact hgrowth T.deletion hjq hqn)
      (hpackingError T.deletion T.error_le) hradius hseparate
      hpieceScale hindex

/-- End-to-end finite integration on a first separated switching
subsequence.  This is the finite theorem used by the eventual assembly. -/
theorem nonempty_pointwiseWindows_of_crowd_subsequence_innerWindowGood
    {n scale nW ell K k m nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ bIndex dPiece : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ → ℕ) (htime : ∀ j ≤ m, time j ≤ nW)
    (center : ℕ → Finset (Fin n) → ℝ) (radius L : ℝ)
    (error : Erdos88.Fourier.BoolSlice S.U0 nD → ℝ) (B : ℝ)
    (r : Erdos88.Fourier.BoolSlice S.U0 nD → ℕ → ℝ)
    {s R : ℝ}
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hwindowProbability : ∀ j ≤ m,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W (time j)) S.U0
          (Q.crowd (time j)) nZ L (center j D) radius D))
    (hB : 0 < B)
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B)
    (hs : 0 < s) (hR : 0 < R)
    (hr : ∀ omega, ∀ u ∈ Finset.Icc 1 m, 0 ≤ r omega u)
    (hgrowth : ∀ omega, ∀ {j q : ℕ}, j < q → q ≤ m →
      ((q - j : ℕ) : ℝ) * s -
          ∑ u ∈ Finset.Ioc j q, r omega u ≤
        center q (Augmentation.boolSliceDeletion S.U0 nD omega) -
          center j (Augmentation.boolSliceDeletion S.U0 nD omega))
    (hpackingError : ∀ omega, error omega ≤ 8 * B →
      ∑ u ∈ Finset.Icc 1 m, r omega u ≤
        (1 / 8 : ℝ) / 2 * m * s)
    (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * m) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  subst k
  obtain ⟨T⟩ :=
    exists_sharedWindowSelection_of_crowd_subsequence_innerWindowGood
      Q time htime center radius L error B hfeasible hU0 hnW hnD hnZ hf
        hwindowProbability hB herror_nonneg herror_mean
  exact T.nonempty_pointwiseWindows_of_markedPacking S.k_pos
    S.k_le (r T.deletion) hs hR (hr T.deletion)
      (by intro j q hjq hqn; exact hgrowth T.deletion hjq hqn)
      (hpackingError T.deletion T.error_le) hradius hseparate
      hpieceScale hindex

/-- Finite first-switching endpoint with the valid raw-increment error
charge specialized internally.  The caller supplies the separated ideal
gaps and the concrete expectation bound; the ordinal error function,
telescoping growth inequality, and partition of raw errors are constructed
here. -/
theorem nonempty_pointwiseWindows_of_crowd_subsequence_rawIncrementError
    {n scale nW ell K k m nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ bIndex dPiece : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    (Q : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ → ℕ)
    (htimeBound : ∀ j ≤ m, time j ≤ nW)
    (htimeMono : ∀ u, 1 ≤ u → u ≤ m → time (u - 1) ≤ time u)
    (htimeZero : time 0 = 0)
    (rawCenter : ℕ → Finset (Fin n) → ℝ) (idealCenter : ℕ → ℝ)
    (radius L B : ℝ) {s R : ℝ}
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (hwindowProbability : ∀ j ≤ m,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G (Q.W (time j)) S.U0
          (Q.crowd (time j)) nZ L (rawCenter (time j) D) radius D))
    (hB : 0 < B)
    (herrorMean :
      Erdos88.Concentration.uniformExpectation
        (fun omega : Erdos88.Fourier.BoolSlice S.U0 nD ↦
          ∑ i ∈ Finset.Icc 1 nW,
            |OuterSwitchingPath.rawIncrementError
              (fun t ↦ rawCenter t
                (Augmentation.boolSliceDeletion S.U0 nD omega))
              idealCenter i|) ≤ B)
    (hidealStep : ∀ u, 1 ≤ u → u ≤ m →
      s ≤ idealCenter (time u) - idealCenter (time (u - 1)))
    (hs : 0 < s) (hR : 0 < R)
    (hpackingBudget : 8 * B ≤ (1 / 8 : ℝ) / 2 * m * s)
    (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * m) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  let error : Erdos88.Fourier.BoolSlice S.U0 nD → ℝ := fun omega ↦
    ∑ i ∈ Finset.Icc 1 nW,
      |OuterSwitchingPath.rawIncrementError
        (fun t ↦ rawCenter t
          (Augmentation.boolSliceDeletion S.U0 nD omega))
        idealCenter i|
  let r : Erdos88.Fourier.BoolSlice S.U0 nD → ℕ → ℝ := fun omega u ↦
    OuterSwitchingPath.separatedIntervalError time
      (OuterSwitchingPath.rawIncrementError
        (fun t ↦ rawCenter t
          (Augmentation.boolSliceDeletion S.U0 nD omega)) idealCenter) u
  apply nonempty_pointwiseWindows_of_crowd_subsequence_innerWindowGood
    Q time htimeBound (fun j D ↦ rawCenter (time j) D) radius L error B r
      hk hkpos hkle hfeasible hU0 hnW hnD hnZ hf hwindowProbability hB
  · intro omega
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · exact herrorMean
  · exact hs
  · exact hR
  · intro omega u hu
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · intro omega j q hjq hqm
    exact OuterSwitchingPath.actual_growth_of_rawIncrementError time
      (fun t ↦ rawCenter t
        (Augmentation.boolSliceDeletion S.U0 nD omega)) idealCenter
      htimeMono hidealStep hjq hqm
  · intro omega homega
    calc
      (∑ u ∈ Finset.Icc 1 m, r omega u) ≤
          ∑ i ∈ Finset.Icc 1 nW,
            |OuterSwitchingPath.rawIncrementError
              (fun t ↦ rawCenter t
                (Augmentation.boolSliceDeletion S.U0 nD omega))
              idealCenter i| :=
        OuterSwitchingPath.sum_separatedRawIncrementError_le time
          (fun t ↦ rawCenter t
            (Augmentation.boolSliceDeletion S.U0 nD omega)) idealCenter
          htimeMono htimeZero (htimeBound m le_rfl)
      _ = error omega := rfl
      _ ≤ 8 * B := homega
      _ ≤ (1 / 8 : ℝ) / 2 * m * s := hpackingBudget
  · exact hradius
  · exact hseparate
  · exact hpieceScale
  · exact hindex

/-! ## Canonical centres on a scheduled crowded path -/

/--
All first-switching bookkeeping after the construction of a scheduled
crowd.  The theorem chooses the separated subsequence, proves the valid
raw-switch `L¹` estimate on the common deletion slice, and invokes the
shared-deletion/marked-packing endpoint above.  Thus its only exposure input
is the concrete graph statement that every raw time has augmentation-window
probability at least `1/4`.

The distinction between the actual deletion-dependent centre and its ideal
centre is important here: only their *raw increments* are summed.  No false
pointwise concentration assertion for the absolute centre is used.
-/
theorem nonempty_pointwiseWindows_of_scheduled_canonical
    {n scale nW ell K k m nD nZ blockLength threshold degreeWindow
      step spread : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ bIndex dPiece lam sigma R : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : OuterSwitchingPath.ScheduledCrowdedPath S blockLength threshold
      degreeWindow step spread)
    (outerCenter radius L : ℝ)
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hnWpos : 0 < nW) (hnDpos : 0 < nD) (hm : 1 ≤ m)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (halpha : alpha = 1 - (nD : ℝ) / S.U0.card)
    (hwindowProbability : ∀ i ≤ nW,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G
          (A.crowded.W i) S.U0 (A.crowded.crowd i) nZ L
          (AugmentationCenterMoments.canonicalAugmentationCenter G
            (A.crowded.W i) S.U0 D nZ
            (degreeInto G (A.crowded.W i) (A.crowded.anchor i))
            S.d0 outerCenter)
          radius D))
    (hsigma : 0 < sigma)
    (hlam : lam + (nZ : ℝ) * |(S.dPlus : ℝ) - S.dMinus| ≤
      aDisc * scale * Real.sqrt scale)
    (hmotion : (m : ℝ) *
        (OuterSwitchingPath.weightedStepBound S + nZ * step + sigma) +
      (nW / blockLength : ℕ) *
        (OuterSwitchingPath.weightedStepBound S +
          nZ * (spread + step)) ≤ lam)
    (hpackingBudget :
      8 * (nW * (2 * Real.sqrt nD)) ≤
        (1 / 8 : ℝ) / 2 * m * sigma)
    (hR : 0 < R) (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / sigma⌉₊ + 2 : ℕ)) * m) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  obtain ⟨idx, hidx, hidxZero, hidxLast, hgap⟩ :=
    A.exists_separatedSwitchingSubsequence hnWpos hm hsigma hlam hmotion
  let time : ℕ → ℕ := fun j ↦
    if hj : j < m + 1 then idx ⟨j, hj⟩ else nW
  have htime_apply {j : ℕ} (hj : j ≤ m) : time j = idx ⟨j, by omega⟩ := by
    simp only [time, show j < m + 1 by omega, ↓reduceDIte]
  have htimeBound : ∀ j ≤ m, time j ≤ nW := by
    intro j hj
    calc
      time j = idx ⟨j, by omega⟩ := htime_apply hj
      _ ≤ idx (Fin.last m) := hidx.monotone (Fin.le_last _)
      _ = nW := hidxLast
  have htimeMono : ∀ u, 1 ≤ u → u ≤ m → time (u - 1) ≤ time u := by
    intro u hu1 hum
    rw [htime_apply (by omega), htime_apply hum]
    apply hidx.monotone
    exact_mod_cast (show u - 1 ≤ u by omega)
  have htimeZero : time 0 = 0 := by
    rw [htime_apply (Nat.zero_le m)]
    exact hidxZero
  let rawCenter : ℕ → Finset (Fin n) → ℝ := fun i D ↦
    AugmentationCenterMoments.canonicalAugmentationCenter G
      (A.crowded.W i) S.U0 D nZ
      (degreeInto G (A.crowded.W i) (A.crowded.anchor i))
      S.d0 outerCenter
  let idealCenter : ℕ → ℝ := fun i ↦
    AugmentationCenterMoments.canonicalAugmentationIdeal G alpha S.U0
      (A.crowded.W i) nZ
      (degreeInto G (A.crowded.W i) (A.crowded.anchor i)) S.d0
  have hidealStep : ∀ u, 1 ≤ u → u ≤ m →
      sigma ≤ idealCenter (time u) - idealCenter (time (u - 1)) := by
    intro u hu1 hum
    let j : Fin m := ⟨u - 1, by omega⟩
    have hj := hgap j
    have hj' : sigma ≤
        A.crowded.center nZ (idx ⟨u, by omega⟩) -
          A.crowded.center nZ (idx ⟨u - 1, by omega⟩) := by
      convert hj using 1 <;> congr 2 <;> apply congrArg idx <;>
        apply Fin.ext <;> simp [j] <;> omega
    rw [htime_apply hum, htime_apply (by omega)]
    have hcenter (t : ℕ) : idealCenter t =
        A.crowded.center nZ t + (nZ : ℝ) * alpha * S.d0 := by
      dsimp only [idealCenter,
        AugmentationCenterMoments.canonicalAugmentationIdeal,
        OuterSwitchingPath.CrowdedPath.center]
    rw [hcenter, hcenter]
    linarith
  have hDle : nD ≤ S.U0.card := by omega
  have hdisjoint : ∀ i, Disjoint (A.crowded.W i) S.U0 :=
    A.crowded.disjoint_W_U0
  have hexchange : ∀ i < nW,
      ((A.crowded.W i \ A.crowded.W (i + 1)).card ≤ 1) ∧
        ((A.crowded.W (i + 1) \ A.crowded.W i).card ≤ 1) := by
    intro i hi
    rw [A.crowded.W_eq]
    exact ⟨A.crowded.raw.sdiff_succ_card_le_one hi,
      A.crowded.raw.succ_sdiff_card_le_one hi⟩
  have hmean :
      Erdos88.Concentration.uniformExpectation
        (fun omega : Erdos88.Fourier.BoolSlice S.U0 nD ↦
          ∑ i ∈ Finset.Icc 1 nW,
            |OuterSwitchingPath.rawIncrementError
              (fun t ↦ rawCenter t
                (Augmentation.boolSliceDeletion S.U0 nD omega))
              idealCenter i|) ≤ nW * (2 * Real.sqrt nD) := by
    simpa only [rawCenter, idealCenter] using
      AugmentationCenterMoments.uniformExpectation_sum_abs_rawIncrementError_canonical_le
        G S.U0 A.crowded.W nZ nD nW
          (fun i ↦ degreeInto G (A.crowded.W i) (A.crowded.anchor i))
          S.d0 outerCenter alpha hDle hdisjoint halpha hexchange
  have hB : (0 : ℝ) < nW * (2 * Real.sqrt nD) := by
    have hnWreal : (0 : ℝ) < nW := by exact_mod_cast hnWpos
    have hsqrt : 0 < Real.sqrt nD := Real.sqrt_pos.2 (by exact_mod_cast hnDpos)
    positivity
  apply nonempty_pointwiseWindows_of_crowd_subsequence_rawIncrementError
    A.crowded time htimeBound htimeMono htimeZero rawCenter idealCenter
      radius L (nW * (2 * Real.sqrt nD)) hk hkpos hkle hfeasible hU0
      hnW hnD hnZ hf
  · intro j hj
    simpa only [rawCenter] using hwindowProbability (time j) (htimeBound j hj)
  · exact hB
  · exact hmean
  · exact hidealStep
  · exact hsigma
  · exact hR
  · exact hpackingBudget
  · exact hradius
  · exact hseparate
  · exact hpieceScale
  · exact hindex

/--
The outer-concentration and crowd-schedule stages, composed with
`nonempty_pointwiseWindows_of_scheduled_canonical`.  The supplied
`OuterBounds` record contains all analytic union-bound and pigeonhole
estimates; this theorem turns it into an actual scheduled path.  Its sole
non-numerical remaining premise is the graph exposure theorem at every
time of the constructed crowd.
-/
theorem nonempty_pointwiseWindows_of_outerBounds_canonical
    {n scale nW ell K k m nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ bIndex dPiece eta
      matchingCoeff boundaryCoeff lam sigma R : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (O : AugmentationScales.OuterBounds K n eta cW
      matchingCoeff boundaryCoeff)
    (outerCenter radius L : ℝ)
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hKpos : 0 < K) (hnWpos : 0 < nW) (hnDpos : 0 < nD)
    (hnWupper : (nW : ℝ) ≤ cW * n)
    (hmatching : matchingCoeff * (n : ℝ) ^ (3 / 4 : ℝ) ≤
      S.matching.card)
    (hm : 1 ≤ m)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (halpha : alpha = 1 - (nD : ℝ) / S.U0.card)
    (hwindowProbability : ∀
      A : OuterSwitchingPath.ScheduledCrowdedPath S
        (AugmentationScales.blockLength n) (AugmentationScales.threshold n)
        (AugmentationScales.window eta n) (2 * K)
        (AugmentationScales.spread n),
      ∀ i ≤ nW,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G
          (A.crowded.W i) S.U0 (A.crowded.crowd i) nZ L
          (AugmentationCenterMoments.canonicalAugmentationCenter G
            (A.crowded.W i) S.U0 D nZ
            (degreeInto G (A.crowded.W i) (A.crowded.anchor i))
            S.d0 outerCenter)
          radius D))
    (hsigma : 0 < sigma)
    (hlam : lam + (nZ : ℝ) * |(S.dPlus : ℝ) - S.dMinus| ≤
      aDisc * scale * Real.sqrt scale)
    (hmotion : (m : ℝ) *
        (OuterSwitchingPath.weightedStepBound S + nZ * (2 * K) + sigma) +
      (nW / AugmentationScales.blockLength n : ℕ) *
        (OuterSwitchingPath.weightedStepBound S +
          nZ * (AugmentationScales.spread n + 2 * K)) ≤ lam)
    (hpackingBudget :
      8 * (nW * (2 * Real.sqrt nD)) ≤
        (1 / 8 : ℝ) / 2 * m * sigma)
    (hR : 0 < R) (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hpieceScale : dPiece * n ≤ L)
    (hindex : bIndex * Real.sqrt n ≤
      (1 / 8 : ℝ) / (2 * (⌈R / sigma⌉₊ + 2 : ℕ)) * m) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  have hmatchingCard : S.matching.card ≤ n := by
    have hmul : S.matching.card ≤ S.matching.card * S.k := by
      nlinarith [S.k_pos]
    calc
      S.matching.card ≤ S.matching.card * S.k := hmul
      _ = S.A.card := S.card_A_eq_mul.symm
      _ ≤ n := by
        simpa using (Finset.card_le_univ S.A)
  have hunion : (((nW + 1) * S.matching.card : ℕ) : ℝ) *
      (2 * Real.exp (-(AugmentationScales.outerError n) ^ 2 /
        (2 * (2 * nW) * (2 * K : ℕ) ^ 2))) < 1 := by
    simpa [AugmentationScales.outerFailure] using
      O.concentration nW S.matching.card hnWpos hnWupper hmatchingCard
  obtain ⟨Q⟩ :=
    StructuralOuterConcentration.exists_uniformDegreeControlledOrderings
      S hnWpos hKpos (AugmentationScales.outerError n)
        (by dsimp [AugmentationScales.outerError]; positivity) hunion
  have hspan : 2 * AugmentationScales.outerError n + 2 ≤
      (AugmentationScales.span n : ℝ) := by
    dsimp only [AugmentationScales.span, AugmentationScales.spread]
    push_cast
    gcongr
    exact Nat.le_ceil _
  have hcount : ∀ q : Fin (Crowd.canonicalBlockCount nW
      (AugmentationScales.blockLength n)),
      (Crowd.canonicalBlockLast nW (AugmentationScales.blockLength n) q /
            AugmentationScales.stride K eta n + 1) *
          Crowd.natBucketCount (AugmentationScales.span n)
            (AugmentationScales.width K eta n) *
          AugmentationScales.threshold n < Fintype.card (OuterSwitchingPath.Particle S) := by
    intro q
    simpa [OuterSwitchingPath.Particle] using
      O.schedule_count nW S.matching.card hmatching q
  obtain ⟨A⟩ :=
    OuterConcentrationPathBridge.exists_scheduledCrowdedPath_of_uniformDegreeControlledOrderings
      Q (by dsimp [AugmentationScales.outerError]; positivity)
      (AugmentationScales.blockLength n) (AugmentationScales.span n)
      (AugmentationScales.width K eta n) (AugmentationScales.threshold n)
      (AugmentationScales.window eta n) (AugmentationScales.stride K eta n)
      O.rounding.block_pos hspan O.rounding.width_pos
      O.rounding.stride_pos (by simpa [AugmentationScales.travel] using
        O.rounding.radius) hcount
  exact nonempty_pointwiseWindows_of_scheduled_canonical A outerCenter
    radius L hk hkpos hkle hnWpos hnDpos hm hfeasible hU0 hnW hnD hnZ hf
      halpha (hwindowProbability A) hsigma hlam (by
        simpa [AugmentationScales.spread] using hmotion) hpackingBudget hR
      hradius hseparate hpieceScale hindex

/--
The six-field asymptotic numerical package specialized to the canonical
outer switching construction.  This is the last deterministic wrapper
before the graph-exposure estimate: all motion, shared-deletion, packing,
separation, and output-scale inequalities are read directly from
`FinalNumericBounds`.
-/
theorem nonempty_pointwiseWindows_of_finalNumericBounds
    {n nW ell K k nD nZ : ℕ}
    {alpha aDisc aDiv b cW c₀ delta₀ eta matchingCoeff boundaryCoeff
      lambdaCoeff sigmaCoeff RCoeff radiusCoeff a₂ : ℝ}
    {branch : Bool} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G n nW ell K alpha aDisc aDiv b}
    (outerCenter radius L : ℝ)
    (F : AugmentationScales.FinalNumericBounds K n nW nD nZ S.dMinus
      S.dPlus eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff
      sigmaCoeff RCoeff radiusCoeff
      (OuterSwitchingPath.weightedStepBound S) radius a₂ delta₀ c₀ L)
    (hk : k = S.k) (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (hKpos : 0 < K) (hnWpos : 0 < nW) (hnDpos : 0 < nD)
    (hsigmaCoeff : 0 < sigmaCoeff) (hRCoeff : 0 < RCoeff)
    (hnWupper : (nW : ℝ) ≤ cW * n)
    (hmatching : matchingCoeff * (n : ℝ) ^ (3 / 4 : ℝ) ≤
      S.matching.card)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hU0 : S.U0.card = RoundedParameters.branchScale branch ell)
    (hnW : nW = OuterAssembly.deletionSize cW n)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize delta₀
      (OuterAssembly.deletionSize c₀ n) S.k)
    (hf : OuterAssembly.deletionSize c₀ n ≤ ell)
    (halpha : alpha = 1 - (nD : ℝ) / S.U0.card)
    (hwindowProbability : ∀
      A : OuterSwitchingPath.ScheduledCrowdedPath S
        (AugmentationScales.blockLength n) (AugmentationScales.threshold n)
        (AugmentationScales.window eta n) (2 * K)
        (AugmentationScales.spread n),
      ∀ i ≤ nW,
      (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
        (fun D ↦ AugmentationGraphFull.innerWindowGood G
          (A.crowded.W i) S.U0 (A.crowded.crowd i) nZ L
          (AugmentationCenterMoments.canonicalAugmentationCenter G
            (A.crowded.W i) S.U0 D nZ
            (degreeInto G (A.crowded.W i) (A.crowded.anchor i))
            S.d0 outerCenter)
          radius D))
    (hradius : 0 ≤ radius) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ delta₀
      (AugmentationScales.finalIndexCoeff K eta RCoeff sigmaCoeff)
      (AugmentationScales.finalPieceCoeff K a₂ delta₀ c₀)
      (Augmentation.fixedOrderEdgeValues G) ell) := by
  apply nonempty_pointwiseWindows_of_outerBounds_canonical F.outer.outer
    outerCenter radius L hk hkpos hkle hKpos hnWpos hnDpos hnWupper
    hmatching F.outer.outer.rounding.stride_pos hfeasible hU0 hnW hnD hnZ hf
    halpha hwindowProbability
  · change 0 < sigmaCoeff * n
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
        F.outer.outer.rounding.order_pos)
    positivity
  · exact F.outer.endpoint_loss
  · exact F.outer.motion_boundary
  · exact F.outer.packing_budget
  · change 0 < RCoeff * n
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
        F.outer.outer.rounding.order_pos)
    positivity
  · exact hradius
  · exact F.outer.radius_separation
  · exact F.piece_scale
  · exact F.outer.index_scale

/--
The eventual scalar packages specialized to one time of a scheduled crowded
path.  This theorem contains the entire partial-to-full exposure invocation;
its hypotheses are finite numerical bounds and structural inequalities, not
probability or event callbacks.
-/
theorem one_fourth_le_layerProbability_innerWindowGood_of_finalBounds
    {n nW ell K degreeWindow time nD nZ nS : ℕ}
    {alpha aDisc aDiv b : ℝ} {G : SimpleGraph (Fin n)}
    {S : StructuralWitness G n nW ell K alpha aDisc aDiv b}
    (path : OuterSwitchingPath.CrowdedPath S
      (AugmentationScales.threshold n) degreeWindow)
    (htime : time ≤ nW)
    {a₀ theta Qpartial C LH c₀ deltaUpper gapCoeff cBalance innerTheta qGeom
      badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff
      mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff badDegreeCoeff
      pieceCoeff outputCoeff a₂ : ℝ}
    (hC : C = AntiConcentration.variancePointMassConstant cBalance
      (theta ^ 2 / 4) (2 * K))
    (htheta : 0 < theta) (hQpartial : 0 < Qpartial) (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hnormalized : theta * S.U0.card ≤ aDiv * n)
    (hselected : cBalance * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : cBalance * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (PF : AugmentationScales.PartialExposureFinalBounds K n nD nZ nS
      S.U0.card a₀ theta Qpartial C LH c₀ deltaUpper gapCoeff)
    (IF : AugmentationInnerScales.InnerExposureFinalBounds K nD nZ nS
      degreeWindow a₀ theta Qpartial LH gapCoeff cBalance innerTheta
      (Qpartial * Real.sqrt nD) qGeom badGeomCoeff sigmaCoeff globalCoeff
      qDegree meanRadius lambdaCoeff mCoeff energyCoeff qScale kappaCoeff
      badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff a₂) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (path.W time) S.U0
        (path.crowd time) nZ
        (AugmentationInnerScales.exposureOutput outputCoeff nD)
        (AugmentationCenterMoments.canonicalAugmentationCenter G
          (path.W time) S.U0 D nZ
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          (AugmentationExposureAssembly.partialDegreeCenter S.U0 nD S.d0))
        (AugmentationScales.exposureGlobalRadius globalCoeff nD) D) := by
  let s₀ := AsymptoticThresholds.partialMatchingSize a₀ nD
  let divDev := AugmentationInnerScales.diversityDeviation theta nD
  let degreeDev := Qpartial * Real.sqrt nD
  let tDegree := AugmentationScales.partialDegreeThreshold a₀ nD
  let tCollision := AugmentationScales.partialCollisionThreshold LH nD
  have hfamilies : 2 * s₀ ≤ (path.crowd time).card :=
    PF.family_fit.trans (path.crowd_large time htime)
  have hdivDev : 0 < divDev := by
    dsimp only [divDev, AugmentationInnerScales.diversityDeviation]
    have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnD
    positivity
  have hdegreeDev : 0 < degreeDev := by
    dsimp only [degreeDev]
    have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnD
    positivity
  have hbudget :
      let pDiv := AugmentationGraphPartial.outerLinearFailure nD K divDev
      let pDegree :=
        AugmentationGraphPartial.outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            cBalance (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv + s₀ * pDegree / tDegree +
          s₀ * pDegree / tDegree +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4 := by
    simpa only [s₀, divDev, degreeDev, tDegree, tCollision, hC,
      AugmentationInnerScales.diversityDeviation] using
      PF.risk.risk_budget
  have P' : AugmentationExposureAssembly.PartialExposureCertificate G S.U0
      (path.crowd time) K nD s₀ S.d0 cBalance theta divDev degreeDev
      tDegree tDegree tCollision := by
    apply partialExposureCertificate_of_crowd path time nD s₀ cBalance theta
      divDev degreeDev tDegree tDegree tCollision htime hnD hfeasible
      hfamilies hnormalized IF.cBalance_pos IF.cBalance_le_half htheta
      hselected hunselected hdivDev hdegreeDev
    · exact PF.risk.degreeThreshold_pos
    · exact PF.risk.degreeThreshold_pos
    · exact PF.risk.collisionThreshold_pos
    · exact hbudget
  have N := IF.toCrowdLargeNumericBounds
    (S := S) (path := path) (time := time)
  exact AugmentationExposureCrowdFinal.one_fourth_le_layerProbability_innerWindowGood_large_of_numeric
    S path time htime nD nS nZ
      (AsymptoticThresholds.partialMatchingSize a₀ nD)
      (AugmentationScales.partialSelectionGap gapCoeff nD)
      (AugmentationScales.partialBadBudget a₀ nD)
      (AugmentationScales.partialSelectionEdgeBudget LH nD)
      (AugmentationInnerScales.exposureSteps mCoeff nD)
      cBalance theta (AugmentationInnerScales.diversityDeviation theta nD)
      (Qpartial * Real.sqrt nD)
      (AugmentationScales.partialDegreeThreshold a₀ nD)
      (AugmentationScales.partialDegreeThreshold a₀ nD)
      (AugmentationScales.partialCollisionThreshold LH nD)
      innerTheta (AugmentationScales.geometricThreshold qGeom K nS nD)
      (AugmentationInnerScales.candidateDegreeThreshold qDegree nD)
      meanRadius (AugmentationInnerScales.exposureLambda lambdaCoeff nD)
      (AugmentationInnerScales.collisionThreshold energyCoeff nD) qScale
      (AugmentationInnerScales.switchingCutoff kappaCoeff nD)
      (AugmentationScales.innerExposureSigma sigmaCoeff nD)
      (AugmentationScales.innerExposureRadius K nS degreeWindow
        (AugmentationInnerScales.candidateDegreeThreshold qDegree nD)
        (Qpartial * Real.sqrt nD))
      (AugmentationScales.exposureGlobalRadius globalCoeff nD)
      (AugmentationScales.geometricBadBudget badGeomCoeff nD)
      (AugmentationInnerScales.collisionBadBudget badCollisionCoeff nD)
      (AugmentationInnerScales.degreeBadBudget badDegreeCoeff nD)
      (AugmentationInnerScales.collisionEdgeBudget energyCoeff nD)
      (AugmentationInnerScales.exposurePiece pieceCoeff nD)
      (AugmentationInnerScales.exposureOutput outputCoeff nD) P' N

/-!
## Eventual structural-witness endpoint

The theorem below performs the constant choices in their genuine dependency
order: first the outer deletion density, then the partial and inner exposure
constants, then the crowd window, and only finally the outer separation
radius.  Consequently its public boundary contains no schedule, event,
probability, or numerical side condition.
-/

theorem exists_eventual_pointwiseWindows_of_structuralWitness
    {K : ℕ} (hK : 0 < K)
    {cW c aDisc aDiv bStruct : ℝ}
    (hcW : 0 < cW) (hc : 0 < c) (haDisc : 0 < aDisc)
    (haDiv : 0 < aDiv) (hbStruct : 0 < bStruct) :
    ∃ c₀ δ₀ δZ bIndex dPiece : ℝ,
      0 < c₀ ∧ 6 * c₀ ≤ c ∧ 0 < δ₀ ∧ δ₀ ≤ δZ ∧
      0 < bIndex ∧ 0 < dPiece ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        ∀ ell ∈ RoundedParameters.outerParameterInterval c n,
          Nonempty (StructuralWitness G n
            (OuterAssembly.deletionSize cW n) ell K
            (1 - (OuterAssembly.deletionSize c₀ n : ℝ) / ell)
            aDisc aDiv bStruct) →
          Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ δ₀
            bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell) := by
  obtain ⟨A⟩ :=
    AugmentationOuterConstants.exists_earlyOuterCoefficientChoice
      hK hcW hc haDisc hbStruct
  let cBalance : ℝ := A.c₀ / (4 * c)
  let theta : ℝ := aDiv / (8 * c)
  have hcBalance : 0 < cBalance := by
    dsimp only [cBalance]
    exact div_pos A.c₀_pos (mul_pos (by norm_num) hc)
  have hcBalanceHalf : cBalance ≤ 1 / 2 := by
    dsimp only [cBalance]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * c)).2
    nlinarith [A.c₀_small]
  have htheta : 0 < theta := by
    dsimp only [theta]
    exact div_pos haDiv (mul_pos (by norm_num) hc)
  let Cpartial : ℝ :=
    AntiConcentration.variancePointMassConstant cBalance
      (theta ^ 2 / 4) (2 * K)
  have hCpartial : 0 ≤ Cpartial := by
    dsimp only [Cpartial]
    exact (AntiConcentration.variancePointMassConstant_pos hcBalance
      (by positivity) (by omega)).le
  let partialCap : ℝ := 1 / (Real.sqrt (2 * A.c₀) + 1)
  have hpartialCap : 0 < partialCap := by
    dsimp only [partialCap]
    positivity
  obtain ⟨a₀, Qpartial, LH, ha₀, ha₀Cap, hQpartial, hLH,
      hpartialRisk⟩ :=
    AugmentationScales.exists_partialExposureRiskConstants hK hpartialCap
      hCpartial
  have hfamilyCoeff : a₀ * Real.sqrt (2 * A.c₀) ≤ 1 := by
    have hsqrt : 0 ≤ Real.sqrt (2 * A.c₀) := Real.sqrt_nonneg _
    calc
      a₀ * Real.sqrt (2 * A.c₀) ≤
          partialCap * Real.sqrt (2 * A.c₀) := by gcongr
      _ ≤ 1 := by
        dsimp only [partialCap]
        rw [one_div, inv_mul_eq_div]
        apply (div_le_iff₀ (by positivity :
          (0 : ℝ) < Real.sqrt (2 * A.c₀) + 1)).2
        linarith
  obtain ⟨X⟩ := nonempty_compatibleInnerScaleCoefficients
    hK ha₀ hLH A.c₀_pos
  obtain ⟨B⟩ :=
    AugmentationOuterConstants.exists_windowedOuterCoefficientChoice A hK
      hcW hc X.window_pos
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hdeltaLower : 0 < X.delta / (4 * (K : ℝ)) :=
    div_pos X.delta_pos (mul_pos (by norm_num) hKreal)
  obtain ⟨I⟩ :=
    AugmentationInnerScales.nonempty_innerExposureCoefficientChoice
      hK ha₀ htheta hQpartial X.gap_pos hcBalance hcBalanceHalf
      hdeltaLower X.delta_pos
      X.window_pos.le X.inner_endpoint
  let O := B.withRadius I.bounds.globalCoeff_nonneg
  have hO_c₀ : O.c₀ = A.c₀ := by
    dsimp only [O]
    exact B.c₀_eq
  have hO_eta : O.eta = B.outer.eta := rfl
  have hO_matching : O.matchingCoeff = bStruct := O.matchingCoeff_eq
  obtain ⟨Npartial, hNpartial⟩ :=
    AugmentationScales.exists_partialExposureFinalBounds hK ha₀ htheta
      hQpartial hCpartial hLH A.c₀_pos X.delta_pos X.gap_pos.le
      hpartialRisk hfamilyCoeff X.partial_turan
  obtain ⟨Ninner, hNinner⟩ :=
    AugmentationInnerScales.exists_innerExposureFinalBounds I.bounds
  obtain ⟨Nwindow, hNwindow⟩ :=
    AugmentationScales.exists_window_le_branchSqrt B.outer.eta_pos.le
      A.c₀_pos B.window_cap
  have hendpointO :
      O.lambdaCoeff + A.c₀ * K * cW * Real.sqrt (2 * A.c₀) ≤ aDisc := by
    simpa only [hO_c₀] using O.endpointCoeff
  have hmotionO :
      AugmentationScales.smallStepCoeff K O.eta *
          (cW + 4 * c + O.sigmaCoeff +
            2 * K * A.c₀ * Real.sqrt (2 * A.c₀)) +
        (cW + 4 * c + A.c₀ * Real.sqrt (2 * A.c₀)) *
          O.boundaryCoeff ≤ O.lambdaCoeff := by
    simpa only [hO_c₀] using O.motionCoeff
  have hpackingO :
      512 * cW * Real.sqrt (2 * A.c₀) ≤
        AugmentationScales.smallStepCoeff K O.eta * O.sigmaCoeff := by
    simpa only [hO_c₀] using O.packingCoeff
  have hradiusO : 4 * I.globalCoeff * A.c₀ < O.RCoeff := by
    simpa only [hO_c₀] using O.radiusCoeffSmall
  obtain ⟨Nfinal, hNfinal⟩ :=
    AugmentationScales.exists_finalNumericBounds hK hc A.c₀_pos
      A.c₀_small X.delta_pos X.delta_le_c₀ O.eta_pos hcW
      O.matchingCoeff_pos O.boundaryCoeff_pos O.sigmaCoeff_pos O.RCoeff_pos
      I.bounds.globalCoeff_nonneg hendpointO hmotionO hpackingO hradiusO
  obtain ⟨Nbranch, hNbranch⟩ :=
    AugmentationScales.exists_branchBounds hc A.c₀_pos A.c₀_small
      X.delta_pos (le_refl X.delta) hK
  obtain ⟨Nswitch, hNswitch⟩ := exists_deletionSize_pos hcW
  obtain ⟨Nlift, hNlift⟩ :=
    AsymptoticThresholds.exists_nat_rpow_ge 1
      (2 * (Ninner : ℝ) / A.c₀) (by norm_num)
  let bIndex : ℝ := AugmentationScales.finalIndexCoeff K O.eta
    O.RCoeff O.sigmaCoeff
  let dPiece : ℝ := AugmentationScales.finalPieceCoeff K I.a₂
    X.delta A.c₀
  have hbIndex : 0 < bIndex := by
    dsimp only [bIndex, AugmentationScales.finalIndexCoeff,
      AugmentationScales.smallStepCoeff]
    exact div_pos
      (div_pos O.eta_pos (mul_pos (by norm_num) (by positivity)))
      (mul_pos (by norm_num) (by positivity))
  have hdPiece : 0 < dPiece := by
    dsimp only [dPiece, AugmentationScales.finalPieceCoeff]
    exact div_pos (mul_pos (mul_pos I.a₂_pos X.delta_pos) A.c₀_pos)
      (mul_pos (by norm_num) hKreal)
  refine ⟨A.c₀, X.delta, A.c₀, bIndex, dPiece, A.c₀_pos,
    A.c₀_small, X.delta_pos, X.delta_le_c₀, hbIndex, hdPiece, ?_⟩
  let N := Npartial + Nwindow + Nfinal + Nbranch + Nswitch + Nlift + 1
  refine ⟨N, ?_⟩
  intro n hn G ell hell hS
  obtain ⟨S⟩ := hS
  have hnPartial : Npartial ≤ n := by dsimp only [N] at hn; omega
  have hnWindow : Nwindow ≤ n := by dsimp only [N] at hn; omega
  have hnFinal : Nfinal ≤ n := by dsimp only [N] at hn; omega
  have hnBranch : Nbranch ≤ n := by dsimp only [N] at hn; omega
  have hnSwitch : Nswitch ≤ n := by dsimp only [N] at hn; omega
  have hnLift : Nlift ≤ n := by dsimp only [N] at hn; omega
  have hnpos : 0 < n := by dsimp only [N] at hn; omega
  obtain ⟨branch, hU0⟩ :=
    AugmentationIntegration.StructuralWitness.exists_branch_card_U0 S
  let nW := OuterAssembly.deletionSize cW n
  let f := OuterAssembly.deletionSize A.c₀ n
  let nD := RoundedParameters.branchScale branch f
  let nZ := OuterAssembly.augmentationSize X.delta f S.k
  let nS := nZ - 1
  have Br := hNbranch n hnBranch ell hell branch S.k S.k_pos S.k_le
  have hnS : nS + 1 = nZ := by
    have hnZtwo : 2 ≤ nZ := by
      simpa only [nZ, f] using Br.augmentation_two
    dsimp only [nS]
    omega
  have hnDinner : Ninner ≤ nD := by
    have hlift := hNlift n hnLift
    rw [Real.rpow_one] at hlift
    have hscaled : (Ninner : ℝ) ≤ A.c₀ / 2 * n := by
      calc
        (Ninner : ℝ) = A.c₀ / 2 * (2 * (Ninner : ℝ) / A.c₀) := by
          field_simp [A.c₀_pos.ne']
        _ ≤ A.c₀ / 2 * n := by
          exact mul_le_mul_of_nonneg_left hlift
            (div_nonneg A.c₀_pos.le (by norm_num))
    have : (Ninner : ℝ) ≤ nD := hscaled.trans (by
      simpa only [nD, f] using Br.order_lower)
    exact_mod_cast this
  have PF := hNpartial n hnPartial nD nZ nS S.U0.card
    (by simpa only [nD, f] using Br.order_lower)
    (by simpa only [nD, f] using Br.order_upper)
    (by simpa only [nZ, nD, f] using Br.augmentation_upper)
    hnS
    (by rw [hU0]; simpa only [nD, f] using Br.feasible)
  have hdegreeWindow := hNwindow n hnWindow nD
    (by simpa only [nD, f] using Br.order_lower)
  have IF := hNinner nD hnDinner n nZ nS
    (AugmentationScales.window O.eta n) S.U0.card
    (by simpa only [nZ, nD, f] using Br.augmentation_lower)
    (by simpa only [nZ, nD, f] using Br.augmentation_upper)
    hnS
    (by simpa only [O, hO_eta] using hdegreeWindow)
    Cpartial LH A.c₀ PF
  have hbalances := branch_partial_balance hc A.c₀_pos A.c₀_small hell Br
    (nD := nD) rfl hU0
  have hnormalized := branch_normalized_diversity hc haDiv hell hU0
  have hnWpos : 0 < nW := by
    simpa only [nW] using hNswitch n hnSwitch
  have hnWupper : (nW : ℝ) ≤ cW * n := by
    simpa only [nW] using RoundedParameters.deletionSize_le hcW.le n
  have hmatchingNonempty : S.matching.Nonempty :=
    AugmentationIntegration.StructuralWitness.matching_nonempty_of_pos
      S hbStruct hnpos
  have hdegreeGap : |(S.dPlus : ℝ) - S.dMinus| ≤ K * nW :=
    AugmentationIntegration.StructuralWitness.abs_dPlus_sub_dMinus_le
      S hmatchingNonempty
  have hellpos : 0 < ell := by
    have hellBounds := (RoundedParameters.mem_outerParameterInterval hc.le).mp hell
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have : (0 : ℝ) < ell := (mul_pos hc hnreal).trans_le hellBounds.1
    exact_mod_cast this
  have halphaRatio :
      (1 - (f : ℝ) / ell) = 1 - (nD : ℝ) / S.U0.card :=
    structuralAlpha_eq_branchDeletionRatio rfl hellpos rfl hU0
  have halphaAbs : |(1 : ℝ) - (f : ℝ) / ell| ≤ 1 :=
    abs_one_sub_natRatio_le_one hellpos Br.deletion_le_parameter
  have hU0upper : (S.U0.card : ℝ) ≤ 4 * c * n := by
    rw [hU0]
    exact branchScale_outerParameter_upper hc.le hell branch
  have hweightedStep : OuterSwitchingPath.weightedStepBound S ≤
      (cW + 4 * c) * n :=
    AugmentationIntegration.StructuralWitness.weightedStepBound_le
      S halphaAbs hnWupper hU0upper
  let radius := AugmentationScales.exposureGlobalRadius I.globalCoeff nD
  let L : ℝ := AugmentationInnerScales.exposureOutput I.outputCoeff nD
  have F := hNfinal n hnFinal ell hell branch S.k S.k_pos S.k_le
    nW S.dMinus S.dPlus (OuterSwitchingPath.weightedStepBound S) radius
    I.a₂ L hnWupper hdegreeGap
    (AugmentationIntegration.StructuralWitness.weightedStepBound_nonneg S)
    hweightedStep
    (by dsimp only [radius, AugmentationScales.exposureGlobalRadius];
        exact le_rfl)
    I.bounds.a₂_nonneg
    (by simpa only [L] using IF.output_scale)
  apply nonempty_pointwiseWindows_of_finalNumericBounds
    (AugmentationExposureAssembly.partialDegreeCenter S.U0 nD S.d0)
    radius L F (k := S.k) rfl S.k_pos S.k_le hK hnWpos Br.order_pos
    O.sigmaCoeff_pos O.RCoeff_pos hnWupper
  · rw [O.matchingCoeff_eq]
    exact S.matching_large
  · rw [hU0]
    simpa only [nD, f] using Br.feasible
  · exact hU0
  · rfl
  · rfl
  · rfl
  · exact Br.deletion_le_parameter
  · simpa only [f, nD] using halphaRatio
  · intro path time htime
    apply one_fourth_le_layerProbability_innerWindowGood_of_finalBounds
      path.crowded htime (C := Cpartial) (c₀ := A.c₀)
      (deltaUpper := X.delta) (gapCoeff := X.gap)
      (hC := rfl) htheta hQpartial Br.order_pos
      (by rw [hU0]; simpa only [nD, f] using Br.feasible)
      (by simpa only [theta] using hnormalized)
      hbalances.1 hbalances.2 PF IF
  · dsimp only [radius, AugmentationScales.exposureGlobalRadius]
    exact mul_nonneg I.bounds.globalCoeff_nonneg (by positivity)

end


end AugmentationIntegration
end Erdos636
