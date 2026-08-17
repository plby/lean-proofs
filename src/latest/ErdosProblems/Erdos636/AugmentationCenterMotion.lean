/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AugmentationIdentity
import ErdosProblems.Erdos636.CrowdScheduleBridge

/-!
# Deterministic motion of augmentation centres

This file is deliberately independent of the probabilistic augmentation
modules.  It provides two bridges used by the final assembly.

* A raw outer switch exchanges at most one vertex in each direction.  Hence
  the weighted structural score changes by at most
  `nW + |alpha| * |U0|`.  Adding the crowd anchor term costs `nZ * step` on
  a regular transition and `nZ * (spread + step)` at a block boundary.
* If an actual centre differs from its ideal centre by raw *increment*
  errors, the error assigned to a separated transition is the sum of the
  absolute raw errors over the corresponding interval.  These intervals
  telescope.  Thus their total mass is at most the original raw `L¹` mass,
  exactly as required by marked packing.

Keeping these deterministic statements here avoids an import cycle between
the crowd schedule and the graph-specific exposure estimates.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace OuterSwitchingPath

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The raw path exchanges one vertex -/

lemma permutationPrefix_mono (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) {r s : ℕ}
    (hrs : r ≤ s) (hs : s ≤ I.card) :
    permutationPrefix I sigma r ⊆ permutationPrefix I sigma s := by
  rw [permutationPrefix_eq_of_le I sigma (hrs.trans hs),
    permutationPrefix_eq_of_le I sigma hs]
  intro x hx
  simp only [Erdos88.BooleanSlices.signedSlicePositiveSupport,
    Finset.mem_map] at hx ⊢
  obtain ⟨j, _hj, rfl⟩ := hx
  let k : Fin s := ⟨j, lt_of_lt_of_le j.isLt hrs⟩
  refine ⟨k, Finset.mem_univ _, ?_⟩
  change (Erdos88.BooleanSlices.decodedCoordinateEmbedding
      I (Finset.equivFin I).symm sigma) _ =
    (Erdos88.BooleanSlices.decodedCoordinateEmbedding
      I (Finset.equivFin I).symm sigma) _
  congr 1

lemma RawPath.sdiff_succ_card_le_one
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) {i : ℕ} (hi : i < nW) :
    (P.W i \ P.W (i + 1)).card ≤ 1 := by
  let M : Finset V :=
    permutationPrefix S.Wminus P.minusPermutation (nW - i)
  let M' : Finset V :=
    permutationPrefix S.Wminus P.minusPermutation (nW - (i + 1))
  let A : Finset V := permutationPrefix S.Wplus P.plusPermutation i
  let A' : Finset V :=
    permutationPrefix S.Wplus P.plusPermutation (i + 1)
  have hMM' : M' ⊆ M := by
    apply permutationPrefix_mono
    · omega
    · rw [S.card_Wminus]
      omega
  have hAA' : A ⊆ A' := by
    apply permutationPrefix_mono
    · omega
    · simpa only [S.card_Wplus] using Nat.succ_le_iff.mpr hi
  have hsub : P.W i \ P.W (i + 1) ⊆ M \ M' := by
    intro x hx
    have hxold := (Finset.mem_sdiff.mp hx).1
    have hxnew := (Finset.mem_sdiff.mp hx).2
    rw [RawPath.W] at hxold hxnew
    change x ∈ M ∪ A at hxold
    change x ∉ M' ∪ A' at hxnew
    rcases Finset.mem_union.mp hxold with hxM | hxA
    · exact Finset.mem_sdiff.mpr
        ⟨hxM, fun hxM' ↦ hxnew (Finset.mem_union_left _ hxM')⟩
    · exact (hxnew (Finset.mem_union_right _ (hAA' hxA))).elim
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sdiff_of_subset hMM']
  have hM : M.card = nW - i := by
    exact card_permutationPrefix_of_le _ _ (by rw [S.card_Wminus]; omega)
  have hM' : M'.card = nW - (i + 1) := by
    exact card_permutationPrefix_of_le _ _ (by rw [S.card_Wminus]; omega)
  rw [hM, hM']
  omega

lemma RawPath.succ_sdiff_card_le_one
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) {i : ℕ} (hi : i < nW) :
    (P.W (i + 1) \ P.W i).card ≤ 1 := by
  let M : Finset V :=
    permutationPrefix S.Wminus P.minusPermutation (nW - i)
  let M' : Finset V :=
    permutationPrefix S.Wminus P.minusPermutation (nW - (i + 1))
  let A : Finset V := permutationPrefix S.Wplus P.plusPermutation i
  let A' : Finset V :=
    permutationPrefix S.Wplus P.plusPermutation (i + 1)
  have hMM' : M' ⊆ M := by
    apply permutationPrefix_mono
    · omega
    · rw [S.card_Wminus]
      omega
  have hAA' : A ⊆ A' := by
    apply permutationPrefix_mono
    · omega
    · simpa only [S.card_Wplus] using Nat.succ_le_iff.mpr hi
  have hsub : P.W (i + 1) \ P.W i ⊆ A' \ A := by
    intro x hx
    have hxnew := (Finset.mem_sdiff.mp hx).1
    have hxold := (Finset.mem_sdiff.mp hx).2
    rw [RawPath.W] at hxnew hxold
    change x ∈ M' ∪ A' at hxnew
    change x ∉ M ∪ A at hxold
    rcases Finset.mem_union.mp hxnew with hxM' | hxA'
    · exact (hxold (Finset.mem_union_left _ (hMM' hxM'))).elim
    · exact Finset.mem_sdiff.mpr
        ⟨hxA', fun hxA ↦ hxold (Finset.mem_union_right _ hxA)⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sdiff_of_subset hAA']
  have hA : A.card = i := by
    exact card_permutationPrefix_of_le _ _
      (by simpa only [S.card_Wplus] using hi.le)
  have hA' : A'.card = i + 1 := by
    exact card_permutationPrefix_of_le _ _
      (by simpa only [S.card_Wplus] using Nat.succ_le_iff.mpr hi)
  rw [hA, hA']
  omega

/-! ## Weighted-score motion -/

lemma inducedEdges_eq_zero_of_card_le_one (G : SimpleGraph V)
    (A : Finset V) (hA : A.card ≤ 1) : Erdos88.inducedEdges G A = 0 := by
  have hedge : Erdos88.inducedEdges G A ≤ A.card.choose 2 := by
    rw [Erdos88.inducedEdges_eq_card_edgeFinset_induce]
    simpa using (G.induce (A : Set V)).card_edgeFinset_le_card_choose_two
  have hchoose : A.card.choose 2 = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  omega

lemma inducedEdges_le_add_card_of_sdiff_card_le_one
    (G : SimpleGraph V) (S T : Finset V)
    (hST : (S \ T).card ≤ 1) :
    (Erdos88.inducedEdges G S : ℝ) ≤
      Erdos88.inducedEdges G T + S.card := by
  let C := S ∩ T
  let D := S \ T
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro x hxC hxD
    exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxC).2
  have hUnion : C ∪ D = S := by
    ext x
    simp only [C, D, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hD : D.card ≤ 1 := hST
  have hcross : (G.interedges C D).card ≤ S.card := by
    calc
      (G.interedges C D).card ≤ C.card * D.card :=
        G.card_interedges_le_mul C D
      _ ≤ C.card * 1 := Nat.mul_le_mul_left C.card hD
      _ = C.card := by simp
      _ ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hid := inducedEdges_union_of_disjoint G hCD
  rw [hUnion, inducedEdges_eq_zero_of_card_le_one G D hD] at hid
  have hCT : Erdos88.inducedEdges G C ≤ Erdos88.inducedEdges G T := by
    rw [Erdos88.inducedEdges_eq_card_filter,
      Erdos88.inducedEdges_eq_card_filter]
    apply Finset.card_le_card
    intro e he
    have he' := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
      he'.trans Finset.inter_subset_right⟩
  exact_mod_cast (by omega)

lemma abs_inducedEdges_sub_le_of_sdiff_card_le_one
    (G : SimpleGraph V) (S T : Finset V) (N : ℕ)
    (hS : S.card ≤ N) (hT : T.card ≤ N)
    (hST : (S \ T).card ≤ 1) (hTS : (T \ S).card ≤ 1) :
    |(Erdos88.inducedEdges G S : ℝ) - Erdos88.inducedEdges G T| ≤ N := by
  have hforward := inducedEdges_le_add_card_of_sdiff_card_le_one G S T hST
  have hback := inducedEdges_le_add_card_of_sdiff_card_le_one G T S hTS
  have hS' : (S.card : ℝ) ≤ N := by exact_mod_cast hS
  have hT' : (T.card : ℝ) ≤ N := by exact_mod_cast hT
  rw [abs_le]
  constructor <;> linarith

lemma crossEdges_le_add_card_of_sdiff_card_le_one
    (G : SimpleGraph V) (U S T : Finset V)
    (hST : (S \ T).card ≤ 1) :
    (crossEdges G U S : ℝ) ≤ crossEdges G U T + U.card := by
  let C := S ∩ T
  let D := S \ T
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro x hxC hxD
    exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxC).2
  have hUnion : C ∪ D = S := by
    ext x
    simp only [C, D, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hC : crossEdges G U C ≤ crossEdges G U T := by
    simp only [crossEdges, degreeInto]
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.card_le_card
    intro y hy
    exact Erdos88.mem_neighborsIn.mpr
      ⟨Finset.inter_subset_right (Erdos88.mem_neighborsIn.mp hy).1,
        (Erdos88.mem_neighborsIn.mp hy).2⟩
  have hD : crossEdges G U D ≤ U.card := by
    change degreeInto G D U ≤ U.card
    calc
      degreeInto G D U ≤ U.card * D.card :=
        degreeInto_le_card_mul_card G D U
      _ ≤ U.card * 1 := Nat.mul_le_mul_left U.card hST
      _ = U.card := by simp
  rw [crossEdges, ← hUnion, degreeInto_union_of_disjoint G hCD]
  exact_mod_cast (Nat.add_le_add hC hD).trans (by omega)

lemma abs_crossEdges_sub_le_of_sdiff_card_le_one
    (G : SimpleGraph V) (U S T : Finset V)
    (hST : (S \ T).card ≤ 1) (hTS : (T \ S).card ≤ 1) :
    |(crossEdges G U S : ℝ) - crossEdges G U T| ≤ U.card := by
  have hforward := crossEdges_le_add_card_of_sdiff_card_le_one G U S T hST
  have hback := crossEdges_le_add_card_of_sdiff_card_le_one G U T S hTS
  rw [abs_le]
  constructor <;> linarith

/-- Coarse but scale-correct motion of the weighted score under one vertex
exchange. -/
lemma abs_weightedScore_sub_le_of_one_exchange
    (G : SimpleGraph V) (alpha : ℝ) (U S T : Finset V) (N : ℕ)
    (hS : S.card ≤ N) (hT : T.card ≤ N)
    (hST : (S \ T).card ≤ 1) (hTS : (T \ S).card ≤ 1) :
    |weightedScore G alpha U S - weightedScore G alpha U T| ≤
      N + |alpha| * U.card := by
  have he := abs_inducedEdges_sub_le_of_sdiff_card_le_one
    G S T N hS hT hST hTS
  have hc := abs_crossEdges_sub_le_of_sdiff_card_le_one G U S T hST hTS
  calc
    |weightedScore G alpha U S - weightedScore G alpha U T| =
        |((Erdos88.inducedEdges G S : ℝ) - Erdos88.inducedEdges G T) +
          alpha * ((crossEdges G U S : ℝ) - crossEdges G U T)| := by
      simp only [weightedScore]
      ring_nf
    _ ≤ |(Erdos88.inducedEdges G S : ℝ) - Erdos88.inducedEdges G T| +
        |alpha| * |(crossEdges G U S : ℝ) - crossEdges G U T| := by
      calc
        _ ≤ |(Erdos88.inducedEdges G S : ℝ) - Erdos88.inducedEdges G T| +
            |alpha * ((crossEdges G U S : ℝ) - crossEdges G U T)| :=
          abs_add_le _ _
        _ = _ := by rw [abs_mul]
    _ ≤ N + |alpha| * U.card := by gcongr

/-- The deterministic weighted-score contribution to one raw switch. -/
def weightedStepBound
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) : ℝ :=
  nW + |alpha| * S.U0.card

lemma CrowdedPath.abs_weightedScore_succ_sub_le
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i < nW) :
    |weightedScore G alpha S.U0 (Q.W (i + 1)) -
      weightedScore G alpha S.U0 (Q.W i)| ≤ weightedStepBound S := by
  apply abs_weightedScore_sub_le_of_one_exchange G alpha S.U0
    (Q.W (i + 1)) (Q.W i) nW
  · simp [Q.card_W (Nat.succ_le_iff.mpr hi)]
  · simp [Q.card_W hi.le]
  · rw [Q.W_eq]
    exact Q.raw.succ_sdiff_card_le_one hi
  · rw [Q.W_eq]
    exact Q.raw.sdiff_succ_card_le_one hi

/-! ## Scheduled centre bounds and first switching -/

/-- One-step centre bound when the anchor moves by at most `motion`. -/
lemma CrowdedPath.abs_center_succ_sub_le
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window nZ motion : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i < nW)
    (hdegree : |(degreeInto G (Q.W (i + 1)) (Q.anchor (i + 1)) : ℤ) -
      degreeInto G (Q.W i) (Q.anchor i)| ≤ motion) :
    |Q.center nZ (i + 1) - Q.center nZ i| ≤
      weightedStepBound S + nZ * motion := by
  have hscore := Q.abs_weightedScore_succ_sub_le hi
  have hdegreeReal :
      |(degreeInto G (Q.W (i + 1)) (Q.anchor (i + 1)) : ℝ) -
        degreeInto G (Q.W i) (Q.anchor i)| ≤ motion := by
    exact_mod_cast hdegree
  calc
    |Q.center nZ (i + 1) - Q.center nZ i| =
        |(weightedScore G alpha S.U0 (Q.W (i + 1)) -
            weightedScore G alpha S.U0 (Q.W i)) +
          (nZ : ℝ) *
            ((degreeInto G (Q.W (i + 1)) (Q.anchor (i + 1)) : ℝ) -
              degreeInto G (Q.W i) (Q.anchor i))| := by
      simp only [CrowdedPath.center]
      push_cast
      ring_nf
    _ ≤ |weightedScore G alpha S.U0 (Q.W (i + 1)) -
          weightedScore G alpha S.U0 (Q.W i)| +
        (nZ : ℝ) *
          |(degreeInto G (Q.W (i + 1)) (Q.anchor (i + 1)) : ℝ) -
            degreeInto G (Q.W i) (Q.anchor i)| := by
      calc
        _ ≤ |weightedScore G alpha S.U0 (Q.W (i + 1)) -
              weightedScore G alpha S.U0 (Q.W i)| +
            |(nZ : ℝ) *
              ((degreeInto G (Q.W (i + 1)) (Q.anchor (i + 1)) : ℝ) -
                degreeInto G (Q.W i) (Q.anchor i))| := abs_add_le _ _
        _ = _ := by
          have hnZabs : |(nZ : ℝ)| = (nZ : ℝ) :=
            abs_of_nonneg (by positivity)
          rw [abs_mul]
          rw [hnZabs]
    _ ≤ weightedStepBound S + nZ * motion := by gcongr

lemma ScheduledCrowdedPath.center_regular_abs_le
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : ScheduledCrowdedPath S blockLength threshold window step spread)
    (nZ : ℕ) {i : ℕ} (hi : i < nW)
    (hib : i ∉ Crowd.canonicalBoundary nW blockLength) :
    |A.crowded.center nZ (i + 1) - A.crowded.center nZ i| ≤
      weightedStepBound S + nZ * step :=
  A.crowded.abs_center_succ_sub_le hi
    (A.regular_degree_motion i hi hib)

lemma ScheduledCrowdedPath.center_regular_increment_le
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : ScheduledCrowdedPath S blockLength threshold window step spread)
    (nZ : ℕ) {i : ℕ} (hi : i < nW)
    (hib : i ∉ Crowd.canonicalBoundary nW blockLength) :
    A.crowded.center nZ (i + 1) - A.crowded.center nZ i ≤
      weightedStepBound S + nZ * step :=
  (le_abs_self _).trans (A.center_regular_abs_le nZ hi hib)

lemma ScheduledCrowdedPath.center_boundary_abs_le
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : ScheduledCrowdedPath S blockLength threshold window step spread)
    (nZ : ℕ) {i : ℕ} (hi : i ∈ Crowd.canonicalBoundary nW blockLength) :
    |A.crowded.center nZ (i + 1) - A.crowded.center nZ i| ≤
      weightedStepBound S + nZ * (spread + step) := by
  have hit : i < nW := Finset.mem_range.mp (A.boundary_subset hi)
  simpa [Nat.cast_add] using A.crowded.abs_center_succ_sub_le (nZ := nZ) hit
    (A.boundary_degree_motion i hi)

lemma ScheduledCrowdedPath.rise_le_center_sub
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b lam : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : ScheduledCrowdedPath S blockLength threshold window step spread)
    {nZ : ℕ}
    (hlam : lam + (nZ : ℝ) * |(S.dPlus : ℝ) - S.dMinus| ≤
      aDisc * scale * Real.sqrt scale) :
    lam ≤ A.crowded.center nZ nW - A.crowded.center nZ 0 :=
  A.crowded.rise_le_center_sub hlam

/-- Complete deterministic first-switching package from a scheduled crowd.
The exceptional contribution is charged using the canonical boundary-card
bound rather than its exact cardinality. -/
theorem ScheduledCrowdedPath.exists_separatedSwitchingSubsequence
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread m nZ : ℕ}
    {alpha aDisc aDiv b lam sigma : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (A : ScheduledCrowdedPath S blockLength threshold window step spread)
    (hnW : 0 < nW) (hm : 1 ≤ m) (hsigma : 0 < sigma)
    (hlam : lam + (nZ : ℝ) * |(S.dPlus : ℝ) - S.dMinus| ≤
      aDisc * scale * Real.sqrt scale)
    (hbudget : (m : ℝ) *
        (weightedStepBound S + nZ * step + sigma) +
      (nW / blockLength : ℕ) *
        (weightedStepBound S + nZ * (spread + step)) ≤ lam) :
    ∃ idx : Fin (m + 1) → ℕ,
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = nW ∧
        ∀ j : Fin m, sigma ≤
          A.crowded.center nZ (idx j.succ) -
            A.crowded.center nZ (idx j.castSucc) := by
  let rho : ℝ := weightedStepBound S + nZ * step
  let jump : ℝ := weightedStepBound S + nZ * (spread + step)
  have hrho : 0 < rho := by
    have hnWReal : (0 : ℝ) < nW := by exact_mod_cast hnW
    dsimp only [rho, weightedStepBound]
    positivity
  have hjump : 0 ≤ jump := by
    dsimp only [jump, weightedStepBound]
    positivity
  have hboundaryBudget :
      ((Crowd.canonicalBoundary nW blockLength).card : ℝ) * jump ≤
        (nW / blockLength : ℕ) * jump := by
    gcongr
    exact_mod_cast A.boundary_card
  apply A.crowded.exists_separatedSwitchingSubsequence
    (Crowd.canonicalBoundary nW blockLength) A.boundary_subset hm hrho hsigma
      hjump (A.rise_le_center_sub hlam)
  · intro i hi hib
    exact A.center_regular_increment_le nZ hi hib
  · intro i hi
    exact A.center_boundary_abs_le nZ hi
  · calc
      (m : ℝ) * (rho + sigma) +
          ((Crowd.canonicalBoundary nW blockLength).card : ℝ) * jump ≤
        (m : ℝ) * (rho + sigma) + (nW / blockLength : ℕ) * jump :=
          by simpa [add_comm] using
            add_le_add_left hboundaryBudget ((m : ℝ) * (rho + sigma))
      _ ≤ lam := by simpa [rho, jump] using hbudget

/-! ## Raw increment errors and restriction to a separated path -/

/-- Error in the actual increment ending at raw time `i`.  The value at
`i = 0` is irrelevant, because all sums below start at one. -/
def rawIncrementError (actual ideal : ℕ → ℝ) (i : ℕ) : ℝ :=
  (actual i - actual (i - 1)) - (ideal i - ideal (i - 1))

/-- Error charged to one transition of a separated subsequence. -/
def separatedIntervalError (time : ℕ → ℕ) (rawError : ℕ → ℝ)
    (u : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc (time (u - 1)) (time u), |rawError i|

lemma sum_Ioc_sub_pred (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ioc a b, (f i - f (i - 1))) = f b - f a := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ioc_succ_top hab', ih hab']
        simp only [Nat.add_sub_cancel]
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

lemma sum_Icc_sub_pred (f : ℕ → ℝ) (m : ℕ) :
    (∑ u ∈ Finset.Icc 1 m, (f u - f (u - 1))) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

lemma sum_rawIncrementError_Ioc (actual ideal : ℕ → ℝ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ioc a b, rawIncrementError actual ideal i) =
      (actual b - actual a) - (ideal b - ideal a) := by
  simp only [rawIncrementError, Finset.sum_sub_distrib,
    sum_Ioc_sub_pred actual hab, sum_Ioc_sub_pred ideal hab]

lemma neg_sum_abs_le_sum (e : ℕ → ℝ) (I : Finset ℕ) :
    -(∑ i ∈ I, |e i|) ≤ ∑ i ∈ I, e i := by
  calc
    -(∑ i ∈ I, |e i|) = ∑ i ∈ I, -|e i| := by
      rw [Finset.sum_neg_distrib]
    _ ≤ ∑ i ∈ I, e i := Finset.sum_le_sum fun i _ ↦ neg_abs_le (e i)

/-- Consecutive ideal gaps along the separated ordinal accumulate linearly. -/
lemma ideal_growth_of_separated_steps
    (time : ℕ → ℕ) (ideal : ℕ → ℝ) {m : ℕ} {sigma : ℝ}
    (hstep : ∀ u, 1 ≤ u → u ≤ m →
      sigma ≤ ideal (time u) - ideal (time (u - 1)))
    {j q : ℕ} (hjq : j < q) (hqm : q ≤ m) :
    ((q - j : ℕ) : ℝ) * sigma ≤
      ideal (time q) - ideal (time j) := by
  have hsum :
      ∑ u ∈ Finset.Ioc j q, sigma ≤
        ∑ u ∈ Finset.Ioc j q,
          (ideal (time u) - ideal (time (u - 1))) := by
    apply Finset.sum_le_sum
    intro u hu
    have hu' := Finset.mem_Ioc.mp hu
    exact hstep u (by omega) (hu'.2.trans hqm)
  rw [sum_Ioc_sub_pred (fun u ↦ ideal (time u)) hjq.le] at hsum
  simpa [Nat.cast_sub hjq.le, mul_comm] using hsum

/-- Exact marked-packing growth inequality obtained from raw increment
errors.  No pointwise control of the centre error is assumed. -/
lemma actual_growth_of_rawIncrementError
    (time : ℕ → ℕ) (actual ideal : ℕ → ℝ)
    {m : ℕ} {sigma : ℝ}
    (htime : ∀ u, 1 ≤ u → u ≤ m → time (u - 1) ≤ time u)
    (hstep : ∀ u, 1 ≤ u → u ≤ m →
      sigma ≤ ideal (time u) - ideal (time (u - 1)))
    {j q : ℕ} (hjq : j < q) (hqm : q ≤ m) :
    ((q - j : ℕ) : ℝ) * sigma -
        ∑ u ∈ Finset.Ioc j q,
          separatedIntervalError time (rawIncrementError actual ideal) u ≤
      actual (time q) - actual (time j) := by
  have hideal := ideal_growth_of_separated_steps time ideal hstep hjq hqm
  have hrawTime : time j ≤ time q := by
    exact Nat.le_induction (m := j)
      (P := fun b _ ↦ b ≤ q → time j ≤ time b)
      (fun _ ↦ le_rfl)
      (fun b hjb ih hbq ↦
        (ih (by omega)).trans
          (htime (b + 1) (by omega) (hbq.trans hqm)))
      q hjq.le le_rfl
  have herrorLower := neg_sum_abs_le_sum
    (rawIncrementError actual ideal) (Finset.Ioc (time j) (time q))
  rw [sum_rawIncrementError_Ioc actual ideal hrawTime] at herrorLower
  have hpartition :
      ∑ u ∈ Finset.Ioc j q,
          separatedIntervalError time (rawIncrementError actual ideal) u =
        ∑ i ∈ Finset.Ioc (time j) (time q),
          |rawIncrementError actual ideal i| := by
    let F : ℕ → ℝ := fun t ↦
      ∑ i ∈ Finset.range (t + 1), |rawIncrementError actual ideal i|
    have hinterval (u : ℕ) (hu1 : 1 ≤ u) (hum : u ≤ m) :
        separatedIntervalError time (rawIncrementError actual ideal) u =
          F (time u) - F (time (u - 1)) := by
      have htu := htime u hu1 hum
      dsimp only [separatedIntervalError, F]
      have hset : Finset.Ioc (time (u - 1)) (time u) =
          Finset.Ico (time (u - 1) + 1) (time u + 1) := by
        ext i
        simp
      rw [hset, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right htu 1)]
    calc
      _ = ∑ u ∈ Finset.Ioc j q,
          (F (time u) - F (time (u - 1))) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hu' := Finset.mem_Ioc.mp hu
        exact hinterval u (by omega) (hu'.2.trans hqm)
      _ = F (time q) - F (time j) :=
        sum_Ioc_sub_pred (fun u ↦ F (time u)) hjq.le
      _ = _ := by
        have hset : Finset.Ioc (time j) (time q) =
            Finset.Ico (time j + 1) (time q + 1) := by
          ext i
          simp
        rw [hset, Finset.sum_Ico_eq_sub _
          (Nat.add_le_add_right hrawTime 1)]
  rw [hpartition]
  linarith

/-- The separated interval errors partition the raw error interval.  This
is the global-error estimate consumed by marked packing. -/
lemma sum_separatedIntervalError_le_raw
    (time : ℕ → ℕ) (rawError : ℕ → ℝ) {m sourceLast : ℕ}
    (htime : ∀ u, 1 ≤ u → u ≤ m → time (u - 1) ≤ time u)
    (hzero : time 0 = 0) (hlast : time m ≤ sourceLast) :
    (∑ u ∈ Finset.Icc 1 m, separatedIntervalError time rawError u) ≤
      ∑ i ∈ Finset.Icc 1 sourceLast, |rawError i| := by
  let F : ℕ → ℝ := fun t ↦ ∑ i ∈ Finset.range (t + 1), |rawError i|
  have hinterval (u : ℕ) (hu1 : 1 ≤ u) (hum : u ≤ m) :
      separatedIntervalError time rawError u =
        F (time u) - F (time (u - 1)) := by
    have htu := htime u hu1 hum
    dsimp only [separatedIntervalError, F]
    have hset : Finset.Ioc (time (u - 1)) (time u) =
        Finset.Ico (time (u - 1) + 1) (time u + 1) := by
      ext i
      simp
    rw [hset, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right htu 1)]
  calc
    (∑ u ∈ Finset.Icc 1 m, separatedIntervalError time rawError u) =
        ∑ u ∈ Finset.Icc 1 m, (F (time u) - F (time (u - 1))) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu' := Finset.mem_Icc.mp hu
      exact hinterval u hu'.1 hu'.2
    _ = F (time m) - F (time 0) :=
      sum_Icc_sub_pred (fun u ↦ F (time u)) m
    _ = ∑ i ∈ Finset.Ioc 0 (time m), |rawError i| := by
      rw [hzero]
      simp only [F]
      have hset : Finset.Ioc 0 (time m) =
          Finset.Ico 1 (time m + 1) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      rw [hset, Finset.sum_Ico_eq_sub _ (by omega)]
    _ ≤ ∑ i ∈ Finset.Ioc 0 sourceLast, |rawError i| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have hi' := Finset.mem_Ioc.mp hi
        exact Finset.mem_Ioc.mpr ⟨hi'.1, hi'.2.trans hlast⟩
      · intro i hi _hiOld
        exact abs_nonneg _
    _ = ∑ i ∈ Finset.Icc 1 sourceLast, |rawError i| := by
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      · intro i hi
        rfl

/-- Specialization to an actual/ideal centre pair. -/
lemma sum_separatedRawIncrementError_le
    (time : ℕ → ℕ) (actual ideal : ℕ → ℝ) {m sourceLast : ℕ}
    (htime : ∀ u, 1 ≤ u → u ≤ m → time (u - 1) ≤ time u)
    (hzero : time 0 = 0) (hlast : time m ≤ sourceLast) :
    (∑ u ∈ Finset.Icc 1 m,
        separatedIntervalError time (rawIncrementError actual ideal) u) ≤
      ∑ i ∈ Finset.Icc 1 sourceLast,
        |rawIncrementError actual ideal i| :=
  sum_separatedIntervalError_le_raw time
    (rawIncrementError actual ideal) htime hzero hlast

end

end OuterSwitchingPath
end Erdos636
