/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularProfileMarkedSkeleton

/-!
# Literal stopped atoms for fixed constrained profiles

The stopped successful-point event is partitioned here by the exact internal
excursion profile `m₂,...,mₙ`.  The terminal excursion count and the forced
first count are retained in each atom.  This supplies the literal event
inclusion, pairwise disjointness, measurability, and exhaustive-union facts
needed by the full complementary-skeleton construction.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AnnularProfileLiteralAtoms

noncomputable section

open AppendixFirstMoment Proposition13Assembly

/-- Read entries `2,...,n` from the full HLOZ excursion array. -/
def internalProfile {n : ℕ} (N : Fin (n + 2) → ℕ) : Profile n :=
  fun i ↦ N ⟨scaleIndex i, by
    unfold scaleIndex
    omega⟩

/-- The successful-profile conditions after fixing every internal entry to
`m`.  The initial and terminal conditions remain literal. -/
def FixedSuccessfulProfile (n : ℕ) (delta : ℝ) (m : Profile n)
    (N : Fin (n + 2) → ℕ) : Prop :=
  N ⟨1, by omega⟩ = 1 ∧
    (∀ i, N ⟨scaleIndex i, by
      unfold scaleIndex
      omega⟩ = m i) ∧
    ThickPoint.terminalLower n delta ≤ (N ⟨n + 1, by omega⟩ : ℝ) ∧
    N ⟨n + 1, by omega⟩ ≤ n ^ 3

@[simp] lemma internalProfile_apply {n : ℕ} (N : Fin (n + 2) → ℕ)
    (i : Fin (n - 1)) :
    internalProfile N i = N ⟨scaleIndex i, by
      unfold scaleIndex
      omega⟩ := rfl

lemma fixedSuccessfulProfile_internalProfile
    {n : ℕ} {delta : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n delta N) :
    FixedSuccessfulProfile n delta (internalProfile N) N := by
  refine ⟨hN.1, ?_, hN.2.2⟩
  intro i
  rfl

lemma internalProfile_isConstrained
    {n : ℕ} {delta : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n delta N) :
    IsConstrainedProfile delta (internalProfile N) := by
  intro i
  have hiLower : 2 ≤ scaleIndex i := by simp [scaleIndex]
  have hiUpper : scaleIndex i ≤ n := by
    unfold scaleIndex
    omega
  simpa [InProfileWindow, profileCenter, internalProfile] using
    (hN.2.1 ⟨scaleIndex i, by
      unfold scaleIndex
      omega⟩ hiLower hiUpper)

lemma fixedSuccessfulProfile_iff
    {n : ℕ} {delta : ℝ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (N : Fin (n + 2) → ℕ) :
    FixedSuccessfulProfile n delta m N ↔
      ThickPoint.SuccessfulProfile n delta N ∧ internalProfile N = m := by
  constructor
  · rintro ⟨hone, hentries, hterminal⟩
    have hmiddle : ∀ k : Fin (n + 2), 2 ≤ k.1 → k.1 ≤ n →
        |(N k : ℝ) - 2 * (k.1 : ℝ) ^ 2| ≤
          (k.1 : ℝ) ^ (1 + delta) := by
      intro k hk2 hkn
      let i : Fin (n - 1) := ⟨k.1 - 2, by omega⟩
      have hscale : scaleIndex i = k.1 := by
        dsimp only [i, scaleIndex]
        omega
      have hentry : N k = m i := by
        have := hentries i
        simpa only [hscale, Fin.eta] using this
      rw [hentry, ← hscale]
      simpa [InProfileWindow, profileCenter] using hm i
    refine ⟨⟨hone, hmiddle, hterminal⟩, funext fun i ↦ ?_⟩
    exact hentries i
  · rintro ⟨hN, rfl⟩
    exact fixedSuccessfulProfile_internalProfile hN

/-- Fixed-profile atom at one concrete outer-exit horizon. -/
def fixedProfileAtEvent (start scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) (m : Profile scale) : Set StepPath :=
  {omega |
    ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
      x ∈ ThickPoint.candidateBox scale ∧
      FixedSuccessfulProfile scale profileDelta m
        (ThickPoint.excursionProfile
          (shiftedWalk start omega) scale horizon x)}

/-- Literal stopped event realizing one exact internal profile. -/
def stoppedFixedProfileEvent (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) (m : Profile scale) : Set StepPath :=
  ⋃ horizon : ℕ, fixedProfileAtEvent start scale horizon profileDelta x m

lemma measurableSet_fixedProfileAtEvent
    (start scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) (m : Profile scale) :
    MeasurableSet (fixedProfileAtEvent start scale horizon profileDelta x m) := by
  change MeasurableSet ((shiftedWalk start) ⁻¹'
    {s : WalkPath |
      ThickPoint.IsOuterExitTime s scale horizon ∧
        x ∈ ThickPoint.candidateBox scale ∧
        FixedSuccessfulProfile scale profileDelta m
          (ThickPoint.excursionProfile s scale horizon x)})
  apply (measurable_shiftedWalk start)
  exact measurableSet_of_pathPrefix_dependent horizon _ fun s t hst ↦ by
    rw [ThickPoint.isOuterExitTime_congr_prefix hst]
    have hprofile := ThickPoint.excursionProfile_congr_prefix
      (n := scale) hst x
    rw [hprofile]

lemma measurableSet_stoppedFixedProfileEvent
    (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) (m : Profile scale) :
    MeasurableSet (stoppedFixedProfileEvent start scale profileDelta x m) := by
  exact MeasurableSet.iUnion fun horizon ↦
    measurableSet_fixedProfileAtEvent start scale horizon profileDelta x m

lemma stoppedFixedProfileEvent_subset
    {start scale : ℕ} {profileDelta : ℝ} {x : Point} {m : Profile scale}
    (hm : IsConstrainedProfile profileDelta m) :
    stoppedFixedProfileEvent start scale profileDelta x m ⊆
      stoppedSuccessfulPointEvent start scale profileDelta x := by
  intro omega homega
  obtain ⟨horizon, hexit, hx, hfixed⟩ := mem_iUnion.mp homega
  have hN := (fixedSuccessfulProfile_iff hm _).mp hfixed
  exact ⟨horizon, hexit, hx, hN.1⟩

private lemma outerExitTime_unique
    {s : WalkPath} {n horizon horizon' : ℕ}
    (h : ThickPoint.IsOuterExitTime s n horizon)
    (h' : ThickPoint.IsOuterExitTime s n horizon') :
    horizon = horizon' := by
  rcases lt_trichotomy horizon horizon' with hlt | heq | hgt
  · exact (h'.2 horizon hlt h.1).elim
  · exact heq
  · exact (h.2 horizon' hgt h'.1).elim

lemma stoppedFixedProfileEvent_disjoint
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    {m m' : Profile scale} (hne : m ≠ m') :
    Disjoint (stoppedFixedProfileEvent start scale profileDelta x m)
      (stoppedFixedProfileEvent start scale profileDelta x m') := by
  rw [Set.disjoint_left]
  intro omega hmAtom hm'Atom
  obtain ⟨horizon, hexit, _hx, hfixed⟩ := mem_iUnion.mp hmAtom
  obtain ⟨horizon', hexit', _hx', hfixed'⟩ := mem_iUnion.mp hm'Atom
  have heq := outerExitTime_unique hexit hexit'
  subst horizon'
  apply hne
  funext i
  exact (hfixed.2.1 i).symm.trans (hfixed'.2.1 i)

/-- Every stopped successful path belongs to the unique atom determined by
its literal internal excursion profile. -/
theorem stoppedSuccessfulPointEvent_eq_iUnion_fixedProfiles
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ m ∈ constrainedProfiles scale profileDelta,
        stoppedFixedProfileEvent start scale profileDelta x m := by
  ext omega
  constructor
  · rintro ⟨horizon, hexit, hx, hN⟩
    let m := internalProfile
      (ThickPoint.excursionProfile (shiftedWalk start omega) scale horizon x)
    simp only [mem_iUnion]
    refine ⟨m, ?_, ?_⟩
    · exact mem_constrainedProfiles.mpr (internalProfile_isConstrained hN)
    · exact mem_iUnion.mpr
        ⟨horizon, hexit, hx, fixedSuccessfulProfile_internalProfile hN⟩
  · intro homega
    simp only [mem_iUnion] at homega
    obtain ⟨m, hm, hatom⟩ := homega
    exact stoppedFixedProfileEvent_subset (mem_constrainedProfiles.mp hm) hatom

end

end Erdos1165.AnnularProfileLiteralAtoms
