/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedPreludeCode

/-!
# Literal padded factorization of one remote coarse bridge

This file cuts a genuine level-`l` first-exit word at its first visit to the
padded predecessor boundary.  The direct branch is already a prelude word;
the entered branch consists of one prelude word followed by a genuine
middle/inner excursion-count word.  All fields are literal stopped words, so
their mass product is the mass of the original coarse bridge.
-/

open Set
open scoped ENNReal

namespace Erdos1165.AsymmetricPaddedBridgeLiteralFactorization

open AlternatingConcatPrefixFree AnnularBoundaryExcursionKernel
open AnnularOffspringRenewal AnnularProfileClocks
open AsymmetricPaddedPreludeCode AsymmetricPaddedRemoteRenewal
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open PlanarPotential RealDiscFinite TerminalSequentialVisitLaw
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- First visit of either the padded predecessor boundary or the retained
outer boundary along a coarse bridge. -/
def paddedPreludeHitTime
    (n l p : ℕ) (center start endpoint : Point)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) : ℕ :=
  firstHitThrough (trajectoryFrom start (extendStoppedWord bridge.1))
    (profileInnerBoundary n (p - 1) center ∪
      profileInnerBoundary n l center) 0 bridge.1.1

theorem paddedPreludeHitTime_le
    (n l p : ℕ) (center start endpoint : Point)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    paddedPreludeHitTime n l p center start endpoint bridge ≤ bridge.1.1 := by
  apply (firstHitThrough_le_horizon_iff _ _ 0 bridge.1.1).2
  refine ⟨bridge.1.1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, le_rfl⟩, ?_⟩⟩
  · exact Nat.zero_le _
  · exact Or.inr bridge.2.1.1

theorem paddedPreludeHitTime_mem
    (n l p : ℕ) (center start endpoint : Point)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    trajectoryFrom start (extendStoppedWord bridge.1)
        (paddedPreludeHitTime n l p center start endpoint bridge) ∈
      profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center := by
  exact firstHitThrough_mem_set_of_le _ _ 0 bridge.1.1
    (paddedPreludeHitTime_le n l p center start endpoint bridge)

/-- The two possible first-hit packages of one coarse bridge. -/
inductive PaddedPreludeSplit
    (n l p : ℕ) (center : Point)
    (start : PaddedNearPoint n l center)
    (endpoint : PaddedOuterPoint n l center)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start.1 endpoint.1) : Type
  | direct
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center) start.1 endpoint.1)
      (word_eq : first.1 = bridge.1) :
      PaddedPreludeSplit n l p center start endpoint bridge
  | entered
      (u : PaddedMiddlePoint n p center)
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center) start.1 u.1)
      (q : ℕ)
      (parent : BoundaryExcursionExitWordCode
        (profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) u.1 q endpoint.1)
      (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
        List.ofFn bridge.1.2) :
      PaddedPreludeSplit n l p center start endpoint bridge

private theorem incrementSlice_extendStoppedWord_zero_eq
    (word : StoppedWord) :
    incrementSlice (extendStoppedWord word) 0 word.1 = List.ofFn word.2 := by
  apply List.ext_get
  · simp
  · intro j hj hj'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp [incrementSlice, extendStoppedWord]

/-- Canonical literal first-hit split of a coarse bridge. -/
def paddedPreludeSplit
    {n l p : ℕ} {center : Point}
    (start : PaddedNearPoint n l center)
    (endpoint : PaddedOuterPoint n l center)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start.1 endpoint.1) :
    PaddedPreludeSplit n l p center start endpoint bridge := by
  let omega := extendStoppedWord bridge.1
  let boundary := profileInnerBoundary n (p - 1) center ∪
    profileInnerBoundary n l center
  let t := paddedPreludeHitTime n l p center start.1 endpoint.1 bridge
  have ht : t ≤ bridge.1.1 :=
    paddedPreludeHitTime_le n l p center start.1 endpoint.1 bridge
  have hspec :
      0 ≤ t ∧ trajectoryFrom start.1 omega t ∈ boundary ∧
        ∀ q < t, 0 ≤ q → trajectoryFrom start.1 omega q ∉ boundary := by
    simpa only [t, boundary, omega, paddedPreludeHitTime] using
      (firstHitThrough_spec_of_le
        (trajectoryFrom start.1 omega) boundary 0 bridge.1.1 (by
          simpa only [t, boundary, omega, paddedPreludeHitTime] using ht))
  have htmem : trajectoryFrom start.1 omega t ∈ boundary := hspec.2.1
  by_cases houter : trajectoryFrom start.1 omega t ∈
      profileInnerBoundary n l center
  · have hteq : t = bridge.1.1 := by
      apply Nat.le_antisymm ht
      by_contra hnot
      have hlt : t < bridge.1.1 := Nat.lt_of_not_ge hnot
      exact bridge.2.1.2 t hlt houter
    let first : BoundaryExitWordCode boundary start.1 endpoint.1 := by
      refine ⟨bridge.1, ?_, bridge.2.2⟩
      constructor
      · exact Or.inr bridge.2.1.1
      · intro r hr
        apply hspec.2.2 r
        · simpa only [hteq] using hr
        · exact Nat.zero_le _
    exact .direct first rfl
  · have hmiddle : trajectoryFrom start.1 omega t ∈
        profileInnerBoundary n (p - 1) center :=
      htmem.resolve_right houter
    let u : PaddedMiddlePoint n p center :=
      ⟨trajectoryFrom start.1 omega t,
        mem_discBoundaryFinset.mpr (by
          simpa only [profileInnerBoundary] using hmiddle)⟩
    let first : BoundaryExitWordCode boundary start.1 u.1 := by
      have code := incrementSliceBoundaryExitWordCode start.1 omega boundary
        (Nat.zero_le t) htmem (by
          intro r _hr0 hrt
          exact hspec.2.2 r hrt (Nat.zero_le _))
      refine ⟨code.1, ?_, ?_⟩
      · simpa only [PlanarPotential.trajectoryFrom_zero, u] using code.2.1
      · simpa only [PlanarPotential.trajectoryFrom_zero, u] using code.2.2
    let tail : BoundaryExitWordCode (profileInnerBoundary n l center)
        u.1 endpoint.1 := by
      have code := incrementSliceBoundaryExitWordCode start.1 omega
        (profileInnerBoundary n l center) ht bridge.2.1.1 (by
          intro r _htr hr
          exact bridge.2.1.2 r hr)
      refine ⟨code.1, ?_, ?_⟩
      · simpa only [u] using code.2.1
      · simpa only [u] using code.2.2.trans bridge.2.2
    let q := boundaryExcursionCount
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1
      (extendStoppedWord tail.1) tail.1.1
    let parent : BoundaryExcursionExitWordCode
        (profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) u.1 q endpoint.1 :=
      ⟨tail.1, tail.2.1, rfl, tail.2.2⟩
    refine .entered u first q parent ?_
    have hslices : incrementSlice omega 0 t ++
        incrementSlice omega t bridge.1.1 =
          incrementSlice omega 0 bridge.1.1 :=
      incrementSlice_append omega (Nat.zero_le t) ht
    have hfirstList : List.ofFn first.1.2 = incrementSlice omega 0 t := by
      simp only [first, incrementSliceBoundaryExitWordCode,
        TerminalVisitSpliceInvariance.stoppedWordOfList]
      exact List.ofFn_get _
    have htailList : List.ofFn parent.1.2 =
        incrementSlice omega t bridge.1.1 := by
      simp only [parent, tail, incrementSliceBoundaryExitWordCode,
        TerminalVisitSpliceInvariance.stoppedWordOfList]
      exact List.ofFn_get _
    rw [hfirstList, htailList, hslices]
    exact incrementSlice_extendStoppedWord_zero_eq bridge.1

/-- The split does not change the stopped-word mass of the coarse bridge. -/
theorem paddedPreludeSplit_mass
    {n l p : ℕ} {center : Point}
    (start : PaddedNearPoint n l center)
    (endpoint : PaddedOuterPoint n l center)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start.1 endpoint.1) :
    (match paddedPreludeSplit (p := p) start endpoint bridge with
    | .direct first _ => stoppedWordMass first.1
    | .entered _ first _ parent _ =>
        stoppedWordMass first.1 * stoppedWordMass parent.1) =
      stoppedWordMass bridge.1 := by
  generalize hsplit : paddedPreludeSplit (p := p) start endpoint bridge = split
  cases split with
  | direct first hword =>
      simpa only [hword]
  | entered u first q parent hword =>
      change stoppedWordMass first.1 * stoppedWordMass parent.1 =
        stoppedWordMass bridge.1
      calc
        _ = stoppedWordMass (listStoppedWord
              (List.ofFn first.1.2 ++ List.ofFn parent.1.2)) := by
            rw [AnnularRecursiveProfileCodeAssembly.stoppedWordMass_listStoppedWord_append,
              listStoppedWord_ofFn, listStoppedWord_ofFn]
        _ = stoppedWordMass (listStoppedWord (List.ofFn bridge.1.2)) := by
            rw [hword]
        _ = stoppedWordMass bridge.1 := by rw [listStoppedWord_ofFn]

end

end Erdos1165.AsymmetricPaddedBridgeLiteralFactorization
