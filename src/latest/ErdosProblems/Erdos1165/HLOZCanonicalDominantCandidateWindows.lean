/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZDominantStoppedCandidatePartition
import ErdosProblems.Erdos1165.HLOZTilingConditionalCandidateWindows

/-!
# Conditional windows for the canonical dominant source

The existing oriented conditional window splits candidates by checkerboard
orientation.  HLOZ's spatial source `M_e`, however, consists of normalized
dominant endpoints which are canonical tiling bases.  This file gives the
corresponding exact conditional denominator:

`away D_eta ∩ away {Theta_eta = ∅} ∩ {canonical dominant broad set = S}`.

It is reconstructed from the full away-total vector and then written as one
finite broad window per coordinate.  At a selected member of `S`, the
numerator replaces exactly that broad window by the narrow window.  No
prefix-invariance or path-level probability inequality is assumed.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZCanonicalDominantCandidateWindows

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows
open HLOZTilingConditionalCandidateWindows
open HLOZTilingConditionalCoordinateReconstruction HLOZThetaSourceBalance
open LazyDecomposition
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Canonical dominant broad candidates reconstructed from the represented
away totals. -/
noncomputable def reconstructedCanonicalDominantBroadAwaySites {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (broadWindow : Finset ℕ) (ell : TruncatedTotals upper) : Finset Point := by
  classical
  exact ((Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
        reconstructedTilingXiPlus t x r terminal D upper ell b ∈
          broadWindow).image
      (fun b ↦ tilingFixedDominantEndpoint x r terminal b.1)).filter
        (IsTilingBase t)

/-- Actual represented-away counterpart of the canonical reconstructed set. -/
noncomputable def actualCanonicalDominantBroadAwaySites {i : ℕ}
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (broadWindow : Finset ℕ) : Finset Point := by
  classical
  exact ((Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
        tilingXiPlusAt t s n b.1.1 ∈ broadWindow).image
      (fun b ↦ tilingDominantEndpointAt t s n b.1.1)).filter
        (IsTilingBase t)

/-- Full reconstructed broad denominator for `M_e`. -/
def reconstructedCanonicalCandidateBaseAccepts {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper) : Prop :=
  reconstructedAwayDEtaClassifies t x r terminal D upper m w low ell ∧
    reconstructedAwayThetaGood t x r terminal D upper
      m w externalLow externalHigh ell ∧
    reconstructedCanonicalDominantBroadAwaySites
      t x r terminal D upper broadWindow ell = S

/-- The canonical numerator adds one narrow single-site window. -/
def reconstructedCanonicalCandidateScreenedAccepts {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper) : Prop :=
  reconstructedCanonicalCandidateBaseAccepts t x r terminal D upper
      m w low externalLow externalHigh broadWindow S ell ∧
    reconstructedTilingEndpointLocalTime t x r terminal D upper ell chosen
        (tilingFixedDominantEndpoint x r terminal chosen.1) ∈ narrowWindow

/-- Actual represented-away canonical denominator. -/
def actualCanonicalCandidateBaseAccepts {i : ℕ}
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) : Prop :=
  (∀ b : TilingAwayDomino t x r D,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b.1.1 ∨
        tilingVThreeAt t m low s n b.1.1) ∧
    (∀ b : TilingAwayDomino t x r D,
      ¬actualTilingThetaBadAt t s n x r D
        m w externalLow externalHigh b) ∧
    actualCanonicalDominantBroadAwaySites
      t s n x r D broadWindow = S

/-- Actual represented-away canonical numerator. -/
def actualCanonicalCandidateScreenedAccepts {i : ℕ}
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) : Prop :=
  actualCanonicalCandidateBaseAccepts t s n x r D
      m w low externalLow externalHigh broadWindow S ∧
    localTime s n (tilingDominantEndpointAt t s n chosen.1.1) ∈ narrowWindow

/-! ## Exact reconstruction -/

theorem actualCanonicalDominantBroadAwaySites_eq_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (broadWindow : Finset ℕ) :
    actualCanonicalDominantBroadAwaySites t s n x r D broadWindow =
      reconstructedCanonicalDominantBroadAwaySites
        t x r terminal D upper broadWindow
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  classical
  let actualFiltered := Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
    tilingXiPlusAt t s n b.1.1 ∈ broadWindow
  let reconstructedFiltered :=
    Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
      reconstructedTilingXiPlus t x r terminal D upper
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b ∈ broadWindow
  have hfiltered : actualFiltered = reconstructedFiltered := by
    ext b
    simp only [actualFiltered, reconstructedFiltered, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [tilingXiPlusAt_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b]
  have himage :
      actualFiltered.image
          (fun b ↦ tilingDominantEndpointAt t s n b.1.1) =
        reconstructedFiltered.image
          (fun b ↦ tilingFixedDominantEndpoint x r terminal b.1) := by
    rw [hfiltered]
    apply Finset.image_congr
    intro b _
    exact tilingDominantEndpointAt_eq_fixed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
  unfold actualCanonicalDominantBroadAwaySites
    reconstructedCanonicalDominantBroadAwaySites
  exact congrArg (fun A : Finset Point ↦ A.filter (IsTilingBase t)) himage

theorem actualCanonicalCandidateBaseAccepts_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) :
    actualCanonicalCandidateBaseAccepts t s n x r D
        m w low externalLow externalHigh broadWindow S ↔
      reconstructedCanonicalCandidateBaseAccepts t x r terminal D upper
        m w low externalLow externalHigh broadWindow S
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  unfold actualCanonicalCandidateBaseAccepts
    reconstructedCanonicalCandidateBaseAccepts
    reconstructedAwayDEtaClassifies reconstructedAwayThetaGood
  rw [actualCanonicalDominantBroadAwaySites_eq_reconstructed_of_exact_prefix
    t s x r q terminal D upper hupper hpath broadWindow]
  apply and_congr
  · apply forall_congr'
    intro b
    rw [tilingVTwoAt_iff_reconstructed_of_exact_prefix
        t s x r q terminal D upper hupper hpath
          (shellZeroSourceTotalWindow m w) b,
      tilingVThreeAt_iff_reconstructed_of_exact_prefix
        t s x r q terminal D upper hupper hpath m low b]
  · apply and_congr
    · apply forall_congr'
      intro b
      unfold actualTilingThetaBadAt
      rw [tilingThetaBadAt_iff_reconstructed_of_exact_prefix
        t s x r q terminal D upper hupper hpath
          m w externalLow externalHigh b]
    · rfl

theorem actualCanonicalCandidateScreenedAccepts_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) :
    actualCanonicalCandidateScreenedAccepts t s n x r D
        m w low externalLow externalHigh broadWindow S chosen narrowWindow ↔
      reconstructedCanonicalCandidateScreenedAccepts t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  unfold actualCanonicalCandidateScreenedAccepts
    reconstructedCanonicalCandidateScreenedAccepts
  rw [actualCanonicalCandidateBaseAccepts_iff_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath m w low externalLow externalHigh
        broadWindow S,
    localTime_dominantEndpoint_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath chosen]

/-! ## Coordinatewise canonical windows -/

def reconstructedCanonicalCandidateLocalAccepts {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (b : TilingAwayDomino t x r D) (v : ℕ) : Prop :=
  ((tilingFixedBoundaryLocalTime x r terminal (tilingPartner t b.1.1) ≤
        tilingFixedBoundaryLocalTime x r terminal b.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal b.1.1 + v ∈
        shellZeroSourceTotalWindow m w) ∨
    (tilingFixedBoundaryLocalTime x r terminal b.1.1 + v ≤ low ∨
      (tilingFixedBoundaryLocalTime x r terminal b.1.1 + v <
          tilingFixedBoundaryLocalTime x r terminal
            (tilingPartner t b.1.1) + v ∧
        tilingFixedBoundaryLocalTime x r terminal
            (tilingPartner t b.1.1) + v < m))) ∧
  ¬(tilingFixedBoundaryLocalTime x r terminal b.1.1 + v ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ tilingFixedBoundaryLocalTime x r terminal b.1.1 ∧
        tilingFixedBoundaryLocalTime x r terminal b.1.1 < externalHigh)) ∧
  ((tilingFixedBoundaryDominoMax x r terminal b.1 + v ∈ broadWindow ∧
      IsTilingBase t (tilingFixedDominantEndpoint x r terminal b.1)) ↔
    tilingFixedDominantEndpoint x r terminal b.1 ∈ S)

noncomputable def reconstructedCanonicalCandidateBaseWindow {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (b : TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact (Finset.range (upper b)).filter
    (reconstructedCanonicalCandidateLocalAccepts t x r terminal D
      m w low externalLow externalHigh broadWindow S b)

noncomputable def reconstructedCanonicalCandidateScreenedWindow {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (b : TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact if b = chosen then
      (reconstructedCanonicalCandidateBaseWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b).filter fun v ↦
          tilingFixedBoundaryDominoMax x r terminal b.1 + v ∈ narrowWindow
    else
      reconstructedCanonicalCandidateBaseWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b

theorem reconstructedCanonicalDominantBroadAwaySites_eq_iff_forall
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedCanonicalDominantBroadAwaySites
        t x r terminal D upper broadWindow ell = S ↔
      ∀ b,
        ((reconstructedTilingXiPlus t x r terminal D upper ell b ∈
              broadWindow ∧
            IsTilingBase t
              (tilingFixedDominantEndpoint x r terminal b.1)) ↔
          tilingFixedDominantEndpoint x r terminal b.1 ∈ S) := by
  classical
  let f := fun b : TilingAwayDomino t x r D ↦
    tilingFixedDominantEndpoint x r terminal b.1
  let p := fun b : TilingAwayDomino t x r D ↦
    reconstructedTilingXiPlus t x r terminal D upper ell b ∈ broadWindow
  have hf : Function.Injective f :=
    tilingFixedDominantEndpoint_injective t x r terminal D
  constructor
  · intro heq b
    constructor
    · rintro ⟨hpb, hbbase⟩
      rw [← heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpb⟩, rfl⟩, hbbase⟩
    · intro hbS
      have hbmem : f b ∈ ((Finset.univ.filter p).image f).filter
          (IsTilingBase t) := by
        change f b ∈ reconstructedCanonicalDominantBroadAwaySites
          t x r terminal D upper broadWindow ell
        rw [heq]
        exact hbS
      obtain ⟨himage, hbbase⟩ := Finset.mem_filter.mp hbmem
      obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp himage
      have hbc : c = b := hf hcb
      subst c
      exact ⟨(Finset.mem_filter.mp hc).2, hbbase⟩
  · intro hall
    apply Finset.ext
    intro y
    constructor
    · intro hy
      obtain ⟨himage, hybase⟩ := Finset.mem_filter.mp hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp himage
      exact (hall b).mp ⟨(Finset.mem_filter.mp hb).2, hybase⟩
    · intro hyS
      obtain ⟨b, _, hby⟩ := Finset.mem_image.mp (hcoverage hyS)
      subst y
      obtain ⟨hpb, hbbase⟩ := (hall b).mpr hyS
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpb⟩, rfl⟩, hbbase⟩

theorem reconstructedCanonicalCandidateBaseAccepts_iff_windows
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedCanonicalCandidateBaseAccepts t x r terminal D upper
        m w low externalLow externalHigh broadWindow S ell ↔
      ∀ b, (ell b : ℕ) ∈ reconstructedCanonicalCandidateBaseWindow
        t x r terminal D upper m w low externalLow externalHigh
          broadWindow S b := by
  unfold reconstructedCanonicalCandidateBaseAccepts
  rw [reconstructedCanonicalDominantBroadAwaySites_eq_iff_forall
    t x r terminal D upper broadWindow S ell hcoverage]
  simp only [reconstructedCanonicalCandidateBaseWindow, Finset.mem_filter,
    Finset.mem_range, (ell _).isLt, true_and]
  unfold reconstructedAwayDEtaClassifies reconstructedAwayThetaGood
    reconstructedCanonicalCandidateLocalAccepts reconstructedTilingVTwoAt
    reconstructedTilingVThreeAt reconstructedTilingThetaBadAt
    reconstructedTilingEndpointLocalTime reconstructedTilingXiPlus
  aesop

theorem reconstructedCanonicalCandidateScreenedAccepts_iff_windows
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedCanonicalCandidateScreenedAccepts t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow ell ↔
      ∀ b, (ell b : ℕ) ∈ reconstructedCanonicalCandidateScreenedWindow
        t x r terminal D upper m w low externalLow externalHigh broadWindow S
          chosen narrowWindow b := by
  unfold reconstructedCanonicalCandidateScreenedAccepts
  rw [reconstructedCanonicalCandidateBaseAccepts_iff_windows
    t x r terminal D upper m w low externalLow externalHigh broadWindow S ell
      hcoverage]
  constructor
  · rintro ⟨hbase, hnarrow⟩ b
    by_cases hb : b = chosen
    · subst b
      simp only [reconstructedCanonicalCandidateScreenedWindow, if_pos,
        Finset.mem_filter]
      refine ⟨hbase chosen, ?_⟩
      simpa only [reconstructedTilingEndpointLocalTime,
        tilingFixedBoundaryLocalTime_fixedDominant] using hnarrow
    · simpa only [reconstructedCanonicalCandidateScreenedWindow,
        if_neg hb] using hbase b
  · intro hall
    refine ⟨?_, ?_⟩
    · intro b
      by_cases hb : b = chosen
      · subst b
        have hchosen := hall chosen
        unfold reconstructedCanonicalCandidateScreenedWindow at hchosen
        rw [if_pos rfl] at hchosen
        exact (Finset.mem_filter.mp hchosen).1
      · have hbmem := hall b
        unfold reconstructedCanonicalCandidateScreenedWindow at hbmem
        rw [if_neg hb] at hbmem
        exact hbmem
    · have hchosen := hall chosen
      unfold reconstructedCanonicalCandidateScreenedWindow at hchosen
      rw [if_pos rfl] at hchosen
      simpa only [reconstructedTilingEndpointLocalTime,
        tilingFixedBoundaryLocalTime_fixedDominant] using
          (Finset.mem_filter.mp hchosen).2

theorem reconstructedCanonicalCandidateScreenedWindow_eq_base
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen b : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (hne : b ≠ chosen) :
    reconstructedCanonicalCandidateScreenedWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow b =
      reconstructedCanonicalCandidateBaseWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b := by
  simp only [reconstructedCanonicalCandidateScreenedWindow, if_neg hne]

/-! ## The selected canonical coordinate -/

theorem isTilingBase_fixedDominantEndpoint_of_base_dominates
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r)
    (hdominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t b.1) ≤
      tilingFixedBoundaryLocalTime x r terminal b.1) :
    IsTilingBase t (tilingFixedDominantEndpoint x r terminal b) := by
  rw [tilingFixedDominantEndpoint, if_pos hdominant]
  rw [← tilingExternalDomino_isBase t x r b]
  exact isTilingBase_tilingBase t b.1

theorem reconstructedCanonicalCandidateLocalAccepts_iff_sourceWindow
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w) (v : ℕ) :
    reconstructedCanonicalCandidateLocalAccepts t x r terminal D
        m w low externalLow externalHigh broadWindow S chosen v ↔
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 + v ∈
        shellZeroSourceTotalWindow m w := by
  have hchosenBase : IsTilingBase t chosen.1.1 := by
    rw [← tilingExternalDomino_isBase t x r chosen.1]
    exact isTilingBase_tilingBase t chosen.1.1
  simp only [reconstructedCanonicalCandidateLocalAccepts,
    tilingFixedBoundaryDominoMax, tilingFixedDominantEndpoint,
    if_pos hbDominant, max_eq_left hbDominant, hbroad, hchosenBase, hS,
    hexternal.1, hexternal.2, true_and, iff_true]
  tauto

theorem reconstructedCanonicalCandidateBaseWindow_chosen
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w) :
    reconstructedCanonicalCandidateBaseWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
        (upper chosen) (shellZeroSourceTotalWindow m w) := by
  ext v
  simp only [reconstructedCanonicalCandidateBaseWindow, shiftedEndpointWindow,
    Finset.mem_filter, Finset.mem_range]
  rw [reconstructedCanonicalCandidateLocalAccepts_iff_sourceWindow
    t x r terminal D m w low externalLow externalHigh broadWindow S chosen
      hbDominant hS hexternal hbroad v]

theorem reconstructedCanonicalCandidateScreenedWindow_chosen
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w)
    (hnarrow : narrowWindow ⊆ shellZeroSourceTotalWindow m w) :
    reconstructedCanonicalCandidateScreenedWindow t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow
          chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
        (upper chosen) narrowWindow := by
  rw [reconstructedCanonicalCandidateScreenedWindow, if_pos rfl,
    reconstructedCanonicalCandidateBaseWindow_chosen t x r terminal D upper
      m w low externalLow externalHigh broadWindow S chosen hbDominant hS
        hexternal hbroad]
  ext v
  simp only [shiftedEndpointWindow, Finset.mem_filter, Finset.mem_range,
    tilingFixedBoundaryDominoMax, max_eq_left hbDominant]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, hnarrow h.2⟩, h.2⟩

/-! ## Checked conditional negative-binomial comparison -/

structure CanonicalDominantCandidateWindowSpec where
  i : ℕ
  t : DominoTiling
  x : Point
  r : TilingRetainedWord t x i
  terminal : Option Point
  D : Finset Point
  upper : TilingAwayDomino t x r D → ℕ
  m : ℕ
  w : ℕ
  low : ℕ
  externalLow : ℕ
  externalHigh : ℕ
  broadWindow : Finset ℕ
  S : Finset Point
  chosen : TilingAwayDomino t x r D
  narrowWindow : Finset ℕ

namespace CanonicalDominantCandidateWindowSpec

abbrev Away (spec : CanonicalDominantCandidateWindowSpec) :=
  TilingAwayDomino spec.t spec.x spec.r spec.D

noncomputable def baseWindow (spec : CanonicalDominantCandidateWindowSpec) :
    spec.Away → Finset ℕ :=
  reconstructedCanonicalCandidateBaseWindow spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S

noncomputable def screenedWindow
    (spec : CanonicalDominantCandidateWindowSpec) : spec.Away → Finset ℕ :=
  reconstructedCanonicalCandidateScreenedWindow spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S spec.chosen spec.narrowWindow

noncomputable def baseAccepts (spec : CanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide
    (reconstructedCanonicalCandidateBaseAccepts spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S ell)

noncomputable def screenedAccepts
    (spec : CanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide
    (reconstructedCanonicalCandidateScreenedAccepts spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S spec.chosen
          spec.narrowWindow ell)

def pointMass (cap : ℕ) (spec : CanonicalDominantCandidateWindowSpec) :
    spec.Away → ℕ → ℝ :=
  tilingAwayPointMass (cap := cap) spec.t spec.x spec.r spec.D

structure RatioData (cap : ℕ) (C : ℝ)
    (spec : CanonicalDominantCandidateWindowSpec) : Prop where
  coverage : spec.S ⊆ (Finset.univ.image fun b : spec.Away ↦
    tilingFixedDominantEndpoint spec.x spec.r spec.terminal b.1)
  basePos : 0 < screenMass (spec.pointMass cap) spec.upper
    (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.baseWindow b)
  screenedUpper : ∀ v ∈ spec.screenedWindow spec.chosen,
    v < spec.upper spec.chosen
  baseUpper : ∀ v ∈ spec.baseWindow spec.chosen,
    v < spec.upper spec.chosen
  screenedCap : ∀ v ∈ spec.screenedWindow spec.chosen, v ≤ cap
  baseCap : ∀ v ∈ spec.baseWindow spec.chosen, v ≤ cap
  coordinates : 0 < Fintype.card
    (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1)
  ratio : SmallWindow.windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.screenedWindow spec.chosen) ≤
    C * SmallWindow.windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.baseWindow spec.chosen)

theorem conditionalScreenMass_le {cap : ℕ} {C : ℝ}
    (spec : CanonicalDominantCandidateWindowSpec)
    (data : RatioData cap C spec) :
    conditionalScreenMass (spec.pointMass cap) spec.upper
      (fun ell ↦ spec.baseAccepts ell = true)
      (fun ell ↦ spec.screenedAccepts ell = true) ≤ C := by
  classical
  have hbasePred : (fun ell ↦ spec.baseAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.baseWindow b) := by
    funext ell
    apply propext
    rw [show spec.baseAccepts ell = true ↔
        reconstructedCanonicalCandidateBaseAccepts spec.t spec.x spec.r
          spec.terminal spec.D spec.upper spec.m spec.w spec.low
            spec.externalLow spec.externalHigh spec.broadWindow spec.S ell by
      simp only [baseAccepts, decide_eq_true_eq]]
    exact reconstructedCanonicalCandidateBaseAccepts_iff_windows
      spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m spec.w
        spec.low spec.externalLow spec.externalHigh spec.broadWindow spec.S ell
          data.coverage
  have hscreenedPred : (fun ell ↦ spec.screenedAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.screenedWindow b) := by
    funext ell
    apply propext
    rw [show spec.screenedAccepts ell = true ↔
        reconstructedCanonicalCandidateScreenedAccepts spec.t spec.x spec.r
          spec.terminal spec.D spec.upper spec.m spec.w spec.low
            spec.externalLow spec.externalHigh spec.broadWindow spec.S
              spec.chosen spec.narrowWindow ell by
      simp only [screenedAccepts, decide_eq_true_eq]]
    exact reconstructedCanonicalCandidateScreenedAccepts_iff_windows
      spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m spec.w
        spec.low spec.externalLow spec.externalHigh spec.broadWindow spec.S
          spec.chosen spec.narrowWindow ell data.coverage
  simp only [hbasePred, hscreenedPred]
  simpa only [pointMass, Away] using
    tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
      (cap := cap) (C := C) spec.t spec.x spec.r spec.D spec.upper spec.chosen
        spec.baseWindow spec.screenedWindow data.basePos
        (fun b hb ↦ reconstructedCanonicalCandidateScreenedWindow_eq_base
          spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m spec.w
            spec.low spec.externalLow spec.externalHigh spec.broadWindow spec.S
              spec.chosen b spec.narrowWindow hb)
        data.screenedUpper data.baseUpper data.screenedCap data.baseCap
        data.coordinates data.ratio

end CanonicalDominantCandidateWindowSpec

/-! ## Supplying the product field of a stopped-coordinate package -/

/-- The source parameters which turn one cap of an existing semantic
stopped-coordinate skeleton into the literal canonical window spec.  The
tiling, retained trace, distinguished set, and upper bounds are taken
definitionally from the skeleton. -/
structure CanonicalDominantWindowParameters
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {skeletonCost : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData
      piece next skeletonCost)
    (z : index) (cap : ℕ) where
  m : ℕ
  w : ℕ
  low : ℕ
  externalLow : ℕ
  externalHigh : ℕ
  terminal : Option Point
  broadWindow : Finset ℕ
  S : Finset Point
  chosen : TilingAwayDomino (data.tiling z cap) (data.start z cap)
    (data.retained z cap) (data.distinguished z cap)
  narrowWindow : Finset ℕ

namespace CanonicalDominantWindowParameters

noncomputable def toSpec
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {skeletonCost : ℝ≥0∞}
    {data : TilingConditionalFactoredStoppedCoordinateData
      piece next skeletonCost}
    {z : index} {cap : ℕ}
    (p : CanonicalDominantWindowParameters data z cap) :
    CanonicalDominantCandidateWindowSpec where
  i := data.retainedCount z cap
  t := data.tiling z cap
  x := data.start z cap
  r := data.retained z cap
  terminal := p.terminal
  D := data.distinguished z cap
  upper := data.upper z cap
  m := p.m
  w := p.w
  low := p.low
  externalLow := p.externalLow
  externalHigh := p.externalHigh
  broadWindow := p.broadWindow
  S := p.S
  chosen := p.chosen
  narrowWindow := p.narrowWindow

end CanonicalDominantWindowParameters

/-- Identification of every semantic denominator/numerator in a stopped
coordinate skeleton with the canonical dominant broad/narrow acceptors,
together with the checked finite negative-binomial data. -/
structure CanonicalDominantWindowProductCertificate
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {skeletonCost : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData
      piece next skeletonCost)
    (ratio : ℝ≥0∞) where
  parameters : ∀ z cap, CanonicalDominantWindowParameters data z cap
  baseAccepts_eq : ∀ z cap,
    data.baseAccepts z cap = (parameters z cap).toSpec.baseAccepts
  screenedAccepts_eq : ∀ z cap,
    data.screenedAccepts z cap = (parameters z cap).toSpec.screenedAccepts
  ratioData : ∀ z cap,
    CanonicalDominantCandidateWindowSpec.RatioData cap ratio.toReal
      (parameters z cap).toSpec

/-- The product bound is derived from the exact canonical broad denominator
and narrow numerator.  This is the field used when the same semantic
skeleton is re-packaged at finite `ratio`; no path-probability premise is
involved. -/
theorem product_bound_of_canonicalDominantWindowCertificate
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {skeletonCost ratio : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData
      piece next skeletonCost)
    (certificate : CanonicalDominantWindowProductCertificate data ratio) :
    ∀ z cap,
      conditionalScreenMass
        (tilingAwayPointMass (cap := cap) (data.tiling z cap)
          (data.start z cap) (data.retained z cap)
          (data.distinguished z cap))
        (data.upper z cap)
        (fun ell ↦ data.baseAccepts z cap ell = true)
        (fun ell ↦ data.screenedAccepts z cap ell = true) ≤ ratio.toReal := by
  intro z cap
  rw [certificate.baseAccepts_eq z cap,
    certificate.screenedAccepts_eq z cap]
  exact CanonicalDominantCandidateWindowSpec.conditionalScreenMass_le
    (certificate.parameters z cap).toSpec
      (certificate.ratioData z cap)

/-- Repackage a semantic stopped-coordinate skeleton at the checked finite
canonical window ratio.  Every path/fiber/factorization field is inherited
verbatim; only the finite product bound is replaced. -/
noncomputable def conditionalFactoredDataOfCanonicalDominantWindowCertificate
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {skeletonCost ratio : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData
      piece next skeletonCost)
    (certificate : CanonicalDominantWindowProductCertificate data ratio) :
    TilingConditionalFactoredStoppedCoordinateData piece next ratio where
  tiling := data.tiling
  retainedCount := data.retainedCount
  start := data.start
  retained := data.retained
  tail := data.tail
  stoppingTime := data.stoppingTime
  isStoppingTime := data.isStoppingTime
  basePredicate := data.basePredicate
  screenedPredicate := data.screenedPredicate
  screened_subset_base := data.screened_subset_base
  base_subset_piece := data.base_subset_piece
  distinguished := data.distinguished
  selected := data.selected
  upper := data.upper
  baseAccepts := data.baseAccepts
  screenedAccepts := data.screenedAccepts
  screenedAccepts_subset_base := data.screenedAccepts_subset_base
  base_factorization := data.base_factorization
  screened_factorization := data.screened_factorization
  upper_pos := data.upper_pos
  base_mass_ne_zero := data.base_mass_ne_zero
  monotone_screened := data.monotone_screened
  transition_covered := data.transition_covered
  product_bound :=
    product_bound_of_canonicalDominantWindowCertificate data certificate

end

end Erdos1165.HLOZCanonicalDominantCandidateWindows
