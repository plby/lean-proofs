/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingConditionalCoordinateReconstruction

/-!
# Coordinate windows for the source-correct conditional candidate history

The broad `D_eta ∩ {Theta_eta = ∅} ∩ {M_o = S}` denominator is not treated
as prefix-invariant.  Instead, after the retained word and the represented
away dominoes are fixed, this file writes it literally as one finite window
on every reconstructed away total.  The exact candidate-set equality is
converted to pointwise membership using injectivity of the fixed dominant
endpoint map.

At a selected canonical-dominant candidate with good external history, its
local broad window simplifies to the shifted source `I₁` window.  Adding the
narrow screen replaces precisely that coordinate's broad window.  The
checked negative-binomial comparison can therefore be applied without a
transition-probability premise.
-/

open Set

namespace Erdos1165.HLOZTilingConditionalCandidateWindows

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows
open HLOZTilingConditionalCoordinateReconstruction HLOZThetaSourceBalance
open LazyDecomposition SpatialInsertionFiber
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Local form of the reconstructed broad source acceptor on one away
domino and one proposed total. -/
def reconstructedSourceCandidateLocalAccepts {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (v : ℕ) : Prop :=
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
      OrientationCompatible o
        (tilingFixedDominantEndpoint x r terminal b.1)) ↔
    tilingFixedDominantEndpoint x r terminal b.1 ∈ S)

/-- The finite coordinate window cut out by the local broad source
classification. -/
noncomputable def reconstructedSourceCandidateBaseWindow {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact (Finset.range (upper b)).filter
    (reconstructedSourceCandidateLocalAccepts o t x r terminal D
      m w low externalLow externalHigh broadWindow S b)

/-- Only the chosen coordinate receives the additional narrow window. -/
noncomputable def reconstructedSourceCandidateScreenedWindow {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact if b = chosen then
      (reconstructedSourceCandidateBaseWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b).filter fun v ↦
          tilingFixedBoundaryDominoMax x r terminal b.1 + v ∈ narrowWindow
    else
      reconstructedSourceCandidateBaseWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b

/-- Values of an absolute endpoint window after subtracting the fixed
retained-prefix contribution, restricted to the literal total support. -/
noncomputable def shiftedEndpointWindow
    (fixed upper : ℕ) (window : Finset ℕ) : Finset ℕ :=
  (Finset.range upper).filter fun v ↦ fixed + v ∈ window

theorem tilingFixedDominantEndpoint_injective {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point) :
    Function.Injective (fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingFixedDominantEndpoint x r terminal b.1) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  have hb := tilingBase_fixedDominantEndpoint t x r terminal b.1
  have hc := tilingBase_fixedDominantEndpoint t x r terminal c.1
  exact hb.symm.trans ((congrArg (tilingBase t) h).trans hc)

theorem tilingFixedBoundaryLocalTime_fixedDominant {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r) :
    tilingFixedBoundaryLocalTime x r terminal
        (tilingFixedDominantEndpoint x r terminal b) =
      tilingFixedBoundaryDominoMax x r terminal b := by
  unfold tilingFixedDominantEndpoint tilingFixedBoundaryDominoMax
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (Nat.le_of_not_ge h)).symm

/-- Exact equality of the reconstructed candidate Finset is equivalent to
one local membership bit per away coordinate.  `hcoverage` is fixed-history
data: every requested point of `S` must be the dominant endpoint of a
represented away domino. -/
theorem reconstructedOrientedDominantBroadAwaySites_eq_iff_forall
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (broadWindow : Finset ℕ) (S : Finset Point)
    (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedOrientedDominantBroadAwaySites
        o t x r terminal D upper broadWindow ell = S ↔
      ∀ b,
        ((reconstructedTilingXiPlus
              t x r terminal D upper ell b ∈ broadWindow ∧
            OrientationCompatible o
              (tilingFixedDominantEndpoint x r terminal b.1)) ↔
          tilingFixedDominantEndpoint x r terminal b.1 ∈ S) := by
  classical
  let f := fun b : TilingCappedMarginalization.TilingAwayDomino t x r D ↦
    tilingFixedDominantEndpoint x r terminal b.1
  let p := fun b : TilingCappedMarginalization.TilingAwayDomino t x r D ↦
    reconstructedTilingXiPlus t x r terminal D upper ell b ∈ broadWindow
  have hf : Function.Injective f :=
    tilingFixedDominantEndpoint_injective t x r terminal D
  constructor
  · intro heq b
    constructor
    · rintro ⟨hpb, hob⟩
      rw [← heq]
      refine Finset.mem_filter.mpr ⟨?_, hob⟩
      exact Finset.mem_image.mpr ⟨b,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpb⟩, rfl⟩
    · intro hbS
      have hbmem : f b ∈
          ((Finset.univ.filter p).image f).filter
            (OrientationCompatible o) := by
        change f b ∈ reconstructedOrientedDominantBroadAwaySites
          o t x r terminal D upper broadWindow ell
        rw [heq]
        exact hbS
      obtain ⟨himage, hob⟩ := Finset.mem_filter.mp hbmem
      obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp himage
      have hbc : c = b := hf hcb
      subst c
      exact ⟨(Finset.mem_filter.mp hc).2, hob⟩
  · intro hall
    apply Finset.ext
    intro y
    constructor
    · intro hy
      have hy' : y ∈ ((Finset.univ.filter p).image f).filter
          (OrientationCompatible o) := by
        exact hy
      obtain ⟨himage, hoy⟩ := Finset.mem_filter.mp hy'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp himage
      exact (hall b).mp ⟨(Finset.mem_filter.mp hb).2, hoy⟩
    · intro hyS
      obtain ⟨b, _, hby⟩ := Finset.mem_image.mp (hcoverage hyS)
      subst y
      obtain ⟨hpb, hob⟩ := (hall b).mpr hyS
      change f b ∈ ((Finset.univ.filter p).image f).filter
        (OrientationCompatible o)
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpb⟩, rfl⟩, hob⟩

theorem reconstructedSourceCandidateBaseAccepts_iff_local
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedSourceCandidateBaseAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S ell ↔
      ∀ b, reconstructedSourceCandidateLocalAccepts o t x r terminal D
        m w low externalLow externalHigh broadWindow S b (ell b : ℕ) := by
  unfold reconstructedSourceCandidateBaseAccepts
  rw [reconstructedOrientedDominantBroadAwaySites_eq_iff_forall
    o t x r terminal D upper broadWindow S ell hcoverage]
  unfold
    reconstructedAwayDEtaClassifies reconstructedAwayThetaGood
    reconstructedSourceCandidateLocalAccepts reconstructedTilingVTwoAt
    reconstructedTilingVThreeAt reconstructedTilingThetaBadAt
    reconstructedTilingEndpointLocalTime reconstructedTilingXiPlus
  aesop

theorem reconstructedSourceCandidateBaseAccepts_iff_windows
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedSourceCandidateBaseAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S ell ↔
      ∀ b, (ell b : ℕ) ∈ reconstructedSourceCandidateBaseWindow
        o t x r terminal D upper m w low externalLow externalHigh
          broadWindow S b := by
  rw [reconstructedSourceCandidateBaseAccepts_iff_local
    o t x r terminal D upper m w low externalLow externalHigh
      broadWindow S ell hcoverage]
  apply forall_congr'
  intro b
  simp only [reconstructedSourceCandidateBaseWindow, Finset.mem_filter,
    Finset.mem_range, (ell b).isLt, true_and]

theorem reconstructedSourceCandidateScreenedAccepts_iff_windows
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ (Finset.univ.image fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingFixedDominantEndpoint x r terminal b.1)) :
    reconstructedSourceCandidateScreenedAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow ell ↔
      ∀ b, (ell b : ℕ) ∈ reconstructedSourceCandidateScreenedWindow
        o t x r terminal D upper m w low externalLow externalHigh
          broadWindow S chosen narrowWindow b := by
  unfold reconstructedSourceCandidateScreenedAccepts
  rw [reconstructedSourceCandidateBaseAccepts_iff_windows
    o t x r terminal D upper m w low externalLow externalHigh
      broadWindow S ell hcoverage]
  constructor
  · rintro ⟨hbase, hnarrow⟩ b
    by_cases hb : b = chosen
    · subst b
      unfold reconstructedSourceCandidateScreenedWindow
      rw [if_pos rfl]
      refine Finset.mem_filter.mpr ⟨hbase chosen, ?_⟩
      simpa only [reconstructedTilingEndpointLocalTime,
        tilingFixedBoundaryLocalTime_fixedDominant] using hnarrow
    · unfold reconstructedSourceCandidateScreenedWindow
      rw [if_neg hb]
      exact hbase b
  · intro hall
    refine ⟨?_, ?_⟩
    · intro b
      by_cases hb : b = chosen
      · subst b
        have hchosen := hall chosen
        unfold reconstructedSourceCandidateScreenedWindow at hchosen
        rw [if_pos rfl] at hchosen
        exact (Finset.mem_filter.mp hchosen).1
      · have hbmem := hall b
        unfold reconstructedSourceCandidateScreenedWindow at hbmem
        rw [if_neg hb] at hbmem
        exact hbmem
    · have hchosen := hall chosen
      unfold reconstructedSourceCandidateScreenedWindow at hchosen
      rw [if_pos rfl] at hchosen
      have hnarrow := (Finset.mem_filter.mp hchosen).2
      simpa only [reconstructedTilingEndpointLocalTime,
        tilingFixedBoundaryLocalTime_fixedDominant] using hnarrow

theorem reconstructedSourceCandidateScreenedWindow_eq_base
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen b : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (hne : b ≠ chosen) :
    reconstructedSourceCandidateScreenedWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow b =
      reconstructedSourceCandidateBaseWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b := by
  simp only [reconstructedSourceCandidateScreenedWindow, if_neg hne]

/-! ## Simplification at the selected canonical-dominant coordinate -/

theorem reconstructedSourceCandidateLocalAccepts_iff_sourceWindow
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (horient : OrientationCompatible o chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w)
    (v : ℕ) :
    reconstructedSourceCandidateLocalAccepts o t x r terminal D
        m w low externalLow externalHigh broadWindow S chosen v ↔
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 + v ∈
        shellZeroSourceTotalWindow m w := by
  simp only [reconstructedSourceCandidateLocalAccepts,
    tilingFixedBoundaryDominoMax, tilingFixedDominantEndpoint,
    if_pos hbDominant, max_eq_left hbDominant, hbroad, horient, hS,
    hexternal.1, hexternal.2, true_and, iff_true]
  tauto

theorem reconstructedSourceCandidateBaseWindow_chosen
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (horient : OrientationCompatible o chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w) :
    reconstructedSourceCandidateBaseWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
        (upper chosen) (shellZeroSourceTotalWindow m w) := by
  ext v
  simp only [reconstructedSourceCandidateBaseWindow, shiftedEndpointWindow,
    Finset.mem_filter, Finset.mem_range]
  rw [reconstructedSourceCandidateLocalAccepts_iff_sourceWindow
    o t x r terminal D m w low externalLow externalHigh broadWindow S chosen
      hbDominant horient hS hexternal hbroad v]

theorem reconstructedSourceCandidateScreenedWindow_chosen
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ)
    (hbDominant : tilingFixedBoundaryLocalTime x r terminal
        (tilingPartner t chosen.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
    (horient : OrientationCompatible o chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        tilingFixedBoundaryLocalTime x r terminal chosen.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal chosen.1.1 < externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w)
    (hnarrow : narrowWindow ⊆ shellZeroSourceTotalWindow m w) :
    reconstructedSourceCandidateScreenedWindow o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow
          chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime x r terminal chosen.1.1)
        (upper chosen) narrowWindow := by
  rw [reconstructedSourceCandidateScreenedWindow, if_pos rfl,
    reconstructedSourceCandidateBaseWindow_chosen o t x r terminal D upper
      m w low externalLow externalHigh broadWindow S chosen hbDominant
        horient hS hexternal hbroad]
  ext v
  simp only [shiftedEndpointWindow, Finset.mem_filter, Finset.mem_range,
    tilingFixedBoundaryDominoMax, max_eq_left hbDominant]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, hnarrow h.2⟩, h.2⟩

/-! ## The literal negative-binomial conditional comparison -/

structure ReconstructedSourceCandidateWindowSpec where
  i : ℕ
  o : LazyDecomposition.Orientation
  t : DominoTiling
  x : Point
  r : TilingRetainedWord t x i
  terminal : Option Point
  D : Finset Point
  upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ
  m : ℕ
  w : ℕ
  low : ℕ
  externalLow : ℕ
  externalHigh : ℕ
  broadWindow : Finset ℕ
  S : Finset Point
  chosen : TilingCappedMarginalization.TilingAwayDomino t x r D
  narrowWindow : Finset ℕ

namespace ReconstructedSourceCandidateWindowSpec

abbrev Away (spec : ReconstructedSourceCandidateWindowSpec) :=
  TilingCappedMarginalization.TilingAwayDomino
    spec.t spec.x spec.r spec.D

noncomputable def baseWindow (spec : ReconstructedSourceCandidateWindowSpec) :
    spec.Away → Finset ℕ :=
  reconstructedSourceCandidateBaseWindow spec.o spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S

noncomputable def screenedWindow
    (spec : ReconstructedSourceCandidateWindowSpec) : spec.Away → Finset ℕ :=
  reconstructedSourceCandidateScreenedWindow spec.o spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S spec.chosen spec.narrowWindow

noncomputable def baseAccepts (spec : ReconstructedSourceCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide
    (reconstructedSourceCandidateBaseAccepts spec.o spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S ell)

noncomputable def screenedAccepts
    (spec : ReconstructedSourceCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide
    (reconstructedSourceCandidateScreenedAccepts spec.o spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S spec.chosen
          spec.narrowWindow ell)

def pointMass (cap : ℕ) (spec : ReconstructedSourceCandidateWindowSpec) :
    spec.Away → ℕ → ℝ :=
  tilingAwayPointMass (cap := cap) spec.t spec.x spec.r spec.D

structure RatioData (cap : ℕ) (C : ℝ)
    (spec : ReconstructedSourceCandidateWindowSpec) : Prop where
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

/-- The literal NB window comparison, after the exact broad history has
been rewritten as coordinate windows. -/
theorem conditionalScreenMass_le {cap : ℕ} {C : ℝ}
    (spec : ReconstructedSourceCandidateWindowSpec)
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
        reconstructedSourceCandidateBaseAccepts spec.o spec.t spec.x spec.r
          spec.terminal spec.D spec.upper spec.m spec.w spec.low
            spec.externalLow spec.externalHigh spec.broadWindow spec.S ell by
      simp only [baseAccepts, decide_eq_true_eq]]
    exact reconstructedSourceCandidateBaseAccepts_iff_windows
      spec.o spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m
        spec.w spec.low spec.externalLow spec.externalHigh spec.broadWindow
        spec.S ell data.coverage
  have hscreenedPred : (fun ell ↦ spec.screenedAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.screenedWindow b) := by
    funext ell
    apply propext
    rw [show spec.screenedAccepts ell = true ↔
        reconstructedSourceCandidateScreenedAccepts spec.o spec.t spec.x spec.r
          spec.terminal spec.D spec.upper spec.m spec.w spec.low
            spec.externalLow spec.externalHigh spec.broadWindow spec.S
              spec.chosen spec.narrowWindow ell by
      simp only [screenedAccepts, decide_eq_true_eq]]
    exact reconstructedSourceCandidateScreenedAccepts_iff_windows
      spec.o spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m
        spec.w spec.low spec.externalLow spec.externalHigh spec.broadWindow
        spec.S spec.chosen spec.narrowWindow ell data.coverage
  simp only [hbasePred, hscreenedPred]
  simpa only [pointMass, Away] using
    tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
    (cap := cap) (C := C) spec.t spec.x spec.r spec.D spec.upper spec.chosen
      spec.baseWindow spec.screenedWindow data.basePos
      (fun b hb ↦ reconstructedSourceCandidateScreenedWindow_eq_base
        spec.o spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m
          spec.w spec.low spec.externalLow spec.externalHigh spec.broadWindow
          spec.S spec.chosen b spec.narrowWindow hb)
      data.screenedUpper data.baseUpper data.screenedCap data.baseCap
      data.coordinates data.ratio

end ReconstructedSourceCandidateWindowSpec

end

end Erdos1165.HLOZTilingConditionalCandidateWindows
