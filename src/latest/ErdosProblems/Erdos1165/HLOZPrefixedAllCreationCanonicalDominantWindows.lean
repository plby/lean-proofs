/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedTilingConditionalCoordinateReconstruction

/-!
# Coordinatewise canonical windows on physical prefixed fibres

The denominator fixes the complete prefix-correct `D_eta`, Theta-good, and
exact canonical broad-candidate classification.  The numerator adds the
narrow window at one selected coordinate.  Both are literal intersections
of one finite window per away coordinate.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationCanonicalDominantWindows

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows
open HLOZThetaSourceBalance
open HLOZTilingConditionalCandidateWindows
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open LazyDecomposition SmallWindow
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def prefixedCanonicalCandidateLocalAccepts (initial : List Direction)
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (b : TilingAwayDomino t x r D) (v : ℕ) : Prop :=
  ((prefixedTilingFixedBoundaryLocalTime initial x r terminal
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 + v ∈
        shellZeroSourceTotalWindow m w) ∨
    (prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 + v ≤
        low ∨
      (prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 + v <
          prefixedTilingFixedBoundaryLocalTime initial x r terminal
            (tilingPartner t b.1.1) + v ∧
        prefixedTilingFixedBoundaryLocalTime initial x r terminal
            (tilingPartner t b.1.1) + v < m))) ∧
  ¬(prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 + v ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤
          prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 ∧
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 <
          externalHigh)) ∧
  ((prefixedTilingFixedBoundaryDominoMax initial x r terminal b.1 + v ∈
        broadWindow ∧
      IsTilingBase t
        (prefixedTilingFixedDominantEndpoint initial x r terminal b.1)) ↔
    prefixedTilingFixedDominantEndpoint initial x r terminal b.1 ∈ S)

noncomputable def prefixedCanonicalCandidateBaseWindow
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (b : TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact (Finset.range (upper b)).filter
    (prefixedCanonicalCandidateLocalAccepts initial t x r terminal D
      m w low externalLow externalHigh broadWindow S b)

noncomputable def prefixedCanonicalCandidateScreenedWindow
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (b : TilingAwayDomino t x r D) : Finset ℕ := by
  classical
  exact if b = chosen then
      (prefixedCanonicalCandidateBaseWindow initial t x r terminal D upper
        m w low externalLow externalHigh broadWindow S b).filter fun v ↦
          prefixedTilingFixedBoundaryDominoMax initial x r terminal b.1 + v ∈
            narrowWindow
    else prefixedCanonicalCandidateBaseWindow initial t x r terminal D upper
      m w low externalLow externalHigh broadWindow S b

theorem reconstructedPrefixedCanonicalDominantBroadAwaySites_eq_iff_forall
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (broadWindow : Finset ℕ) (S : Finset Point)
    (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      prefixedTilingFixedDominantEndpoint initial x r terminal b.1) :
    reconstructedPrefixedCanonicalDominantBroadAwaySites initial t x r terminal
        D upper broadWindow ell = S ↔
      ∀ b, ((reconstructedPrefixedTilingXiPlus initial t x r terminal D upper
              ell b ∈ broadWindow ∧
            IsTilingBase t
              (prefixedTilingFixedDominantEndpoint initial x r terminal b.1)) ↔
          prefixedTilingFixedDominantEndpoint initial x r terminal b.1 ∈ S) := by
  classical
  let f := fun b : TilingAwayDomino t x r D ↦
    prefixedTilingFixedDominantEndpoint initial x r terminal b.1
  let p := fun b : TilingAwayDomino t x r D ↦
    reconstructedPrefixedTilingXiPlus initial t x r terminal D upper ell b ∈
      broadWindow
  have hf : Function.Injective f :=
    prefixedTilingFixedDominantEndpoint_injective initial t x r terminal D
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
        change f b ∈ reconstructedPrefixedCanonicalDominantBroadAwaySites
          initial t x r terminal D upper broadWindow ell
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

theorem reconstructedPrefixedCanonicalCandidateBaseAccepts_iff_windows
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      prefixedTilingFixedDominantEndpoint initial x r terminal b.1) :
    reconstructedPrefixedCanonicalCandidateBaseAccepts initial t x r terminal D
        upper m w low externalLow externalHigh broadWindow S ell ↔
      ∀ b, (ell b : ℕ) ∈ prefixedCanonicalCandidateBaseWindow initial t x
        r terminal D upper m w low externalLow externalHigh broadWindow S b := by
  unfold reconstructedPrefixedCanonicalCandidateBaseAccepts
  rw [reconstructedPrefixedCanonicalDominantBroadAwaySites_eq_iff_forall
    initial t x r terminal D upper broadWindow S ell hcoverage]
  simp only [prefixedCanonicalCandidateBaseWindow, Finset.mem_filter,
    Finset.mem_range, (ell _).isLt, true_and]
  unfold reconstructedPrefixedAwayDEtaClassifies
    reconstructedPrefixedAwayThetaGood prefixedCanonicalCandidateLocalAccepts
    reconstructedPrefixedTilingVTwoAt reconstructedPrefixedTilingVThreeAt
    reconstructedPrefixedTilingThetaBadAt
    reconstructedPrefixedTilingEndpointLocalTime
    reconstructedPrefixedTilingXiPlus
  aesop

theorem reconstructedPrefixedCanonicalCandidateScreenedAccepts_iff_windows
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper)
    (hcoverage : S ⊆ Finset.univ.image fun b : TilingAwayDomino t x r D ↦
      prefixedTilingFixedDominantEndpoint initial x r terminal b.1) :
    reconstructedPrefixedCanonicalCandidateScreenedAccepts initial t x r terminal
        D upper m w low externalLow externalHigh broadWindow S chosen
          narrowWindow ell ↔
      ∀ b, (ell b : ℕ) ∈ prefixedCanonicalCandidateScreenedWindow initial
        t x r terminal D upper m w low externalLow externalHigh broadWindow S
          chosen narrowWindow b := by
  unfold reconstructedPrefixedCanonicalCandidateScreenedAccepts
  rw [reconstructedPrefixedCanonicalCandidateBaseAccepts_iff_windows initial t x
    r terminal D upper m w low externalLow externalHigh broadWindow S ell
      hcoverage]
  constructor
  · rintro ⟨hbase, hnarrow⟩ b
    by_cases hb : b = chosen
    · subst b
      simp only [prefixedCanonicalCandidateScreenedWindow, if_pos,
        Finset.mem_filter]
      refine ⟨hbase chosen, ?_⟩
      simpa only [reconstructedPrefixedTilingEndpointLocalTime,
        prefixedTilingFixedBoundaryLocalTime_fixedDominant] using hnarrow
    · simpa only [prefixedCanonicalCandidateScreenedWindow, if_neg hb]
        using hbase b
  · intro hall
    refine ⟨?_, ?_⟩
    · intro b
      by_cases hb : b = chosen
      · subst b
        have hchosen := hall chosen
        unfold prefixedCanonicalCandidateScreenedWindow at hchosen
        rw [if_pos rfl] at hchosen
        exact (Finset.mem_filter.mp hchosen).1
      · simpa only [prefixedCanonicalCandidateScreenedWindow, if_neg hb]
          using hall b
    · have hchosen := hall chosen
      unfold prefixedCanonicalCandidateScreenedWindow at hchosen
      rw [if_pos rfl] at hchosen
      simpa only [reconstructedPrefixedTilingEndpointLocalTime,
        prefixedTilingFixedBoundaryLocalTime_fixedDominant] using
          (Finset.mem_filter.mp hchosen).2

theorem prefixedCanonicalCandidateLocalAccepts_iff_sourceWindow
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (m w low externalLow externalHigh : ℕ)
    (broadWindow : Finset ℕ) (S : Finset Point)
    (chosen : TilingAwayDomino t x r D)
    (hbDominant : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t chosen.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 <
        externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w) (v : ℕ) :
    prefixedCanonicalCandidateLocalAccepts initial t x r terminal D
        m w low externalLow externalHigh broadWindow S chosen v ↔
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 + v ∈
        shellZeroSourceTotalWindow m w := by
  have hchosenBase : IsTilingBase t chosen.1.1 := by
    rw [← tilingExternalDomino_isBase t x r chosen.1]
    exact isTilingBase_tilingBase t chosen.1.1
  simp only [prefixedCanonicalCandidateLocalAccepts,
    prefixedTilingFixedBoundaryDominoMax,
    prefixedTilingFixedDominantEndpoint, if_pos hbDominant,
    max_eq_left hbDominant, hbroad, hchosenBase, hS, hexternal.1,
    hexternal.2, true_and, iff_true]
  tauto

theorem prefixedCanonicalCandidateBaseWindow_chosen
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (hbDominant : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t chosen.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 <
        externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w) :
    prefixedCanonicalCandidateBaseWindow initial t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen =
      shiftedEndpointWindow
        (prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1)
        (upper chosen) (shellZeroSourceTotalWindow m w) := by
  ext v
  simp only [prefixedCanonicalCandidateBaseWindow, shiftedEndpointWindow,
    Finset.mem_filter, Finset.mem_range]
  rw [prefixedCanonicalCandidateLocalAccepts_iff_sourceWindow initial t x r
    terminal D m w low externalLow externalHigh broadWindow S chosen
      hbDominant hS hexternal hbroad v]

theorem prefixedCanonicalCandidateScreenedWindow_chosen
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ)
    (hbDominant : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t chosen.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1)
    (hS : chosen.1.1 ∈ S)
    (hexternal : externalLow ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1 <
        externalHigh)
    (hbroad : broadWindow = shellZeroSourceTotalWindow m w)
    (hnarrow : narrowWindow ⊆ shellZeroSourceTotalWindow m w) :
    prefixedCanonicalCandidateScreenedWindow initial t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow
          chosen =
      shiftedEndpointWindow
        (prefixedTilingFixedBoundaryLocalTime initial x r terminal chosen.1.1)
        (upper chosen) narrowWindow := by
  rw [prefixedCanonicalCandidateScreenedWindow, if_pos rfl,
    prefixedCanonicalCandidateBaseWindow_chosen initial t x r terminal D upper
      m w low externalLow externalHigh broadWindow S chosen hbDominant hS
        hexternal hbroad]
  ext v
  simp only [shiftedEndpointWindow, Finset.mem_filter, Finset.mem_range,
    prefixedTilingFixedBoundaryDominoMax, max_eq_left hbDominant]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, hnarrow h.2⟩, h.2⟩

structure PrefixedCanonicalDominantCandidateWindowSpec where
  initial : List Direction
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

namespace PrefixedCanonicalDominantCandidateWindowSpec

abbrev Away (spec : PrefixedCanonicalDominantCandidateWindowSpec) :=
  TilingAwayDomino spec.t spec.x spec.r spec.D

noncomputable def baseWindow (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    : spec.Away → Finset ℕ :=
  prefixedCanonicalCandidateBaseWindow spec.initial spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S

noncomputable def screenedWindow
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) :
    spec.Away → Finset ℕ :=
  prefixedCanonicalCandidateScreenedWindow spec.initial spec.t spec.x spec.r
    spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
      spec.externalHigh spec.broadWindow spec.S spec.chosen spec.narrowWindow

def strictAwaySupport (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  ∀ b : spec.Away,
    prefixedTilingFixedBoundaryDominoMax spec.initial spec.x spec.r spec.terminal
      b.1 + (ell b : ℕ) < spec.m

def acceptedBaseProp (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  reconstructedPrefixedCanonicalCandidateBaseAccepts spec.initial spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
        spec.externalLow spec.externalHigh spec.broadWindow spec.S ell ∧
    spec.strictAwaySupport ell

def acceptedScreenedProp (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  reconstructedPrefixedCanonicalCandidateScreenedAccepts spec.initial spec.t
      spec.x spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
        spec.externalLow spec.externalHigh spec.broadWindow spec.S spec.chosen
          spec.narrowWindow ell ∧ spec.strictAwaySupport ell

theorem acceptedScreenedProp_subset_base
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    {ell : TruncatedTotals spec.upper}
    (h : spec.acceptedScreenedProp ell) : spec.acceptedBaseProp ell :=
  ⟨h.1.1, h.2⟩

noncomputable def acceptedBaseWindow
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) (b : spec.Away) :
    Finset ℕ := by
  classical
  exact (spec.baseWindow b).filter fun v ↦
    prefixedTilingFixedBoundaryDominoMax spec.initial spec.x spec.r spec.terminal
      b.1 + v < spec.m

noncomputable def acceptedScreenedWindow
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) (b : spec.Away) :
    Finset ℕ := by
  classical
  exact (spec.screenedWindow b).filter fun v ↦
    prefixedTilingFixedBoundaryDominoMax spec.initial spec.x spec.r spec.terminal
      b.1 + v < spec.m

theorem acceptedBaseProp_iff_windows
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
      prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
        spec.terminal b.1) :
    spec.acceptedBaseProp ell ↔
      ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b := by
  rw [acceptedBaseProp,
    reconstructedPrefixedCanonicalCandidateBaseAccepts_iff_windows
      spec.initial spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m
      spec.w spec.low spec.externalLow spec.externalHigh spec.broadWindow spec.S
      ell hcoverage]
  simp only [strictAwaySupport, acceptedBaseWindow, baseWindow,
    Finset.mem_filter]
  aesop

theorem acceptedScreenedProp_iff_windows
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
      prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
        spec.terminal b.1) :
    spec.acceptedScreenedProp ell ↔
      ∀ b, (ell b : ℕ) ∈ spec.acceptedScreenedWindow b := by
  rw [acceptedScreenedProp,
    reconstructedPrefixedCanonicalCandidateScreenedAccepts_iff_windows
      spec.initial spec.t spec.x spec.r spec.terminal spec.D spec.upper spec.m
      spec.w spec.low spec.externalLow spec.externalHigh spec.broadWindow spec.S
      spec.chosen spec.narrowWindow ell hcoverage]
  simp only [strictAwaySupport, acceptedScreenedWindow, screenedWindow,
    Finset.mem_filter]
  aesop

theorem acceptedScreenedWindow_eq_base
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (b : spec.Away) (hne : b ≠ spec.chosen) :
    spec.acceptedScreenedWindow b = spec.acceptedBaseWindow b := by
  unfold acceptedScreenedWindow acceptedBaseWindow screenedWindow baseWindow
  rw [prefixedCanonicalCandidateScreenedWindow, if_neg hne]

theorem acceptedBaseWindow_chosen
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (hbDominant : prefixedTilingFixedBoundaryLocalTime spec.initial spec.x
        spec.r spec.terminal (tilingPartner spec.t spec.chosen.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
        spec.terminal spec.chosen.1.1)
    (hS : spec.chosen.1.1 ∈ spec.S)
    (hexternal : spec.externalLow ≤
        prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1 < spec.externalHigh)
    (hbroad : spec.broadWindow = shellZeroSourceTotalWindow spec.m spec.w) :
    spec.acceptedBaseWindow spec.chosen =
      shiftedEndpointWindow
        (prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1)
        (spec.upper spec.chosen)
        (shellZeroSourceTotalWindow spec.m spec.w) := by
  rw [acceptedBaseWindow, baseWindow,
    prefixedCanonicalCandidateBaseWindow_chosen spec.initial spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S spec.chosen
      hbDominant hS hexternal hbroad]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [prefixedTilingFixedBoundaryDominoMax, max_eq_left hbDominant]
    exact (mem_shellZeroSourceTotalWindow.mp
      (Finset.mem_filter.mp hv).2).2

theorem acceptedScreenedWindow_chosen
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (hbDominant : prefixedTilingFixedBoundaryLocalTime spec.initial spec.x
        spec.r spec.terminal (tilingPartner spec.t spec.chosen.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
        spec.terminal spec.chosen.1.1)
    (hS : spec.chosen.1.1 ∈ spec.S)
    (hexternal : spec.externalLow ≤
        prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1 < spec.externalHigh)
    (hbroad : spec.broadWindow = shellZeroSourceTotalWindow spec.m spec.w)
    (hnarrow : spec.narrowWindow ⊆
      shellZeroSourceTotalWindow spec.m spec.w) :
    spec.acceptedScreenedWindow spec.chosen =
      shiftedEndpointWindow
        (prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal spec.chosen.1.1)
        (spec.upper spec.chosen) spec.narrowWindow := by
  rw [acceptedScreenedWindow, screenedWindow,
    prefixedCanonicalCandidateScreenedWindow_chosen spec.initial spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S spec.chosen
      spec.narrowWindow hbDominant hS hexternal hbroad hnarrow]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [prefixedTilingFixedBoundaryDominoMax, max_eq_left hbDominant]
    exact (mem_shellZeroSourceTotalWindow.mp
      (hnarrow (Finset.mem_filter.mp hv).2)).2

noncomputable def acceptedBaseAccepts
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedBaseProp ell)

noncomputable def acceptedScreenedAccepts
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedScreenedProp ell)

def pointMass (cap : ℕ) (spec : PrefixedCanonicalDominantCandidateWindowSpec) :
    spec.Away → ℕ → ℝ :=
  tilingAwayPointMass (cap := cap) spec.t spec.x spec.r spec.D

structure AcceptedRatioData (cap : ℕ) (C : ℝ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) : Prop where
  coverage : spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
    prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
      spec.terminal b.1
  basePos : 0 < screenMass (spec.pointMass cap) spec.upper
    (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b)
  screenedUpper : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen,
    v < spec.upper spec.chosen
  baseUpper : ∀ v ∈ spec.acceptedBaseWindow spec.chosen,
    v < spec.upper spec.chosen
  screenedCap : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen, v ≤ cap
  baseCap : ∀ v ∈ spec.acceptedBaseWindow spec.chosen, v ≤ cap
  coordinates : 0 < Fintype.card
    (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1)
  ratio : windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.acceptedScreenedWindow spec.chosen) ≤
    C * windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.acceptedBaseWindow spec.chosen)

theorem acceptedConditionalScreenMass_le {cap : ℕ} {C : ℝ}
    (spec : PrefixedCanonicalDominantCandidateWindowSpec)
    (data : AcceptedRatioData cap C spec) :
    conditionalScreenMass (spec.pointMass cap) spec.upper
      (fun ell ↦ spec.acceptedBaseAccepts ell = true)
      (fun ell ↦ spec.acceptedScreenedAccepts ell = true) ≤ C := by
  classical
  have hbase : (fun ell ↦ spec.acceptedBaseAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b) := by
    funext ell
    apply propext
    simpa only [acceptedBaseAccepts, decide_eq_true_eq] using
      spec.acceptedBaseProp_iff_windows ell data.coverage
  have hscreened : (fun ell ↦ spec.acceptedScreenedAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedScreenedWindow b) := by
    funext ell
    apply propext
    simpa only [acceptedScreenedAccepts, decide_eq_true_eq] using
      spec.acceptedScreenedProp_iff_windows ell data.coverage
  simp only [hbase, hscreened]
  simpa only [pointMass, Away] using
    tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
      (cap := cap) (C := C) spec.t spec.x spec.r spec.D spec.upper
        spec.chosen spec.acceptedBaseWindow spec.acceptedScreenedWindow
          data.basePos (fun b hb ↦ spec.acceptedScreenedWindow_eq_base b hb)
          data.screenedUpper data.baseUpper data.screenedCap data.baseCap
          data.coordinates data.ratio

end PrefixedCanonicalDominantCandidateWindowSpec

end

end Erdos1165.HLOZPrefixedAllCreationCanonicalDominantWindows
