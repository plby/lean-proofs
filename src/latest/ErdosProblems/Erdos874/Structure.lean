/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import ErdosProblems.Erdos874.FreimanDimension
import ErdosProblems.Erdos874.FreimanEngine
import ErdosProblems.Erdos874.ModularStructure
import ErdosProblems.Erdos874.ProgressionExtraction
import ErdosProblems.Erdos874.RegularSpan
import ErdosProblems.Erdos874.RoughUpper
import ErdosProblems.Erdos874.SmallFourLayer
import ErdosProblems.Erdos874.StrausUpper
import ErdosProblems.Erdos874.Thresholds

/-!
# The Deshouillers--Freiman structural seam for Erdős Problem 874

This file packages the two quantitative conclusions from Deshouillers and
Freiman's 1995 argument in forms used by the 1999 exact upper-bound proof.

`HasLargeSetStructure N A` says that, after removing at most
`10^5 N^(5/12)` exceptional elements, the remainder of `A` lies in a short
arithmetic progression.  A restricted layer of the exceptional set contains
a much longer arithmetic progression of the same positive difference.

The natural number `longLength` counts terms, not gaps.  Consequently the
inequality `3 * N^(5/6) ≤ longLength` is the literal formal counterpart of
"at least `3 N^(5/6)` terms".  Likewise `shortLength ≤ N^(7/12)` records
the number of terms in the progression containing the regular part.
-/

namespace Erdos874

noncomputable section

open Filter

/-- A certificate for the large-set structure theorem of
Deshouillers--Freiman. -/
structure LargeSetStructure (N : ℕ) (A : Finset ℤ) where
  /-- The exceptional part of `A`. -/
  exceptional : Finset ℤ
  /-- The positive common difference shared by the two progressions. -/
  step : ℕ
  /-- The restricted layer of the exceptional set producing the long AP. -/
  layer : ℕ
  /-- The first term of a short AP containing the regular part. -/
  shortStart : ℤ
  /-- Number of terms in the long AP. -/
  longLength : ℕ
  /-- Number of terms in the short containing AP. -/
  shortLength : ℕ
  exceptional_subset : exceptional ⊆ A
  step_pos : 0 < step
  layer_pos : 0 < layer
  exceptional_card_le :
    (exceptional.card : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12)
  longLength_ge :
    3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (longLength : ℝ)
  long_progression :
    ContainsAP (restrictedSumset layer exceptional) (step : ℤ) longLength
  regular_contained :
    ContainedInAP (A \ exceptional) shortStart step shortLength
  shortLength_le :
    (shortLength : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 12)

/-- Predicate form of `LargeSetStructure`, convenient for theorem
statements and existential elimination. -/
def HasLargeSetStructure (N : ℕ) (A : Finset ℤ) : Prop :=
  Nonempty (LargeSetStructure N A)

/-- The coordinate-based progression containment used by the Freiman module
agrees with literal containment in the finite progression used by the
progression-extraction module. -/
lemma containedInAP_iff_subset_arithmeticProgression
    {A : Finset ℤ} {start : ℤ} {step length : ℕ} (hstep : 0 < step) :
    ContainedInAP A start step length ↔
      A ⊆ arithmeticProgression start (step : ℤ) length := by
  constructor
  · intro hA x hx
    obtain ⟨i, hi, hxi⟩ := hA.exists_coordinate hx
    apply mem_arithmeticProgression.mpr
    refine ⟨i, hi, ?_⟩
    rw [hxi]
    ring
  · intro hA
    refine ⟨hstep, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_arithmeticProgression.mp (hA hx)
    refine ⟨i, hi, ?_⟩
    rw [hxi]
    ring

/-- Existential-start version of
`containedInAP_iff_subset_arithmeticProgression`. -/
lemma containedInSomeAP_iff_exists_containedInAP
    {A : Finset ℤ} {step length : ℕ} (hstep : 0 < step) :
    ContainedInSomeAP A (step : ℤ) length ↔
      ∃ start : ℤ, ContainedInAP A start step length := by
  constructor
  · rintro ⟨start, hA⟩
    exact ⟨start, (containedInAP_iff_subset_arithmeticProgression hstep).2 hA⟩
  · rintro ⟨start, hA⟩
    exact ⟨start, (containedInAP_iff_subset_arithmeticProgression hstep).1 hA⟩

lemma LargeSetStructure.regular_subset
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A) :
    A \ S.exceptional ⊆ A :=
  Finset.sdiff_subset

lemma LargeSetStructure.exceptional_disjoint_regular
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A) :
    Disjoint S.exceptional (A \ S.exceptional) := by
  rw [Finset.disjoint_left]
  intro x hx hxdiff
  exact (Finset.mem_sdiff.mp hxdiff).2 hx

lemma LargeSetStructure.exceptional_union_regular
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A) :
    S.exceptional ∪ (A \ S.exceptional) = A := by
  exact Finset.union_sdiff_of_subset S.exceptional_subset

/-- The regular part has cardinality at most the number of terms in its
containing progression. -/
lemma LargeSetStructure.regular_card_le_shortLength
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A) :
    (A \ S.exceptional).card ≤ S.shortLength :=
  S.regular_contained.card_le

/-- Every regular element is explicitly represented by a coordinate in the
short progression. -/
lemma LargeSetStructure.exists_regular_coordinate
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A)
    {x : ℤ} (hx : x ∈ A \ S.exceptional) :
    ∃ i : ℕ, i < S.shortLength ∧
      x = S.shortStart + (i : ℤ) * (S.step : ℤ) :=
  S.regular_contained.exists_coordinate hx

/-- Elementwise form of the long-progression conclusion. -/
lemma LargeSetStructure.long_progression_mem
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A) :
    ∃ a : ℤ, ∀ i : ℕ, i < S.longLength →
      a + (S.step : ℤ) * (i : ℤ) ∈
        restrictedSumset S.layer S.exceptional := by
  obtain ⟨a, ha⟩ := S.long_progression
  refine ⟨a, fun i hi ↦ ha ?_⟩
  exact mem_arithmeticProgression.mpr ⟨i, hi, rfl⟩

/-- The real-valued rough upper estimate with a specified absolute
constant. -/
def RoughUpperBoundWith (C₀ : ℝ) : Prop :=
  ∀ (N : ℕ) (A : Finset ℤ), IsBoundedAdmissible N A →
    (A.card : ℝ) ≤
      2 * Real.sqrt N + C₀ * (N : ℝ) ^ ((5 : ℝ) / 12)

/-- The literal asymptotic upper-bound assertion proved in the 1995 paper:
there is one nonnegative absolute constant valid for all `N` and all bounded
admissible sets. -/
def HasRoughUpperBound : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ RoughUpperBoundWith C₀

/-- The literal sufficiently-large-`N` formulation of the 1995 structure
theorem.  The decimal `1.96` is represented exactly by `49 / 25`. -/
def HasEventuallyLargeSetStructure : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℤ, IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
        HasLargeSetStructure N A

/-- Convert the filter form used while assembling eventual numerical
estimates into the public explicit-threshold formulation. -/
theorem hasEventuallyLargeSetStructure_of_eventually
    (h : ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      HasLargeSetStructure N A) :
    HasEventuallyLargeSetStructure := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h
  exact ⟨N₀, fun N hN A hA hlarge ↦ hN₀ N hN A hA hlarge⟩

/-! ## The two DF95 selection propositions, assembled -/

/-- For every sufficiently large `N`, Propositions 1 and 2 of DF95 select a
block of the canonical size whose fourth restricted layer is below the
`5.8 |B|` inverse-theorem threshold.  Keeping the selected layer `s` in the
conclusion is useful in the subsequent residue-packing argument. -/
theorem eventually_exists_df95_small_four_block :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      ∃ s B,
        A.card / 10 ≤ s ∧
        s ≤ 3 * A.card / 4 ∧
        25 * (restrictedSumset s A).card < 36 * s * (A.card - s) ∧
        B ⊆ A ∧
        B.card = dfBlockSize N ∧
        5 * (restrictedSumset 4 B).card < 29 * B.card := by
  filter_upwards [eventually_ge_atTop 105000000,
      eventually_le_dfBlockSize 1,
      eventually_dfBlockSize_le_div_large_window] with N hN hLpos hLsmall
  intro A hA hlarge
  obtain ⟨s, hslow, hshi, hsmall⟩ :=
    exists_df95_small_restricted_sum_layer_of_large hN hA hlarge
  have hNreal : (105000000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase_sq : (((20060 : ℝ) * 25 / 49) ^ 2) ≤ (105000000 : ℝ) := by
    norm_num
  have hroot : (20060 : ℝ) * 25 / 49 ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (hbase_sq.trans hNreal)
  have hcardlarge : (20060 : ℝ) < (A.card : ℝ) := by
    calc
      (20060 : ℝ) = (49 / 25 : ℝ) * ((20060 : ℝ) * 25 / 49) := by
        norm_num
      _ ≤ (49 / 25 : ℝ) * Real.sqrt N := by gcongr
      _ < A.card := hlarge
  have hK : 20060 ≤ A.card := by exact_mod_cast hcardlarge.le
  have hsLarge : 1000 ≤ s := by omega
  have hJLarge : 1000 ≤ (A.card - s) / 4 := by omega
  have hLcard : 2000 * dfBlockSize N ≤ A.card := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2000)).mp (hLsmall A.card hlarge)
  obtain ⟨B, hBA, hBcard, hBsmall⟩ :=
    exists_df95_small_four_layer A s (dfBlockSize N)
      hslow hshi hsmall hsLarge hJLarge hLpos hLcard
  exact ⟨s, B, hslow, hshi, hsmall, hBA, hBcard, by simpa [hBcard] using hBsmall⟩

/-- The selected layer also has the absolute capacity required in the
residue-class packing step.  The constant `9/4` leaves room below the
eventual `5/2` progression-repetition capacity. -/
theorem eventually_exists_df95_small_four_block_with_capacity :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      ∃ s B,
        A.card / 10 ≤ s ∧
        s ≤ 3 * A.card / 4 ∧
        25 * (restrictedSumset s A).card < 36 * s * (A.card - s) ∧
        4 * (restrictedSumset s A).card < 9 * N ∧
        B ⊆ A ∧
        B.card = dfBlockSize N ∧
        5 * (restrictedSumset 4 B).card < 29 * B.card := by
  filter_upwards [eventually_exists_df95_small_four_block] with N hN
  intro A hA hlarge
  obtain ⟨s, B, hslow, hshi, hsmall, hBA, hBcard, hBsmall⟩ :=
    hN A hA hlarge
  exact ⟨s, B, hslow, hshi, hsmall,
    four_mul_restrictedSumset_card_lt_nine_mul hA hsmall,
    hBA, hBcard, hBsmall⟩

/-- The two DF95 selection propositions followed by the checked Freiman
engine.  In addition to the small target layer used for residue packing, this
produces the proper long progression in the canonical restricted layer of the
selected block. -/
theorem eventually_exists_df95_long_progression_block :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      ∃ s B ell, ∃ q : ℕ,
        A.card / 10 ≤ s ∧
        s ≤ 3 * A.card / 4 ∧
        25 * (restrictedSumset s A).card < 36 * s * (A.card - s) ∧
        4 * (restrictedSumset s A).card < 9 * N ∧
        B ⊆ A ∧
        B.card = dfBlockSize N ∧
        5 * (restrictedSumset 4 B).card < 29 * B.card ∧
        B.card ^ 2 ≤ 100000000 * ell ∧
        0 < q ∧
        (18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (ell : ℝ) ∧
        3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (ell : ℝ) ∧
        ContainsAP (restrictedSumset (B.card / 500000) B) (q : ℤ) ell := by
  filter_upwards [eventually_exists_df95_small_four_block_with_capacity,
      eventually_le_dfBlockSize 100000000,
      eventually_ge_atTop 1] with N hselect hengine hN
  intro A hA hlarge
  obtain ⟨s, B, hslow, hshi, hsmall, hcapacity, hBA, hBcard, hBsmall⟩ :=
    hselect A hA hlarge
  have hengineB : 100000000 ≤ B.card := by
    simpa [hBcard] using hengine
  obtain ⟨ell, hell, q, hq, hAP⟩ :=
    exists_long_restrictedSumset_AP_of_small_four B hengineB (by omega)
  have hellReal : (B.card : ℝ) ^ 2 ≤ 100000000 * (ell : ℝ) := by
    exact_mod_cast hell
  have hratio :
      (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2 ≤ (ell : ℝ) := by
    rw [hBcard] at hellReal
    norm_num [zpow_neg] at *
    nlinarith
  have hlong : 3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (ell : ℝ) :=
    (dfBlockSize_long_bound hN).le.trans hratio
  have hslack :
      (18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (ell : ℝ) :=
    (dfBlockSize_engine_slack_eighteen_fifths hN).trans hratio
  exact ⟨s, B, ell, q, hslow, hshi, hsmall, hcapacity, hBA, hBcard,
    hBsmall, hell, hq, hslack, hlong, hAP⟩

/-- The numerical conversion used by the modular packing argument.  It is
kept separate from the eventual estimates: all rounding and asymptotic work
is isolated in `Thresholds`, while this lemma only clears the exact factors
`4` and `9`. -/
theorem df95_layer_card_lt_residue_mul_long
    {N R ell c : ℕ}
    (hcapacity : 4 * c < 9 * N)
    (hmargin : (9 : ℝ) / 4 * N <
      (R : ℝ) * (3 * (N : ℝ) ^ ((5 : ℝ) / 6)))
    (hlong : 3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (ell : ℝ)) :
    c < R * ell := by
  have hcapacityReal : (4 : ℝ) * c < 9 * N := by
    exact_mod_cast hcapacity
  have hc : (c : ℝ) < (9 : ℝ) / 4 * N := by nlinarith
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hprod :
      (R : ℝ) * (3 * (N : ℝ) ^ ((5 : ℝ) / 6)) ≤
        (R : ℝ) * ell :=
    mul_le_mul_of_nonneg_left hlong hR
  have hfinal : (c : ℝ) < (R : ℝ) * (ell : ℝ) := by
    exact hc.trans (hmargin.trans_le hprod)
  exact_mod_cast hfinal

/-- Exact factor-clearing for the endpoint-absorption capacity estimate. -/
theorem df95_layer_card_lt_central_min_short
    {N c T U L : ℕ} (hcapacity : 4 * c < 9 * N)
    (hcentral : 9 * N < 4 * (T * min U L)) :
    c < T * min U L := by
  omega

/-! ## Endpoint absorption and the public structure record -/

/-- Package a fully finite DF95 certificate as the public structure record.
This is the final interface used after the modular alignment and endpoint
absorption arguments have produced the exceptional set and both arithmetic
progressions. -/
theorem largeSetStructure_of_finite_certificate
    {N d ell L U : ℕ} {A C : Finset ℤ} {start : ℤ}
    (hCA : C ⊆ A) (hd : 0 < d) (hell : 0 < ell)
    (hbudget : (C.card : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12))
    (hlongLength : 3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (L : ℝ))
    (hlong : ContainsAP (restrictedSumset ell C) (d : ℤ) L)
    (hshort : ContainedInAP (A \ C) start d U)
    (hshortLength : (U : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) :
    HasLargeSetStructure N A := by
  exact ⟨⟨C, d, ell, start, L, U, hCA, hd, hell, hbudget,
    hlongLength, hlong, hshort, hshortLength⟩⟩

/-- Package the checked endpoint-absorption theorem as the public DF95
structure certificate.  The hypotheses are exactly the finite numerical and
modular outputs produced before the final two extreme blocks are absorbed. -/
theorem largeSetStructure_of_regularSpan
    {N s d ell L T U filler : ℕ} {A C : Finset ℤ}
    (hCA : C ⊆ A) (hd : 0 < d) (hell : 0 < ell) (hT : 0 < T)
    (hlayer : ell + (filler + T) = s)
    (hfiller : filler ≤ (A \ C).card - 2 * T)
    (hcapacity : (restrictedSumset s A).card < T * min U L)
    (hlong : ContainsAP (restrictedSumset ell C) (d : ℤ) L)
    (hregular : IsDifferenceDivisor d (A \ C))
    (hbudget : ((C.card + 2 * T : ℕ) : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12))
    (hlongLength : 3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (L : ℝ))
    (hshortLength : (U : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 12)) :
    HasLargeSetStructure N A := by
  obtain ⟨C', start, hCC', hC'A, hC'card, hlong', hshort⟩ :=
    exists_regular_span_after_absorbing_extremes hCA hd hT hlayer hfiller
      hcapacity hlong hregular
  refine ⟨⟨C', d, ell, start, L, U, hC'A, hd, hell, ?_, hlongLength,
    hlong', hshort, hshortLength⟩⟩
  have hC'cardReal : (C'.card : ℝ) ≤ (C.card + 2 * T : ℕ) := by
    exact_mod_cast hC'card
  exact hC'cardReal.trans hbudget

/-! ## The unconditional eventual DF95 structure theorem -/

/-- The complete eventual structure theorem.  This theorem combines the
small-layer selection, the concrete Freiman engine, the repaired two-scale
integer alignment argument, and endpoint absorption. -/
theorem eventually_hasLargeSetStructure :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      HasLargeSetStructure N A := by
  filter_upwards [eventually_exists_df95_long_progression_block,
      eventually_one_le_dfResidueScale,
      eventually_four_mul_dfResidueScale_lt_dfAlignmentScale,
      eventually_nine_fourths_lt_residue_mul_long,
      eventually_df_alignment_aggregate_fit,
      eventually_df_modular_room,
      eventually_df_alignment_mass_room,
      eventually_df_alignment_convex_margin,
      eventually_df_alignment_exception_budget,
      eventually_nine_mul_lt_four_mul_central_min_short,
      eventually_one_le_dfCentralScale,
      eventually_le_dfBlockSize 100000000,
      eventually_ge_atTop 1] with
      N hselect hRpos hRFstrong hresidueCapacity haggregate hrooms
        hmass hconvex hbudget hcentral hTpos hBlarge hN
  intro A hA hlarge
  obtain ⟨s, B, ell, q, hslow, hshi, _hsmall, hsmallAbs, hBA, hBcard,
      _hfour, _hell, hq, hslack, hlong, hAP⟩ := hselect A hA hlarge
  let R := dfResidueScale N
  let F := dfAlignmentScale N
  let J := Nat.log 2 (N + 1)
  let t := dfBlockSize N / 500000
  let K := dfLongTarget N
  let T := dfCentralScale N
  let U := dfShortScale N
  have hDcard : (A \ B).card = A.card - B.card :=
    Finset.card_sdiff_of_subset hBA
  have hAP' : ContainsAP (restrictedSumset t B) (q : ℤ) ell := by
    simpa [t, hBcard] using hAP
  have hR : 0 < R := by exact hRpos
  have hRF : R ≤ F := by
    dsimp [R, F]
    omega
  have hdouble : 2 * R ≤ F := by
    dsimp [R, F]
    omega
  have hroom := hrooms (card := A.card) (layer := s) (generators := J)
    hlarge hslow hshi le_rfl
  dsimp only [t, R, F, J, T] at hroom
  obtain ⟨hendLayer, _hendRoom, hsupportLayer, hsupportRoom,
      horderLayer, horderRoom, hsubgroupLayer, hsubgroupRoom,
      halignLayer, halignRoom⟩ := hroom
  have hsupportRoom' : s - (t + 1) + R ≤ (A \ B).card := by
    rw [hDcard, hBcard]
    simpa [t, R] using hsupportRoom
  have horderRoom' : s - (t + R) + 2 * (R * R) ≤ (A \ B).card := by
    rw [hDcard, hBcard]
    simpa [t, R, pow_two] using horderRoom
  have hsubgroupRoom' :
      s - (t + R * R) + 2 * (R * R) ≤ (A \ B).card := by
    rw [hDcard, hBcard]
    simpa [t, R, pow_two] using hsubgroupRoom
  have halignRoom' : s - (t + F) + 2 * F ≤ (A \ B).card := by
    rw [hDcard, hBcard]
    simpa [t, F] using halignRoom
  have hcapacity : (restrictedSumset s A).card < R * ell := by
    apply df95_layer_card_lt_residue_mul_long hsmallAbs
    · simpa [R] using hresidueCapacity
    · exact hlong
  have hmass' := hmass (card := A.card) (generators := J) hlarge le_rfl
  have hrichMass : R * F + R * (R * R + J * F) < (A \ B).card := by
    rw [hDcard, hBcard]
    dsimp [R, F, J] at hmass' ⊢
    simp only [pow_two] at hmass'
    omega
  have halignMargin : 2 * (restrictedSumset s A).card <
      (F - 2 * R + 2) * ell := by
    simpa [R, F] using hconvex hsmallAbs hslack
  have hRle : R ≤ N + 1 := by
    have hRreal := dfResidueScale_cast_le N
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 6) ≤ (N : ℝ) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ N by exact_mod_cast hN) (by norm_num : (1 : ℝ) / 6 ≤ 1))
    have hcast : (R : ℝ) ≤ (N + 1 : ℕ) := by
      dsimp [R]
      have hNs : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.le_succ N
      exact hRreal.trans (hpow.trans hNs)
    exact_mod_cast hcast
  have hlog : Nat.log 2 R ≤ J := by
    exact Nat.log_mono_right hRle
  have hfit :
      2 * J * (restrictedSumset s A).card + (F - 2 * R + 2) * K ≤
        (F - 2 * R + 2) * ell := by
    simpa [R, F, J, K] using
      haggregate hsmallAbs le_rfl hslack
  have hcentral' := hcentral (dfLongTarget N) (dfLongTarget_cast_ge N)
  have hendpointCapacity : (restrictedSumset s A).card < T * min U K := by
    apply df95_layer_card_lt_central_min_short hsmallAbs
    simpa [T, U, K] using hcentral'
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.div_pos (le_trans (by norm_num) hBlarge) (by omega)
  have hendRoom' :
      s - (t + J * F + T) + (B.card + R * F + 2 * J * F) + 2 * T ≤
        A.card := by
    simpa [t, R, F, J, T, hBcard] using _hendRoom
  obtain ⟨C, start, d, hCA, hCcard, hd, hlayerPos, hlongC, hshort⟩ :=
    finite_DF95_modular_structure hBA hq hR ht hAP'
      (by simpa [t] using hsupportLayer) hsupportRoom' hcapacity hrichMass
      hRF (by simpa [t, R] using horderLayer) horderRoom'
      (by simpa [t, R, pow_two] using hsubgroupLayer) hsubgroupRoom'
      (by simpa [t, F] using halignLayer) halignRoom' hdouble
      halignMargin hlog hfit (by exact hTpos)
      (by simpa [t, F, J, T] using hendLayer) hendRoom'
      hendpointCapacity
  have hbudget' := hbudget J le_rfl
  have hbudgetReal : (C.card : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
    have hcast : (C.card : ℝ) ≤
        (dfBlockSize N + R * F + 2 * J * F + 2 * T : ℕ) := by
      exact_mod_cast (by simpa [hBcard] using hCcard)
    exact hcast.trans (by simpa [R, F, J, T] using hbudget')
  apply largeSetStructure_of_finite_certificate hCA hd hlayerPos hbudgetReal
      (dfLongTarget_cast_ge N) hlongC hshort
  simpa [U] using dfShortScale_cast_le N

/-- Explicit-threshold form of `eventually_hasLargeSetStructure`. -/
theorem hasEventuallyLargeSetStructure : HasEventuallyLargeSetStructure :=
  hasEventuallyLargeSetStructure_of_eventually eventually_hasLargeSetStructure

/-! ## The rough estimate from a structural certificate -/

private lemma natSqrt_cast_le_realSqrt (N : ℕ) :
    (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
  rw [show (Nat.sqrt N : ℝ) = Real.sqrt ((Nat.sqrt N : ℝ) ^ 2) from by
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
  apply Real.sqrt_le_sqrt
  have h : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hreal : (Nat.sqrt N : ℝ) * Nat.sqrt N ≤ (N : ℝ) := by
    exact_mod_cast h
  simpa [pow_two] using hreal

/-- The finite complementary-block packing argument turns the eventual DF95
structure theorem into the global rough upper bound.  The finite prefix is
absorbed into the absolute constant by `roughUpperBound_of_eventually`. -/
theorem hasRoughUpperBound_of_eventuallyLargeSetStructure
    (hstructure : HasEventuallyLargeSetStructure) : HasRoughUpperBound := by
  obtain ⟨N₀, hN₀⟩ := hstructure
  have hshortLong :=
    eventually_const_mul_rpow_seven_twelfths_le_five_sixths 2 (by positivity)
  have heventual : ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (A.card : ℝ) ≤
        2 * Real.sqrt N + 100003 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
    filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1,
        hshortLong] with N hNstruct hNpos hshortLongN
    intro A hA
    by_cases hlarge :
        (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ)
    · obtain ⟨S⟩ := hN₀ N hNstruct A hA hlarge
      have hlongPosReal : (0 : ℝ) < S.longLength :=
        (show (0 : ℝ) < 3 * (N : ℝ) ^ ((5 : ℝ) / 6) by positivity).trans_le
          S.longLength_ge
      have hlongPos : 0 < S.longLength := by exact_mod_cast hlongPosReal
      have hshortLong' : (2 : ℝ) * S.shortLength ≤ S.longLength := by
        calc
          (2 : ℝ) * S.shortLength ≤
              2 * (N : ℝ) ^ ((7 : ℝ) / 12) := by
            gcongr
            exact S.shortLength_le
          _ ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := hshortLongN
          _ ≤ 3 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
            have : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := by positivity
            linarith
          _ ≤ S.longLength := S.longLength_ge
      have hshortLongNat : 2 * S.shortLength ≤ S.longLength := by
        exact_mod_cast hshortLong'
      have hregular :
          (A \ S.exceptional).card ≤ 2 * Nat.sqrt N + 3 :=
        regular_card_le_two_sqrt_add_three hA.2 S.exceptional_subset
          (by rfl) (S.regular_subset.trans hA.1) S.layer_pos S.step_pos
          hlongPos S.long_progression S.regular_contained hshortLongNat
      have hcardEq :
          A.card = S.exceptional.card + (A \ S.exceptional).card := by
        rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
          S.exceptional_union_regular]
      have hregularReal :
          ((A \ S.exceptional).card : ℝ) ≤ 2 * Real.sqrt N + 3 := by
        calc
          ((A \ S.exceptional).card : ℝ) ≤
              (2 * Nat.sqrt N + 3 : ℕ) := by exact_mod_cast hregular
          _ = 2 * (Nat.sqrt N : ℝ) + 3 := by push_cast; ring
          _ ≤ 2 * Real.sqrt N + 3 := by
            gcongr
            exact natSqrt_cast_le_realSqrt N
      have hpowOne : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 12) :=
        Real.one_le_rpow (by exact_mod_cast hNpos) (by norm_num)
      rw [hcardEq]
      push_cast
      have hexceptional :
          (S.exceptional.card : ℝ) ≤
            100000 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
        have h := S.exceptional_card_le
        norm_num at h ⊢
        exact h
      calc
        (S.exceptional.card : ℝ) + ((A \ S.exceptional).card : ℝ) ≤
            100000 * (N : ℝ) ^ ((5 : ℝ) / 12) +
              (2 * Real.sqrt N + 3) :=
          add_le_add hexceptional hregularReal
        _ ≤ 2 * Real.sqrt N +
            100003 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
          nlinarith
    · have hsmall : (A.card : ℝ) ≤ 2 * Real.sqrt N := by
        have hsqrt : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
        have := le_of_not_gt hlarge
        nlinarith
      exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.1 heventual)
  exact roughUpperBound_of_eventually (N₀ := N₁) (C := 100003)
    (by positivity) hN₁

/-- The Deshouillers--Freiman rough upper bound, globally packaged by
absorbing the finite prefix into its absolute constant. -/
theorem roughUpperBound_exists : HasRoughUpperBound :=
  hasRoughUpperBound_of_eventuallyLargeSetStructure hasEventuallyLargeSetStructure

end

end Erdos874
