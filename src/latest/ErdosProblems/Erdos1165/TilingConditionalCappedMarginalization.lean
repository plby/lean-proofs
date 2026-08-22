/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.CappedCoordinateMassCertificate
import ErdosProblems.Erdos1165.TilingAwayNegativeBinomial

/-!
# Conditional stopped-coordinate marginalization for all six tilings

`TilingFactoredStoppedCoordinateData` normalizes its screened event against
the whole away-coordinate support.  The low-scale Proposition 4.9 argument
instead conditions on a nontrivial broad history: the broad `I₁`
classification, the source `D_eta / Theta_eta` data, and the exact finite
candidate set have already been fixed, and the numerator adds one narrow
window.

This file supplies the corresponding literal finite-coordinate law.  Both
the denominator and numerator are predicates on the reconstructed vector of
away-domino totals.  Their ratio is derived from two explicit finite sums;
no path-space transition inequality is a field of the certificate.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingConditionalCappedMarginalization

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open HLOZTraceCappedProductScreening
open PathInsertion PreStoppingFiber SpatialInsertionFiber
open TilingCappedMarginalization TilingSpatialInsertionFiber
open TilingAwayNegativeBinomial
open TilingStoppedProductDisintegration
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Reconstructing the actual away-total vector -/

/-- The actual truncated away-total vector reconstructed from a grouped
insertion assignment and a proof that it lies below the coordinatewise
cutoff.  This is the value on which the broad-history and narrow-window
acceptors are evaluated. -/
def reconstructedTilingAwayTotals {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (a : TilingAwayCoordinates (cap := cap) t x r D)
    (hupper : ∀ b, tilingAwayTotal t x r D a b < upper b) :
    TruncatedTotals upper :=
  fun b ↦ ⟨tilingAwayTotal t x r D a b, hupper b⟩

/-- An away-total screen is exactly evaluation of its predicate on the
reconstructed total vector.  In particular, the existential total vector
in `TilingAwayTotalsScreen` carries no additional choice. -/
theorem tilingAwayTotalsScreen_iff_reconstructed
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (screen : TruncatedTotals upper → Prop)
    (a : TilingAwayCoordinates (cap := cap) t x r D)
    (hupper : ∀ b, tilingAwayTotal t x r D a b < upper b) :
    TilingAwayTotalsScreen t x r D upper screen a ↔
      screen (reconstructedTilingAwayTotals t x r D upper a hupper) := by
  constructor
  · rintro ⟨ell, hell, htotal⟩
    have heq : ell = reconstructedTilingAwayTotals t x r D upper a hupper := by
      funext b
      apply Fin.ext
      exact (htotal b).symm
    rw [heq] at hell
    exact hell
  · intro hscreen
    refine ⟨reconstructedTilingAwayTotals t x r D upper a hupper,
      hscreen, ?_⟩
    intro b
    rfl

/-- Direct reconstruction from the original capped insertion coordinates.
The value at an away domino is definitionally its complete insertion total,
not a selected coordinate or a prefix approximation. -/
def reconstructedTilingAwayTotalsOfCoordinates {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (q : TilingCappedCoordinates i cap)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b) :
    TruncatedTotals upper :=
  fun b ↦ ⟨tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1,
    hupper b⟩

/-- Coordinate reconstruction after the distinguished/away split.  This is
the deterministic seam used by a concrete broad-`I₁` classification: once
the literal upper support is known, accepting the split away coordinates is
equivalent to accepting their uniquely reconstructed total vector. -/
theorem tilingAwayTotalsScreen_split_iff_reconstructed
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (screen : TruncatedTotals upper → Prop)
    (q : TilingCappedCoordinates i cap)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b) :
    TilingAwayTotalsScreen t x r D upper screen
        (splitTilingCoordinatesEquiv t x r D q).2 ↔
      screen
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) := by
  constructor
  · rintro ⟨ell, hell, htotal⟩
    have heq : ell = reconstructedTilingAwayTotalsOfCoordinates
        t x r D upper q hupper := by
      funext b
      apply Fin.ext
      exact (htotal b).symm.trans
        (tilingAwayTotal_split_eq_dominoTotal t x r D q b)
    rw [heq] at hell
    exact hell
  · intro hscreen
    refine ⟨reconstructedTilingAwayTotalsOfCoordinates
      t x r D upper q hupper, hscreen, ?_⟩
    intro b
    exact tilingAwayTotal_split_eq_dominoTotal t x r D q b

/-! ## The exact conditional finite-product ratio -/

/-- Conditional mass of `screened` inside a nontrivial finite `base`
screen.  Both masses use the same normalized independent away-coordinate
law, so its global normalization cancels from the quotient. -/
noncomputable def conditionalScreenMass
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    [DecidablePred base] [DecidablePred screened] : ℝ :=
  screenMass pointMass upper screened /
    screenMass pointMass upper base

theorem screenMass_mono_of_pointMass_nonneg
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    [DecidablePred base] [DecidablePred screened]
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, screened ell → base ell) :
    screenMass pointMass upper screened ≤
      screenMass pointMass upper base := by
  classical
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _
  have hjoint : 0 ≤ jointMass pointMass upper ell := by
    exact Finset.prod_nonneg fun b _ ↦ hpoint b (ell b)
  have htotal : 0 ≤ ∑ z : TruncatedTotals upper,
      jointMass pointMass upper z := by
    exact Finset.sum_nonneg fun z _ ↦
      Finset.prod_nonneg fun b _ ↦ hpoint b (z b)
  have hnormalized : 0 ≤ normalizedJointMass pointMass upper ell := by
    exact div_nonneg hjoint htotal
  by_cases hs : screened ell
  · rw [if_pos hs, if_pos (hsub ell hs)]
  · rw [if_neg hs]
    by_cases hb : base ell
    · simp only [if_pos hb]
      exact hnormalized
    · simp only [if_neg hb]
      exact le_rfl

theorem conditionalScreenMass_le_one_of_subset
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    [DecidablePred base] [DecidablePred screened]
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, screened ell → base ell)
    (hbasePos : 0 < screenMass pointMass upper base) :
    conditionalScreenMass pointMass upper base screened ≤ 1 := by
  unfold conditionalScreenMass
  exact (div_le_one hbasePos).2
    (screenMass_mono_of_pointMass_nonneg pointMass upper base screened
      hpoint hsub)

/-- A coordinatewise window screen has exactly the product of its
one-coordinate window masses. -/
theorem screenMass_all_coordinate_windows_eq_prod
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (window : Domino → Finset ℕ) :
    screenMass pointMass upper
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈ window b) =
      ∏ b, ∑ v : Fin (upper b),
        if (v : ℕ) ∈ window b then
          coordinateMass pointMass upper b v else 0 := by
  classical
  rw [screenMass_eq_product]
  calc
    (∑ ell : TruncatedTotals upper,
        if (∀ b, (ell b : ℕ) ∈ window b) then
          ∏ b, coordinateMass pointMass upper b (ell b)
        else 0) =
        ∑ ell : TruncatedTotals upper,
          ∏ b, if (ell b : ℕ) ∈ window b then
            coordinateMass pointMass upper b (ell b) else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      by_cases hall : ∀ b, (ell b : ℕ) ∈ window b
      · rw [if_pos hall]
        apply Finset.prod_congr rfl
        intro b _
        rw [if_pos (hall b)]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨b, hb⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ b)
        rw [if_neg hb]
    _ = ∏ b, ∑ v : Fin (upper b),
        if (v : ℕ) ∈ window b then
          coordinateMass pointMass upper b v else 0 :=
      (Fintype.prod_sum fun b (v : Fin (upper b)) ↦
        if (v : ℕ) ∈ window b then
          coordinateMass pointMass upper b v else 0).symm

/-- A one-coordinate window comparison survives arbitrary fixed
coordinatewise broad-history classifications on all other coordinates. -/
theorem conditionalScreenMass_all_coordinate_windows_le
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (chosen : Domino) (baseWindow screenedWindow : Domino → Finset ℕ)
    {C : ℝ}
    (hbasePos : 0 < screenMass pointMass upper
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ baseWindow b))
    (hsame : ∀ b, b ≠ chosen → screenedWindow b = baseWindow b)
    (hcoordinateNonneg : ∀ b (v : Fin (upper b)),
      0 ≤ coordinateMass pointMass upper b v)
    (hlocal :
      (∑ v : Fin (upper chosen),
        if (v : ℕ) ∈ screenedWindow chosen then
          coordinateMass pointMass upper chosen v else 0) ≤
        C * ∑ v : Fin (upper chosen),
          if (v : ℕ) ∈ baseWindow chosen then
            coordinateMass pointMass upper chosen v else 0) :
    conditionalScreenMass pointMass upper
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈ baseWindow b)
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈ screenedWindow b) ≤ C := by
  classical
  let localMass := fun (window : Domino → Finset ℕ) (b : Domino) ↦
    ∑ v : Fin (upper b), if (v : ℕ) ∈ window b then
      coordinateMass pointMass upper b v else 0
  have hlocalNonneg : ∀ window b, 0 ≤ localMass window b := by
    intro window b
    apply Finset.sum_nonneg
    intro v _
    split
    · exact hcoordinateNonneg b v
    · exact le_rfl
  have hrest :
      (∏ b ∈ (Finset.univ.erase chosen), localMass screenedWindow b) =
        ∏ b ∈ (Finset.univ.erase chosen), localMass baseWindow b := by
    apply Finset.prod_congr rfl
    intro b hb
    have hne : b ≠ chosen := (Finset.mem_erase.mp hb).1
    simp only [localMass, hsame b hne]
  have hproduct :
      (∏ b, localMass screenedWindow b) ≤
        C * ∏ b, localMass baseWindow b := by
    rw [← Finset.mul_prod_erase Finset.univ
        (localMass screenedWindow) (Finset.mem_univ chosen),
      ← Finset.mul_prod_erase Finset.univ
        (localMass baseWindow) (Finset.mem_univ chosen), hrest]
    calc
      localMass screenedWindow chosen *
          ∏ b ∈ Finset.univ.erase chosen, localMass baseWindow b ≤
        (C * localMass baseWindow chosen) *
          ∏ b ∈ Finset.univ.erase chosen, localMass baseWindow b :=
        mul_le_mul_of_nonneg_right hlocal
          (Finset.prod_nonneg fun b _ ↦ hlocalNonneg baseWindow b)
      _ = C * (localMass baseWindow chosen *
          ∏ b ∈ Finset.univ.erase chosen, localMass baseWindow b) := by ring
  unfold conditionalScreenMass
  rw [div_le_iff₀ hbasePos]
  simpa only [screenMass_all_coordinate_windows_eq_prod, localMass]
    using hproduct

/-- Concrete all-six specialization: the checked negative-binomial window
ratio at the chosen away domino supplies the finite conditional product
bound, while all other broad-history coordinate windows are held fixed. -/
theorem tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (baseWindow screenedWindow :
      TilingCappedMarginalization.TilingAwayDomino t x r D → Finset ℕ)
    {C : ℝ}
    (hbasePos : 0 < screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ baseWindow b))
    (hsame : ∀ b, b ≠ chosen → screenedWindow b = baseWindow b)
    (hscreenedUpper : ∀ v ∈ screenedWindow chosen, v < upper chosen)
    (hbaseUpper : ∀ v ∈ baseWindow chosen, v < upper chosen)
    (hscreenedCap : ∀ v ∈ screenedWindow chosen, v ≤ cap)
    (hbaseCap : ∀ v ∈ baseWindow chosen, v ≤ cap)
    (hcoordinates :
      0 < Fintype.card (TilingCoordinatesAt t x r chosen.1))
    (hratio :
      SmallWindow.windowMass
          (Fintype.card (TilingCoordinatesAt t x r chosen.1))
          (screenedWindow chosen) ≤
        C * SmallWindow.windowMass
          (Fintype.card (TilingCoordinatesAt t x r chosen.1))
          (baseWindow chosen)) :
    conditionalScreenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈ baseWindow b)
        (fun ell ↦ ∀ b, (ell b : ℕ) ∈ screenedWindow b) ≤ C := by
  apply conditionalScreenMass_all_coordinate_windows_le
    (tilingAwayPointMass (cap := cap) t x r D) upper chosen
    baseWindow screenedWindow hbasePos hsame
  · intro b v
    rw [coordinateMass, if_pos v.isLt]
    exact div_nonneg
      (tilingAwayExactTotalMass_nonneg t x r D b v)
      (Finset.sum_nonneg fun j _ ↦
        tilingAwayExactTotalMass_nonneg t x r D b j)
  · exact tilingAway_coordinateMass_window_ratio
      t x r D upper chosen (screenedWindow chosen) (baseWindow chosen)
      hscreenedUpper hbaseUpper hscreenedCap hbaseCap hcoordinates hratio

theorem conditionalScreenMass_mul_base
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    [DecidablePred base] [DecidablePred screened]
    (hbase : screenMass pointMass upper base ≠ 0) :
    conditionalScreenMass pointMass upper base screened *
        screenMass pointMass upper base =
      screenMass pointMass upper screened := by
  unfold conditionalScreenMass
  exact div_mul_cancel₀ _ hbase

/-- One coordinate predicate whose accepted stopped mass factors through a
finite away-total screen.  This helper is the arbitrary-denominator version
of the unconditional distinguished marginalization identity. -/
theorem tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (predicate : TilingCappedCoordinates i cap → Prop)
    [DecidablePred predicate]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen]
    (hfactor : ∀ q,
      predicate q ∧ TilingStoppingAccepted tau t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0) :
    tilingStoppedAcceptedGeometricMass tau t x r cap tail predicate =
      screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell := by
  classical
  rw [tilingStoppedAcceptedGeometricMass_eq_indicatorSum]
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if predicate q ∧ TilingStoppingAccepted tau t x r
            (fun k ↦ (q k : ℕ)) tail then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
        ∑ q : TilingCappedCoordinates i cap,
          if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
              TilingAwayTotalsScreen t x r D upper screen
                ((splitTilingCoordinatesEquiv t x r D q).2) then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      exact if_congr (hfactor q) rfl rfl
    _ = ∑ ell : TruncatedTotals upper,
        if screen ell then
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell
        else 0 :=
      tilingCappedScreenedMass_factorization
        t x r D selected upper screen
    _ = screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell :=
      (screenMass_mul_distinguishedBase
        (tilingAwayPointMass (cap := cap) t x r D) upper screen
        (fun d ↦ if selected d then
          tilingDistinguishedAssignmentMass t x r D d else 0) htotal).symm

/-- Exact conditional factorization.  The denominator may encode the whole
broad history, while the numerator may add a narrow window.  The only
nonvanishing assumption is the literal finite denominator mass. -/
theorem tilingStoppedAcceptedGeometricMass_conditional_product_of_factorization
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (basePredicate screenedPredicate :
      TilingCappedCoordinates i cap → Prop)
    [DecidablePred basePredicate] [DecidablePred screenedPredicate]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (baseAccepts screenedAccepts : TruncatedTotals upper → Prop)
    [DecidablePred baseAccepts] [DecidablePred screenedAccepts]
    (hbase : ∀ q,
      basePredicate q ∧ TilingStoppingAccepted tau t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper baseAccepts
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (hscreened : ∀ q,
      screenedPredicate q ∧ TilingStoppingAccepted tau t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screenedAccepts
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (hbaseMass : screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper baseAccepts ≠ 0) :
    tilingStoppedAcceptedGeometricMass tau t x r cap tail
        screenedPredicate =
      conditionalScreenMass
          (tilingAwayPointMass (cap := cap) t x r D) upper
          baseAccepts screenedAccepts *
        tilingStoppedAcceptedGeometricMass tau t x r cap tail
          basePredicate := by
  let common := ∑ ell : TruncatedTotals upper,
    distinguishedAwayMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun d ↦ if selected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) ell
  rw [tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      tau t x r tail screenedPredicate D selected upper screenedAccepts
      hscreened htotal,
    tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      tau t x r tail basePredicate D selected upper baseAccepts hbase htotal]
  change screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper screenedAccepts * common =
    conditionalScreenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
        baseAccepts screenedAccepts *
      (screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        baseAccepts * common)
  rw [← mul_assoc, conditionalScreenMass_mul_base _ _ _ _ hbaseMass]

/-! ## Conditional stopped-coordinate certificates -/

/-- Factored all-six stopped-coordinate data with a genuine conditional
denominator.  `baseAccepts` is intended to fix the broad `I₁`, source
eligibility, and exact candidate-set classification.  `screenedAccepts`
adds the chosen candidate's narrow window.

The two factorization fields are deterministic reconstruction statements.
`product_bound` is solely a finite-product bound, normally supplied by the
checked negative-binomial window ratio. -/
structure TilingConditionalFactoredStoppedCoordinateData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  tiling : index → ℕ → DominoTiling
  retainedCount : index → ℕ → ℕ
  start : index → ℕ → Point
  retained : ∀ z cap,
    TilingRetainedWord (tiling z cap) (start z cap) (retainedCount z cap)
  tail : index → ℕ → List Direction
  stoppingTime : index → ℕ → StepPath → ℕ
  isStoppingTime : ∀ z cap, IsFiniteStoppingTime (stoppingTime z cap)
  basePredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screenedPredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screened_subset_base : ∀ z cap q,
    screenedPredicate z cap q → basePredicate z cap q
  base_subset_piece : ∀ z cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (basePredicate z cap)) ⊆ piece z
  distinguished : index → ℕ → Finset Point
  selected : ∀ z cap,
    TilingDistinguishedCoordinates (cap := cap)
      (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → Prop
  upper : ∀ z cap,
    TilingCappedMarginalization.TilingAwayDomino
      (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → ℕ
  baseAccepts : ∀ z cap, TruncatedTotals (upper z cap) → Bool
  screenedAccepts : ∀ z cap, TruncatedTotals (upper z cap) → Bool
  screenedAccepts_subset_base : ∀ z cap ell,
    screenedAccepts z cap ell = true → baseAccepts z cap ell = true
  base_factorization : ∀ z cap q,
    basePredicate z cap q ∧
        TilingStoppingAccepted (stoppingTime z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun ell ↦ baseAccepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  screened_factorization : ∀ z cap q,
    screenedPredicate z cap q ∧
        TilingStoppingAccepted (stoppingTime z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun ell ↦ screenedAccepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  upper_pos : ∀ z cap b, 0 < upper z cap b
  base_mass_ne_zero : ∀ z cap,
    screenMass
      (tilingAwayPointMass (cap := cap) (tiling z cap) (start z cap)
        (retained z cap) (distinguished z cap)) (upper z cap)
      (fun ell ↦ baseAccepts z cap ell = true) ≠ 0
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  product_bound : ∀ z cap,
    conditionalScreenMass
      (tilingAwayPointMass (cap := cap) (tiling z cap) (start z cap)
        (retained z cap) (distinguished z cap)) (upper z cap)
      (fun ell ↦ baseAccepts z cap ell = true)
      (fun ell ↦ screenedAccepts z cap ell = true) ≤ cost.toReal

/-- Exact coordinate-mass specification constructed from the conditional
factored data.  Its `productProbability` is the finite conditional ratio,
and its disintegration equality is proved by finite marginalization. -/
noncomputable def coordinateMassSpecOfTilingConditionalFactoredData
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData piece next cost) :
    CoordinateMassSpec piece next cost := by
  classical
  refine {
    screened := fun z cap ↦ walkLift
      (tilingPreStoppingFiberEvent (data.stoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.screenedPredicate z cap))
    fiber := fun z cap ↦ walkLift
      (tilingPreStoppingFiberEvent (data.stoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.basePredicate z cap))
    measurable_screened := fun z cap ↦ measurableSet_walkLift
      (measurableSet_tilingPreStoppingFiberEvent (data.isStoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.screenedPredicate z cap))
    measurable_fiber := fun z cap ↦ measurableSet_walkLift
      (measurableSet_tilingPreStoppingFiberEvent (data.isStoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.basePredicate z cap))
    screened_subset_piece := ?_
    fiber_subset_piece := data.base_subset_piece
    monotone_screened := data.monotone_screened
    transition_covered := data.transition_covered
    commonFactor := fun z cap ↦
      prefixFiberConstant (data.retainedCount z cap) (data.tail z cap)
    screenedCoordinateMass := fun z cap ↦
      tilingStoppedAcceptedGeometricMass (data.stoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.screenedPredicate z cap)
    fiberCoordinateMass := fun z cap ↦
      tilingStoppedAcceptedGeometricMass (data.stoppingTime z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
        (data.tail z cap) (data.basePredicate z cap)
    productProbability := fun z cap ↦
      conditionalScreenMass
        (tilingAwayPointMass (cap := cap) (data.tiling z cap)
          (data.start z cap) (data.retained z cap)
          (data.distinguished z cap)) (data.upper z cap)
        (fun ell ↦ data.baseAccepts z cap ell = true)
        (fun ell ↦ data.screenedAccepts z cap ell = true)
    coordinate_identity := ?_
    screened_event_mass := ?_
    fiber_event_mass := ?_
    product_bound := data.product_bound }
  · intro z cap s hs
    apply data.base_subset_piece z cap
    exact ⟨hs.1, tilingPreStoppingFiberEvent_mono
      (data.stoppingTime z cap) (data.tiling z cap) (data.start z cap)
      (data.retained z cap) (data.tail z cap)
      (data.screened_subset_base z cap) hs.2⟩
  · intro z cap
    apply tilingStoppedAcceptedGeometricMass_conditional_product_of_factorization
      (data.stoppingTime z cap) (data.tiling z cap) (data.start z cap)
      (data.retained z cap) (data.tail z cap)
      (data.basePredicate z cap) (data.screenedPredicate z cap)
      (data.distinguished z cap) (data.selected z cap) (data.upper z cap)
      (fun ell ↦ data.baseAccepts z cap ell = true)
      (fun ell ↦ data.screenedAccepts z cap ell = true)
      (data.base_factorization z cap) (data.screened_factorization z cap)
    · exact tilingAwayPointMass_normalization_ne_zero_of_upper_pos
        (data.tiling z cap) (data.start z cap) (data.retained z cap)
        (data.distinguished z cap) (data.upper z cap) (data.upper_pos z cap)
    · exact data.base_mass_ne_zero z cap
  · intro z cap
    exact simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      (data.isStoppingTime z cap) (data.tiling z cap) (data.start z cap)
      (data.retained z cap) cap (data.tail z cap)
      (data.screenedPredicate z cap)
  · intro z cap
    exact simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      (data.isStoppingTime z cap) (data.tiling z cap) (data.start z cap)
      (data.retained z cap) cap (data.tail z cap)
      (data.basePredicate z cap)

/-- Complete capped product certificate for the conditional all-six
coordinate law. -/
noncomputable def cappedProductScreenCertificateOfTilingConditionalFactoredData
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData piece next cost) :
    PreStoppingConditionalLaw.CappedProductScreenCertificate
      piece next cost :=
  cappedProductScreenCertificateOfCoordinateMassSpec
    (coordinateMassSpecOfTilingConditionalFactoredData data)

/-- The exact restricted-real factorization exposed without converting it
to a transition estimate. -/
theorem restrictedReal_conditional_factorization
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (data : TilingConditionalFactoredStoppedCoordinateData piece next cost)
    (z : index) (cap : ℕ) :
    (simpleRandomWalk.restrict (piece z)).real
        ((coordinateMassSpecOfTilingConditionalFactoredData data).screened
          z cap) =
      (coordinateMassSpecOfTilingConditionalFactoredData data).productProbability
          z cap *
        (simpleRandomWalk.restrict (piece z)).real
          ((coordinateMassSpecOfTilingConditionalFactoredData data).fiber
            z cap) :=
  (coordinateMassSpecOfTilingConditionalFactoredData data).disintegrate z cap

end

end Erdos1165.TilingConditionalCappedMarginalization
