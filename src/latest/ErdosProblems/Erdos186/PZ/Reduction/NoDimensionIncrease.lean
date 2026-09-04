/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.FailureEstimates
import ErdosProblems.Erdos186.PZ.Reduction.CoordinateReplacement
import ErdosProblems.Erdos186.DiscreteJohn

/-!
# The no-dimension-increase estimate for coordinate replacements

This file proves the residue-fibre substitute for the discrete John step in
Pham--Zakharov Lemma 8.  Because a coordinate replacement lies in the
difference of the current coefficient box, all subset sums used by the next
CFP witness lie in an explicit centered coordinate GAP.  Dividing a
difference of two such subset sums by the next dilation scale still lies in
a fixed dilation of that centered GAP.  The residue-fibre theorem then
cancels the scale and bounds the next progression by the current one.
-/

namespace Erdos186.PZ.Reduction

open scoped BigOperators

noncomputable section

variable {d r : ℕ}

namespace GAP

/-- Evaluation in a dilated difference coefficient GAP is coordinatewise. -/
@[simp] theorem dilate_differenceCoefficientGAP_coordPoint
    (P : Erdos186.GAP d r) (t : ℕ)
    (n : ((differenceCoefficientGAP P).dilate t).Coord) :
    ((differenceCoefficientGAP P).dilate t).coordPoint n =
      fun j ↦ -((t * (P.widths j - 1) : ℕ) : ℤ) + (n j : ℤ) := by
  funext j
  simp [Erdos186.GAP.coordPoint, Erdos186.GAP.dilate,
    differenceCoefficientGAP, Nat.cast_sub (P.width_pos j)]
  ring

/-- Coordinate characterization of a positive integral dilation of the
standard centered difference GAP. -/
theorem mem_dilate_differenceCoefficientGAP_iff
    (P : Erdos186.GAP d r) (t : ℕ) (z : LatticePoint r) :
    z ∈ ((differenceCoefficientGAP P).dilate t).carrier ↔
      ∀ i, -((t * (P.widths i - 1) : ℕ) : ℤ) ≤ z i ∧
        z i ≤ ((t * (P.widths i - 1) : ℕ) : ℤ) := by
  constructor
  · intro hz i
    obtain ⟨n, rfl⟩ := Erdos186.GAP.mem_carrier_iff.mp hz
    have hn := (n i).isLt
    change (n i : ℕ) <
      t * ((differenceCoefficientGAP P).widths i - 1) + 1 at hn
    have hwidth : (differenceCoefficientGAP P).widths i - 1 =
        2 * (P.widths i - 1) := by
      change (2 * (P.widths i - 1) + 1) - 1 = _
      omega
    rw [hwidth] at hn
    rw [show t * (2 * (P.widths i - 1)) =
        2 * (t * (P.widths i - 1)) by ring] at hn
    rw [dilate_differenceCoefficientGAP_coordPoint]
    constructor <;> push_cast at hn ⊢ <;> omega
  · intro hz
    let n : ((differenceCoefficientGAP P).dilate t).Coord := fun i ↦
      ⟨(z i + (t * (P.widths i - 1) : ℕ)).toNat, by
        have hi := hz i
        have hnonneg : 0 ≤ z i + (t * (P.widths i - 1) : ℕ) := by
          omega
        have hupper : z i + (t * (P.widths i - 1) : ℕ) ≤
            (2 * (t * (P.widths i - 1) : ℕ) : ℕ) := by
          push_cast
          omega
        change (z i + (t * (P.widths i - 1) : ℕ)).toNat <
          t * ((differenceCoefficientGAP P).widths i - 1) + 1
        have htoNat : (z i + (t * (P.widths i - 1) : ℕ)).toNat ≤
            2 * (t * (P.widths i - 1)) := by
          rw [Int.toNat_le]
          exact hupper
        change _ < t * (2 * (P.widths i - 1)) + 1
        rw [show t * (2 * (P.widths i - 1)) =
          2 * (t * (P.widths i - 1)) by ring]
        omega⟩
    refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    funext i
    have hi := hz i
    have hnonneg : 0 ≤ z i + (t * (P.widths i - 1) : ℕ) := by
      omega
    rw [dilate_differenceCoefficientGAP_coordPoint]
    simp only [n]
    rw [Int.toNat_of_nonneg hnonneg]
    ring

/-- If two points of an `s`-dilate of a coefficient-difference GAP differ
by `k*q`, and `s ≤ den*k`, then `q` lies in the fixed `2*den` dilate.  This
is the cancellation estimate shared by the initial-box and replacement
forms of Lemma 8. -/
theorem divided_sub_mem_dilate_differenceCoefficientGAP
    (P : Erdos186.GAP d r) {s k den : ℕ}
    (hk : 0 < k) (hscale : s ≤ den * k)
    (q : LatticePoint r) {x y : LatticePoint r}
    (hx : x ∈ ((differenceCoefficientGAP P).dilate s).carrier)
    (hy : y ∈ ((differenceCoefficientGAP P).dilate s).carrier)
    (hxy : ∀ j, x j - y j = (k : ℤ) * q j) :
    q ∈ ((differenceCoefficientGAP P).dilate (2 * den)).carrier := by
  have hxQ := (mem_dilate_differenceCoefficientGAP_iff P s x).mp hx
  have hyQ := (mem_dilate_differenceCoefficientGAP_iff P s y).mp hy
  rw [mem_dilate_differenceCoefficientGAP_iff]
  intro i
  let radius : ℕ := P.widths i - 1
  have hboundNat : 2 * s * radius ≤ k * (2 * den * radius) := by
    calc
      2 * s * radius ≤ 2 * (den * k) * radius :=
        Nat.mul_le_mul_right radius (Nat.mul_le_mul_left 2 hscale)
      _ = k * (2 * den * radius) := by ring
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hboundZ : ((2 * s * radius : ℕ) : ℤ) ≤
      ((k * (2 * den * radius) : ℕ) : ℤ) := by
    exact_mod_cast hboundNat
  have hupperMul : (k : ℤ) * q i ≤
      (k : ℤ) * (2 * den * radius : ℕ) := by
    rw [← hxy i]
    have hxi := (hxQ i).2
    have hyi := (hyQ i).1
    calc
      x i - y i ≤ ((2 * s * radius : ℕ) : ℤ) := by
        dsimp [radius] at hxi hyi ⊢
        linarith
      _ ≤ ((k * (2 * den * radius) : ℕ) : ℤ) := hboundZ
      _ = (k : ℤ) * (2 * den * radius : ℕ) := by
        push_cast
        ring
  have hlowerMul : (k : ℤ) * (-(2 * den * radius : ℕ) : ℤ) ≤
      (k : ℤ) * q i := by
    rw [← hxy i]
    have hxi := (hxQ i).1
    have hyi := (hyQ i).2
    calc
      (k : ℤ) * (-(2 * den * radius : ℕ) : ℤ) =
          -((k * (2 * den * radius) : ℕ) : ℤ) := by
        push_cast
        ring
      _ ≤ -((2 * s * radius : ℕ) : ℤ) := neg_le_neg hboundZ
      _ ≤ x i - y i := by
        dsimp [radius] at hxi hyi ⊢
        linarith
  constructor
  · exact le_of_mul_le_mul_left hlowerMul hkZ
  · exact le_of_mul_le_mul_left hupperMul hkZ

end GAP

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  {selector : BoundedCFPSelector C} {d : ℕ}
  {A : Finset (LatticePoint d)} {hA : selector.Eligible A} {δ γ : ℝ}

namespace BoundedIrreducibilityFailure

variable (F : BoundedIrreducibilityFailure selector A hA δ γ)

private abbrev current
    (_F : BoundedIrreducibilityFailure selector A hA δ γ) : SelectedCFP A :=
  selector.chosen A hA

private abbrev next : SelectedCFP F.nextPoints :=
  selector.chosen F.nextPoints F.shifted_eligible

/-- The subset sums used by the next CFP witness stay in the corresponding
dilation of the current difference coefficient GAP. -/
theorem nextReserved_subsetSums_subset_differenceDilate :
    Erdos186.GAP.subsetSums F.next.witness.reserved ⊆
      ((GAP.differenceCoefficientGAP F.current.progression).dilate
        F.next.reserveBound).carrier := by
  apply GAP.subsetSums_subset_dilate_of_zero_mem
    (GAP.differenceCoefficientGAP F.current.progression)
    (GAP.zero_mem_differenceCoefficientGAP F.current.progression)
  · exact F.next.witness.reserved_subset.trans
      F.nextPoints_subset_differenceGAP
  · exact F.next.witness.reserved_small

/-- Dividing a difference of two next-witness subset sums by the positive
next dilation scale lands in a fixed dilation of the current difference
coefficient GAP. -/
theorem divided_subsetSum_difference_mem_controlDilation
    (q : LatticePoint F.current.dimension)
    (hq : ∃ x ∈ Erdos186.GAP.subsetSums F.next.witness.reserved,
      ∃ y ∈ Erdos186.GAP.subsetSums F.next.witness.reserved,
        ∀ j, x j - y j = (F.next.dilation : ℤ) * q j) :
    q ∈ ((GAP.differenceCoefficientGAP F.current.progression).dilate
      (2 * F.next.witness.scaleDen)).carrier := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hq
  have hxQ := GAP.mem_dilate_differenceCoefficientGAP_iff
    F.current.progression F.next.reserveBound x |>.mp
      (F.nextReserved_subsetSums_subset_differenceDilate hx)
  have hyQ := GAP.mem_dilate_differenceCoefficientGAP_iff
    F.current.progression F.next.reserveBound y |>.mp
      (F.nextReserved_subsetSums_subset_differenceDilate hy)
  rw [GAP.mem_dilate_differenceCoefficientGAP_iff]
  intro i
  let radius : ℕ := F.current.progression.widths i - 1
  have hs : F.next.reserveBound ≤
      F.next.witness.scaleDen * F.next.dilation := by
    calc
      F.next.reserveBound = 1 * F.next.reserveBound := by simp
      _ ≤ F.next.witness.scaleNum * F.next.reserveBound :=
        Nat.mul_le_mul_right _ F.next.witness.scaleNum_pos
      _ ≤ F.next.witness.scaleDen * F.next.dilation :=
        F.next.witness.scale_lower
  have hboundNat : 2 * F.next.reserveBound * radius ≤
      F.next.dilation * (2 * F.next.witness.scaleDen * radius) := by
    calc
      2 * F.next.reserveBound * radius ≤
          2 * (F.next.witness.scaleDen * F.next.dilation) * radius :=
        Nat.mul_le_mul_right radius (Nat.mul_le_mul_left 2 hs)
      _ = F.next.dilation *
          (2 * F.next.witness.scaleDen * radius) := by ring
  have hk : (0 : ℤ) < F.next.dilation := by
    exact_mod_cast F.next.witness.k_pos
  have hboundZ : ((2 * F.next.reserveBound * radius : ℕ) : ℤ) ≤
      ((F.next.dilation *
        (2 * F.next.witness.scaleDen * radius) : ℕ) : ℤ) := by
    exact_mod_cast hboundNat
  have hupperMul : (F.next.dilation : ℤ) * q i ≤
      (F.next.dilation : ℤ) *
        (2 * F.next.witness.scaleDen * radius : ℕ) := by
    rw [← hxy i]
    have hxi := (hxQ i).2
    have hyi := (hyQ i).1
    calc
      x i - y i ≤ ((2 * F.next.reserveBound * radius : ℕ) : ℤ) := by
        dsimp [radius] at hxi hyi ⊢
        linarith
      _ ≤ ((F.next.dilation *
          (2 * F.next.witness.scaleDen * radius) : ℕ) : ℤ) := hboundZ
      _ = (F.next.dilation : ℤ) *
          (2 * F.next.witness.scaleDen * radius : ℕ) := by
        push_cast
        ring
  have hlowerMul : (F.next.dilation : ℤ) *
      (-(2 * F.next.witness.scaleDen * radius : ℕ) : ℤ) ≤
        (F.next.dilation : ℤ) * q i := by
    rw [← hxy i]
    have hxi := (hxQ i).1
    have hyi := (hyQ i).2
    calc
      (F.next.dilation : ℤ) *
          (-(2 * F.next.witness.scaleDen * radius : ℕ) : ℤ) =
          -((F.next.dilation *
            (2 * F.next.witness.scaleDen * radius) : ℕ) : ℤ) := by
        push_cast
        ring
      _ ≤ -((2 * F.next.reserveBound * radius : ℕ) : ℤ) :=
        neg_le_neg hboundZ
      _ ≤ x i - y i := by
        dsimp [radius] at hxi hyi ⊢
        linarith
  constructor
  · exact le_of_mul_le_mul_left hlowerMul hk
  · exact le_of_mul_le_mul_left hupperMul hk

/-- Source-faithful no-dimension-increase estimate for a coordinate
replacement.  The proof is the residue-fibre cancellation substitute for
the qualitative discrete John theorem: it does not require a separately
postulated certificate. -/
theorem noDimensionIncrease :
    F.next.progression.volume ≤
      2 ^ F.next.dimension *
        ((2 * F.next.witness.scaleDen + 1) ^ F.current.dimension *
          (2 ^ F.current.dimension * F.current.progression.volume)) := by
  let Q := GAP.differenceCoefficientGAP F.current.progression
  let sums := Erdos186.GAP.subsetSums F.next.witness.reserved
  let control := (Q.dilate (2 * F.next.witness.scaleDen)).carrier
  have hcontain : ∀ n : (F.next.progression.dilate F.next.dilation).Coord,
      (fun j ↦ F.next.witness.translatePoint j +
        (F.next.progression.dilate F.next.dilation).coordPoint n j) ∈ sums := by
    intro n
    apply F.next.witness.covered
    rw [CFP.mem_translate_iff]
    exact ⟨(F.next.progression.dilate F.next.dilation).coordPoint n,
      (F.next.progression.dilate F.next.dilation).coordPoint_mem_carrier n,
      rfl⟩
  have hfiber : F.next.progression.volume ≤
      2 ^ F.next.dimension * control.card := by
    exact DiscreteJohn.volume_le_pow_two_mul_card_of_translate_containment
      F.next.progression F.next.witness.progression_proper
      F.next.witness.k_pos F.next.witness.translatePoint sums control
      hcontain (F.divided_subsetSum_difference_mem_controlDilation)
  calc
    F.next.progression.volume ≤ 2 ^ F.next.dimension * control.card := hfiber
    _ ≤ 2 ^ F.next.dimension * (Q.dilate
          (2 * F.next.witness.scaleDen)).volume :=
      Nat.mul_le_mul_left _ (Erdos186.GAP.card_carrier_le_volume _)
    _ ≤ 2 ^ F.next.dimension *
        ((2 * F.next.witness.scaleDen + 1) ^ F.current.dimension * Q.volume) :=
      Nat.mul_le_mul_left _ (Erdos186.GAP.volume_dilate_le _ _)
    _ ≤ 2 ^ F.next.dimension *
        ((2 * F.next.witness.scaleDen + 1) ^ F.current.dimension *
          (2 ^ F.current.dimension * F.current.progression.volume)) := by
      exact Nat.mul_le_mul_left _ <|
        Nat.mul_le_mul_left _ <|
          GAP.differenceCoefficientGAP_volume_le F.current.progression

end BoundedIrreducibilityFailure

namespace CoordinateReplacement

variable {S T : CoordinateReplacementState selector}

/-- Coordinate replacement is obtained by restriction, identification, and
translation, so it can never increase cardinality. -/
theorem card_le (hST : CoordinateReplacement selector δ γ S T) :
    T.points.card ≤ S.points.card := by
  obtain ⟨F, rfl⟩ := hST
  calc
    F.nextState.points.card = F.retained.card := F.card_nextPoints
    _ ≤ (selector.chosen S.points S.eligible).identifiedCore.card :=
      Finset.card_le_card F.retained_subset
    _ = (selector.chosen S.points S.eligible).core.card :=
      (selector.chosen S.points S.eligible).card_identifiedCore
    _ ≤ S.points.card := Finset.card_le_card
      (selector.chosen S.points S.eligible).witness.core_subset

/-- The next ambient lattice is exactly the current selected coefficient
dimension. -/
theorem next_ambientDimension (hST : CoordinateReplacement selector δ γ S T) :
    T.ambientDimension = S.selected.dimension := by
  obtain ⟨F, rfl⟩ := hST
  rfl

/-- Relation-level form of the residue-fibre volume estimate. -/
theorem selectedVolume_le (hST : CoordinateReplacement selector δ γ S T) :
    T.selected.progression.volume ≤
      2 ^ T.selected.dimension *
        ((2 * T.selected.witness.scaleDen + 1) ^ S.selected.dimension *
          (2 ^ S.selected.dimension * S.selected.progression.volume)) := by
  obtain ⟨F, rfl⟩ := hST
  exact F.noDimensionIncrease

/-- Relation-level exact Lemma-6 estimate for an upward selected-rank move. -/
theorem selectedVolume_dimensionIncrease
    (hST : CoordinateReplacement selector δ γ S T)
    (hrank : S.selected.dimension ≤ T.selected.dimension) :
    T.selected.dilation ^ (T.selected.dimension - S.selected.dimension) *
        T.selected.progression.volume ≤
      2 ^ T.selected.dimension *
        (2 * T.selected.witness.scaleDen) ^ S.selected.dimension *
          (2 ^ S.selected.dimension * S.selected.progression.volume) := by
  obtain ⟨F, rfl⟩ := hST
  exact F.dimensionIncrease hrank

/-- Relation-level strict `gamma` shrink in the equal-rank branch. -/
theorem selectedVolume_lt_of_dimension_eq
    (hST : CoordinateReplacement selector δ γ S T)
    (hdim : T.selected.dimension = S.selected.dimension) :
    (T.selected.progression.volume : ℝ) <
      γ * (S.selected.progression.volume : ℝ) := by
  obtain ⟨F, rfl⟩ := hST
  exact F.volume_lt_of_dimension_eq hdim

end CoordinateReplacement

namespace RelationTrace

/-- Cardinality is antitone along every coordinate-replacement trace. -/
theorem coordinate_card_antitone
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace (CoordinateReplacement selector δ γ) initial length)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ length) :
    (T.state j).points.card ≤ (T.state i).points.card := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (T.valid j (by omega)).card_le.trans (ih (by omega))

end RelationTrace

namespace CoordinateReplacementState

/-- At every eligible state, for any bounded selector, the selected witness
uses the fixed CFP denominator for that ambient dimension. -/
theorem selected_scaleDen
    {selector : BoundedCFPSelector C}
    (S : CoordinateReplacementState selector) :
    S.selected.witness.scaleDen = C.scaleDen S.ambientDimension := by
  exact (selector.input S.points S.eligible).selectedCFP_scaleDen

/-- Backwards-compatible specialization to the canonical selector. -/
theorem canonical_selected_scaleDen
    (S : CoordinateReplacementState C.canonicalSelector) :
    S.selected.witness.scaleDen = C.scaleDen S.ambientDimension :=
  S.selected_scaleDen

/-- The selected rank is bounded by the fixed CFP rank bound at the current
ambient dimension for every bounded selector. -/
theorem selected_dimension_le
    {selector : BoundedCFPSelector C}
    (S : CoordinateReplacementState selector) :
    S.selected.dimension ≤ C.rankBound S.ambientDimension := by
  exact S.selected.witness.rank_le

theorem canonical_selected_dimension_le
    (S : CoordinateReplacementState C.canonicalSelector) :
    S.selected.dimension ≤ C.rankBound S.ambientDimension :=
  S.selected_dimension_le

end CoordinateReplacementState

end

end Erdos186.PZ.Reduction
