/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure
import ErdosProblems.Erdos1165.TilingConditionalCappedMarginalization

/-!
# Aggregate product tails after coordinatewise conditioning

An honest all-creation atom generally conditions every away-domino total on
a broad coordinatewise window.  The remaining coordinates are still
independent: their one-coordinate laws are simply normalized restrictions of
the original laws.  This file records that finite algebra and feeds the
restricted product directly to the aggregate random-total estimate.

There is no path-event estimate in this module.  In particular, the theorem
below is the missing coordinate identity needed by a prefixed cofinal sharp
interface once its deterministic broad/screened reconstruction is supplied.
-/

open scoped BigOperators

namespace Erdos1165.HLOZConditionalRandomTotalProductBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure NearFavoriteThresholded
open TilingConditionalCappedMarginalization

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-- Conditional screen mass depends only on the two screen predicates, not
on the particular decidability witnesses used to present them. -/
theorem conditionalScreenMass_congr
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base₁ base₂ screened₁ screened₂ :
      TruncatedTotals upperBound → Prop)
    [DecidablePred base₁] [DecidablePred base₂]
    [DecidablePred screened₁] [DecidablePred screened₂]
    (hbase : ∀ ell, base₁ ell ↔ base₂ ell)
    (hscreened : ∀ ell, screened₁ ell ↔ screened₂ ell) :
    conditionalScreenMass pointMass upperBound base₁ screened₁ =
      conditionalScreenMass pointMass upperBound base₂ screened₂ := by
  classical
  have screenMass_congr : ∀
      (p q : TruncatedTotals upperBound → Prop)
      [DecidablePred p] [DecidablePred q],
      (∀ ell, p ell ↔ q ell) →
        screenMass pointMass upperBound p =
          screenMass pointMass upperBound q := by
    intro p q _ _ hpq
    unfold screenMass
    apply Finset.sum_congr rfl
    intro ell _
    exact if_congr (hpq ell) rfl rfl
  unfold conditionalScreenMass
  rw [screenMass_congr screened₁ screened₂ hscreened,
    screenMass_congr base₁ base₂ hbase]

/-- The normalized restriction of a heterogeneous coordinate weight to a
coordinatewise broad window. -/
noncomputable def restrictedCoordinateWeight
    (weight : ∀ c, State c → ℝ)
    (base : ∀ c, State c → Prop) [∀ c, DecidablePred (base c)]
    (c : Coordinate) (v : State c) : ℝ :=
  if base c v then
    weight c v / ∑ u, if base c u then weight c u else 0
  else 0

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem sum_restrictedCoordinateWeight_eq_one
    (weight : ∀ c, State c → ℝ)
    (base : ∀ c, State c → Prop) [∀ c, DecidablePred (base c)]
    (hbase : ∀ c, 0 < ∑ v, if base c v then weight c v else 0)
    (c : Coordinate) :
    ∑ v, restrictedCoordinateWeight weight base c v = 1 := by
  classical
  let M := ∑ v, if base c v then weight c v else 0
  have hM : M ≠ 0 := ne_of_gt (hbase c)
  calc
    (∑ v, restrictedCoordinateWeight weight base c v) =
        (∑ v, if base c v then weight c v else 0) / M := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : base c v <;>
        simp [restrictedCoordinateWeight, hv, M]
    _ = M / M := rfl
    _ = 1 := div_self hM

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem restrictedCoordinateWeight_nonneg
    (weight : ∀ c, State c → ℝ)
    (base : ∀ c, State c → Prop) [∀ c, DecidablePred (base c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hbase : ∀ c, 0 < ∑ v, if base c v then weight c v else 0) :
    ∀ c v, 0 ≤ restrictedCoordinateWeight weight base c v := by
  intro c v
  by_cases hv : base c v
  · simp only [restrictedCoordinateWeight, hv, if_true]
    exact div_nonneg (hweight c v) (le_of_lt (hbase c))
  · simp [restrictedCoordinateWeight, hv]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
/-- Restricting both sides of a one-coordinate comparison to the same broad
window preserves the comparison after normalization. -/
theorem restrictedCoordinateWeight_ratio
    (weight : ∀ c, State c → ℝ)
    (base upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (base c)] [∀ c, DecidablePred (upper c)]
    [∀ c, DecidablePred (lower c)]
    (hbase : ∀ c, 0 < ∑ v, if base c v then weight c v else 0)
    (hupper : ∀ c v, upper c v → base c v)
    (hlower : ∀ c v, lower c v → base c v)
    {C : ℝ}
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    ∀ c,
      (∑ v, if upper c v then
          restrictedCoordinateWeight weight base c v else 0) ≤
        C * ∑ v, if lower c v then
          restrictedCoordinateWeight weight base c v else 0 := by
  classical
  intro c
  let M := ∑ v, if base c v then weight c v else 0
  have hM : 0 < M := hbase c
  have hupperEq :
      (∑ v, if upper c v then
          restrictedCoordinateWeight weight base c v else 0) =
        (∑ v, if upper c v then weight c v else 0) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : upper c v
    · simp [restrictedCoordinateWeight, hv, hupper c v hv, M]
    · simp [hv]
  have hlowerEq :
      (∑ v, if lower c v then
          restrictedCoordinateWeight weight base c v else 0) =
        (∑ v, if lower c v then weight c v else 0) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : lower c v
    · simp [restrictedCoordinateWeight, hv, hlower c v hv, M]
    · simp [hv]
  rw [hupperEq, hlowerEq]
  calc
    (∑ v, if upper c v then weight c v else 0) / M ≤
        (C * ∑ v, if lower c v then weight c v else 0) / M :=
      div_le_div_of_nonneg_right (hratio c) (le_of_lt hM)
    _ = C * ((∑ v, if lower c v then weight c v else 0) / M) := by
      ring

/-- Predicate-valued form of the coordinate-window product identity. -/
theorem screenMass_all_coordinate_predicates_eq_prod
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base : ∀ c, Fin (upperBound c) → Prop)
    [∀ c, DecidablePred (base c)] :
    screenMass pointMass upperBound (fun ell ↦ ∀ c, base c (ell c)) =
      ∏ c, ∑ v : Fin (upperBound c),
        if base c v then coordinateMass pointMass upperBound c v else 0 := by
  classical
  rw [screenMass_eq_product]
  calc
    (∑ ell : TruncatedTotals upperBound,
        if (∀ c, base c (ell c)) then
          ∏ c, coordinateMass pointMass upperBound c (ell c)
        else 0) =
      ∑ ell : TruncatedTotals upperBound,
        ∏ c, if base c (ell c) then
          coordinateMass pointMass upperBound c (ell c) else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      by_cases hall : ∀ c, base c (ell c)
      · rw [if_pos hall]
        apply Finset.prod_congr rfl
        intro c _
        rw [if_pos (hall c)]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨c, hc⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ c)
        rw [if_neg hc]
    _ = ∏ c, ∑ v : Fin (upperBound c),
        if base c v then coordinateMass pointMass upperBound c v else 0 :=
      (Fintype.prod_sum fun c (v : Fin (upperBound c)) ↦
        if base c v then coordinateMass pointMass upperBound c v else 0).symm

/-- Exact finite-product identity: conditioning on coordinatewise broad
windows is the product of the normalized restricted one-coordinate laws. -/
theorem conditionalScreenMass_inter_eq_restricted_product
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base : ∀ c, Fin (upperBound c) → Prop)
    [∀ c, DecidablePred (base c)]
    (screen : TruncatedTotals upperBound → Prop) [DecidablePred screen]
    (hbase : ∀ c, 0 < ∑ v : Fin (upperBound c),
      if base c v then coordinateMass pointMass upperBound c v else 0) :
    conditionalScreenMass pointMass upperBound
        (fun ell ↦ ∀ c, base c (ell c))
        (fun ell ↦ (∀ c, base c (ell c)) ∧ screen ell) =
      ∑ ell : TruncatedTotals upperBound,
        if screen ell then
          productPointMass
            (restrictedCoordinateWeight
              (fun c (v : Fin (upperBound c)) ↦
                coordinateMass pointMass upperBound c v)
              base) ell
        else 0 := by
  classical
  let weight := fun c (v : Fin (upperBound c)) ↦
    coordinateMass pointMass upperBound c v
  let localMass := fun c ↦ ∑ v, if base c v then weight c v else 0
  let restricted := restrictedCoordinateWeight weight base
  have hlocal : ∀ c, 0 < localMass c := hbase
  have hlocalNe : ∀ c, localMass c ≠ 0 := fun c ↦ ne_of_gt (hlocal c)
  have hprodPos : 0 < ∏ c, localMass c :=
    Finset.prod_pos fun c _ ↦ hlocal c
  have hpointwise : ∀ ell,
      (if (∀ c, base c (ell c)) ∧ screen ell then
          ∏ c, weight c (ell c) else 0) =
        (∏ c, localMass c) *
          (if screen ell then ∏ c, restricted c (ell c) else 0) := by
    intro ell
    by_cases hall : ∀ c, base c (ell c)
    · by_cases hs : screen ell
      · rw [if_pos ⟨hall, hs⟩, if_pos hs]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro c _
        simp only [restricted, restrictedCoordinateWeight, hall c, if_true]
        change weight c (ell c) =
          localMass c * (weight c (ell c) / localMass c)
        field_simp [hlocalNe c]
      · rw [if_neg (fun hpair : (∀ c, base c (ell c)) ∧ screen ell ↦
          hs hpair.2), if_neg hs, mul_zero]
    · rw [if_neg]
      · by_cases hs : screen ell
        · rw [if_pos hs]
          have : ∃ c, ¬ base c (ell c) := by simpa only [not_forall] using hall
          obtain ⟨c, hc⟩ := this
          have hz : ∏ c, restricted c (ell c) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ c)
            simp [restricted, restrictedCoordinateWeight, hc]
          rw [hz, mul_zero]
        · rw [if_neg hs, mul_zero]
      · exact fun h ↦ hall h.1
  unfold conditionalScreenMass
  rw [screenMass_eq_product,
    screenMass_all_coordinate_predicates_eq_prod]
  change
    (∑ ell, if (∀ c, base c (ell c)) ∧ screen ell then
        ∏ c, weight c (ell c) else 0) /
      (∏ c, localMass c) =
        ∑ ell, if screen ell then productPointMass restricted ell else 0
  rw [show (∑ ell, if (∀ c, base c (ell c)) ∧ screen ell then
      ∏ c, weight c (ell c) else 0) =
        (∏ c, localMass c) *
          ∑ ell, if screen ell then ∏ c, restricted c (ell c) else 0 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ell _
    exact hpointwise ell]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hprodPos)]
  apply Finset.sum_congr rfl
  intro ell _
  rw [productPointMass]

/-- The aggregate random-total estimate under an honest coordinatewise
broad conditioning.  The one-coordinate upper/lower comparison is checked
against the original masses; normalization by the common broad window
cancels on both sides. -/
theorem conditionalScreenMass_randomTotalThresholdedUpperTail_le
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base upper lower : ∀ c, Fin (upperBound c) → Prop)
    [∀ c, DecidablePred (base c)] [∀ c, DecidablePred (upper c)]
    [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ)
    (hweight : ∀ c (v : Fin (upperBound c)),
      0 ≤ coordinateMass pointMass upperBound c v)
    (hbase : ∀ c, 0 < ∑ v : Fin (upperBound c),
      if base c v then coordinateMass pointMass upperBound c v else 0)
    (hupper : ∀ c v, upper c v → base c v)
    (hlower : ∀ c v, lower c v → base c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hratio : ∀ c,
      (∑ v, if upper c v then
          coordinateMass pointMass upperBound c v else 0) ≤
        C * ∑ v, if lower c v then
          coordinateMass pointMass upperBound c v else 0)
    (henvelope : ∀ total < bound + 1,
      (1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K) :
    conditionalScreenMass pointMass upperBound
        (fun ell ↦ ∀ c, base c (ell c))
        (fun ell ↦ (∀ c, base c (ell c)) ∧
          randomTotalThresholdedUpperTail upper lower
            threshold G j bound ell) ≤ K := by
  classical
  let weight := fun c (v : Fin (upperBound c)) ↦
    coordinateMass pointMass upperBound c v
  let restricted := restrictedCoordinateWeight weight base
  rw [conditionalScreenMass_inter_eq_restricted_product
    pointMass upperBound base
      (randomTotalThresholdedUpperTail upper lower threshold G j bound) hbase]
  exact randomTotalThresholdedUpperTail_product_bound restricted upper lower
    threshold G j bound
    (restrictedCoordinateWeight_nonneg weight base hweight hbase)
    (fun c ↦ (sum_restrictedCoordinateWeight_eq_one
      weight base hbase c).le)
    hdisjoint hC hK
    (restrictedCoordinateWeight_ratio weight base upper lower hbase
      hupper hlower hratio)
    henvelope

/-- Instance-independent presentation of the conditional aggregate tail.

The raw broad and screened predicates may use any decidability witnesses and
need only be logically equivalent to the coordinatewise broad window and its
intersection with the aggregate tail.  This form is useful for concrete
stopped-coordinate acceptors, whose Boolean decisions are generally not
definitionally equal to the decisions synthesized for the semantic
predicates. -/
theorem conditionalScreenMass_randomTotalThresholdedUpperTail_le_of_iff
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base upper lower : ∀ c, Fin (upperBound c) → Prop)
    [∀ c, DecidablePred (base c)] [∀ c, DecidablePred (upper c)]
    [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ)
    {rawBase rawScreen : TruncatedTotals upperBound → Prop}
    [DecidablePred rawBase] [DecidablePred rawScreen]
    (hrawBase : ∀ ell, rawBase ell ↔ ∀ c, base c (ell c))
    (hrawScreen : ∀ ell, rawScreen ell ↔
      (∀ c, base c (ell c)) ∧
        randomTotalThresholdedUpperTail upper lower threshold G j bound ell)
    (hweight : ∀ c (v : Fin (upperBound c)),
      0 ≤ coordinateMass pointMass upperBound c v)
    (hbase : ∀ c, 0 < ∑ v : Fin (upperBound c),
      if base c v then coordinateMass pointMass upperBound c v else 0)
    (hupper : ∀ c v, upper c v → base c v)
    (hlower : ∀ c v, lower c v → base c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hratio : ∀ c,
      (∑ v, if upper c v then
          coordinateMass pointMass upperBound c v else 0) ≤
        C * ∑ v, if lower c v then
          coordinateMass pointMass upperBound c v else 0)
    (henvelope : ∀ total < bound + 1,
      (1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K) :
    conditionalScreenMass pointMass upperBound rawBase rawScreen ≤ K := by
  rw [conditionalScreenMass_congr pointMass upperBound rawBase
    (fun ell ↦ ∀ c, base c (ell c)) rawScreen
    (fun ell ↦ (∀ c, base c (ell c)) ∧
      randomTotalThresholdedUpperTail upper lower threshold G j bound ell)
    hrawBase hrawScreen]
  exact conditionalScreenMass_randomTotalThresholdedUpperTail_le
    pointMass upperBound base upper lower threshold G j bound hweight hbase
    hupper hlower hdisjoint hC hK hratio henvelope

end

end Erdos1165.HLOZConditionalRandomTotalProductBound
