/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.ElekesSharir
import ErdosProblems.Erdos95.SpecialRichPoints
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Erdős Problem 95

For a finite set `P` of points in the Euclidean plane, let `f_P u` be the
number of unordered pairs of distinct points of `P` at distance `u`.  Erdős
Problem 95 asks for an upper bound for the second moment of these
multiplicities.  Guth and Katz proved the stronger estimate

`∑ u, f_P(u)^2 ≪ |P|^3 log |P|`.

This file formalizes the consequence requested in the problem: for every
positive real `ε`, the second moment is at most a constant depending only on
`ε` times `|P|^(3+ε)`.
-/

open scoped BigOperators

namespace Erdos95

/-- The Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance, regarded as a function of an unordered pair. -/
noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ dist p q, dist_comm⟩

@[simp]
theorem pairDistance_mk (p q : Point) : pairDistance s(p, q) = dist p q :=
  rfl

/-- The finset of unordered pairs of distinct points of `P`. -/
noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.offDiag.image Sym2.mk.uncurry

/-- The set of nonzero distances determined by `P`. -/
noncomputable def distances (P : Finset Point) : Finset ℝ :=
  (pointPairs P).image pairDistance

/-- The number of unordered pairs of points of `P` at distance `u`. -/
noncomputable def distanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((pointPairs P).filter fun e ↦ pairDistance e = u).card

/-- The second moment of the distance multiplicities of `P`. -/
noncomputable def distanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ distances P, distanceMultiplicity P u ^ 2

@[simp]
theorem card_pointPairs (P : Finset Point) :
    (pointPairs P).card = P.card.choose 2 := by
  classical
  exact Sym2.card_image_offDiag P

theorem mem_distances_iff {P : Finset Point} {u : ℝ} :
    u ∈ distances P ↔ ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ dist p q = u := by
  classical
  simp only [distances, pointPairs, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨e, ⟨pq, hpq, rfl⟩, rfl⟩
    exact ⟨pq.1, hpq.1, pq.2, hpq.2.1, hpq.2.2, rfl⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact ⟨s(p, q), ⟨(p, q), ⟨hp, hq, hpq⟩, rfl⟩, rfl⟩

/-- Summing all distance multiplicities counts every unordered pair once. -/
theorem sum_distanceMultiplicity (P : Finset Point) :
    ∑ u ∈ distances P, distanceMultiplicity P u = P.card.choose 2 := by
  classical
  rw [← card_pointPairs]
  exact (Finset.card_eq_sum_card_image pairDistance (pointPairs P)).symm

/-- A fiber of `pairDistance` outside `distances P` is empty. -/
theorem distanceMultiplicity_eq_zero_of_not_mem {P : Finset Point} {u : ℝ}
    (hu : u ∉ distances P) : distanceMultiplicity P u = 0 := by
  classical
  simp only [distanceMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  exact fun heu ↦ hu (Finset.mem_image.mpr ⟨e, he, heu⟩)

/-- The energy is equivalently the sum over all values in any finite ambient
set containing the determined distances. -/
theorem distanceEnergy_eq_sum_filter (P : Finset Point) :
    distanceEnergy P =
      ∑ u ∈ (pointPairs P).image pairDistance,
        ((pointPairs P).filter fun e ↦ pairDistance e = u).card ^ 2 := by
  rfl

/-! ## Ordered segments and the factor of four -/

/-- The ordered pairs of distinct points of `P`. -/
noncomputable def orderedSegments (P : Finset Point) : Finset (Point × Point) :=
  P.offDiag

/-- The distance of an ordered segment. -/
noncomputable def orderedDistance (e : Point × Point) : ℝ :=
  dist e.1 e.2

/-- The number of ordered segments of `P` at distance `u`. -/
noncomputable def orderedDistanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((orderedSegments P).filter fun e ↦ orderedDistance e = u).card

/-- The ordered equal-distance energy.  This counts ordered pairs of ordered
segments of the same nonzero length. -/
noncomputable def orderedDistanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ (orderedSegments P).image orderedDistance,
    orderedDistanceMultiplicity P u ^ 2

/-- Ordered pairs of ordered nondegenerate segments having the same length.
This is the finite set denoted `Q(P)` in the Guth--Katz argument. -/
noncomputable def orderedDistanceQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) :=
  ((orderedSegments P).product (orderedSegments P)).filter fun q ↦
    orderedDistance q.1 = orderedDistance q.2

/-- The fiber-square definition of ordered distance energy is exactly the
cardinality of the equal-distance quadruple set. -/
theorem card_orderedDistanceQuadruples (P : Finset Point) :
    (orderedDistanceQuadruples P).card = orderedDistanceEnergy P := by
  classical
  let leftDistance : ((Point × Point) × (Point × Point)) → ℝ :=
    fun q ↦ orderedDistance q.1
  rw [Finset.card_eq_sum_card_image leftDistance (orderedDistanceQuadruples P)]
  have himage :
      (orderedDistanceQuadruples P).image leftDistance =
        (orderedSegments P).image orderedDistance := by
    ext u
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      unfold orderedDistanceQuadruples at hq
      rw [Finset.mem_filter] at hq
      have hqmem := Finset.mem_product.mp hq.1
      exact ⟨q.1, hqmem.1, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨(e, e), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, he⟩, rfl⟩, rfl⟩
  rw [himage]
  simp only [orderedDistanceEnergy, orderedDistanceMultiplicity]
  apply Finset.sum_congr rfl
  intro u hu
  have hfiber :
      (orderedDistanceQuadruples P).filter (fun q ↦ leftDistance q = u) =
        ((orderedSegments P).filter fun e ↦ orderedDistance e = u).product
        ((orderedSegments P).filter fun e ↦ orderedDistance e = u) := by
    ext q
    unfold orderedDistanceQuadruples leftDistance
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hqmem, heq⟩, hleft⟩
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqmem
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hq₁, hleft⟩,
        Finset.mem_filter.mpr ⟨hq₂, heq.symm.trans hleft⟩⟩
    · intro hqmem
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqmem
      obtain ⟨hq₁mem, hq₁dist⟩ := Finset.mem_filter.mp hq₁
      obtain ⟨hq₂mem, hq₂dist⟩ := Finset.mem_filter.mp hq₂
      exact ⟨⟨Finset.mem_product.mpr ⟨hq₁mem, hq₂mem⟩,
        hq₁dist.trans hq₂dist.symm⟩, hq₁dist⟩
  rw [hfiber]
  simp [Finset.card_product, pow_two]

/-- The equal-distance quadruples which arise from a common translation of
the two ordered segments. -/
noncomputable def translationQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact (orderedDistanceQuadruples P).filter fun q ↦
    ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2

/-- The elementary exceptional-case estimate in the Elekes--Sharir
reduction: a translation quadruple is determined by its first three
points. -/
theorem card_translationQuadruples_le (P : Finset Point) :
    (translationQuadruples P).card ≤ P.card ^ 3 := by
  classical
  let forgetLast : ((Point × Point) × (Point × Point)) →
      ((Point × Point) × Point) := fun q ↦ (q.1, q.2.1)
  have hmaps : Set.MapsTo forgetLast (translationQuadruples P)
      ((P.product P).product P) := by
    intro q hq
    unfold translationQuadruples at hq
    have hQ := (Finset.mem_filter.mp hq).1
    unfold orderedDistanceQuadruples at hQ
    have hsegments := (Finset.mem_filter.mp hQ).1
    obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hsegments
    have hfirst' : q.1.1 ∈ P ∧ q.1.2 ∈ P := by
      have h := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using hfirst)
      exact ⟨h.1, h.2.1⟩
    have hsecond' : q.2.1 ∈ P ∧ q.2.2 ∈ P := by
      have h := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using hsecond)
      exact ⟨h.1, h.2.1⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_product.mpr ⟨hfirst'.1, hfirst'.2⟩, hsecond'.1⟩
  have hinj : Set.InjOn forgetLast (translationQuadruples P) := by
    intro q hq r hr heq
    unfold translationQuadruples at hq hr
    have htransq : ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2 := by
      exact (Finset.mem_filter.mp hq).2
    have htransr : ES.IsTranslation r.1.1 r.1.2 r.2.1 r.2.2 := by
      exact (Finset.mem_filter.mp hr).2
    change (q.1, q.2.1) = (r.1, r.2.1) at heq
    have hparts := Prod.ext_iff.mp heq
    have hfirst : q.1 = r.1 := hparts.1
    have hthird : q.2.1 = r.2.1 := hparts.2
    have hlast : q.2.2 = r.2.2 := by
      apply PiLp.ext
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · dsimp [ES.IsTranslation] at htransq htransr
        rw [hfirst, hthird] at htransq
        exact sub_left_injective (htransq.1.symm.trans htransr.1)
      · dsimp [ES.IsTranslation] at htransq htransr
        rw [hfirst, hthird] at htransq
        exact sub_left_injective (htransq.2.symm.trans htransr.2)
    apply Prod.ext hfirst
    exact Prod.ext hthird hlast
  calc
    (translationQuadruples P).card ≤ ((P.product P).product P).card :=
      Finset.card_le_card_of_injOn forgetLast hmaps hinj
    _ = P.card ^ 3 := by simp [pow_succ]

/-- The nontranslation part of the equal-distance quadruple set. -/
noncomputable def incidentQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact (orderedDistanceQuadruples P).filter fun q ↦
    ¬ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2

/-- Every quadruple in the nontranslation part gives an intersection of the
two Elekes--Sharir lines indexed by `(a,c)` and `(b,d)`. -/
theorem intersects_of_mem_incidentQuadruples {P : Finset Point}
    {q : (Point × Point) × (Point × Point)}
    (hq : q ∈ incidentQuadruples P) :
    ES.Intersects q.1.1 q.2.1 q.1.2 q.2.2 := by
  classical
  unfold incidentQuadruples at hq
  obtain ⟨hQ, hnot⟩ := Finset.mem_filter.mp hq
  unfold orderedDistanceQuadruples at hQ
  have hdist := (Finset.mem_filter.mp hQ).2
  apply ES.intersects_of_sqDist_eq_of_not_translation
  · exact ES.sqDist_eq_iff_dist_eq.mpr hdist
  · exact hnot

/-- The translation and incidence cases partition all equal-distance
quadruples. -/
theorem card_translation_add_incident (P : Finset Point) :
    (translationQuadruples P).card + (incidentQuadruples P).card =
      (orderedDistanceQuadruples P).card := by
  classical
  unfold translationQuadruples incidentQuadruples
  exact Finset.card_filter_add_card_filter_not
    (s := orderedDistanceQuadruples P)
    (fun q ↦ ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2)

/-! ## Intersecting pairs in the Elekes--Sharir line family -/

/-- Indices of the `|P|^2` Elekes--Sharir lines. -/
noncomputable def lineIndices (P : Finset Point) : Finset (Point × Point) :=
  P.product P

/-- Ordered pairs of distinct indexed Elekes--Sharir lines which meet. -/
noncomputable def intersectingLinePairs (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact ((lineIndices P).product (lineIndices P)).filter fun l ↦
    l.1 ≠ l.2 ∧ ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2

@[simp]
theorem card_lineIndices (P : Finset Point) :
    (lineIndices P).card = P.card ^ 2 := by
  simp [lineIndices, pow_two]

/-! ### Rich points of the line family -/

/-- The unique common point selected for an intersecting pair of normalized
Elekes--Sharir lines.  The fallback value is irrelevant off the incidence
relation. -/
noncomputable def linePairIntersection
    (l : (Point × Point) × (Point × Point)) : ES.Space3 := by
  classical
  exact if h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2 then
    Classical.choose h
  else 0

theorem linePairIntersection_on_first
    {l : (Point × Point) × (Point × Point)}
    (h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2) :
    ES.OnLine l.1.1 l.1.2 (linePairIntersection l) := by
  classical
  simp only [linePairIntersection, dif_pos h]
  exact (Classical.choose_spec h).1

theorem linePairIntersection_on_second
    {l : (Point × Point) × (Point × Point)}
    (h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2) :
    ES.OnLine l.2.1 l.2.2 (linePairIntersection l) := by
  classical
  simp only [linePairIntersection, dif_pos h]
  exact (Classical.choose_spec h).2

/-- Lines of the indexed family passing through a point of parameter
three-space. -/
noncomputable def linesThrough (P : Finset Point) (x : ES.Space3) :
    Finset (Point × Point) := by
  classical
  exact (lineIndices P).filter fun l ↦ ES.OnLine l.1 l.2 x

/-- The finite set of actual intersection points of distinct indexed lines. -/
noncomputable def intersectionPoints (P : Finset Point) : Finset ES.Space3 := by
  classical
  exact (intersectingLinePairs P).image linePairIntersection

theorem mem_linesThrough_iff {P : Finset Point} {x : ES.Space3}
    {l : Point × Point} :
    l ∈ linesThrough P x ↔ l ∈ lineIndices P ∧ ES.OnLine l.1 l.2 x := by
  classical
  simp [linesThrough]

/-- At a fixed rigid-motion parameter there is at most one indexed line for
each first endpoint.  Consequently every rich point of the Elekes--Sharir
family is incident to at most `|P|` lines. -/
theorem card_linesThrough_le (P : Finset Point) (x : ES.Space3) :
    (linesThrough P x).card ≤ P.card := by
  classical
  let S := linesThrough P x
  have hinj : Set.InjOn Prod.fst (S : Set (Point × Point)) := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hint : ES.Intersects a.1 a.2 b.1 b.2 :=
      ⟨x, ha'.2, hb'.2⟩
    have hdist : dist a.1 b.1 = dist a.2 b.2 :=
      ES.sqDist_eq_iff_dist_eq.mp (ES.sqDist_eq_of_intersects hint)
    have hsecond : a.2 = b.2 := by
      apply dist_eq_zero.mp
      simpa [hab] using hdist.symm
    exact Prod.ext hab hsecond
  have hcard : (S.image Prod.fst).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hl).1).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

/-- A fiber of the intersection-point map is exactly the ordered off-diagonal
of the lines through that point.  This uses uniqueness of the intersection of
two distinct normalized lines. -/
theorem intersectionPoint_fiber (P : Finset Point) (x : ES.Space3) :
    (intersectingLinePairs P).filter (fun l ↦ linePairIntersection l = x) =
      (linesThrough P x).offDiag := by
  classical
  ext l
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨hl, hlx⟩
    have hdata := Finset.mem_filter.mp hl
    have hmem := Finset.mem_product.mp hdata.1
    refine ⟨Finset.mem_filter.mpr ⟨hmem.1, ?_⟩,
      Finset.mem_filter.mpr ⟨hmem.2, ?_⟩, hdata.2.1⟩
    · rw [← hlx]
      exact linePairIntersection_on_first hdata.2.2
    · rw [← hlx]
      exact linePairIntersection_on_second hdata.2.2
  · rintro ⟨hl₁, hl₂, hne⟩
    have hl₁' := Finset.mem_filter.mp hl₁
    have hl₂' := Finset.mem_filter.mp hl₂
    have hint : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2 :=
      ⟨x, hl₁'.2, hl₂'.2⟩
    have hlmem : l ∈ intersectingLinePairs P := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hl₁'.1, hl₂'.1⟩, hne, hint⟩
    refine ⟨hlmem, ?_⟩
    exact ES.intersection_unique hne
      (linePairIntersection_on_first hint)
      (linePairIntersection_on_second hint) hl₁'.2 hl₂'.2

/-- Exact rich-point decomposition of the ordered intersecting-pair count. -/
theorem card_intersectingLinePairs_eq_sum_rich (P : Finset Point) :
    (intersectingLinePairs P).card =
      ∑ x ∈ intersectionPoints P,
        (linesThrough P x).card * ((linesThrough P x).card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_image linePairIntersection (intersectingLinePairs P)]
  change _ = ∑ x ∈ (intersectingLinePairs P).image linePairIntersection, _
  apply Finset.sum_congr rfl
  intro x hx
  rw [intersectionPoint_fiber, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Intersection points incident to at least `k` indexed lines. -/
noncomputable def richIntersectionPoints (P : Finset Point) (k : ℕ) :
    Finset ES.Space3 := by
  classical
  exact (intersectionPoints P).filter fun x ↦ k ≤ (linesThrough P x).card

/-- The presentation-level rich-point set is definitionally the same as the
generic finite line-family construction used in the incidence induction. -/
theorem richIntersectionPoints_eq_lineFamilyRichPoints
    (P : Finset Point) (k : ℕ) :
    richIntersectionPoints P k =
      LineFamilies.richPoints (P.product P) k := by
  rfl

private theorem sum_two_mul_pred (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), 2 * (k - 1) = r * (r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      cases r with
      | zero => simp
      | succ s =>
          simp only [Nat.add_sub_cancel, Nat.succ_sub_one]
          ring

private theorem sum_two_mul_pred_truncate {r n : ℕ} (hrn : r ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (if k ≤ r then 2 * (k - 1) else 0) = r * (r - 1) := by
  calc
    ∑ k ∈ Finset.range (n + 1),
          (if k ≤ r then 2 * (k - 1) else 0) =
        ∑ k ∈ Finset.range (r + 1),
          (if k ≤ r then 2 * (k - 1) else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hrn))
      intro k hkn hkr
      simp only [Finset.mem_range] at hkn hkr
      simp [Nat.not_le.mpr (by omega : r < k)]
    _ = ∑ k ∈ Finset.range (r + 1), 2 * (k - 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [show k ≤ r by omega]
    _ = r * (r - 1) := sum_two_mul_pred r

private theorem sum_indicator_eq_mul_card {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x ∈ S, if p x then c else 0) = c * (S.filter p).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases hpa : p a
      · rw [Finset.filter_insert]
        simp [ha, hpa, ih, Nat.mul_succ, Nat.add_comm]
      · rw [Finset.filter_insert]
        simp [ha, hpa, ih]

/-- Layer-cake identity for line intersections.  It reduces the desired pair
bound to estimates for `k`-rich points, with the exact weight `2(k-1)`. -/
theorem card_intersectingLinePairs_eq_sum_richLevels (P : Finset Point) :
    (intersectingLinePairs P).card =
      ∑ k ∈ Finset.range (P.card + 1),
        2 * (k - 1) * (richIntersectionPoints P k).card := by
  classical
  rw [card_intersectingLinePairs_eq_sum_rich]
  calc
    ∑ x ∈ intersectionPoints P,
          (linesThrough P x).card * ((linesThrough P x).card - 1) =
        ∑ x ∈ intersectionPoints P,
          ∑ k ∈ Finset.range (P.card + 1),
            if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (sum_two_mul_pred_truncate (card_linesThrough_le P x)).symm
    _ = ∑ k ∈ Finset.range (P.card + 1),
          ∑ x ∈ intersectionPoints P,
            if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (P.card + 1),
          2 * (k - 1) * (richIntersectionPoints P k).card := by
      apply Finset.sum_congr rfl
      intro k hk
      change (∑ x ∈ intersectionPoints P,
          if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0) =
        2 * (k - 1) *
          ((intersectionPoints P).filter fun x ↦
            k ≤ (linesThrough P x).card).card
      exact sum_indicator_eq_mul_card (intersectionPoints P)
        (fun x ↦ k ≤ (linesThrough P x).card) (2 * (k - 1))

private theorem intersectingLinePairs_le_of_rich_point_bound_scale
    (P : Finset Point) (X : ℝ) (hX : 0 ≤ X)
    (hRich : ∀ k : ℕ, 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤ X / (k : ℝ) ^ 2) :
    ((intersectingLinePairs P).card : ℝ) ≤
      2 * X * (1 + Real.log P.card) := by
  classical
  have hterm : ∀ k ∈ Finset.range (P.card + 1),
      2 * ((k - 1 : ℕ) : ℝ) * ((richIntersectionPoints P k).card : ℝ) ≤
        if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := by
    intro k hk
    split_ifs with hk2
    · have hkpos_nat : 0 < k := by omega
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
      have hkm1 : (1 : ℕ) ≤ k := by omega
      push_cast [Nat.cast_sub hkm1]
      calc
        2 * ((k : ℝ) - 1) * (richIntersectionPoints P k).card ≤
            2 * (k : ℝ) * (richIntersectionPoints P k).card := by
          gcongr <;> linarith
        _ ≤ 2 * (k : ℝ) * (X / (k : ℝ) ^ 2) := by
          gcongr
          exact hRich k hk2
        _ = 2 * X * (k : ℝ)⁻¹ := by
          field_simp
    · have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl <;> simp
  have hsum :
      ((∑ k ∈ Finset.range (P.card + 1),
          2 * (k - 1) * (richIntersectionPoints P k).card : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := by
    push_cast
    exact Finset.sum_le_sum fun k hk ↦ hterm k hk
  have hfilter :
      (Finset.range (P.card + 1)).filter (fun k ↦ 2 ≤ k) =
        Finset.Icc 2 P.card := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hrange :
      (∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0) =
        2 * X * ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ := by
    rw [← hfilter]
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum]
  have hsubset : Finset.Icc 2 P.card ⊆ Finset.Icc 1 P.card := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  have hinv_nonneg : ∀ k ∈ Finset.Icc 1 P.card, 0 ≤ (k : ℝ)⁻¹ := by
    intro k hk
    positivity
  have hpartial :
      ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ ≤
        ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro k hk1 hk2
      positivity)
  have hharmonic :
      ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ ≤
        1 + Real.log P.card := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast] using harmonic_le_one_add_log P.card
  rw [card_intersectingLinePairs_eq_sum_richLevels]
  calc
    ((∑ k ∈ Finset.range (P.card + 1),
        2 * (k - 1) * (richIntersectionPoints P k).card : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := hsum
    _ = 2 * X * ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ := hrange
    _ ≤ 2 * X * ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ := by
      gcongr
    _ ≤ 2 * X * (1 + Real.log P.card) := by
      gcongr

/-- The analytic summation step in the rich-point method.  A `k⁻²`
estimate for the number of `k`-rich intersection points gives the expected
logarithmic bound for ordered pairs of intersecting lines. -/
theorem intersectingLinePairs_le_of_rich_point_bound
    (A : ℝ) (hA : 0 < A)
    (hRich : ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤
        A * (P.card : ℝ) ^ 3 / (k : ℝ) ^ 2)
    (P : Finset Point) :
    ((intersectingLinePairs P).card : ℝ) ≤
      2 * A * (P.card : ℝ) ^ 3 * (1 + Real.log P.card) := by
  have h := intersectingLinePairs_le_of_rich_point_bound_scale P
    (A * (P.card : ℝ) ^ 3) (mul_nonneg hA.le (by positivity))
    (fun k hk ↦ hRich P k hk)
  convert h using 1 <;> ring

/-- The same harmonic summation with a real-power scale; this is the form
used by Guth's epsilon-loss low-degree partitioning theorem. -/
theorem intersectingLinePairs_le_of_rich_point_bound_rpow
    (A : ℝ) (hA : 0 < A) (δ : ℝ)
    (hRich : ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤
        A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2)
    (P : Finset Point) :
    ((intersectingLinePairs P).card : ℝ) ≤
      2 * A * (P.card : ℝ) ^ (3 + δ) *
        (1 + Real.log P.card) := by
  have h := intersectingLinePairs_le_of_rich_point_bound_scale P
    (A * (P.card : ℝ) ^ (3 + δ))
    (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
    (fun k hk ↦ hRich P k hk)
  convert h using 1 <;> ring

/-- Unshuffle a pair of ordered planar segments into the corresponding pair
of Elekes--Sharir line indices. -/
def toLinePair (q : (Point × Point) × (Point × Point)) :
    (Point × Point) × (Point × Point) :=
  ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- The inverse coordinate shuffle. -/
def ofLinePair (l : (Point × Point) × (Point × Point)) :
    (Point × Point) × (Point × Point) :=
  ((l.1.1, l.2.1), (l.1.2, l.2.2))

@[simp]
theorem ofLinePair_toLinePair
    (q : (Point × Point) × (Point × Point)) :
    ofLinePair (toLinePair q) = q := by
  rcases q with ⟨⟨a, b⟩, c, d⟩
  rfl

@[simp]
theorem toLinePair_ofLinePair
    (l : (Point × Point) × (Point × Point)) :
    toLinePair (ofLinePair l) = l := by
  rcases l with ⟨⟨a, c⟩, b, d⟩
  rfl

/-- Nontranslation distance quadruples are exactly ordered pairs of
distinct intersecting Elekes--Sharir lines. -/
theorem card_incidentQuadruples_eq_intersectingLinePairs (P : Finset Point) :
    (incidentQuadruples P).card = (intersectingLinePairs P).card := by
  classical
  apply Finset.card_bij (fun q _ ↦ toLinePair q)
  · intro q hq
    unfold incidentQuadruples at hq
    have hQ := (Finset.mem_filter.mp hq).1
    unfold orderedDistanceQuadruples at hQ
    have hsegments := (Finset.mem_filter.mp hQ).1
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hsegments
    have h₁' := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using h₁)
    have h₂' := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using h₂)
    unfold intersectingLinePairs
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_product.mpr
      · exact ⟨h₁'.1, h₂'.1⟩
      · exact ⟨h₁'.2.1, h₂'.2.1⟩
    · constructor
      · intro heq
        exact h₁'.2.2 (congrArg Prod.fst heq)
      · exact intersects_of_mem_incidentQuadruples hq
  · intro q hq r hr heq
    exact ofLinePair_toLinePair q ▸ ofLinePair_toLinePair r ▸
      congrArg ofLinePair heq
  · intro l hl
    refine ⟨ofLinePair l, ?_, toLinePair_ofLinePair l⟩
    unfold intersectingLinePairs at hl
    obtain ⟨hlines, hne, hint⟩ := Finset.mem_filter.mp hl
    obtain ⟨hl₁, hl₂⟩ := Finset.mem_product.mp hlines
    unfold lineIndices at hl₁ hl₂
    obtain ⟨ha, hc⟩ := Finset.mem_product.mp hl₁
    obtain ⟨hb, hd⟩ := Finset.mem_product.mp hl₂
    have hdist : dist l.1.1 l.2.1 = dist l.1.2 l.2.2 :=
      ES.sqDist_eq_iff_dist_eq.mp (ES.sqDist_eq_of_intersects hint)
    have hab : l.1.1 ≠ l.2.1 := by
      intro heq
      have hcd : l.1.2 = l.2.2 := by
        apply dist_eq_zero.mp
        simpa [heq] using hdist.symm
      exact hne (Prod.ext heq hcd)
    have hcd : l.1.2 ≠ l.2.2 := by
      intro heq
      have hab' : l.1.1 = l.2.1 := by
        apply dist_eq_zero.mp
        simpa [heq] using hdist
      exact hne (Prod.ext hab' heq)
    unfold incidentQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold orderedDistanceQuadruples
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · simpa only [orderedSegments, Finset.mem_offDiag] using ⟨ha, hb, hab⟩
        · simpa only [orderedSegments, Finset.mem_offDiag] using ⟨hc, hd, hcd⟩
      · exact hdist
    · intro htrans
      exact hne (Prod.ext (ES.eq_of_intersects_of_translation hint htrans).1
        (ES.eq_of_intersects_of_translation hint htrans).2)

private theorem two_mul_card_sym2_image_of_swap_mem
    {α : Type*} [DecidableEq α] (S : Finset (α × α))
    (hswap : ∀ p ∈ S, p.swap ∈ S)
    (hne : ∀ p ∈ S, p.1 ≠ p.2) :
    2 * (S.image Sym2.mk.uncurry).card = S.card := by
  rw [Finset.card_eq_sum_card_image (Sym2.mk.uncurry : α × α → Sym2 α) S]
  have hfiber : ∀ z ∈ S.image (Sym2.mk.uncurry : α × α → Sym2 α),
      (S.filter fun p ↦ Sym2.mk.uncurry p = z).card = 2 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hps : p.swap ∈ S := hswap p hp
    have hp_ne_swap : p ≠ p.swap := by
      intro h
      exact hne p hp (congrArg Prod.fst h)
    have hset :
        S.filter (fun q ↦ Sym2.mk.uncurry q = Sym2.mk.uncurry p) =
          {p, p.swap} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      change q ∈ S ∧ s(q.1, q.2) = s(p.1, p.2) ↔ q = p ∨ q = p.swap
      rw [Sym2.mk_eq_mk_iff]
      constructor
      · exact fun h ↦ h.2
      · rintro (rfl | rfl)
        · exact ⟨hp, Or.inl rfl⟩
        · exact ⟨hps, Or.inr rfl⟩
    rw [hset]
    simp [hp_ne_swap]
  rw [Finset.sum_const_nat hfiber]
  omega

theorem distanceMultiplicity_ordered (P : Finset Point) (u : ℝ) :
    orderedDistanceMultiplicity P u = 2 * distanceMultiplicity P u := by
  classical
  let S := (orderedSegments P).filter fun e ↦ orderedDistance e = u
  have hswap : ∀ p ∈ S, p.swap ∈ S := by
    rintro ⟨p, q⟩ hpq
    change (p, q) ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u) at hpq
    change (q, p) ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u)
    rw [Finset.mem_filter] at hpq ⊢
    have hpqP : (p, q) ∈ P.offDiag := by
      simpa only [orderedSegments] using hpq.1
    have hpqData : p ∈ P ∧ q ∈ P ∧ p ≠ q := by
      simpa only [Finset.mem_offDiag] using hpqP
    refine ⟨?_, ?_⟩
    · simpa only [orderedSegments, Finset.mem_offDiag] using
        ⟨hpqData.2.1, hpqData.1, hpqData.2.2.symm⟩
    · simpa only [orderedDistance, dist_comm] using hpq.2
  have hne : ∀ p ∈ S, p.1 ≠ p.2 := by
    intro p hp
    change p ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u) at hp
    have hpSeg : p ∈ P.offDiag := by
      simpa only [orderedSegments] using (Finset.mem_filter.mp hp).1
    exact (Finset.mem_offDiag.mp hpSeg).2.2
  have himage :
      S.image Sym2.mk.uncurry =
        (pointPairs P).filter fun e ↦ pairDistance e = u := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩, (Finset.mem_filter.mp hp).2⟩
    · intro hz
      obtain ⟨hzpair, hzdist⟩ := Finset.mem_filter.mp hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzpair
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hzdist⟩, rfl⟩
  have htwo := two_mul_card_sym2_image_of_swap_mem S hswap hne
  rw [himage] at htwo
  exact htwo.symm

theorem orderedDistanceEnergy_eq_four_mul (P : Finset Point) :
    orderedDistanceEnergy P = 4 * distanceEnergy P := by
  classical
  have himage :
      (orderedSegments P).image orderedDistance = distances P := by
    ext u
    simp only [orderedSegments, orderedDistance, distances, pointPairs,
      Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s(p.1, p.2), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  simp only [orderedDistanceEnergy, distanceEnergy, himage,
    distanceMultiplicity_ordered]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-! ## The exact asymptotic statement -/

/-- The quantifiers in Erdős Problem 95.  The power on the right is real
exponentiation; in particular, the constant is uniform in the finite point
set and depends only on `ε`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
    (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε)

/-- Once the geometric estimate for distinct intersecting Elekes--Sharir
line pairs is available, the translation estimate and the exact coordinate
shuffle give Erdős 95. -/
theorem statement_of_intersecting_line_pair_bound
    (hInc : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ P : Finset Point,
      ((intersectingLinePairs P).card : ℝ) ≤
        B * (P.card : ℝ) ^ (3 + ε)) :
    Statement := by
  intro ε hε
  obtain ⟨B, hB, hbound⟩ := hInc ε hε
  refine ⟨B + 1, by positivity, ?_⟩
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    have hexp : 0 < 3 + ε := by linarith
    simp [distanceEnergy, distances, pointPairs, distanceMultiplicity,
      Real.zero_rpow hexp.ne']
  have hnpos : 0 < (P.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hP)
  have hnone : 1 ≤ (P.card : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hP)
  have hexp : (3 : ℝ) ≤ 3 + ε := by linarith
  have hpow : (P.card : ℝ) ^ (3 : ℕ) ≤ (P.card : ℝ) ^ (3 + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hnone hexp
  have htranslation : ((translationQuadruples P).card : ℝ) ≤
      (P.card : ℝ) ^ (3 + ε) := by
    calc
      ((translationQuadruples P).card : ℝ) ≤ (P.card ^ 3 : ℕ) := by
        exact_mod_cast card_translationQuadruples_le P
      _ = (P.card : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (P.card : ℝ) ^ (3 + ε) := hpow
  have hquad : ((orderedDistanceQuadruples P).card : ℝ) ≤
      (B + 1) * (P.card : ℝ) ^ (3 + ε) := by
    rw [← card_translation_add_incident P]
    push_cast
    rw [card_incidentQuadruples_eq_intersectingLinePairs]
    nlinarith [hbound P, htranslation,
      Real.rpow_nonneg (by positivity : 0 ≤ (P.card : ℝ)) (3 + ε)]
  calc
    (distanceEnergy P : ℝ) ≤ (orderedDistanceQuadruples P).card := by
      rw [card_orderedDistanceQuadruples, orderedDistanceEnergy_eq_four_mul]
      push_cast
      have hnonneg : 0 ≤ (distanceEnergy P : ℝ) := by positivity
      linarith
    _ ≤ (B + 1) * (P.card : ℝ) ^ (3 + ε) := hquad

/-- The elementary analytic last step: a uniform `n³ log n` estimate implies
the `n^(3+ε)` formulation of Erdős Problem 95. -/
theorem statement_of_log_bound (A : ℝ) (hA : 0 < A)
    (hGK : ∀ P : Finset Point,
      (distanceEnergy P : ℝ) ≤
        A * (P.card : ℝ) ^ 3 * (Real.log P.card + 1)) :
    Statement := by
  intro ε hε
  refine ⟨A * (1 + ε⁻¹), mul_pos hA (by positivity), ?_⟩
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    have hexp : 0 < 3 + ε := by linarith
    simp [distanceEnergy, distances, pointPairs, distanceMultiplicity,
      Real.zero_rpow hexp.ne']
  have hnpos : 0 < (P.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hP)
  have hnone : 1 ≤ (P.card : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hP)
  have hpowone : 1 ≤ (P.card : ℝ) ^ ε :=
    Real.one_le_rpow hnone hε.le
  have hlog : Real.log P.card ≤ (P.card : ℝ) ^ ε / ε :=
    Real.log_natCast_le_rpow_div P.card hε
  have hlogpow :
      Real.log P.card + 1 ≤ (P.card : ℝ) ^ ε * (1 + ε⁻¹) := by
    calc
      Real.log P.card + 1 ≤ (P.card : ℝ) ^ ε / ε + (P.card : ℝ) ^ ε :=
        add_le_add hlog hpowone
      _ = (P.card : ℝ) ^ ε * (1 + ε⁻¹) := by
        rw [div_eq_mul_inv]
        ring
  calc
    (distanceEnergy P : ℝ) ≤
        A * (P.card : ℝ) ^ 3 * (Real.log P.card + 1) := hGK P
    _ ≤ A * (P.card : ℝ) ^ 3 *
        ((P.card : ℝ) ^ ε * (1 + ε⁻¹)) := by
      gcongr
    _ = A * (1 + ε⁻¹) * (P.card : ℝ) ^ (3 + ε) := by
      rw [Real.rpow_add hnpos]
      have hthree : (P.card : ℝ) ^ (3 : ℝ) = (P.card : ℝ) ^ (3 : ℕ) :=
        Real.rpow_natCast _ 3
      rw [hthree]
      ring

/-- A uniform `k⁻²` rich-point estimate for the Elekes--Sharir lines is the
precise geometric input needed for Erdős 95.  This theorem packages all
remaining finite summation, translation, and epsilon-absorption steps. -/
theorem statement_of_rich_point_bound (A : ℝ) (hA : 0 < A)
    (hRich : ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤
        A * (P.card : ℝ) ^ 3 / (k : ℝ) ^ 2) :
    Statement := by
  apply statement_of_log_bound (2 * A + 1) (by positivity)
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    simp [distanceEnergy, distances, pointPairs, distanceMultiplicity]
  have hnpos : 0 < (P.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hP
  have hnone : 1 ≤ (P.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hP
  have hlog : 0 ≤ Real.log P.card := Real.log_nonneg hnone
  have htranslation : ((translationQuadruples P).card : ℝ) ≤
      (P.card : ℝ) ^ 3 := by
    exact_mod_cast card_translationQuadruples_le P
  have hintersection :=
    intersectingLinePairs_le_of_rich_point_bound A hA hRich P
  have hquad : ((orderedDistanceQuadruples P).card : ℝ) ≤
      (2 * A + 1) * (P.card : ℝ) ^ 3 * (Real.log P.card + 1) := by
    rw [← card_translation_add_incident P]
    push_cast
    rw [card_incidentQuadruples_eq_intersectingLinePairs]
    nlinarith [mul_nonneg (show 0 ≤ (P.card : ℝ) ^ 3 by positivity)
      (show 0 ≤ Real.log P.card by exact hlog)]
  calc
    (distanceEnergy P : ℝ) ≤ (orderedDistanceQuadruples P).card := by
      rw [card_orderedDistanceQuadruples, orderedDistanceEnergy_eq_four_mul]
      push_cast
      have henergy : 0 ≤ (distanceEnergy P : ℝ) := by positivity
      linarith
    _ ≤ (2 * A + 1) * (P.card : ℝ) ^ 3 *
        (Real.log P.card + 1) := hquad

/-- Guth's shorter low-degree argument gives a loss in the power of `n`.
Taking half of the requested epsilon here leaves enough room to absorb the
harmonic logarithm, and yields the exact quantifiers of `Statement`. -/
theorem statement_of_epsilon_rich_point_bound
    (hRich : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
      ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
        ((richIntersectionPoints P k).card : ℝ) ≤
          A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2) :
    Statement := by
  apply statement_of_intersecting_line_pair_bound
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hrich⟩ := hRich δ hδ
  refine ⟨2 * A * (1 + δ⁻¹), by positivity, ?_⟩
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    have hexp : 0 < 3 + ε := by linarith
    rw [show (intersectingLinePairs ∅).card = 0 by
      simp [intersectingLinePairs, lineIndices]]
    push_cast
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow hexp.ne']
    positivity
  have hnpos : 0 < (P.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hP
  have hnone : 1 ≤ (P.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hP
  have hpowone : 1 ≤ (P.card : ℝ) ^ δ :=
    Real.one_le_rpow hnone hδ.le
  have hlog : Real.log P.card ≤ (P.card : ℝ) ^ δ / δ :=
    Real.log_natCast_le_rpow_div P.card hδ
  have hlogpow :
      1 + Real.log P.card ≤ (P.card : ℝ) ^ δ * (1 + δ⁻¹) := by
    calc
      1 + Real.log P.card ≤
          (P.card : ℝ) ^ δ + (P.card : ℝ) ^ δ / δ :=
        add_le_add hpowone hlog
      _ = (P.card : ℝ) ^ δ * (1 + δ⁻¹) := by
        rw [div_eq_mul_inv]
        ring
  have hpairs :=
    intersectingLinePairs_le_of_rich_point_bound_rpow A hA δ hrich P
  calc
    ((intersectingLinePairs P).card : ℝ) ≤
        2 * A * (P.card : ℝ) ^ (3 + δ) *
          (1 + Real.log P.card) := hpairs
    _ ≤ 2 * A * (P.card : ℝ) ^ (3 + δ) *
        ((P.card : ℝ) ^ δ * (1 + δ⁻¹)) := by
      gcongr
    _ = (2 * A * (1 + δ⁻¹)) * (P.card : ℝ) ^ (3 + ε) := by
      have hadd : (3 : ℝ) + ε = (3 + δ) + δ := by
        dsimp [δ]
        ring
      have hpow : (P.card : ℝ) ^ (3 + ε) =
          (P.card : ℝ) ^ (3 + δ) * (P.card : ℝ) ^ δ := by
        rw [hadd, Real.rpow_add hnpos]
      rw [hpow]
      ring

/-- Erdős Problem 95, resolved via the Guth--Katz/Elekes--Sharir incidence
method and Guth's epsilon-loss polynomial-partitioning theorem. -/
theorem erdos95 : Statement := by
  apply statement_of_epsilon_rich_point_bound
  intro δ hδ
  obtain ⟨A, hA, hrich⟩ :=
    SpecialRichPoints.full_family_rich_point_bound δ hδ
  refine ⟨A, hA, ?_⟩
  intro P k hk
  rw [richIntersectionPoints_eq_lineFamilyRichPoints]
  exact hrich P k hk

end Erdos95
