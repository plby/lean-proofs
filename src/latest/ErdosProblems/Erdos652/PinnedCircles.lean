import ErdosProblems.Erdos652.Circles
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators Real
noncomputable section

namespace Erdos652

open Classical in
/-- The radii determined from `p` by the points of `Q`. -/
def distanceRadii (p : Point) (Q : Finset Point) : Finset ℝ := Q.image (dist p)

open Classical in
/-- The points of `Q` on the circle keyed by `a`. -/
def pointsOnCircle (Q : Finset Point) (a : CircleKey) : Finset Point :=
  Q.filter fun q => q ∈ circle a

open Classical in
/-- All center-radius circles obtained from centers in `P` and points in `Q`. -/
def circleKeys (P Q : Finset Point) : Finset CircleKey :=
  P.biUnion fun p => (distanceRadii p Q).image fun r => (p, r)

@[simp] lemma mem_distanceRadii {p q : Point} {Q : Finset Point} (hq : q ∈ Q) :
    dist p q ∈ distanceRadii p Q := by
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

lemma mem_circleKeys_iff {P Q : Finset Point} {a : CircleKey} :
    a ∈ circleKeys P Q ↔ a.1 ∈ P ∧ a.2 ∈ distanceRadii a.1 Q := by
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨p, hp, ha⟩
    rcases Finset.mem_image.mp ha with ⟨r, hr, har⟩
    subst a
    exact ⟨hp, hr⟩
  · rintro ⟨hp, hr⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨a.1, hp, Finset.mem_image.mpr ⟨a.2, hr, Prod.ext rfl rfl⟩⟩

lemma circleKeys_card_le (P Q : Finset Point) (t : ℕ)
    (ht : ∀ p ∈ P, (distanceRadii p Q).card ≤ t) :
    (circleKeys P Q).card ≤ P.card * t := by
  unfold circleKeys
  apply Finset.card_biUnion_le_card_mul
  intro p hp
  calc
    ((distanceRadii p Q).image fun r => (p, r)).card
        ≤ (distanceRadii p Q).card := Finset.card_image_le
    _ ≤ t := ht p hp

/-- For a fixed center, the keyed circles are in bijection with a subset of
the radii determined from that center. -/
lemma circleKeys_fixed_center_card_le (P Q : Finset Point) (p : Point) :
    ((circleKeys P Q).filter (fun a => a.1 = p)).card ≤
      (distanceRadii p Q).card := by
  let S := (circleKeys P Q).filter (fun a => a.1 = p)
  have hinj : Set.InjOn (fun a : CircleKey => a.2) (S : Set CircleKey) := by
    intro a ha b hb hab
    apply Prod.ext
    · exact ((Finset.mem_filter.mp ha).2).trans
        ((Finset.mem_filter.mp hb).2).symm
    · exact hab
  have hcard : S.card = (S.image fun a : CircleKey => a.2).card := by
    symm
    exact Finset.card_image_iff.mpr hinj
  rw [hcard]
  apply Finset.card_le_card
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨a, ha, rfl⟩
  have haKey := (Finset.mem_filter.mp ha).1
  have hac := (Finset.mem_filter.mp ha).2
  have hradius := (mem_circleKeys_iff.mp haKey).2
  simpa [hac] using hradius

lemma circleKey_radius_pos {P Q : Finset Point} (hPQ : Disjoint P Q)
    {a : CircleKey} (ha : a ∈ circleKeys P Q) : 0 < a.2 := by
  rcases (mem_circleKeys_iff.mp ha) with ⟨hp, hr⟩
  rcases Finset.mem_image.mp hr with ⟨q, hq, hrq⟩
  have hpq : a.1 ≠ q := by
    intro hpq
    subst q
    exact Finset.disjoint_left.mp hPQ hp hq
  calc
    0 < dist a.1 q := dist_pos.mpr hpq
    _ = a.2 := hrq

lemma pointsOnCircle_subset (Q : Finset Point) (a : CircleKey) :
    pointsOnCircle Q a ⊆ Q := by
  classical
  exact Finset.filter_subset _ _

lemma pointsOnCircle_on_circle (Q : Finset Point) (a : CircleKey) :
    (↑(pointsOnCircle Q a) : Set Point) ⊆ circle a := by
  classical
  intro q hq
  exact (Finset.mem_filter.mp hq).2

/-- The distance fibres for a fixed center partition `Q`. -/
lemma sum_distance_fibres (p : Point) (Q : Finset Point) :
    ∑ r ∈ distanceRadii p Q,
      (Q.filter fun q => dist p q = r).card = Q.card := by
  simpa [distanceRadii] using (Finset.card_eq_sum_card_image (dist p) Q).symm

/-- Removing fibres of size at most two loses at most twice the number of radii. -/
lemma retained_distance_fibres_lower (p : Point) (Q : Finset Point) :
    Q.card ≤
      (∑ r ∈ (distanceRadii p Q).filter
          (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
        (Q.filter fun q => dist p q = r).card) +
        2 * (distanceRadii p Q).card := by
  classical
  let fibre : ℝ → ℕ := fun r => (Q.filter fun q => dist p q = r).card
  let good : ℝ → Prop := fun r => 3 ≤ fibre r
  have hsplit :
      ∑ r ∈ distanceRadii p Q, fibre r =
        (∑ r ∈ (distanceRadii p Q).filter good, fibre r) +
          ∑ r ∈ (distanceRadii p Q).filter (fun r => ¬ good r), fibre r := by
    simpa using (Finset.sum_filter_add_sum_filter_not
      (s := distanceRadii p Q) (p := good) (f := fibre)).symm
  have hbad :
      ∑ r ∈ (distanceRadii p Q).filter (fun r => ¬ good r), fibre r ≤
        2 * (distanceRadii p Q).card := by
    calc
      ∑ r ∈ (distanceRadii p Q).filter (fun r => ¬ good r), fibre r
          ≤ ∑ _r ∈ (distanceRadii p Q).filter (fun r => ¬ good r), 2 := by
            apply Finset.sum_le_sum
            intro r hr
            have := (Finset.mem_filter.mp hr).2
            dsimp [good] at this
            omega
      _ = 2 * ((distanceRadii p Q).filter (fun r => ¬ good r)).card := by
            simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ 2 * (distanceRadii p Q).card :=
            Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.filter_subset _ _))
  have htotal : ∑ r ∈ distanceRadii p Q, fibre r = Q.card := by
    simpa [fibre] using sum_distance_fibres p Q
  rw [← htotal, hsplit]
  exact Nat.add_le_add_left hbad _

/-- Summed over all centers, the retained circle fibres contain all but at
most `2 |P| t` of the `|P||Q|` incidences. -/
lemma retained_circle_incidence_lower (P Q : Finset Point) (t : ℕ)
    (ht : ∀ p ∈ P, (distanceRadii p Q).card ≤ t) :
    P.card * Q.card ≤
      (∑ p ∈ P, ∑ r ∈ (distanceRadii p Q).filter
          (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
        (Q.filter fun q => dist p q = r).card) + 2 * P.card * t := by
  calc
    P.card * Q.card = ∑ _p ∈ P, Q.card := by simp
    _ ≤ ∑ p ∈ P,
        ((∑ r ∈ (distanceRadii p Q).filter
            (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
          (Q.filter fun q => dist p q = r).card) + 2 * t) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (retained_distance_fibres_lower p Q).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (ht p hp)) _)
    _ = (∑ p ∈ P, ∑ r ∈ (distanceRadii p Q).filter
          (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
        (Q.filter fun q => dist p q = r).card) + 2 * P.card * t := by
      simp_rw [Finset.sum_add_distrib]
      simp [Nat.mul_assoc, Nat.mul_comm]

end Erdos652
