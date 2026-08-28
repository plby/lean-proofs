import Wikipedia.NoExoticSixSphere.SphereFoldHemisphereInverse
import Wikipedia.NoExoticSixSphere.SpherePinchMap
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# The actual intersection pairs of a hemisphere pinch

When the comparison map avoids the common base value, every intersection
is off the equator. The two explicit inverse branches of the fold identify
the actual intersection pairs with the disjoint sum of the input pairs.
Finiteness, the natural-number count, and mod-two additivity follow from
this bijection. No homological or homotopy-group identification is assumed.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereFold

open MapIntersections

variable {E Y Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y] (v : UnitSphere E) (f g : C(UnitSphere E, Y))
  (hbase : f (antipode v) = g (antipode v)) (k : Z → Y)
  (hm : f (antipode v) ∉ range k)

include hm

theorem pair_first_ne_antipode (p : pairs f k) : p.val.1 ≠ antipode v := by
  intro h
  exact hm ⟨p.val.2, p.property.symm.trans (congrArg f h)⟩

include hbase in
theorem right_base_notMem : g (antipode v) ∉ range k := by
  rwa [← hbase]

def northPair (p : pairs f k) : pairs (pinch v f g hbase) k :=
  ⟨(northInverse v p.val.1, p.val.2), by
    have ha := pair_first_ne_antipode v f k hm p
    change pinch v f g hbase (northInverse v p.val.1) = k p.val.2
    rw [pinch_north v f g hbase _ (height_northInverse_pos v _ ha).le,
      fold_northInverse v _ ha]
    exact p.property⟩

def southPair (p : pairs g k) : pairs (pinch v f g hbase) k :=
  ⟨(antipode (northInverse v p.val.1), p.val.2), by
    have ha := pair_first_ne_antipode v g k (right_base_notMem v f g hbase k hm) p
    have hs : height v (antipode (northInverse v p.val.1)) ≤ 0 := by
      rw [height_antipode]
      exact (neg_neg_of_pos (height_northInverse_pos v _ ha)).le
    change pinch v f g hbase (antipode (northInverse v p.val.1)) = k p.val.2
    rw [pinch_south v f g hbase _ hs, fold_antipode, fold_northInverse v _ ha]
    exact p.property⟩

theorem height_northPair_pos (p : pairs f k) :
    0 < height v (northPair v f g hbase k hm p).val.1 :=
  height_northInverse_pos v _ (pair_first_ne_antipode v f k hm p)

theorem height_southPair_neg (p : pairs g k) :
    height v (southPair v f g hbase k hm p).val.1 < 0 := by
  change height v (antipode (northInverse v p.val.1)) < 0
  rw [height_antipode]
  exact neg_neg_of_pos (height_northInverse_pos v _
    (pair_first_ne_antipode v g k (right_base_notMem v f g hbase k hm) p))

theorem northPair_coordinates (p : pairs f k) :
    (fold v (northPair v f g hbase k hm p).val.1,
      (northPair v f g hbase k hm p).val.2) = p.val := by
  change (fold v (northInverse v p.val.1), p.val.2) = p.val
  rw [fold_northInverse v _ (pair_first_ne_antipode v f k hm p)]

theorem southPair_coordinates (p : pairs g k) :
    (fold v (southPair v f g hbase k hm p).val.1,
      (southPair v f g hbase k hm p).val.2) = p.val := by
  change (fold v (antipode (northInverse v p.val.1)), p.val.2) = p.val
  rw [fold_antipode, fold_northInverse v _
    (pair_first_ne_antipode v g k (right_base_notMem v f g hbase k hm) p)]

theorem northPair_ne_southPair (p : pairs f k) (q : pairs g k) :
    northPair v f g hbase k hm p ≠ southPair v f g hbase k hm q := by
  intro h
  have hp := height_northPair_pos v f g hbase k hm p
  rw [h] at hp
  exact (height_southPair_neg v f g hbase k hm q).not_gt hp

def sumPair : pairs f k ⊕ pairs g k → pairs (pinch v f g hbase) k :=
  Sum.elim (northPair v f g hbase k hm) (southPair v f g hbase k hm)

theorem sumPair_injective : Injective (sumPair v f g hbase k hm) := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hc := congrArg (fun a : pairs (pinch v f g hbase) k ↦
      (fold v a.val.1, a.val.2)) h
    exact (northPair_coordinates v f g hbase k hm p).symm.trans
      (hc.trans (northPair_coordinates v f g hbase k hm q))
  · exact (northPair_ne_southPair v f g hbase k hm p q h).elim
  · exact (northPair_ne_southPair v f g hbase k hm q p h.symm).elim
  · apply congrArg Sum.inr
    apply Subtype.ext
    have hc := congrArg (fun a : pairs (pinch v f g hbase) k ↦
      (fold v a.val.1, a.val.2)) h
    exact (southPair_coordinates v f g hbase k hm p).symm.trans
      (hc.trans (southPair_coordinates v f g hbase k hm q))

theorem sumPair_surjective : Surjective (sumPair v f g hbase k hm) := by
  intro q
  have hn := pinch_intersection_off_equator v f g hbase k hm q.val.1 q.val.2 q.property
  rcases lt_or_gt_of_ne hn with hs | hn
  · have hp : g (fold v q.val.1) = k q.val.2 :=
      (pinch_south v f g hbase q.val.1 hs.le).symm.trans q.property
    refine ⟨Sum.inr ⟨(fold v q.val.1, q.val.2), hp⟩, ?_⟩
    apply Subtype.ext
    change (antipode (northInverse v (fold v q.val.1)), q.val.2) = q.val
    rw [antipode_northInverse_fold v _ hs]
  · have hp : f (fold v q.val.1) = k q.val.2 :=
      (pinch_north v f g hbase q.val.1 hn.le).symm.trans q.property
    refine ⟨Sum.inl ⟨(fold v q.val.1, q.val.2), hp⟩, ?_⟩
    apply Subtype.ext
    change (northInverse v (fold v q.val.1), q.val.2) = q.val
    rw [northInverse_fold v _ hn]

def intersectionEquiv : (pairs f k ⊕ pairs g k) ≃ pairs (pinch v f g hbase) k :=
  Equiv.ofBijective (sumPair v f g hbase k hm)
    ⟨sumPair_injective v f g hbase k hm, sumPair_surjective v f g hbase k hm⟩

theorem finite_pinch_pairs (hf : (pairs f k).Finite) (hg : (pairs g k).Finite) :
    (pairs (pinch v f g hbase) k).Finite := by
  let := hf.to_subtype
  let := hg.to_subtype
  exact finite_coe_iff.mp (Finite.of_equiv (pairs f k ⊕ pairs g k)
    (intersectionEquiv v f g hbase k hm))

theorem pinch_pairs_ncard (hf : (pairs f k).Finite) (hg : (pairs g k).Finite) :
    (pairs (pinch v f g hbase) k).ncard = (pairs f k).ncard + (pairs g k).ncard := by
  let := hf.to_subtype
  let := hg.to_subtype
  change Nat.card (pairs (pinch v f g hbase) k) = Nat.card (pairs f k) + Nat.card (pairs g k)
  rw [← Nat.card_congr (intersectionEquiv v f g hbase k hm), Nat.card_sum]

theorem pinch_parity (hf : (pairs f k).Finite) (hg : (pairs g k).Finite) :
    parity (pinch v f g hbase) k = parity f k + parity g k := by
  simp only [parity, pinch_pairs_ncard v f g hbase k hm hf hg, Nat.cast_add]

end NoExoticSixSphere.SphereFold
