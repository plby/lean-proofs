import Wikipedia.NoExoticSixSphere.SmoothNativeSphereConcatenation
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# Actual intersection-pair additivity for native sphere concatenation

The two proved partial diffeomorphisms supply explicit inverse branches on
actual source pairs. When the comparison map avoids the base value, no
intersection lies on the seam or at the pole. The pair set is therefore
in bijection with the disjoint sum of the two input pair sets.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization MapIntersections

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] {m : M}
  (f g : BasedMap 3 M m) (k : Sphere 3 → M) (hm : m ∉ range k)

include hm

theorem pair_first_ne_pole (p : pairs f.val k) : p.val.1 ≠ spherePole 3 := by
  intro h
  exact hm ⟨p.val.2, p.property.symm.trans ((congrArg f.val h).trans f.property)⟩

def leftPair (p : pairs f.val k) : pairs (concatenate f g).val k :=
  ⟨((halfSphereCoordinates 0 (by constructor <;> norm_num)).symm p.val.1, p.val.2), by
    have ht := pair_first_ne_pole f k hm p
    have hs := (halfSphereCoordinates 0 (by constructor <;> norm_num)).map_target ht
    change (concatenate f g).val
      ((halfSphereCoordinates 0 (by constructor <;> norm_num)).symm p.val.1) = k p.val.2
    exact (concatenate_left f g _ hs).trans ((congrArg f.val
      (halfSphereCoordinates_right_inv 0 (by constructor <;> norm_num) ht)).trans p.property)⟩

def rightPair (p : pairs g.val k) : pairs (concatenate f g).val k :=
  ⟨((halfSphereCoordinates 1 (by constructor <;> norm_num)).symm p.val.1, p.val.2), by
    have ht := pair_first_ne_pole g k hm p
    have hs := (halfSphereCoordinates 1 (by constructor <;> norm_num)).map_target ht
    change (concatenate f g).val
      ((halfSphereCoordinates 1 (by constructor <;> norm_num)).symm p.val.1) = k p.val.2
    exact (concatenate_right f g _ hs).trans ((congrArg g.val
      (halfSphereCoordinates_right_inv 1 (by constructor <;> norm_num) ht)).trans p.property)⟩

theorem leftPair_source (p : pairs f.val k) : (leftPair f g k hm p).val.1 ∈ halfSphere 0 :=
  (halfSphereCoordinates 0 (by constructor <;> norm_num)).map_target (pair_first_ne_pole f k hm p)

theorem rightPair_source (p : pairs g.val k) : (rightPair f g k hm p).val.1 ∈ halfSphere 1 :=
  (halfSphereCoordinates 1 (by constructor <;> norm_num)).map_target (pair_first_ne_pole g k hm p)

theorem leftPair_coordinates (p : pairs f.val k) :
    (halfSphereCoordinates 0 (by constructor <;> norm_num) (leftPair f g k hm p).val.1,
      (leftPair f g k hm p).val.2) = p.val := by
  change (halfSphereCoordinates 0 (by constructor <;> norm_num)
    ((halfSphereCoordinates 0 (by constructor <;> norm_num)).symm p.val.1), p.val.2) = p.val
  exact Prod.ext (halfSphereCoordinates_right_inv 0 (by constructor <;> norm_num)
    (pair_first_ne_pole f k hm p)) rfl

theorem rightPair_coordinates (p : pairs g.val k) :
    (halfSphereCoordinates 1 (by constructor <;> norm_num) (rightPair f g k hm p).val.1,
      (rightPair f g k hm p).val.2) = p.val := by
  change (halfSphereCoordinates 1 (by constructor <;> norm_num)
    ((halfSphereCoordinates 1 (by constructor <;> norm_num)).symm p.val.1), p.val.2) = p.val
  exact Prod.ext (halfSphereCoordinates_right_inv 1 (by constructor <;> norm_num)
    (pair_first_ne_pole g k hm p)) rfl

theorem leftPair_ne_rightPair (p : pairs f.val k) (q : pairs g.val k) :
    leftPair f g k hm p ≠ rightPair f g k hm q := by
  intro h
  have hp := leftPair_source f g k hm p
  rw [h] at hp
  exact disjoint_left.mp halfSphere_disjoint hp (rightPair_source f g k hm q)

def concatenateSumPair : pairs f.val k ⊕ pairs g.val k → pairs (concatenate f g).val k :=
  Sum.elim (leftPair f g k hm) (rightPair f g k hm)

theorem concatenateSumPair_injective : Injective (concatenateSumPair f g k hm) := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hc := congrArg (fun a : pairs (concatenate f g).val k ↦
      (halfSphereCoordinates 0 (by constructor <;> norm_num) a.val.1, a.val.2)) h
    exact (leftPair_coordinates f g k hm p).symm.trans
      (hc.trans (leftPair_coordinates f g k hm q))
  · exact (leftPair_ne_rightPair f g k hm p q h).elim
  · exact (leftPair_ne_rightPair f g k hm q p h.symm).elim
  · apply congrArg Sum.inr
    apply Subtype.ext
    have hc := congrArg (fun a : pairs (concatenate f g).val k ↦
      (halfSphereCoordinates 1 (by constructor <;> norm_num) a.val.1, a.val.2)) h
    exact (rightPair_coordinates f g k hm p).symm.trans
      (hc.trans (rightPair_coordinates f g k hm q))

theorem concatenateSumPair_surjective : Surjective (concatenateSumPair f g k hm) := by
  intro q
  have hs := concatenate_intersection_off_seam f g k hm q.val.1 q.val.2 q.property
  rcases lt_or_gt_of_ne hs.2 with hl | hr
  · have hL := mem_halfSphere_zero hs.1 hl
    have hp := (concatenate_left f g q.val.1 hL).symm.trans q.property
    refine ⟨Sum.inl ⟨(halfSphereCoordinates 0 (by constructor <;> norm_num) q.val.1,
      q.val.2), hp⟩, ?_⟩
    apply Subtype.ext
    change ((halfSphereCoordinates 0 (by constructor <;> norm_num)).symm
      (halfSphereCoordinates 0 (by constructor <;> norm_num) q.val.1), q.val.2) = q.val
    exact Prod.ext (halfSphereCoordinates_left_inv 0 (by constructor <;> norm_num) hL) rfl
  · have hR := mem_halfSphere_one hs.1 hr
    have hp := (concatenate_right f g q.val.1 hR).symm.trans q.property
    refine ⟨Sum.inr ⟨(halfSphereCoordinates 1 (by constructor <;> norm_num) q.val.1,
      q.val.2), hp⟩, ?_⟩
    apply Subtype.ext
    change ((halfSphereCoordinates 1 (by constructor <;> norm_num)).symm
      (halfSphereCoordinates 1 (by constructor <;> norm_num) q.val.1), q.val.2) = q.val
    exact Prod.ext (halfSphereCoordinates_left_inv 1 (by constructor <;> norm_num) hR) rfl

def concatenateIntersectionEquiv :
    (pairs f.val k ⊕ pairs g.val k) ≃ pairs (concatenate f g).val k :=
  Equiv.ofBijective (concatenateSumPair f g k hm)
    ⟨concatenateSumPair_injective f g k hm, concatenateSumPair_surjective f g k hm⟩

theorem finite_concatenate_pairs (hf : (pairs f.val k).Finite) (hg : (pairs g.val k).Finite) :
    (pairs (concatenate f g).val k).Finite := by
  let := hf.to_subtype
  let := hg.to_subtype
  exact finite_coe_iff.mp (Finite.of_equiv (pairs f.val k ⊕ pairs g.val k)
    (concatenateIntersectionEquiv f g k hm))

theorem concatenate_pairs_ncard (hf : (pairs f.val k).Finite) (hg : (pairs g.val k).Finite) :
    (pairs (concatenate f g).val k).ncard = (pairs f.val k).ncard + (pairs g.val k).ncard := by
  let := hf.to_subtype
  let := hg.to_subtype
  change Nat.card (pairs (concatenate f g).val k) =
    Nat.card (pairs f.val k) + Nat.card (pairs g.val k)
  rw [← Nat.card_congr (concatenateIntersectionEquiv f g k hm), Nat.card_sum]

theorem concatenate_parity (hf : (pairs f.val k).Finite) (hg : (pairs g.val k).Finite) :
    parity (concatenate f g).val k = parity f.val k + parity g.val k := by
  simp only [parity, concatenate_pairs_ncard f g k hm hf hg, Nat.cast_add]

end NoExoticSixSphere.SmoothCube
