import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairMap
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# Exactly two actual intersections of the reference sphere pair

The sphere equations reduce the coincidence locus to two specified source
pairs. Their finite cardinality and mod-two count follow from an explicit
bijection with `Bool`, not from a postulated intersection number.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereCylinder
open WhitneySphere (head head_apply join_head_tail)

theorem source_eq_of_coordinates {x y : Sphere 3}
    (hh : head x.val = head y.val) (ht : tail 2 x.val = tail 2 y.val) : x = y := by
  apply Subtype.ext
  rw [← join_head_tail x.val, ← join_head_tail y.val, hh, ht]

theorem coincidence_coordinates {x y : Sphere 3} (h : left x = right y) :
    tail 2 x.val = (head y.val + 1) • axis ∧
      tail 2 y.val = (head x.val + 1) • axis := by
  rw [left, right, leftAmbient_apply, rightAmbient_apply] at h
  exact ⟨congrArg Prod.fst h, (congrArg Prod.snd h).symm⟩

theorem coincidence_head {x y : Sphere 3} (h : left x = right y) :
    head x.val = head y.val ∧ (head x.val = -1 ∨ head x.val = 0) := by
  obtain ⟨htx, hty⟩ := coincidence_coordinates h
  have hx := head_sq_add_tail_sq x
  have hy := head_sq_add_tail_sq y
  rw [htx, norm_smul, norm_axis, mul_one, Real.norm_eq_abs, sq_abs] at hx
  rw [hty, norm_smul, norm_axis, mul_one, Real.norm_eq_abs, sq_abs] at hy
  have he : head x.val = head y.val := by nlinarith
  have hm : head x.val * (head x.val + 1) = 0 := by rw [← he] at hx; nlinarith
  refine ⟨he, ?_⟩
  rcases mul_eq_zero.mp hm with hz | hz
  · exact Or.inr hz
  · exact Or.inl (by linarith)

theorem coincidence_iff (x y : Sphere 3) : left x = right y ↔
    (x = endPole 2 false ∧ y = endPole 2 false) ∨
      (x = secondSource ∧ y = secondSource) := by
  constructor
  · intro h
    obtain ⟨htx, hty⟩ := coincidence_coordinates h
    obtain ⟨he, hfirst | hsecond⟩ := coincidence_head h
    · have hy : head y.val = -1 := he.symm.trans hfirst
      have tx : tail 2 x.val = 0 := by simpa only [hy, neg_add_cancel, zero_smul] using htx
      have ty : tail 2 y.val = 0 := by simpa only [hfirst, neg_add_cancel, zero_smul] using hty
      exact Or.inl ⟨source_eq_of_coordinates hfirst (tx.trans (tail_endPole 2 false).symm),
        source_eq_of_coordinates hy (ty.trans (tail_endPole 2 false).symm)⟩
    · have hy : head y.val = 0 := he.symm.trans hsecond
      have tx : tail 2 x.val = axis := by simpa only [hy, zero_add, one_smul] using htx
      have ty : tail 2 y.val = axis := by simpa only [hsecond, zero_add, one_smul] using hty
      exact Or.inr ⟨source_eq_of_coordinates hsecond (tx.trans tail_secondSource.symm),
        source_eq_of_coordinates hy (ty.trans tail_secondSource.symm)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact left_first.trans right_first.symm
    · exact left_second.trans right_second.symm

def intersectionPair (b : Bool) : MapIntersections.pairs left right :=
  if b then ⟨(secondSource, secondSource), left_second.trans right_second.symm⟩
  else ⟨(endPole 2 false, endPole 2 false), left_first.trans right_first.symm⟩

theorem intersectionPair_bijective : Bijective intersectionPair := by
  constructor
  · intro b c h
    cases b <;> cases c
    · rfl
    · exact (first_ne_second
        (congrArg (fun p : MapIntersections.pairs left right ↦ p.val.1) h)).elim
    · exact (first_ne_second
        (congrArg (fun p : MapIntersections.pairs left right ↦ p.val.1) h).symm).elim
    · rfl
  · intro p
    rcases (coincidence_iff p.val.1 p.val.2).mp p.property with h | h
    · exact ⟨false, Subtype.ext (Prod.ext h.1.symm h.2.symm)⟩
    · exact ⟨true, Subtype.ext (Prod.ext h.1.symm h.2.symm)⟩

def intersectionPairEquiv : Bool ≃ MapIntersections.pairs left right :=
  Equiv.ofBijective intersectionPair intersectionPair_bijective

theorem finite_intersectionPairs : (MapIntersections.pairs left right).Finite :=
  finite_coe_iff.mp (Finite.of_equiv Bool intersectionPairEquiv)

theorem intersectionPairs_ncard : (MapIntersections.pairs left right).ncard = 2 := by
  change Nat.card (MapIntersections.pairs left right) = 2
  rw [← Nat.card_congr intersectionPairEquiv]
  simp

theorem intersectionParity_zero : MapIntersections.parity left right = 0 := by
  rw [MapIntersections.parity, intersectionPairs_ncard]
  decide

theorem left_unorderedParity_zero : SphereSelfIntersections.unorderedParity left = 0 :=
  SphereSelfIntersections.unorderedParity_zero_of_injective left injective_left

theorem right_unorderedParity_zero : SphereSelfIntersections.unorderedParity right = 0 :=
  SphereSelfIntersections.unorderedParity_zero_of_injective right injective_right

end NoExoticSixSphere.DoubleCrossingSpherePair
