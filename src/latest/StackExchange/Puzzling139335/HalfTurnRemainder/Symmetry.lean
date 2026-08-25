import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# The actual remainder of a half-turn pair is central

Removing a pair of tiles is interpreted by the exact regular-closed identity
`A ∪ D = closure (Q \ (B ∪ C))`. Thus symmetry of the outer square and of the
removed pair proves symmetry of the remaining union. No topological property
of that union is assumed.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

section RegularClosed

variable {X : Type*} [TopologicalSpace X]

/-- The two remaining regular closed sets are the closure of the uncovered
part of the outer set. -/
theorem union_eq_closure_sdiff {A D R Q : Set X}
    (hAclosed : IsClosed A) (hDclosed : IsClosed D)
    (hAreg : closure (interior A) = A) (hDreg : closure (interior D) = D)
    (hcover : (A ∪ D) ∪ R = Q)
    (hAR : Disjoint (interior A) R) (hDR : Disjoint (interior D) R) :
    A ∪ D = closure (Q \ R) := by
  apply Subset.antisymm
  · apply union_subset
    · rw [← hAreg]
      apply closure_mono
      intro x hx
      refine ⟨?_, fun hr => Set.disjoint_left.mp hAR hx hr⟩
      rw [← hcover]
      exact Or.inl (Or.inl (interior_subset hx))
    · rw [← hDreg]
      apply closure_mono
      intro x hx
      refine ⟨?_, fun hr => Set.disjoint_left.mp hDR hx hr⟩
      rw [← hcover]
      exact Or.inl (Or.inr (interior_subset hx))
  · apply closure_minimal ?_ (hAclosed.union hDclosed)
    intro x hx
    have hxQ := hx.1
    rw [← hcover] at hxQ
    exact hxQ.resolve_right hx.2

/-- One member of a disjoint-interior regular-closed pair is recovered by
removing the other from their union and taking closure. -/
theorem right_eq_closure_union_sdiff {A D : Set X}
    (hDclosed : IsClosed D) (hDreg : closure (interior D) = D)
    (hDA : Disjoint (interior D) A) :
    D = closure ((A ∪ D) \ A) := by
  apply Subset.antisymm
  · calc
      D = closure (interior D) := hDreg.symm
      _ ⊆ closure ((A ∪ D) \ A) := by
        apply closure_mono
        intro x hx
        exact ⟨Or.inr (interior_subset hx), fun hA => Set.disjoint_left.mp hDA hx hA⟩
  · apply closure_minimal ?_ hDclosed
    intro x hx
    exact hx.1.resolve_left hx.2

/-- A homeomorphism preserving both the outer set and the removed set also
preserves the actual remaining regular-closed union. -/
theorem image_union_eq_of_invariant_outer_removed {A D R Q : Set X}
    (e : X ≃ₜ X) (hAclosed : IsClosed A) (hDclosed : IsClosed D)
    (hAreg : closure (interior A) = A) (hDreg : closure (interior D) = D)
    (hcover : (A ∪ D) ∪ R = Q)
    (hAR : Disjoint (interior A) R) (hDR : Disjoint (interior D) R)
    (hQ : e '' Q = Q) (hR : e '' R = R) : e '' (A ∪ D) = A ∪ D := by
  have hU := union_eq_closure_sdiff hAclosed hDclosed hAreg hDreg hcover hAR hDR
  rw [hU, e.image_closure, Set.image_sdiff e.injective, hQ, hR]

end RegularClosed

/-- Coordinate formula for the half-turn about the square center. -/
theorem pointReflection_squareCenter_apply (x : Plane) (i : Fin 2) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter x) i = 1 - x i := by
  rw [AffineIsometryEquiv.pointReflection_apply]
  change squareCenter i - x i + squareCenter i = 1 - x i
  fin_cases i <;> norm_num [squareCenter] <;> ring

/-- The closed unit square is invariant under its central half-turn. -/
theorem pointReflection_image_unitSquare :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' unitSquare = unitSquare := by
  let e := AffineIsometryEquiv.pointReflection ℝ squareCenter
  have hmaps : MapsTo e unitSquare unitSquare := by
    intro x hx
    change (e x) 0 ∈ Icc (0 : ℝ) 1 ∧ (e x) 1 ∈ Icc (0 : ℝ) 1
    dsimp only [e]
    rw [pointReflection_squareCenter_apply, pointReflection_squareCenter_apply]
    constructor <;> constructor <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]
  apply Subset.antisymm (mapsTo_iff_image_subset.mp hmaps)
  intro x hx
  exact ⟨e x, hmaps hx, AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) squareCenter x⟩

end Puzzling139335.HalfTurnRemainder

namespace Puzzling139335.SquareDissection

open HalfTurnRemainder

/-- The four actual pieces, grouped into the remaining and removed pairs. -/
theorem four_piece_pair_union (d : SquareDissection) :
    (d.piece 0 ∪ d.piece 1) ∪ (d.piece 2 ∪ d.piece 3) = unitSquare := by
  apply Subset.antisymm
  · rintro x ((hx | hx) | hx | hx)
    · exact d.piece_subset 0 hx
    · exact d.piece_subset 1 hx
    · exact d.piece_subset 2 hx
    · exact d.piece_subset 3 hx
  · intro x hx
    obtain ⟨i, hi⟩ := d.exists_piece_mem hx
    fin_cases i <;> simp_all

/-- Exact remainder identity for an actual square dissection. -/
theorem pair_remainder_eq_closure (d : SquareDissection) :
    d.piece 0 ∪ d.piece 1 = closure (unitSquare \ (d.piece 2 ∪ d.piece 3)) := by
  apply union_eq_closure_sdiff (d.jordan 0).isClosed (d.jordan 1).isClosed
    (d.jordan 0).closure_interior (d.jordan 1).closure_interior d.four_piece_pair_union
  · exact disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩
  · exact disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩

/-- An actual half-turn pair makes the other two pieces centrally symmetric as
a union. This conclusion precedes, and does not assume, any Jordan-remainder
or connectedness assertion. -/
theorem pair_remainder_pointReflection (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' (d.piece 0 ∪ d.piece 1) =
      d.piece 0 ∪ d.piece 1 := by
  let e := (AffineIsometryEquiv.pointReflection ℝ squareCenter).toHomeomorph
  have hinv : Function.Involutive e :=
    AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) squareCenter
  have hback : e '' d.piece 3 = d.piece 2 := by
    rw [← hpair, image_image]
    change (fun x => e (e x)) '' d.piece 2 = d.piece 2
    have hee : (fun x => e (e x)) = id := funext hinv
    rw [hee, image_id]
  have hremoved : e '' (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3 := by
    rw [image_union, show e '' d.piece 2 = d.piece 3 from hpair, hback, union_comm]
  change e '' (d.piece 0 ∪ d.piece 1) = d.piece 0 ∪ d.piece 1
  rw [d.pair_remainder_eq_closure, e.image_closure, Set.image_sdiff e.injective,
    show e '' unitSquare = unitSquare from pointReflection_image_unitSquare, hremoved]

end Puzzling139335.SquareDissection
