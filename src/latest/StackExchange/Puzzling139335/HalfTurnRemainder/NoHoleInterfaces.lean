import StackExchange.Puzzling139335.InterfacePairing
import StackExchange.Puzzling139335.HalfTurnRemainder.NoHoleInterfaces.ExteriorPartner
import Wikipedia.SchoenfliesTheorem.Topology

/-!
# Interface partners when the two omitted pieces fill holes

The boundary of an actual complementary component lies in the excluded closed
set. Thus a point on a hole piece's boundary lies on one of the two remaining
pieces. Away from the common junction set, it cannot lie on any third region,
so the interface partner is one of those remaining pieces.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

private theorem frontier_interior_piece (d : SquareDissection) (i : Fin 4) :
    frontier (interior (d.piece i)) = frontier (d.piece i) := by
  simp only [frontier, interior_interior, (d.jordan i).closure_interior,
    (d.jordan i).isClosed.closure_eq]

/-- If a piece's interior is a complementary component of the two-piece
remainder, its whole boundary belongs to that remainder. -/
theorem frontier_subset_remaining_of_hole_component (d : SquareDissection)
    {i : Fin 4} {x : Plane}
    (hcomp : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x = interior (d.piece i)) :
    frontier (d.piece i) ⊆ d.piece 0 ∪ d.piece 1 := by
  have hclosed : IsClosed (d.piece 0 ∪ d.piece 1) :=
    (d.jordan 0).isClosed.union (d.jordan 1).isClosed
  have hfront := Schoenflies.Plane.frontier_connectedComponentIn_compl_subset hclosed x
  rwa [hcomp, frontier_interior_piece d i] at hfront

private theorem partner_eq_of_mem_off_junctions {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {i j : ExtendedPieceIndex} {k : Fin (F.n i)}
    {x : Plane} (hij : i ≠ j) (hx : x ∈ F.arc i k)
    (hxnot : x ∉ tripleContactSet d.extendedPiece) (hxj : x ∈ d.extendedPiece j) :
    F.partner i k = j := by
  have hxi : x ∈ d.extendedPiece i :=
    (d.extendedPiece_closed i).closure_eq ▸ (F.subset_frontiers i k hx).1.1
  have hxp : x ∈ d.extendedPiece (F.partner i k) :=
    (d.extendedPiece_closed (F.partner i k)).closure_eq ▸
      (F.subset_frontiers i k hx).2.1
  by_contra hpj
  exact hxnot ⟨i, F.partner i k, j, (F.partner_ne i k).symm, hij, hpj, hxi, hxp, hxj⟩

/-- A boundary lying in the two remaining pieces can have no other interface
partner, because every exact arc has a point away from the triple junctions. -/
theorem partner_eq_zero_or_one_of_frontier_subset {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {i : Fin 4} (hi0 : i ≠ 0) (hi1 : i ≠ 1)
    (hfront : frontier (d.piece i) ⊆ d.piece 0 ∪ d.piece 1)
    (k : Fin (F.n (Sum.inl i))) :
    F.partner (Sum.inl i) k = Sum.inl 0 ∨ F.partner (Sum.inl i) k = Sum.inl 1 := by
  obtain ⟨x, hx, hxnot⟩ := F.exists_mem_off_junctions (Sum.inl i) k
  have hxfront : x ∈ frontier (d.piece i) := (F.subset_frontiers (Sum.inl i) k hx).1
  rcases hfront hxfront with hx0 | hx1
  · exact Or.inl (partner_eq_of_mem_off_junctions F
      (fun h => hi0 (Sum.inl.inj h)) hx hxnot hx0)
  · exact Or.inr (partner_eq_of_mem_off_junctions F
      (fun h => hi1 (Sum.inl.inj h)) hx hxnot hx1)

/-- Concrete partner restriction for any omitted piece known to fill a hole. -/
theorem hole_partner_eq_zero_or_one {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {i : Fin 4} {x : Plane}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1)
    (hcomp : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x = interior (d.piece i))
    (k : Fin (F.n (Sum.inl i))) :
    F.partner (Sum.inl i) k = Sum.inl 0 ∨ F.partner (Sum.inl i) k = Sum.inl 1 :=
  partner_eq_zero_or_one_of_frontier_subset F hi0 hi1
    (frontier_subset_remaining_of_hole_component d hcomp) k

theorem piece_two_partner_eq_zero_or_one {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {x : Plane}
    (hcomp : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x = interior (d.piece 2))
    (k : Fin (F.n (Sum.inl 2))) :
    F.partner (Sum.inl 2) k = Sum.inl 0 ∨ F.partner (Sum.inl 2) k = Sum.inl 1 :=
  hole_partner_eq_zero_or_one F (by decide) (by decide) hcomp k

theorem piece_three_partner_eq_zero_or_one {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {x : Plane}
    (hcomp : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x = interior (d.piece 3))
    (k : Fin (F.n (Sum.inl 3))) :
    F.partner (Sum.inl 3) k = Sum.inl 0 ∨ F.partner (Sum.inl 3) k = Sum.inl 1 :=
  hole_partner_eq_zero_or_one F (by decide) (by decide) hcomp k

/-- When the two omitted pieces are the hole components, no exterior interface
can border either omitted piece. Reciprocal pairing would contradict that
hole piece's already proved partner restriction. -/
theorem exterior_partner_eq_zero_or_one_of_hole_components {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {x₂ x₃ : Plane}
    (h₂ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₂ = interior (d.piece 2))
    (h₃ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₃ = interior (d.piece 3))
    (k : Fin (F.n (Sum.inr ()))) :
    F.partner (Sum.inr ()) k = Sum.inl 0 ∨ F.partner (Sum.inr ()) k = Sum.inl 1 :=
  exterior_partner_eq_zero_or_one_of_piece_partners F
    (piece_two_partner_eq_zero_or_one F h₂) (piece_three_partner_eq_zero_or_one F h₃) k

/-- Every exact interface occurrence on a hole piece or on the exterior names
one of the two remaining pieces as partner. The hypotheses identify the actual
complementary components; no absence-of-interfaces assumption is used. -/
theorem partner_eq_zero_or_one_of_two_holes {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {x₂ x₃ : Plane}
    (h₂ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₂ = interior (d.piece 2))
    (h₃ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₃ = interior (d.piece 3))
    (i : ExtendedPieceIndex) (hi0 : i ≠ Sum.inl 0) (hi1 : i ≠ Sum.inl 1)
    (k : Fin (F.n i)) :
    F.partner i k = Sum.inl 0 ∨ F.partner i k = Sum.inl 1 := by
  cases i with
  | inl j =>
      fin_cases j
      · exact False.elim (hi0 rfl)
      · exact False.elim (hi1 rfl)
      · exact piece_two_partner_eq_zero_or_one F h₂ k
      · exact piece_three_partner_eq_zero_or_one F h₃ k
  | inr u =>
      cases u
      exact exterior_partner_eq_zero_or_one_of_hole_components F h₂ h₃ k

end

end Puzzling139335.HalfTurnRemainder
