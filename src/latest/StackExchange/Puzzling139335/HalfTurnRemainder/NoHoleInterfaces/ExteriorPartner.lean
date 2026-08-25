import StackExchange.Puzzling139335.InterfacePairing

/-!
# Exterior partner labels from reciprocal interface occurrences

The exact boundary family supplies reciprocal partner occurrences as a proved
theorem. Thus a region whose every partner is one of the two remaining pieces
cannot be a partner of the exterior boundary.
-/

namespace Puzzling139335.HalfTurnRemainder

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- A specified partner label has an actual reciprocal occurrence, with the
dependent arc index transported to that specified label. -/
theorem exists_reciprocal_partner_of_partner_eq (i : ExtendedPieceIndex)
    (k : Fin (F.n i)) {j : ExtendedPieceIndex} (hpartner : F.partner i k = j) :
    ∃ l : Fin (F.n j), F.partner j l = i := by
  subst j
  obtain ⟨l, hl, _⟩ := F.exists_unique_reciprocal_partner_arc i k
  exact ⟨l, hl.2⟩

/-- If pieces `2` and `3` have only pieces `0` and `1` as interface partners,
then every exterior interface also has one of those two partners. -/
theorem exterior_partner_eq_zero_or_one_of_piece_partners
    (h2 : ∀ k : Fin (F.n (Sum.inl 2)),
      F.partner (Sum.inl 2) k = Sum.inl 0 ∨ F.partner (Sum.inl 2) k = Sum.inl 1)
    (h3 : ∀ k : Fin (F.n (Sum.inl 3)),
      F.partner (Sum.inl 3) k = Sum.inl 0 ∨ F.partner (Sum.inl 3) k = Sum.inl 1) :
    ∀ k : Fin (F.n (Sum.inr ())),
      F.partner (Sum.inr ()) k = Sum.inl 0 ∨ F.partner (Sum.inr ()) k = Sum.inl 1 := by
  intro k
  cases hp : F.partner (Sum.inr ()) k with
  | inr u =>
      cases u
      exact False.elim (F.partner_ne (Sum.inr ()) k hp)
  | inl i =>
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · obtain ⟨l, hl⟩ := exists_reciprocal_partner_of_partner_eq F (Sum.inr ()) k hp
        rcases h2 l with h0 | h1
        · cases hl.symm.trans h0
        · cases hl.symm.trans h1
      · obtain ⟨l, hl⟩ := exists_reciprocal_partner_of_partner_eq F (Sum.inr ()) k hp
        rcases h3 l with h0 | h1
        · cases hl.symm.trans h0
        · cases hl.symm.trans h1

end Puzzling139335.HalfTurnRemainder
