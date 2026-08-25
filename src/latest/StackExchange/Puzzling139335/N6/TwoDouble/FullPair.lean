import StackExchange.Puzzling139335.N6.Incidence
import StackExchange.Puzzling139335.N6.TwoDouble.SingletonBranch
import StackExchange.Puzzling139335.N5.TypeReduction

/-!
# The two actual copies of the full-corner unit pair

When the two uniquely owned physical corners use just one intrinsic type,
their copies both have two corners and their second intrinsic endpoint is
the same. Every property below is derived from the actual dissection.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- The actual repeated full-corner copies have one common unit pair. -/
theorem repeated_full_pair (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    {i j a b : Fin 4} (hij : i ≠ j) (ha : corner a ∈ d.piece i)
    (hunique : ∀ l, l ≠ i → corner a ∉ d.piece l)
    (htype : d.intrinsicCorner i a = d.intrinsicCorner j b) :
    ∃ v : Plane, d.intrinsicCorner i a ≠ v ∧
      UnitPairs.IsFullSquareCorner (d.piece 0) (d.intrinsicCorner i a) ∧
      N8.intrinsicPair d i = {d.intrinsicCorner i a, v} ∧
      N8.intrinsicPair d j = {d.intrinsicCorner i a, v} ∧
      d.relativePlacement i j '' unitSquare = unitSquare ∧
      squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  classical
  obtain ⟨hi, hj⟩ := repeated_unique_counts_two d hc hN hU hij ha hunique htype
  have hfull := N5.isFullSquareCorner_of_unique_corner d i a hunique
  have hri : d.intrinsicCorner i a ∈ N8.intrinsicPair d i :=
    (N8.mem_intrinsicPair d i _).mpr ⟨a, ha, rfl⟩
  have hb : corner b ∈ d.piece j := by
    apply (d.intrinsicCorner_mem_iff j b).mp
    rw [← htype]
    exact (d.intrinsicCorner_mem_iff i a).mpr ha
  have hrj : d.intrinsicCorner i a ∈ N8.intrinsicPair d j :=
    (N8.mem_intrinsicPair d j _).mpr ⟨b, hb, htype.symm⟩
  obtain ⟨v, hrv, hv⟩ := exists_partner ((N8.intrinsicPair_card d i).trans hi) hri
  have hpair := pair_eq_of_common_full_type d hc hi hj hfull hri hrj
  exact ⟨v, hrv, hfull, hv, hpair.symm.trans hv,
    d.relativePlacement_preserves_square_of_unique_corner hunique htype,
    d.center_not_mem_of_repeated_unique_corner hij hunique htype⟩

/-- The two unique corners in the two-double-corner pattern are distinct
actual corners, independently of whether they lie in one or two pieces. -/
theorem exists_two_unique_corners (d : SquareDissection) (hD : HasTwoDoubleCorners d) :
    ∃ a b : Fin 4, a ≠ b ∧ d.cornerTileCount a = 1 ∧ d.cornerTileCount b = 1 := by
  classical
  obtain ⟨s, t, hst, _, _, hrest⟩ := hD
  let U : Finset (Fin 4) := (Finset.univ.erase s).erase t
  have hcard : U.card = 2 := by
    simp [U, Finset.card_erase_of_mem, hst.symm]
  obtain ⟨a, b, hab, hU⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ U := by rw [hU]; simp
  have hb : b ∈ U := by rw [hU]; simp
  have has : a ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  have hat : a ≠ t := (Finset.mem_erase.mp ha).1
  have hbs : b ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
  have hbt : b ≠ t := (Finset.mem_erase.mp hb).1
  exact ⟨a, b, hab, hrest a has hat, hrest b hbs hbt⟩

/-- If only one intrinsic type occurs at the unique corners, the repeated
full-corner pair is obtained from the two actual unique-corner owners. -/
theorem exists_full_pair_of_one_full_type (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3) (hD : HasTwoDoubleCorners d)
    (hfullCount : (N5.fullCornerTypes d).card ≤ 1) :
    ∃ i j : Fin 4, i ≠ j ∧ ∃ r v : Plane, r ≠ v ∧
      UnitPairs.IsFullSquareCorner (d.piece 0) r ∧
      N8.intrinsicPair d i = {r, v} ∧ N8.intrinsicPair d j = {r, v} ∧
      d.relativePlacement i j '' unitSquare = unitSquare ∧
      squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  classical
  obtain ⟨a, b, hab, hac, hbc⟩ := exists_two_unique_corners d hD
  obtain ⟨i, hi, hui⟩ := N5.unique_owner_of_count_one d a hac
  obtain ⟨j, hj, _⟩ := N5.unique_owner_of_count_one d b hbc
  have hri : d.intrinsicCorner i a ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr ⟨i, a, hi, hac, rfl⟩
  have hrj : d.intrinsicCorner j b ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr ⟨j, b, hj, hbc, rfl⟩
  have htype : d.intrinsicCorner i a = d.intrinsicCorner j b :=
    Finset.card_le_one_iff.mp hfullCount hri hrj
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hab (d.intrinsicCorner_injective i htype)
  have hunique : ∀ l, l ≠ i → corner a ∉ d.piece l := by
    intro l hli hl
    exact hli (hui l hl)
  obtain ⟨v, hv, hfull, hip, hjp, hS, hci, hcj⟩ :=
    repeated_full_pair d hc hN hU hij hi hunique htype
  exact ⟨i, j, hij, d.intrinsicCorner i a, v, hv, hfull, hip, hjp, hS, hci, hcj⟩

end

end Puzzling139335.N6.TwoDouble
