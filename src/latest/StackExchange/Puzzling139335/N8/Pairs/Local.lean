import StackExchange.Puzzling139335.N8.Pairs

/-!
# Side pairs for selected individual pieces

The side-pair arguments do not require every piece to contain two square
corners. This module records their local versions, for use when only a
selected collection of pieces has two corners.
-/

open Set

namespace Puzzling139335.N8

noncomputable section

/-- The two actual square corners of one piece are precisely the endpoints
of the indicated square side. -/
def IsLocalSide (d : SquareDissection) (i s : Fin 4) : Prop :=
  ∀ a, corner a ∈ d.piece i ↔ a = s ∨ a = s + 1

theorem exists_local_side_of_count_two (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) (hcount : d.tileCornerCount i = 2) :
    ∃ s, IsLocalSide d i s := by
  classical
  obtain ⟨a, b, hab, hpair⟩ :=
    Finset.card_eq_two.mp ((cornerSet_card d i).trans hcount)
  have ha : corner a ∈ d.piece i := by
    apply (mem_cornerSet d i a).mp
    rw [hpair]
    simp
  have hb : corner b ∈ d.piece i := by
    apply (mem_cornerSet d i b).mp
    rw [hpair]
    simp
  have hbo : b ≠ a + 2 := by
    intro hba
    exact d.no_opposite_corners hc i a ⟨ha, hba ▸ hb⟩
  have hadj : b = a + 1 ∨ b = a + 3 := by
    fin_cases a <;> fin_cases b <;> simp_all
  have hside : ∃ s : Fin 4, cornerSet d i = {s, s + 1} := by
    rcases hadj with rfl | rfl
    · exact ⟨a, hpair⟩
    · refine ⟨a + 3, ?_⟩
      rw [hpair]
      fin_cases a <;> decide
  obtain ⟨s, hs⟩ := hside
  refine ⟨s, ?_⟩
  intro j
  rw [← mem_cornerSet d i j, hs]
  simp

theorem local_intrinsicPair_eq (d : SquareDissection) {i s : Fin 4}
    (hs : IsLocalSide d i s) :
    intrinsicPair d i = {d.intrinsicCorner i s, d.intrinsicCorner i (s + 1)} := by
  classical
  have hcorners : cornerSet d i = {s, s + 1} := by
    ext a
    simp only [mem_cornerSet, Finset.mem_insert, Finset.mem_singleton]
    exact hs a
  simp [intrinsicPair, hcorners]

theorem local_placement_image_intrinsicPair (d : SquareDissection) {i s : Fin 4}
    (hs : IsLocalSide d i s) :
    d.placement i '' (intrinsicPair d i : Set Plane) =
      {corner s, corner (s + 1)} := by
  classical
  rw [local_intrinsicPair_eq d hs]
  simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton,
    d.placement_intrinsicCorner]

theorem local_relativePlacement_side_endpoints_of_pair_eq (d : SquareDissection)
    {i j s t : Fin 4} (hsi : IsLocalSide d i s) (hsj : IsLocalSide d j t)
    (hpair : intrinsicPair d i = intrinsicPair d j) :
    d.relativePlacement i j '' {corner s, corner (s + 1)} =
      {corner t, corner (t + 1)} := by
  calc
    d.relativePlacement i j '' {corner s, corner (s + 1)} =
        d.relativePlacement i j '' (d.placement i '' (intrinsicPair d i : Set Plane)) := by
      rw [local_placement_image_intrinsicPair d hsi]
    _ = d.placement j '' (intrinsicPair d i : Set Plane) := by
      rw [image_image]
      congr 1
      funext p
      simp [SquareDissection.relativePlacement]
    _ = d.placement j '' (intrinsicPair d j : Set Plane) := by rw [hpair]
    _ = {corner t, corner (t + 1)} := local_placement_image_intrinsicPair d hsj

theorem local_relativePlacement_preserves_square_of_pair_eq (d : SquareDissection)
    {i j s t : Fin 4} (hsi : IsLocalSide d i s) (hsj : IsLocalSide d j t)
    (hpair : intrinsicPair d i = intrinsicPair d j) :
    d.relativePlacement i j '' unitSquare = unitSquare :=
  d.side_congruence_preserves_square i j s t (d.relativePlacement i j)
    (d.relativePlacement_image i j)
    (local_relativePlacement_side_endpoints_of_pair_eq d hsi hsj hpair)

theorem local_center_pair_ne (d : SquareDissection) {i j s t : Fin 4}
    (hsi : IsLocalSide d i s) (hsj : IsLocalSide d j t)
    (hi : squareCenter ∈ interior (d.piece i)) (hij : i ≠ j) :
    intrinsicPair d i ≠ intrinsicPair d j := by
  intro hpair
  have hS := local_relativePlacement_preserves_square_of_pair_eq d hsi hsj hpair
  exact (d.center_not_mem_fixed_pair hij (d.relativePlacement i j)
    (d.relativePlacement_image i j)
    (SquareSymmetry.center_fixed_of_preserves_square _ hS)).1 hi

theorem local_no_three_equal_pairs (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j k s t u : Fin 4} (hsi : IsLocalSide d i s) (hsj : IsLocalSide d j t)
    (hsk : IsLocalSide d k u) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (intrinsicPair d i = intrinsicPair d j ∧ intrinsicPair d i = intrinsicPair d k) := by
  rintro ⟨hijpair, hikpair⟩
  exact d.not_hasProtectedCenter_of_three_square_symmetry_copies hij hik hjk
    (d.relativePlacement i j) (d.relativePlacement i k)
    (local_relativePlacement_preserves_square_of_pair_eq d hsi hsj hijpair).subset
    (local_relativePlacement_preserves_square_of_pair_eq d hsi hsk hikpair).subset
    (d.relativePlacement_image i j) (d.relativePlacement_image i k) hc

theorem local_isUnitSidePair_intrinsic (d : SquareDissection) {i s : Fin 4}
    (hs : IsLocalSide d i s) :
    UnitPairs.IsUnitSidePair (d.piece 0)
      (d.intrinsicCorner i s) (d.intrinsicCorner i (s + 1)) := by
  refine ⟨(d.intrinsicCorner_mem_iff _ _).mpr ((hs _).mpr (Or.inl rfl)),
    (d.intrinsicCorner_mem_iff _ _).mpr ((hs _).mpr (Or.inr rfl)), ?_,
    d.placement i, s, s + 1, ?_, d.placement_intrinsicCorner _ _,
    d.placement_intrinsicCorner _ _⟩
  · rw [SquareDissection.intrinsicCorner, SquareDissection.intrinsicCorner,
      (d.placement i).symm.isometry.dist_eq]
    exact dist_adjacent_corners s
  · rw [d.placement_image]
    exact d.piece_subset i

theorem local_isUnitSidePair_of_pair_eq (d : SquareDissection) {i s : Fin 4}
    (hs : IsLocalSide d i s) {a b : Plane}
    (hab : a ≠ b) (hpair : intrinsicPair d i = {a, b}) :
    UnitPairs.IsUnitSidePair (d.piece 0) a b := by
  classical
  have hunit := local_isUnitSidePair_intrinsic d hs
  have heq := (local_intrinsicPair_eq d hs).symm.trans hpair
  have ha : a = d.intrinsicCorner i s ∨ a = d.intrinsicCorner i (s + 1) := by
    have : a ∈ ({d.intrinsicCorner i s, d.intrinsicCorner i (s + 1)} : Finset Plane) := by
      rw [heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hb : b = d.intrinsicCorner i s ∨ b = d.intrinsicCorner i (s + 1) := by
    have : b ∈ ({d.intrinsicCorner i s, d.intrinsicCorner i (s + 1)} : Finset Plane) := by
      rw [heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact hunit
  · exact hunit.symm
  · exact (hab rfl).elim

end

end Puzzling139335.N8
