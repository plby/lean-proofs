import StackExchange.Puzzling139335.FourIncidences
import StackExchange.Puzzling139335.SymmetryOrbit
import StackExchange.Puzzling139335.UnitPairs

/-!
# Actual side pairs in the eight-incidence case

The two corners of each piece are adjacent. Pulling these actual endpoints
back to the prototype gives two-element subsets of the used corner types.
Equality of two such subsets forces a square symmetry between the pieces.
-/

open Set

namespace Puzzling139335.N8

noncomputable section

def cornerSet (d : SquareDissection) (i : Fin 4) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun a => corner a ∈ d.piece i

@[simp] theorem mem_cornerSet (d : SquareDissection) (i a : Fin 4) :
    a ∈ cornerSet d i ↔ corner a ∈ d.piece i := by
  classical
  simp [cornerSet]

theorem cornerSet_card (d : SquareDissection) (i : Fin 4) :
    (cornerSet d i).card = d.tileCornerCount i := rfl

def intrinsicPair (d : SquareDissection) (i : Fin 4) : Finset Plane := by
  classical
  exact (cornerSet d i).image (d.intrinsicCorner i)

@[simp] theorem mem_intrinsicPair (d : SquareDissection) (i : Fin 4) (p : Plane) :
    p ∈ intrinsicPair d i ↔
      ∃ a : Fin 4, corner a ∈ d.piece i ∧ d.intrinsicCorner i a = p := by
  classical
  simp [intrinsicPair]

theorem intrinsicPair_card (d : SquareDissection) (i : Fin 4) :
    (intrinsicPair d i).card = d.tileCornerCount i := by
  classical
  rw [intrinsicPair, Finset.card_image_of_injective _ (d.intrinsicCorner_injective i)]
  exact cornerSet_card d i

theorem intrinsicPair_subset_usedCornerTypes (d : SquareDissection) (i : Fin 4) :
    intrinsicPair d i ⊆ d.usedCornerTypes := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := (mem_intrinsicPair d i p).mp hp
  exact d.mem_usedCornerTypes.mpr ⟨i, a, ha, hpa⟩

/-- The assigned side records precisely the two actual corners of each piece. -/
def IsSideAssignment (d : SquareDissection) (s : Fin 4 → Fin 4) : Prop :=
  ∀ i a, corner a ∈ d.piece i ↔ a = s i ∨ a = s i + 1

theorem exists_side_assignment (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hcount : ∀ i, d.tileCornerCount i = 2) : ∃ s, IsSideAssignment d s := by
  classical
  have hrow (i : Fin 4) : ∃ a : Fin 4, cornerSet d i = {a, a + 1} := by
    obtain ⟨a, b, hab, hpair⟩ :=
      Finset.card_eq_two.mp ((cornerSet_card d i).trans (hcount i))
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
    rcases hadj with rfl | rfl
    · exact ⟨a, hpair⟩
    · refine ⟨a + 3, ?_⟩
      rw [hpair]
      fin_cases a <;> decide
  choose s hs using hrow
  refine ⟨s, ?_⟩
  intro i a
  rw [← mem_cornerSet d i a, hs i]
  simp

theorem intrinsicPair_eq (d : SquareDissection) {s : Fin 4 → Fin 4}
    (hs : IsSideAssignment d s) (i : Fin 4) :
    intrinsicPair d i = {d.intrinsicCorner i (s i), d.intrinsicCorner i (s i + 1)} := by
  classical
  have hcorners : cornerSet d i = {s i, s i + 1} := by
    ext a
    simp only [mem_cornerSet, Finset.mem_insert, Finset.mem_singleton]
    exact hs i a
  simp [intrinsicPair, hcorners]

theorem placement_image_intrinsicPair (d : SquareDissection) {s : Fin 4 → Fin 4}
    (hs : IsSideAssignment d s) (i : Fin 4) :
    d.placement i '' (intrinsicPair d i : Set Plane) = {corner (s i), corner (s i + 1)} := by
  classical
  rw [intrinsicPair_eq d hs i]
  simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton,
    d.placement_intrinsicCorner]

theorem relativePlacement_side_endpoints_of_pair_eq (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) {i j : Fin 4}
    (hpair : intrinsicPair d i = intrinsicPair d j) :
    d.relativePlacement i j '' {corner (s i), corner (s i + 1)} =
      {corner (s j), corner (s j + 1)} := by
  calc
    d.relativePlacement i j '' {corner (s i), corner (s i + 1)} =
        d.relativePlacement i j '' (d.placement i '' (intrinsicPair d i : Set Plane)) := by
      rw [placement_image_intrinsicPair d hs i]
    _ = d.placement j '' (intrinsicPair d i : Set Plane) := by
      rw [image_image]
      congr 1
      funext p
      simp [SquareDissection.relativePlacement]
    _ = d.placement j '' (intrinsicPair d j : Set Plane) := by rw [hpair]
    _ = {corner (s j), corner (s j + 1)} := placement_image_intrinsicPair d hs j

theorem relativePlacement_preserves_square_of_pair_eq (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) {i j : Fin 4}
    (hpair : intrinsicPair d i = intrinsicPair d j) :
    d.relativePlacement i j '' unitSquare = unitSquare :=
  d.side_congruence_preserves_square i j (s i) (s j) (d.relativePlacement i j)
    (d.relativePlacement_image i j) (relativePlacement_side_endpoints_of_pair_eq d hs hpair)

theorem center_pair_unique (d : SquareDissection) {s : Fin 4 → Fin 4}
    (hs : IsSideAssignment d s) {i : Fin 4}
    (hi : squareCenter ∈ interior (d.piece i)) :
    ∀ j, j ≠ i → intrinsicPair d j ≠ intrinsicPair d i := by
  intro j hji hpair
  have hS := relativePlacement_preserves_square_of_pair_eq d hs hpair.symm
  exact (d.center_not_mem_fixed_pair (Ne.symm hji) (d.relativePlacement i j)
    (d.relativePlacement_image i j)
    (SquareSymmetry.center_fixed_of_preserves_square _ hS)).1 hi

theorem no_three_equal_pairs (d : SquareDissection) (hc : d.HasProtectedCenter)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (intrinsicPair d i = intrinsicPair d j ∧ intrinsicPair d i = intrinsicPair d k) := by
  rintro ⟨hijpair, hikpair⟩
  exact d.not_hasProtectedCenter_of_three_square_symmetry_copies hij hik hjk
    (d.relativePlacement i j) (d.relativePlacement i k)
    (relativePlacement_preserves_square_of_pair_eq d hs hijpair).subset
    (relativePlacement_preserves_square_of_pair_eq d hs hikpair).subset
    (d.relativePlacement_image i j) (d.relativePlacement_image i k) hc

theorem dist_adjacent_corners (a : Fin 4) : dist (corner a) (corner (a + 1)) = 1 := by
  have hs : dist (corner a) (corner (a + 1)) ^ 2 = 1 := by
    fin_cases a <;> norm_num [plane_dist_sq, corner, Fin.ext_iff, Fin.val_add]
  nlinarith [dist_nonneg (x := corner a) (y := corner (a + 1))]

theorem isUnitSidePair_intrinsic (d : SquareDissection) {s : Fin 4 → Fin 4}
    (hs : IsSideAssignment d s) (i : Fin 4) :
    UnitPairs.IsUnitSidePair (d.piece 0)
      (d.intrinsicCorner i (s i)) (d.intrinsicCorner i (s i + 1)) := by
  refine ⟨(d.intrinsicCorner_mem_iff _ _).mpr ((hs i _).mpr (Or.inl rfl)),
    (d.intrinsicCorner_mem_iff _ _).mpr ((hs i _).mpr (Or.inr rfl)), ?_,
    d.placement i, s i, s i + 1, ?_, d.placement_intrinsicCorner _ _,
    d.placement_intrinsicCorner _ _⟩
  · rw [SquareDissection.intrinsicCorner, SquareDissection.intrinsicCorner,
      (d.placement i).symm.isometry.dist_eq]
    exact dist_adjacent_corners (s i)
  · rw [d.placement_image]
    exact d.piece_subset i

theorem isUnitSidePair_of_pair_eq (d : SquareDissection) {s : Fin 4 → Fin 4}
    (hs : IsSideAssignment d s) {i : Fin 4} {a b : Plane}
    (hab : a ≠ b) (hpair : intrinsicPair d i = {a, b}) :
    UnitPairs.IsUnitSidePair (d.piece 0) a b := by
  classical
  have hunit := isUnitSidePair_intrinsic d hs i
  have heq := (intrinsicPair_eq d hs i).symm.trans hpair
  have ha : a = d.intrinsicCorner i (s i) ∨ a = d.intrinsicCorner i (s i + 1) := by
    have : a ∈ ({d.intrinsicCorner i (s i), d.intrinsicCorner i (s i + 1)} : Finset Plane) := by
      rw [heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hb : b = d.intrinsicCorner i (s i) ∨ b = d.intrinsicCorner i (s i + 1) := by
    have : b ∈ ({d.intrinsicCorner i (s i), d.intrinsicCorner i (s i + 1)} : Finset Plane) := by
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
