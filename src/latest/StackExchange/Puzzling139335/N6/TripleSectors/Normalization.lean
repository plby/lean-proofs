import StackExchange.Puzzling139335.N6.TripleSectors.Actual
import StackExchange.Puzzling139335.N6.TripleSectors.Angles
import StackExchange.Puzzling139335.N6.TripleSectors.Placement
import StackExchange.Puzzling139335.N6.TripleSectors.GlobalCone
import StackExchange.Puzzling139335.AcuteCorner.Defs

/-!
# The actual normalized triple-corner alternatives

The local angle trisection and rigidity of the genuine congruences give
the explicit placements used in the two parity cases.  The global support
bounds therefore follow from the original Jordan dissection data.
-/

open Set

namespace Puzzling139335.N6.TripleSectors

noncomputable section

theorem thirtyCone_subset_cone45 : thirtyCone ⊆ AcuteCorner.cone45 := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_right one_lt_sqrt_three.le hp.1, hp.2.1]

namespace NormalizedTriple

/-- Ordering the three actual local sectors determines both middle and
last placement alternatives, and produces an actual positive point on the
first copy's horizontal boundary ray. -/
theorem exists_ordered_placements (T : NormalizedTriple) :
    ∃ σ : Equiv.Perm (Fin 3),
      (T.region (σ 1) = rotateThirty '' T.region (σ 0) ∨
        T.region (σ 1) = reflectThirty '' T.region (σ 0)) ∧
      (T.region (σ 2) = rotateSixty '' T.region (σ 0) ∨
        T.region (σ 2) = ReflectionSeparation.diagonal '' T.region (σ 0)) ∧
      ∃ t > 0, point t 0 ∈ T.region (σ 0) := by
  obtain ⟨g, _, σ, h00, h01, h10, h11, h20, h21⟩ :=
    Angles.exists_raySectorGerms_trisection T.jordan T.quadrant T.straight
      T.disjoint T.local_cover T.congruences
  refine ⟨σ, ?_, ?_, ?_⟩
  · obtain ⟨e, he0, he⟩ := T.congruences (σ 0) (σ 1)
    have hmatch := (g (σ 0)).angular_endpoints_match (g (σ 1)) e he0 he
    have hpair : e '' ({directionZero, directionThirty} : Set Plane) =
        {directionThirty, directionSixty} := by
      rw [image_pair, pair_eq_pair_iff]
      simpa only [h00, h01, h10, h11, ray_zero_eq_direction, ray_pi_six_eq_direction,
        ray_pi_three_eq_direction] using hmatch
    rcases middle_placement_of_boundary_pair e he0 hpair with heq | heq
    · left
      rw [heq] at he
      exact he.symm
    · right
      rw [heq] at he
      exact he.symm
  · obtain ⟨e, he0, he⟩ := T.congruences (σ 0) (σ 2)
    have hmatch := (g (σ 0)).angular_endpoints_match (g (σ 2)) e he0 he
    have hpair : e '' ({directionZero, directionThirty} : Set Plane) =
        {directionSixty, directionNinety} := by
      rw [image_pair, pair_eq_pair_iff]
      simpa only [h00, h01, h20, h21, ray_zero_eq_direction, ray_pi_six_eq_direction,
        ray_pi_three_eq_direction, ray_pi_two_eq_direction] using hmatch
    rcases last_placement_of_boundary_pair e he0 hpair with heq | heq
    · left
      rw [heq] at he
      exact he.symm
    · right
      rw [heq] at he
      exact he.symm
  · have hl : (g (σ 0)).left = point ‖(g (σ 0)).left‖ 0 := by
      calc
        _ = ‖(g (σ 0)).left‖ • ThreeCorners.ray (g (σ 0)).lower := (g (σ 0)).left_eq
        _ = _ := by
          rw [h00, ray_zero_eq_direction]
          apply point_ext <;> simp [directionZero, point]
    refine ⟨‖(g (σ 0)).left‖, norm_pos_iff.mpr (g (σ 0)).left_ne_zero, ?_⟩
    rw [← hl]
    have hf := (g (σ 0)).left_segment (right_mem_segment ℝ 0 (g (σ 0)).left)
    have hp := frontier_subset_closure hf
    rwa [(T.jordan (σ 0)).isClosed.closure_eq] at hp

/-- The derived placements imply the global thirty-degree support bound.
The sharper quadrilateral is obtained whenever the outer parity is equal. -/
theorem exists_ordered_cone (T : NormalizedTriple) :
    ∃ σ : Equiv.Perm (Fin 3),
      (T.region (σ 1) = rotateThirty '' T.region (σ 0) ∨
        T.region (σ 1) = reflectThirty '' T.region (σ 0)) ∧
      (T.region (σ 2) = rotateSixty '' T.region (σ 0) ∨
        T.region (σ 2) = ReflectionSeparation.diagonal '' T.region (σ 0)) ∧
      T.region (σ 0) ⊆ thirtyCone ∧
      (T.region (σ 2) = rotateSixty '' T.region (σ 0) →
        T.region (σ 0) ⊆ equalParityBound) := by
  obtain ⟨σ, hmiddle, hlast, t, ht, hpoint⟩ := T.exists_ordered_placements
  have hquadrilateral (h : T.region (σ 2) = rotateSixty '' T.region (σ 0)) :
      T.region (σ 0) ⊆ equalParityBound := by
    apply subset_equalParityBound_of_square_fits (T.square_fit (σ 0))
    rw [← h]
    exact T.square_fit (σ 2)
  refine ⟨σ, hmiddle, hlast, ?_, hquadrilateral⟩
  rcases hlast with hlast | hlast
  · exact (hquadrilateral hlast).trans equalParityBound_subset_thirtyCone
  · apply subset_thirtyCone_of_opposite_outer_parity (T.jordan (σ 0))
      (T.square_fit (σ 0)) hmiddle
    · exact T.disjoint (fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h))
    · rw [← hlast]
      exact T.disjoint (fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h))
    · exact hpoint
    · simpa only [point_zero, point_one, mul_zero] using ht

end NormalizedTriple

/-- The actual normalized image of one dissection piece at a chosen corner. -/
def cornerPiece (d : SquareDissection) (s i : Fin 4) : Set Plane :=
  SquareSymmetry.cornerFlip s '' d.piece i

/-- The explicit two-parity alternatives and global cone, derived from
three actual owners of one intrinsic square corner. -/
theorem exists_actual_ordered_cone (d : SquareDissection) (s : Fin 4) (a : Plane)
    (hthree : d.cornerTileCount s = 3)
    (htype : ∀ i, corner s ∈ d.piece i → d.intrinsicCorner i s = a) :
    ∃ f : Fin 3 → Fin 4, Function.Injective f ∧
      (∀ i, corner s ∈ d.piece i ↔ ∃ k, f k = i) ∧
      (cornerPiece d s (f 1) = rotateThirty '' cornerPiece d s (f 0) ∨
        cornerPiece d s (f 1) = reflectThirty '' cornerPiece d s (f 0)) ∧
      (cornerPiece d s (f 2) = rotateSixty '' cornerPiece d s (f 0) ∨
        cornerPiece d s (f 2) = ReflectionSeparation.diagonal '' cornerPiece d s (f 0)) ∧
      cornerPiece d s (f 0) ⊆ thirtyCone ∧
      (cornerPiece d s (f 2) = rotateSixty '' cornerPiece d s (f 0) →
        cornerPiece d s (f 0) ⊆ equalParityBound) := by
  obtain ⟨T, f, hf, howners, hregions⟩ := exists_normalized_triple d s a hthree htype
  obtain ⟨σ, hm, hl, hcone, hbound⟩ := T.exists_ordered_cone
  refine ⟨f ∘ σ, hf.comp σ.injective, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [howners]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨σ.symm u, by simpa only [Function.comp_def, σ.apply_symm_apply] using hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨σ u, hu⟩
  · simpa only [hregions, cornerPiece, Function.comp_def] using hm
  · simpa only [hregions, cornerPiece, Function.comp_def] using hl
  · simpa only [hregions, cornerPiece, Function.comp_def] using hcone
  · simpa only [hregions, cornerPiece, Function.comp_def] using hbound

/-- In particular the intrinsic point shared at the triple corner is a
genuine global supporting corner of at most forty-five degrees. -/
theorem supports45_of_three_equal_intrinsic (d : SquareDissection)
    (s : Fin 4) (a : Plane) (hthree : d.cornerTileCount s = 3)
    (htype : ∀ i, corner s ∈ d.piece i → d.intrinsicCorner i s = a) :
    AcuteCorner.Supports45 (d.piece 0) a := by
  obtain ⟨f, _, howners, _, _, hcone, _⟩ := exists_actual_ordered_cone d s a hthree htype
  refine ⟨(d.placement (f 0)).trans (SquareSymmetry.cornerFlip s), ?_, ?_⟩
  · have hmember : corner s ∈ d.piece (f 0) := (howners (f 0)).mpr ⟨0, rfl⟩
    have ha := htype (f 0) hmember
    change SquareSymmetry.cornerFlip s (d.placement (f 0) a) = 0
    rw [← ha, d.placement_intrinsicCorner, SquareSymmetry.cornerFlip_corner]
  · have heq : (d.placement (f 0)).trans (SquareSymmetry.cornerFlip s) '' d.piece 0 =
        cornerPiece d s (f 0) := by
      change (fun p => SquareSymmetry.cornerFlip s (d.placement (f 0) p)) '' d.piece 0 = _
      rw [← image_image, d.placement_image]
      rfl
    rw [heq]
    exact hcone.trans thirtyCone_subset_cone45

end

end Puzzling139335.N6.TripleSectors
