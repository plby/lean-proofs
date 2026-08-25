import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic

/-!
# Pulling a half-turn middle pair into intrinsic coordinates

The congruence transports the entire actual common set. If its center
lies on a source coordinate side, that common set lies in the actual
unit base or half-unit arm, respectively.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

theorem image_pointReflection_image (e : Plane ≃ᵃⁱ[ℝ] Plane) (q : Plane)
    (P : Set Plane) :
    e '' (AffineIsometryEquiv.pointReflection ℝ q '' P) =
      AffineIsometryEquiv.pointReflection ℝ (e q) '' (e '' P) := by
  rw [image_image, image_image]
  congr 1
  funext p
  exact map_pointReflection e q p

theorem image_source_halfTurn {d : SquareDissection} {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {q C : Plane}
    (he : e '' P = d.piece 2) (heq : e q = C)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    e '' (AffineIsometryEquiv.pointReflection ℝ q '' P) = d.piece 3 := by
  rw [image_pointReflection_image, heq, he, hpair]

theorem image_source_union {d : SquareDissection} {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {q C : Plane}
    (he : e '' P = d.piece 2) (heq : e q = C)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P) = middleUnion d := by
  rw [image_union, he, image_source_halfTurn e he heq hpair]
  rfl

theorem image_source_common {d : SquareDissection} {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {q C : Plane}
    (he : e '' P = d.piece 2) (heq : e q = C)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    e '' (P ∩ AffineIsometryEquiv.pointReflection ℝ q '' P) =
      d.piece 2 ∩ d.piece 3 := by
  rw [image_inter e.injective, he, image_source_halfTurn e he heq hpair]

theorem source_interiors_disjoint {d : SquareDissection} {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {q C : Plane}
    (he : e '' P = d.piece 2) (heq : e q = C)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    Disjoint (interior P) (interior (AffineIsometryEquiv.pointReflection ℝ q '' P)) := by
  apply (disjoint_image_iff e.injective).mp
  rw [← interior_image_affineIsometry, ← interior_image_affineIsometry,
    he, image_source_halfTurn e he heq hpair]
  exact d.disjoint_interiors (by decide)

theorem source_common_not_in_unit_segment {d : SquareDissection} {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {q C : Plane}
    (he : e '' P = d.piece 2) (heq : e q = C)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (hlarge : ∀ a b : Plane, dist a b ≤ 1 →
      ¬ (d.piece 2 ∩ d.piece 3 ⊆ segment ℝ a b)) :
    ∀ a b : Plane, dist a b ≤ 1 →
      ¬ (P ∩ AffineIsometryEquiv.pointReflection ℝ q '' P ⊆ segment ℝ a b) := by
  intro a b hab hsub
  apply hlarge (e a) (e b) (by simpa only [e.isometry.dist_eq] using hab)
  rw [← image_source_common e he heq hpair]
  have himage : e '' segment ℝ a b = segment ℝ (e a) (e b) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap a b
  rw [← himage]
  exact image_mono hsub

theorem common_subset_left_arm_of_first_coordinate_zero {P : Set Plane} {q : Plane}
    (hbox : P ⊆ horizontalBand 0 (1 / 2)) (hq : q 0 = 0) :
    P ∩ AffineIsometryEquiv.pointReflection ℝ q '' P ⊆
      segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) := by
  rintro p ⟨hp, z, hz, hzp⟩
  have hpbox := hbox hp
  have hzbox := hbox hz
  have hx := congrArg (fun w : Plane => w 0) hzp
  rw [pointReflection_coord, hq] at hx
  have hpzero : p 0 = 0 := by linarith [hpbox.1.1, hzbox.1.1]
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ⟨hpzero, hpbox.2⟩

theorem common_subset_base_of_second_coordinate_zero {P : Set Plane} {q : Plane}
    (hbox : P ⊆ horizontalBand 0 (1 / 2)) (hq : q 1 = 0) :
    P ∩ AffineIsometryEquiv.pointReflection ℝ q '' P ⊆
      segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) := by
  rintro p ⟨hp, z, hz, hzp⟩
  have hpbox := hbox hp
  have hzbox := hbox hz
  have hy := congrArg (fun w : Plane => w 1) hzp
  rw [pointReflection_coord, hq] at hy
  have hpzero : p 1 = 0 := by linarith [hpbox.2.1, hzbox.2.1]
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨hpzero, hpbox.1⟩

theorem source_coordinates_pos_of_large_common {P : Set Plane} {q : Plane}
    (hbox : P ⊆ horizontalBand 0 (1 / 2)) (hq : q ∈ P)
    (hlarge : ∀ a b : Plane, dist a b ≤ 1 →
      ¬ (P ∩ AffineIsometryEquiv.pointReflection ℝ q '' P ⊆ segment ℝ a b)) :
    0 < q 0 ∧ 0 < q 1 := by
  have hqbox := hbox hq
  constructor
  · by_contra hnot
    have hzero : q 0 = 0 := le_antisymm (not_lt.mp hnot) hqbox.1.1
    apply hlarge (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2))
      _ (common_subset_left_arm_of_first_coordinate_zero hbox hzero)
    have hdist : dist (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) ^ 2 =
        (1 / 4 : ℝ) := by norm_num [plane_dist_sq, Schoenflies.Plane.mk]
    nlinarith
  · by_contra hnot
    have hzero : q 1 = 0 := le_antisymm (not_lt.mp hnot) hqbox.2.1
    apply hlarge (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)
      _ (common_subset_base_of_second_coordinate_zero hbox hzero)
    have hdist : dist (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ^ 2 =
        (1 : ℝ) := by norm_num [plane_dist_sq, Schoenflies.Plane.mk]
    nlinarith

end Puzzling139335.N4MiddleInvolutions.HalfTurn
