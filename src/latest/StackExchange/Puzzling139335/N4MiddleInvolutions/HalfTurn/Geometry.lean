import StackExchange.Puzzling139335.N4MiddleInvolutions.Remainder
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Axes

/-!
# Geometry forced by an actual half-turn middle pair

The half-turn center lies on the horizontal midline and in the actual
common cut. If it lies to one side of the square center, the opposite
outer side is owned by the lower piece up to the midline. All four
coordinate displacement bounds follow from the actual square containment.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

open FaceBounds

variable {d : SquareDissection}

theorem middleUnion_central {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    AffineIsometryEquiv.pointReflection ℝ C '' middleUnion d = middleUnion d :=
  middleUnion_image_of_involution (AffineIsometryEquiv.pointReflection ℝ C)
    (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) C) hpair

theorem center_y_eq_half (h : N4OuterPair.Configuration d) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    C 1 = (1 / 2 : ℝ) := by
  have hfix := center_fixed_of_invariant_central_set (middleUnion_isCompact d)
    (middleUnion_nonempty d) (middleUnion_central hpair)
    ReflectionSeparation.horizontal h.middle_union_reflected
  have hy := congrArg (fun p : Plane => p 1) hfix
  simp only [ReflectionSeparation.horizontal_apply_one] at hy
  linarith

theorem center_x_ne_half (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    C 0 ≠ (1 / 2 : ℝ) := by
  intro hx
  have hy := center_y_eq_half h hpair
  have hC : C = squareCenter := by
    ext i
    fin_cases i <;> simp [squareCenter, hx, hy]
  apply center_not_fixed_of_middle_pair h hc
    (AffineIsometryEquiv.pointReflection ℝ C) hpair
  rw [hC]
  exact AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) squareCenter

theorem center_mem_common (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    C ∈ d.piece 2 ∩ d.piece 3 := by
  have hJ := middleUnion_jordan_of_involution h hc
    (AffineIsometryEquiv.pointReflection ℝ C)
    (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) C) hpair
  have hC : C ∈ middleUnion d :=
    interior_subset (hJ.center_mem_interior_of_pointReflection (middleUnion_central hpair))
  have hback := image_back_of_involution (AffineIsometryEquiv.pointReflection ℝ C)
    (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) C) hpair
  rcases hC with hC | hC
  · refine ⟨hC, ?_⟩
    rw [← hpair]
    exact ⟨C, hC, AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) C⟩
  · refine ⟨?_, hC⟩
    rw [← hback]
    exact ⟨C, hC, AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) C⟩

theorem middleUnion_horizontal (h : N4OuterPair.Configuration d) :
    MapsTo (horizontalAbout (1 / 2)) (middleUnion d) (middleUnion d) := by
  intro p hp
  have hU : ReflectionSeparation.horizontal '' middleUnion d = middleUnion d :=
    h.middle_union_reflected
  have hmem : ReflectionSeparation.horizontal p ∈ middleUnion d :=
    hU ▸ mem_image_of_mem ReflectionSeparation.horizontal hp
  have heq : horizontalAbout (1 / 2) p = ReflectionSeparation.horizontal p := by
    ext i
    fin_cases i <;> simp [horizontalAbout]
  exact heq.symm ▸ hmem

theorem middleUnion_vertical (h : N4OuterPair.Configuration d) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    MapsTo (verticalAbout (C 0)) (middleUnion d) (middleUnion d) := by
  have hy := center_y_eq_half h hpair
  intro p hp
  have hU : ReflectionSeparation.horizontal '' middleUnion d = middleUnion d :=
    h.middle_union_reflected
  have hh : ReflectionSeparation.horizontal p ∈ middleUnion d :=
    hU ▸ mem_image_of_mem ReflectionSeparation.horizontal hp
  have hg : AffineIsometryEquiv.pointReflection ℝ C
      (ReflectionSeparation.horizontal p) ∈ middleUnion d :=
    middleUnion_central hpair ▸ mem_image_of_mem _ hh
  have heq : verticalAbout (C 0) p = AffineIsometryEquiv.pointReflection ℝ C
      (ReflectionSeparation.horizontal p) := by
    ext i
    fin_cases i <;> simp [verticalAbout, pointReflection_coord, hy]
  exact heq.symm ▸ hg

theorem middleUnion_horizontal_displacement_lt_half
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter) {C p : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (hp : p ∈ middleUnion d) : |p 0 - C 0| < (1 / 2 : ℝ) := by
  have hx := (middleUnion_subset_square d hp).1
  have hgp : AffineIsometryEquiv.pointReflection ℝ C p ∈ middleUnion d :=
    middleUnion_central hpair ▸ mem_image_of_mem _ hp
  have hgx := (middleUnion_subset_square d hgp).1
  rw [pointReflection_coord] at hgx
  have hne := center_x_ne_half h hc hpair
  rcases lt_or_gt_of_ne hne with hleft | hright <;>
    rw [abs_lt] <;> constructor <;> linarith [hx.1, hx.2, hgx.1, hgx.2]

theorem middleUnion_vertical_displacement_lt_half
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter) {C p : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (hp : p ∈ middleUnion d) : |p 1 - C 1| < (1 / 2 : ℝ) := by
  have hy := center_y_eq_half h hpair
  have hpheight : 0 < p 1 ∧ p 1 < 1 := by
    rcases hp with hp | hp
    · exact h.middle_strict_height hc (Or.inl rfl) hp
    · exact h.middle_strict_height hc (Or.inr rfl) hp
  rw [hy, abs_lt]
  constructor <;> linarith

/-- Missing an entire vertical line forces the lower outer piece to own
the half-side on that line, including the endpoint on the midline. -/
theorem half_side_mem_of_middle_avoids_line (h : N4OuterPair.Configuration d)
    {x : ℝ} (hx : x = 0 ∨ x = 1)
    (hgap : ∀ p ∈ middleUnion d, p 0 ≠ x) :
    ∀ y ∈ Icc (0 : ℝ) (1 / 2), Schoenflies.Plane.mk x y ∈ d.piece 0 := by
  let E : Set ℝ := {y | Schoenflies.Plane.mk x y ∈ d.piece 0}
  have hE : IsClosed E := (d.jordan 0).isClosed.preimage (by fun_prop)
  have hsub : Ico (0 : ℝ) (1 / 2) ⊆ E := by
    intro y hy
    have hpS : Schoenflies.Plane.mk x y ∈ unitSquare := by
      refine ⟨?_, hy.1, ?_⟩
      · rcases hx with rfl | rfl <;> norm_num
      · change y ≤ 1
        linarith [hy.2]
    obtain ⟨i, hi⟩ := d.exists_piece_mem hpS
    fin_cases i
    · exact hi
    · have hbound := (h.outer_halves.2 hi).2.1
      exact False.elim ((not_le_of_gt hy.2) hbound)
    · exact False.elim (hgap _ (Or.inl hi) rfl)
    · exact False.elim (hgap _ (Or.inr hi) rfl)
  have hfull := closure_minimal hsub hE
  rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1 / 2)] at hfull
  exact fun y hy => hfull hy

theorem half_arm_of_middle_avoids_line (h : N4OuterPair.Configuration d)
    {x : ℝ} (hx : x = 0 ∨ x = 1)
    (hgap : ∀ p ∈ middleUnion d, p 0 ≠ x) :
    segment ℝ (Schoenflies.Plane.mk x 0) (Schoenflies.Plane.mk x (1 / 2)) ⊆
      d.piece 0 := by
  intro p hp
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hp
  have heq : p = Schoenflies.Plane.mk x (p 1) := by
    ext i
    fin_cases i
    · exact hp.1
    · rfl
  rw [heq]
  exact half_side_mem_of_middle_avoids_line h hx hgap (p 1) hp.2

theorem left_arm_of_right_center (h : N4OuterPair.Configuration d) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (hcx : (1 / 2 : ℝ) < C 0) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) ⊆
      d.piece 0 := by
  apply half_arm_of_middle_avoids_line h (Or.inl rfl)
  intro p hp hx
  have hgp : AffineIsometryEquiv.pointReflection ℝ C p ∈ middleUnion d :=
    middleUnion_central hpair ▸ mem_image_of_mem _ hp
  have hb := (middleUnion_subset_square d hgp).1.2
  rw [pointReflection_coord, hx] at hb
  linarith

theorem right_arm_of_left_center (h : N4OuterPair.Configuration d) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (hcx : C 0 < (1 / 2 : ℝ)) :
    segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 (1 / 2)) ⊆
      d.piece 0 := by
  apply half_arm_of_middle_avoids_line h (Or.inr rfl)
  intro p hp hx
  have hgp : AffineIsometryEquiv.pointReflection ℝ C p ∈ middleUnion d :=
    middleUnion_central hpair ▸ mem_image_of_mem _ hp
  have hb := (middleUnion_subset_square d hgp).1.1
  rw [pointReflection_coord, hx] at hb
  linarith

end Puzzling139335.N4MiddleInvolutions.HalfTurn
