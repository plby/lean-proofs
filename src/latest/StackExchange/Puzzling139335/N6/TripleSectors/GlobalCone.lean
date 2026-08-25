import StackExchange.Puzzling139335.N6.TripleSectors.Maps
import StackExchange.Puzzling139335.ReflectionSeparation.Generic
import StackExchange.Puzzling139335.JordanTransport

/-!
# Global support bounds from the actual normalized placements

For equal outer parity, the square fits of the first and last copies give
a bounded quadrilateral.  For opposite parity, reflection separation of
connected Jordan interiors gives a thirty-degree cone.  A strict source
point selects the correct side of the reflection line.
-/

open Set

namespace Puzzling139335.N6.TripleSectors

noncomputable section

/-- The normalized global thirty-degree cone, truncated at the right side. -/
def thirtyCone : Set Plane :=
  {p | 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧ p 0 ≤ 1}

/-- The sharper bound when the two outer placements have equal parity. -/
def equalParityBound : Set Plane :=
  {p | 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧ p 0 ≤ 1 ∧
    Real.sqrt 3 * p 0 + p 1 ≤ 2}

theorem equalParityBound_subset_thirtyCone : equalParityBound ⊆ thirtyCone :=
  fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩

theorem mem_equalParityBound_of_square_fits {p : Plane}
    (hp : p ∈ unitSquare) (hr : rotateSixty p ∈ unitSquare) :
    p ∈ equalParityBound := by
  have hx := hr.1.1
  have hy := hr.2.2
  simp only [rotateSixty_zero] at hx
  simp only [rotateSixty_one] at hy
  exact ⟨hp.2.1, by linarith only [hx], hp.1.2, by linarith only [hy]⟩

theorem subset_equalParityBound_of_square_fits {P : Set Plane}
    (hP : P ⊆ unitSquare) (hR : rotateSixty '' P ⊆ unitSquare) :
    P ⊆ equalParityBound :=
  fun p hp => mem_equalParityBound_of_square_fits (hP hp) (hR (mem_image_of_mem _ hp))

theorem convex_thirtyCone : Convex ℝ thirtyCone := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p 1 + b * q 1 ∧
    Real.sqrt 3 * (a * p 1 + b * q 1) ≤ a * p 0 + b * q 0 ∧
    a * p 0 + b * q 0 ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hp.2.1 ha,
      mul_le_mul_of_nonneg_left hq.2.1 hb]
  · nlinarith only [mul_le_mul_of_nonneg_left hp.2.2 ha,
      mul_le_mul_of_nonneg_left hq.2.2 hb, hab]

theorem convex_equalParityBound : Convex ℝ equalParityBound := by
  intro p hp q hq a b ha hb hab
  have ht := convex_thirtyCone (equalParityBound_subset_thirtyCone hp)
    (equalParityBound_subset_thirtyCone hq) ha hb hab
  refine ⟨ht.1, ht.2.1, ht.2.2, ?_⟩
  change Real.sqrt 3 * (a * p 0 + b * q 0) + (a * p 1 + b * q 1) ≤ 2
  nlinarith only [mul_le_mul_of_nonneg_left hp.2.2.2 ha,
    mul_le_mul_of_nonneg_left hq.2.2.2 hb, hab]

theorem convexHull_subset_equalParityBound_of_square_fits {P : Set Plane}
    (hP : P ⊆ unitSquare) (hR : rotateSixty '' P ⊆ unitSquare) :
    convexHull ℝ P ⊆ equalParityBound :=
  convexHull_min (subset_equalParityBound_of_square_fits hP hR) convex_equalParityBound

theorem reflectFifteen_involutive (p : Plane) : reflectFifteen (reflectFifteen p) = p := by
  apply point_ext
  · simp only [reflectFifteen_zero, reflectFifteen_one]
    ring_nf
    rw [sqrt_three_sq]
    ring
  · simp only [reflectFifteen_zero, reflectFifteen_one]
    ring_nf
    rw [sqrt_three_sq]
    ring

theorem reflectFifteen_cone_difference (p : Plane) :
    Real.sqrt 3 * reflectFifteen p 1 - reflectFifteen p 0 = -2 * p 1 := by
  simp only [reflectFifteen_zero, reflectFifteen_one]
  ring_nf
  rw [sqrt_three_sq]
  ring

theorem reflectFifteen_upper_sum (p : Plane) :
    Real.sqrt 3 * reflectFifteen p 0 + reflectFifteen p 1 = 2 * p 0 := by
  simp only [reflectFifteen_zero, reflectFifteen_one]
  ring_nf
  rw [sqrt_three_sq]
  ring

theorem reflectFifteen_mem_equalParityBound {p : Plane}
    (hp : p ∈ equalParityBound) : reflectFifteen p ∈ equalParityBound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [reflectFifteen_one]
    linarith only [hp.2.1]
  · linarith only [reflectFifteen_cone_difference p, hp.1]
  · simp only [reflectFifteen_zero]
    linarith only [hp.2.2.2]
  · rw [reflectFifteen_upper_sum]
    linarith only [hp.2.2.1]

theorem reflectFifteen_image_equalParityBound :
    reflectFifteen '' equalParityBound = equalParityBound := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact reflectFifteen_mem_equalParityBound hp
  · intro p hp
    exact ⟨reflectFifteen p, reflectFifteen_mem_equalParityBound hp,
      reflectFifteen_involutive p⟩

theorem reflectThirty_image_equalParityBound :
    reflectThirty '' equalParityBound = rotateThirty '' equalParityBound := by
  calc
    _ = (rotateThirty ∘ reflectFifteen) '' equalParityBound := by
      congr 1
      funext p
      exact (rotateThirty_reflectFifteen p).symm
    _ = rotateThirty '' (reflectFifteen '' equalParityBound) := by
      simpa only [Function.comp_def] using
        (image_image (fun p : Plane => rotateThirty p)
          (fun p : Plane => reflectFifteen p) equalParityBound).symm
    _ = _ := by rw [reflectFifteen_image_equalParityBound]

theorem middle_subset_rotated_bound {P M : Set Plane}
    (hP : P ⊆ equalParityBound)
    (hM : M = rotateThirty '' P ∨ M = reflectThirty '' P) :
    M ⊆ rotateThirty '' equalParityBound := by
  rcases hM with rfl | rfl
  · exact image_mono hP
  · rw [← reflectThirty_image_equalParityBound]
    exact image_mono hP

theorem thirtyCone_first_nonneg {p : Plane} (hp : p ∈ thirtyCone) : 0 ≤ p 0 :=
  (mul_nonneg sqrt_three_pos.le hp.1).trans hp.2.1

theorem equalParityBound_second_le_half {p : Plane}
    (hp : p ∈ equalParityBound) : p 1 ≤ 1 / 2 := by
  have h := mul_le_mul_of_nonneg_left hp.2.1 sqrt_three_pos.le
  have hs : Real.sqrt 3 * (Real.sqrt 3 * p 1) = 3 * p 1 := by
    calc
      _ = Real.sqrt 3 ^ 2 * p 1 := by ring
      _ = _ := by rw [sqrt_three_sq]
  rw [hs] at h
  linarith only [h, hp.2.2.2]

theorem rotateThirty_first_lt_one {p : Plane} (hp : p ∈ thirtyCone) :
    rotateThirty p 0 < 1 := by
  simp only [rotateThirty_zero]
  nlinarith only [mul_le_mul_of_nonneg_left hp.2.2 sqrt_three_pos.le,
    hp.1, sqrt_three_lt_two]

theorem rotateThirty_second_lt_one {p : Plane} (hp : p ∈ equalParityBound) :
    rotateThirty p 1 < 1 := by
  simp only [rotateThirty_one]
  nlinarith only [hp.2.2.1, sqrt_three_lt_two,
    mul_le_mul_of_nonneg_left (equalParityBound_second_le_half hp) sqrt_three_pos.le]

theorem equalParityBound_right_height {p : Plane} (hp : p ∈ equalParityBound)
    (hx : p 0 = 1) : p 1 ≤ 2 - Real.sqrt 3 := by
  have h := hp.2.2.2
  rw [hx] at h
  linarith only [h]

theorem rotateSixty_first_lt_one {p : Plane} (hp : p ∈ equalParityBound) :
    rotateSixty p 0 < 1 := by
  simp only [rotateSixty_zero]
  nlinarith only [hp.2.2.1, mul_nonneg sqrt_three_pos.le hp.1]

theorem rotateSixty_top_coordinate {p : Plane} (hp : p ∈ equalParityBound)
    (hy : rotateSixty p 1 = 1) : rotateSixty p 0 ≤ 2 - Real.sqrt 3 := by
  have hsum : Real.sqrt 3 * p 0 + p 1 = 2 := by
    simp only [rotateSixty_one] at hy
    linarith only [hy]
  have heq : rotateSixty p 0 = 2 * p 0 - Real.sqrt 3 := by
    simp only [rotateSixty_zero]
    have hm := congrArg (fun t : ℝ => Real.sqrt 3 * t) hsum
    ring_nf at hm
    rw [sqrt_three_sq] at hm
    linarith only [hm]
  rw [heq]
  linarith only [hp.2.2.1]

private theorem continuous_first : Continuous (fun p : Plane => p 0) := by
  fun_prop

private theorem continuous_second : Continuous (fun p : Plane => p 1) := by
  fun_prop

/-- With a reversed middle placement, the prototype itself is separated
from its reflection about the thirty-degree line. -/
theorem subset_thirtyCone_of_reflected_middle {P : Set Plane}
    (hP : IsJordanRegion P) (hfit : P ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior (reflectThirty '' P)))
    {x : Plane} (hx : x ∈ P) (hside : Real.sqrt 3 * x 1 < x 0) :
    P ⊆ thirtyCone := by
  have hle := ReflectionSeparation.subset_le_of_fixed_level_of_mem_lt hP
    reflectThirty rfl hdis (fun p : Plane => Real.sqrt 3 * p 1 - p 0)
    ((continuous_const.mul continuous_second).sub continuous_first) 0
    (fun p hp => reflectThirty_fixed (by linarith only [hp])) hx
    (by linarith only [hside])
  intro p hp
  have hpbound : Real.sqrt 3 * p 1 - p 0 ≤ 0 := hle hp
  exact ⟨(hfit hp).2.1, by linarith only [hpbound], (hfit hp).1.2⟩

theorem mirrorSixtyLevel_rotateThirty (p : Plane) :
    rotateThirty p 1 - Real.sqrt 3 * rotateThirty p 0 =
      Real.sqrt 3 * p 1 - p 0 := by
  simp only [rotateThirty_zero, rotateThirty_one]
  ring_nf
  rw [sqrt_three_sq]
  ring

/-- With a direct middle placement, the middle and last copies are mirror
images about the sixty-degree line. Pulling the separated side back gives
the same global thirty-degree support bound. -/
theorem subset_thirtyCone_of_direct_middle {P : Set Plane}
    (hP : IsJordanRegion P) (hfit : P ⊆ unitSquare)
    (hdis : Disjoint (interior (rotateThirty '' P))
      (interior (ReflectionSeparation.diagonal '' P)))
    {x : Plane} (hx : x ∈ P) (hside : Real.sqrt 3 * x 1 < x 0) :
    P ⊆ thirtyCone := by
  have hJ := hP.image_homeomorph rotateThirty.toHomeomorph
  have himage : reflectSixty '' (rotateThirty '' P) =
      ReflectionSeparation.diagonal '' P := by
    rw [image_image]
    simp only [Function.comp_def, reflectSixty_rotateThirty]
  have hle := ReflectionSeparation.subset_le_of_fixed_level_of_mem_lt hJ
    reflectSixty himage hdis (fun p : Plane => p 1 - Real.sqrt 3 * p 0)
    (continuous_second.sub (continuous_const.mul continuous_first)) 0
    (fun p hp => reflectSixty_fixed (by linarith only [hp]))
    (mem_image_of_mem rotateThirty hx)
    (by rw [mirrorSixtyLevel_rotateThirty]; linarith only [hside])
  intro p hp
  have hpbound := hle (mem_image_of_mem rotateThirty hp)
  change rotateThirty p 1 - Real.sqrt 3 * rotateThirty p 0 ≤ 0 at hpbound
  rw [mirrorSixtyLevel_rotateThirty] at hpbound
  exact ⟨(hfit hp).2.1, by linarith only [hpbound], (hfit hp).1.2⟩

/-- The opposite-parity outer configuration, allowing both middle parities. -/
theorem subset_thirtyCone_of_opposite_outer_parity {P M : Set Plane}
    (hP : IsJordanRegion P) (hfit : P ⊆ unitSquare)
    (hM : M = rotateThirty '' P ∨ M = reflectThirty '' P)
    (hfirst : Disjoint (interior P) (interior M))
    (hlast : Disjoint (interior M) (interior (ReflectionSeparation.diagonal '' P)))
    {x : Plane} (hx : x ∈ P) (hside : Real.sqrt 3 * x 1 < x 0) :
    P ⊆ thirtyCone := by
  rcases hM with rfl | rfl
  · exact subset_thirtyCone_of_direct_middle hP hfit hlast hx hside
  · exact subset_thirtyCone_of_reflected_middle hP hfit hfirst hx hside

end

end Puzzling139335.N6.TripleSectors
