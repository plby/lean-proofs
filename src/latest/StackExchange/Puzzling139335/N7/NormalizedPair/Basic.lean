import StackExchange.Puzzling139335.N7.NormalizedPair.Defs
import StackExchange.Puzzling139335.CornerMass.Placements
import StackExchange.Puzzling139335.CornerCounting

/-!
# The singleton has the common type at the top-right corner

The diagonal gap forces its physical corner. The positive local weighted
areas of the actual pieces then determine its intrinsic type. No angular
measure or straightness assumption is used.
-/

open Set

namespace Puzzling139335.N7.NormalizedPair

open ReflectionSeparation

noncomputable section

variable {d : SquareDissection}

theorem lower_half (C : NormalizedPair d) :
    ∀ p ∈ d.piece 0, p 1 ≤ (1 / 2 : ℝ) :=
  horizontal_below_of_bottom_left (d.jordan 0) C.reflected
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)) C.bottom_left

theorem upper_half (C : NormalizedPair d) :
    ∀ p ∈ d.piece 1, (1 / 2 : ℝ) ≤ p 1 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := (Set.ext_iff.mp C.reflected p).mpr hp
  have hqhalf := C.lower_half q hq
  simp only [horizontal_apply_one]
  linarith only [hqhalf]

theorem b_square (C : NormalizedPair d) : C.b ∈ unitSquare := d.piece_subset 0 C.b_mem

theorem b_half (C : NormalizedPair d) : C.b 1 ≤ (1 / 2 : ℝ) :=
  C.lower_half C.b C.b_mem

theorem third_zero_square (C : NormalizedPair d) : C.third (corner 0) ∈ unitSquare := by
  apply d.piece_subset 2
  rw [← C.third_image]
  exact mem_image_of_mem C.third C.bottom_left

theorem third_fit (C : NormalizedPair d) : C.third '' d.piece 0 ⊆ unitSquare := by
  rw [C.third_image]
  exact d.piece_subset 2

theorem topRight_not_bottom (C : NormalizedPair d) : corner 2 ∉ d.piece 0 := by
  intro h
  have hhalf := C.lower_half (corner 2) h
  norm_num [corner, Fin.ext_iff] at hhalf

theorem bottomRight_not_top (C : NormalizedPair d) : corner 1 ∉ d.piece 1 := by
  intro h
  have hhalf := C.upper_half (corner 1) h
  norm_num [corner, Fin.ext_iff] at hhalf

theorem topRight_mem_top (C : NormalizedPair d) : corner 2 ∈ d.piece 1 := by
  rw [← C.reflected]
  refine ⟨corner 1, C.bottom_right, ?_⟩
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

theorem topRight_mem_third (C : NormalizedPair d) : corner 2 ∈ d.piece 2 := by
  rw [← C.third_image]
  exact ⟨corner 1, C.bottom_right, C.third_a⟩

theorem bottomRight_mem_third (C : NormalizedPair d) : corner 1 ∈ d.piece 2 := by
  rw [← C.third_image]
  exact ⟨C.b, C.b_mem, C.third_b⟩

/-- The singleton must occur at the top-right corner, because the other
two known copies leave a gap in every neighborhood of that corner. -/
theorem topRight_mem_singleton (C : NormalizedPair d) : corner 2 ∈ d.piece 3 := by
  obtain ⟨i, hi1, hi2, hi⟩ := topRight_has_other_owner d C.third C.reflected C.third_image
    C.b_square C.b_half C.b_ne_zero C.third_a C.third_b C.third_zero_square
  fin_cases i
  · exact (C.topRight_not_bottom hi).elim
  · exact (hi1 rfl).elim
  · exact (hi2 rfl).elim
  · exact hi

theorem singleton_corner_eq (C : NormalizedPair d) {j : Fin 4}
    (hj : corner j ∈ d.piece 3) : j = 2 := by
  classical
  have hcard := C.singleton_count
  change (Finset.univ.filter fun a => corner a ∈ d.piece 3).card = 1 at hcard
  exact Finset.card_le_one_iff.mp hcard.le
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact C.topRight_mem_singleton)

theorem bottomRight_not_singleton (C : NormalizedPair d) : corner 1 ∉ d.piece 3 := by
  intro h
  have heq := C.singleton_corner_eq h
  exact (by decide : (1 : Fin 4) ≠ 2) heq

/-- The explicitly chosen actual placement family, keeping the intrinsic
labels fixed throughout normalization. -/
def placements (C : NormalizedPair d) : Fin 4 → Plane ≃ᵃⁱ[ℝ] Plane :=
  ![AffineIsometryEquiv.refl ℝ Plane, horizontal, C.third, C.single]

theorem placements_image (C : NormalizedPair d) (i : Fin 4) :
    C.placements i '' d.piece 0 = d.piece i := by
  fin_cases i
  · simp [placements]
  · exact C.reflected
  · exact C.third_image
  · exact C.singleton_image

private theorem sum_four_reals (f : Fin 4 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + 0))) = f 0 + f 1 + f 2 + f 3
  ring

/-- The singleton uses the common source corner, rather than the other
endpoint of the third pair. Otherwise two corner-mass equations differ
by one strictly positive common-type contribution. -/
theorem singleton_common_corner (C : NormalizedPair d) :
    C.single (corner 1) = corner 2 := by
  classical
  rcases C.singleton_type 2 C.topRight_mem_singleton with hcommon | hother
  · exact hcommon
  · obtain ⟨m, hm, hsum⟩ := d.exists_positive_corner_weights_of_placements
      (d.piece 0) (d.jordan 0) C.placements C.placements_image
    have hHpre : horizontal.symm (corner 2) = corner 1 := by
      apply horizontal.injective
      rw [horizontal.apply_symm_apply]
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]
    have hTpreA : C.third.symm (corner 2) = corner 1 := by
      rw [← C.third_a, C.third.symm_apply_apply]
    have hTpreB : C.third.symm (corner 1) = C.b := by
      rw [← C.third_b, C.third.symm_apply_apply]
    have hUpreB : C.single.symm (corner 2) = C.b := by
      rw [← hother, C.single.symm_apply_apply]
    have hIdpre : (AffineIsometryEquiv.refl ℝ Plane).symm (corner 1) = corner 1 := rfl
    have hidentity := hsum 1 2
    rw [sum_four_reals, sum_four_reals] at hidentity
    simp [C.bottom_right, C.bottomRight_not_top, C.bottomRight_mem_third,
      C.bottomRight_not_singleton, C.topRight_not_bottom, C.topRight_mem_top,
      C.topRight_mem_third, C.topRight_mem_singleton, placements,
      hIdpre, hHpre, hTpreA, hTpreB, hUpreB] at hidentity
    have hpositive := hm (corner 1) C.bottom_right
    exfalso
    linarith only [hidentity, hpositive]

end

end Puzzling139335.N7.NormalizedPair
