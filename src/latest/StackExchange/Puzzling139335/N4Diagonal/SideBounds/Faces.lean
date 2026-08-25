import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Exact source points on the sides of diagonal-corner placements

These identities concern the placement maps themselves. They require no
regularity or support assumptions on the source set and no bounds on the
side parameter.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

private theorem eq_of_frame_inner_eq (p : Plane) (θ : ℝ) {x y : Plane}
    (hr : inner ℝ (ray θ) (x - p) = inner ℝ (ray θ) (y - p))
    (hp : inner ℝ (perpRay θ) (x - p) = inner ℝ (perpRay θ) (y - p)) :
    x = y := by
  have hx := (rayBasis θ).sum_repr' (x - p)
  have hy := (rayBasis θ).sum_repr' (y - p)
  simp only [Fin.sum_univ_two, rayBasis_zero, rayBasis_one] at hx hy
  rw [hr, hp] at hx
  exact sub_left_inj.mp (hx.symm.trans hy)

private theorem firstPlus_injective (j : Fin 4) (p : Plane) (θ : ℝ) :
    Function.Injective (firstPlus j p θ) := by
  intro x y h
  have hxy := (SquareSymmetry.cornerFlip j).injective h
  apply eq_of_frame_inner_eq p θ
  · exact neg_injective (congrArg (fun z : Plane => z 0) hxy)
  · exact congrArg (fun z : Plane => z 1) hxy

private theorem lastPlus_injective (j : Fin 4) (q : Plane) (β : ℝ) :
    Function.Injective (lastPlus j q β) := by
  intro x y h
  have hxy := (SquareSymmetry.cornerFlip j).injective h
  apply eq_of_frame_inner_eq q β
  · exact neg_injective (congrArg (fun z : Plane => z 1) hxy)
  · exact neg_injective (congrArg (fun z : Plane => z 0) hxy)

private theorem lastMinus_injective (j : Fin 4) (q : Plane) (β : ℝ) :
    Function.Injective (lastMinus j q β) := by
  intro x y h
  exact lastPlus_injective j q β (ReflectionSeparation.antiDiagonal.injective h)

private theorem mem_image_iff_of_value (P : Set Plane) (f : Plane → Plane)
    (hf : Function.Injective f) {x y : Plane} (hxy : f x = y) :
    y ∈ f '' P ↔ x ∈ P := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact (hf (hzy.trans hxy.symm)) ▸ hz
  · intro hx
    exact ⟨x, hx, hxy⟩

private theorem ray_inner_self (θ : ℝ) : inner ℝ (ray θ) (ray θ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_ray]
  norm_num

private theorem perpRay_inner_self (θ : ℝ) :
    inner ℝ (perpRay θ) (perpRay θ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_perpRay]
  norm_num

private theorem perpRay_inner_ray (θ : ℝ) : inner ℝ (perpRay θ) (ray θ) = 0 := by
  rw [real_inner_comm]
  exact ray_inner_perpRay θ

@[simp] private theorem ray_inner_sub_ray (p : Plane) (θ t : ℝ) :
    inner ℝ (ray θ) (p - t • ray θ - p) = -t := by
  have hsub : p - t • ray θ - p = -(t • ray θ) := by abel
  simp only [hsub, inner_neg_right, inner_smul_right, ray_inner_self, mul_one]

@[simp] private theorem perpRay_inner_sub_ray (p : Plane) (θ t : ℝ) :
    inner ℝ (perpRay θ) (p - t • ray θ - p) = 0 := by
  have hsub : p - t • ray θ - p = -(t • ray θ) := by abel
  simp only [hsub, inner_neg_right, inner_smul_right, perpRay_inner_ray, mul_zero,
    neg_zero]

@[simp] private theorem ray_inner_add_perpRay (p : Plane) (θ t : ℝ) :
    inner ℝ (ray θ) (p + t • perpRay θ - p) = 0 := by
  have hsub : p + t • perpRay θ - p = t • perpRay θ := by abel
  simp only [hsub, inner_smul_right, ray_inner_perpRay, mul_zero]

@[simp] private theorem perpRay_inner_add_perpRay (p : Plane) (θ t : ℝ) :
    inner ℝ (perpRay θ) (p + t • perpRay θ - p) = t := by
  have hsub : p + t • perpRay θ - p = t • perpRay θ := by abel
  simp only [hsub, inner_smul_right, perpRay_inner_self, mul_one]

theorem mem_firstPlus_three_top_iff (P : Set Plane) (p : Plane) (θ t : ℝ) :
    (!₂[t, 1] : Plane) ∈ firstPlus 3 p θ '' P ↔ p - t • ray θ ∈ P := by
  apply mem_image_iff_of_value P _ (firstPlus_injective 3 p θ)
  ext i
  fin_cases i <;>
    norm_num [firstPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_firstPlus_one_bottom_iff (P : Set Plane) (p : Plane) (θ t : ℝ) :
    (!₂[1 - t, 0] : Plane) ∈ firstPlus 1 p θ '' P ↔ p - t • ray θ ∈ P := by
  apply mem_image_iff_of_value P _ (firstPlus_injective 1 p θ)
  ext i
  fin_cases i <;>
    norm_num [firstPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_lastPlus_one_right_iff (P : Set Plane) (q : Plane) (β t : ℝ) :
    (!₂[1, t] : Plane) ∈ lastPlus 1 q β '' P ↔ q - t • ray β ∈ P := by
  apply mem_image_iff_of_value P _ (lastPlus_injective 1 q β)
  ext i
  fin_cases i <;>
    norm_num [lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_lastMinus_one_bottom_iff (P : Set Plane) (q : Plane) (β t : ℝ) :
    (!₂[1 - t, 0] : Plane) ∈ lastMinus 1 q β '' P ↔ q - t • ray β ∈ P := by
  apply mem_image_iff_of_value P _ (lastMinus_injective 1 q β)
  ext i
  fin_cases i <;>
    norm_num [lastMinus, lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_lastPlus_three_left_iff (P : Set Plane) (q : Plane) (β t : ℝ) :
    (!₂[0, 1 - t] : Plane) ∈ lastPlus 3 q β '' P ↔ q - t • ray β ∈ P := by
  apply mem_image_iff_of_value P _ (lastPlus_injective 3 q β)
  ext i
  fin_cases i <;>
    norm_num [lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_lastMinus_three_top_iff (P : Set Plane) (q : Plane) (β t : ℝ) :
    (!₂[t, 1] : Plane) ∈ lastMinus 3 q β '' P ↔ q - t • ray β ∈ P := by
  apply mem_image_iff_of_value P _ (lastMinus_injective 3 q β)
  ext i
  fin_cases i <;>
    norm_num [lastMinus, lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_self, perpRay_inner_ray, norm_ray]

theorem mem_firstPlus_three_left_iff (P : Set Plane) (p : Plane) (θ t : ℝ) :
    (!₂[0, 1 - t] : Plane) ∈ firstPlus 3 p θ '' P ↔ p + t • perpRay θ ∈ P := by
  apply mem_image_iff_of_value P _ (firstPlus_injective 3 p θ)
  ext i
  fin_cases i <;>
    norm_num [firstPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff,
      inner_smul_right, ray_inner_perpRay, perpRay_inner_self, norm_perpRay]

end Puzzling139335.N4Diagonal
