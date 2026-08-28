import Wikipedia.NoExoticSixSphere.SphereCylinderCaps
import Wikipedia.NoExoticSixSphere.NormalizedConeContraction

/-!
# Contractibility of the actual endpoint caps

Both caps are sphere sections of explicit convex cones avoiding zero. Their
contractions are the normalized straight segments to their genuine poles.
-/

noncomputable section

open Set Function Metric Topology

namespace NoExoticSixSphere.SphereCylinder

def lowerCone (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 2))) := {x | x 0 < 0}

def upperCone (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 2))) := {x | ‖tail n x‖ < x 0}

theorem convex_lowerCone (n : ℕ) : Convex ℝ (lowerCone n) := by
  intro x hx y hy a b ha hb hab
  change a * x 0 + b * y 0 < 0
  by_cases hzero : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [hzero, hb1, lowerCone] using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hx' := mul_neg_of_pos_of_neg hapos hx
    have hy' := mul_nonpos_of_nonneg_of_nonpos hb hy.le
    linarith

theorem convex_upperCone (n : ℕ) : Convex ℝ (upperCone n) := by
  intro x hx y hy a b ha hb hab
  change ‖tail n (a • x + b • y)‖ < a * x 0 + b * y 0
  rw [map_add, map_smul, map_smul]
  calc
    ‖a • tail n x + b • tail n y‖ ≤ ‖a • tail n x‖ + ‖b • tail n y‖ := norm_add_le _ _
    _ = a * ‖tail n x‖ + b * ‖tail n y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * x 0 + b * y 0 := by
      by_cases hzero : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [hzero, hb1, upperCone] using hy
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx (lt_of_le_of_ne ha (Ne.symm hzero)))
          (mul_le_mul_of_nonneg_left hy.le hb)

theorem zero_not_mem_lowerCone (n : ℕ) : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∉ lowerCone n := by
  change ¬ (0 : ℝ) < 0
  exact lt_irrefl 0

theorem zero_not_mem_upperCone (n : ℕ) : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∉ upperCone n := by
  change ¬ ‖tail n 0‖ < 0
  simp

theorem positive_smul_mem_lowerCone (n : ℕ) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin (n + 2))) (hx : x ∈ lowerCone n) : a • x ∈ lowerCone n :=
  mul_neg_of_pos_of_neg ha hx

theorem positive_smul_mem_upperCone (n : ℕ) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin (n + 2))) (hx : x ∈ upperCone n) : a • x ∈ upperCone n := by
  change ‖tail n (a • x)‖ < a * x 0
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_lt_mul_of_pos_left hx ha

theorem lowerCap_contractible (n : ℕ) : ContractibleSpace (lowerCap n) :=
  NormalizedCone.contractibleSpace (lowerCone n)
    ⟨endPole n false, endPole_mem_capRegion n false⟩
    (convex_lowerCone n) (zero_not_mem_lowerCone n) (positive_smul_mem_lowerCone n)

theorem upperCap_contractible (n : ℕ) : ContractibleSpace (upperCap n) :=
  NormalizedCone.contractibleSpace (upperCone n)
    ⟨endPole n true, endPole_mem_capRegion n true⟩
    (convex_upperCone n) (zero_not_mem_upperCone n) (positive_smul_mem_upperCone n)

theorem capRegion_contractible (n : ℕ) (b : Bool) : ContractibleSpace (capRegion n b) := by
  cases b
  · exact lowerCap_contractible n
  · exact upperCap_contractible n

end NoExoticSixSphere.SphereCylinder
