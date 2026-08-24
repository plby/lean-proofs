import ErdosProblems.Erdos587.SqrtPhaseBounds

/-! An integer just above a square-root phase yields a genuine square coordinate. -/

namespace Erdos587

theorem square_gap_coordinate_bounds {u H L S k : ℝ}
    (hu : 0 < u) (hH : 0 < H) (hL : 0 < L) (hS : 0 ≤ S)
    (hwidth : u * H ≤ L ^ 2) (hambient : u ^ 2 * S ≤ L ^ 2)
    (hgap0 : 0 < k - Real.sqrt S) (hgap1 : k - Real.sqrt S < H / (8 * L)) :
    0 < u * k ^ 2 - u * S ∧ u * k ^ 2 - u * S < H := by
  have hsqrt := Real.sq_sqrt hS
  have hroot : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hk : 0 < k := by linarith
  have hrootU : u * Real.sqrt S ≤ L := by
    have hsquare : (u * Real.sqrt S) ^ 2 ≤ L ^ 2 := by
      rw [mul_pow, hsqrt]
      exact hambient
    nlinarith [mul_nonneg hu.le hroot]
  let δ := H / (8 * L)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : 8 * L * δ = H := by dsimp only [δ]; field_simp
  have hδsq : u * δ ^ 2 ≤ H / 64 := by
    have hh := mul_le_mul_of_nonneg_right hwidth hH.le
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 64 * L ^ 2)).mp
    have heq : (u * δ ^ 2) * (64 * L ^ 2) = u * H ^ 2 := by
      dsimp only [δ]
      field_simp
      norm_num
    rw [heq]
    nlinarith [hh]
  have hgap : k - Real.sqrt S < δ := hgap1
  have hlin : 2 * (u * Real.sqrt S) * (k - Real.sqrt S) ≤ 2 * L * δ := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hrootU (by norm_num)
    · exact hgap.le
    · exact hgap0.le
    · positivity
  have hquad : u * (k - Real.sqrt S) ^ 2 ≤ u * δ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgap0.le hgap.le 2) hu.le
  have hidentity : u * k ^ 2 - u * S =
      2 * (u * Real.sqrt S) * (k - Real.sqrt S) + u * (k - Real.sqrt S) ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => u * x) hsqrt]
  constructor
  · have hsq : S < k ^ 2 := by nlinarith
    have hh := mul_lt_mul_of_pos_left hsq hu
    linarith
  · rw [hidentity]
    nlinarith [hlin, hquad, hδsq, hδeq]

theorem unit_fiber_square_of_sqrt_gap {u t v j H : ℕ} (hu : 0 < u) (hH : 0 < H)
    {T : ℝ} (hT : 0 < T) (hwidth : (u : ℝ) * H ≤ T)
    (hambient : (u : ℝ) * ((t : ℝ) + v * j) ≤ T)
    {k : ℤ} (hgap0 : 0 < (k : ℝ) - Real.sqrt (((t : ℝ) + v * j) / u))
    (hgap1 : (k : ℝ) - Real.sqrt (((t : ℝ) + v * j) / u) < (H : ℝ) / (8 * Real.sqrt T)) :
    ∃ x ≤ H, ∃ z : ℕ, 0 < z ∧ z ^ 2 = u * (t + x + v * j) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hL : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hS : 0 ≤ ((t : ℝ) + v * j) / u := by positivity
  have hSscale : (u : ℝ) ^ 2 * (((t : ℝ) + v * j) / u) ≤ (Real.sqrt T) ^ 2 := by
    rw [Real.sq_sqrt hT.le]
    have heq : (u : ℝ) ^ 2 * (((t : ℝ) + v * j) / u) = (u : ℝ) * ((t : ℝ) + v * j) := by
      field_simp
    rwa [heq]
  have hwidth' : (u : ℝ) * H ≤ (Real.sqrt T) ^ 2 := by rwa [Real.sq_sqrt hT.le]
  obtain ⟨hx0, hxH⟩ := square_gap_coordinate_bounds huR hHR hL hS hwidth' hSscale hgap0 hgap1
  have hcancel : (u : ℝ) * (((t : ℝ) + v * j) / u) = (t : ℝ) + v * j := by field_simp
  rw [hcancel] at hx0 hxH
  have hkR : (0 : ℝ) < k := by linarith [Real.sqrt_nonneg (((t : ℝ) + v * j) / u)]
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hkR
  let X : ℤ := (u : ℤ) * k ^ 2 - t - v * j
  have hXR : (X : ℝ) = (u : ℝ) * (k : ℝ) ^ 2 - ((t : ℝ) + v * j) := by
    dsimp only [X]
    push_cast
    ring
  have hX0 : 0 ≤ X := by
    have hh : (0 : ℝ) ≤ X := by rw [hXR]; exact hx0.le
    exact_mod_cast hh
  have hXH : X.toNat ≤ H := by
    have hh : X ≤ (H : ℤ) := by
      have hhR : (X : ℝ) ≤ H := by rw [hXR]; exact hxH.le
      exact_mod_cast hhR
    exact Int.toNat_le.mpr hh
  have hkNat : 0 < k.toNat := by omega
  refine ⟨X.toNat, hXH, u * k.toNat, Nat.mul_pos hu hkNat, ?_⟩
  have hXcast : (X.toNat : ℤ) = X := Int.toNat_of_nonneg hX0
  have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkZ.le
  have heq : ((u * k.toNat : ℕ) : ℤ) ^ 2 = (u : ℤ) * (t + (X.toNat : ℤ) + v * j) := by
    rw [Nat.cast_mul, hkcast, hXcast]
    dsimp only [X]
    ring
  exact_mod_cast heq

end Erdos587
