import ErdosProblems.Erdos587.NearbyCounting
import ErdosProblems.Erdos587.ProgressionGeometry

/-! A nonzero smoothed count supplies genuine integer coordinates. -/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma exists_ne_zero_of_tsum_ne_zero {α β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    (f : α → β) (h : (∑' x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hnot
  push Not at hnot
  have hh : f = fun _ => 0 := funext hnot
  rw [hh, tsum_zero] at h
  exact h rfl

lemma periodizedSchwartz_ne_zero_witness (g : 𝓢(ℝ, ℂ)) (σ t : ℝ)
    (h : periodizedSchwartz g σ t ≠ 0) : ∃ k : ℤ, g (σ⁻¹ * (t + k)) ≠ 0 :=
  exists_ne_zero_of_tsum_ne_zero _ h

lemma normalized_inverse_coordinate {a v H t : ℕ} (hv : 0 < v) (hH : 0 < H) (z k : ℤ) :
    (((v : ℝ) / H)⁻¹)⁻¹ * ((a : ℝ) * ((z : ℝ) ^ 2 - t) / v + k) =
      (((a : ℤ) * (z ^ 2 - t) + v * k : ℤ) : ℝ) / H := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  rw [inv_inv]
  push_cast
  field_simp

lemma integer_inverse_coordinate_congruence {a u b v : ℕ}
    (hab : a * u = b * v + 1) (t : ℕ) (z k : ℤ) :
    z ^ 2 ≡ (t : ℤ) + u * ((a : ℤ) * (z ^ 2 - t) + v * k) [ZMOD v] := by
  apply Int.modEq_iff_dvd.mpr
  have habZ : (a : ℤ) * u = b * v + 1 := by exact_mod_cast hab
  refine ⟨(b : ℤ) * (z ^ 2 - t) + u * k, ?_⟩
  linear_combination (z ^ 2 - (t : ℤ)) * habZ

theorem weightedSquareCount_ne_zero_witness (f g : 𝓢(ℝ, ℂ))
    {a u b v H : ℕ} (hv : 0 < v) (hH : 0 < H) (hab : a * u = b * v + 1)
    (t : ℕ) (L : ℝ)
    (hcount : weightedSquareCount f g a v t L (((v : ℝ) / H)⁻¹) ≠ 0) :
    ∃ z x : ℤ, f (L⁻¹ * z) ≠ 0 ∧ g ((x : ℝ) / H) ≠ 0 ∧
      z ^ 2 ≡ (t : ℤ) + u * x [ZMOD v] := by
  obtain ⟨z, hz⟩ := exists_ne_zero_of_tsum_ne_zero _ hcount
  obtain ⟨hf, hg⟩ := mul_ne_zero_iff.mp hz
  obtain ⟨k, hk⟩ := periodizedSchwartz_ne_zero_witness g _ _ hg
  refine ⟨z, (a : ℤ) * (z ^ 2 - t) + v * k, hf, ?_, integer_inverse_coordinate_congruence hab t z k⟩
  rwa [normalized_inverse_coordinate hv hH] at hk

theorem positive_square_of_supported_count (f g : 𝓢(ℝ, ℂ))
    {a u b v H J : ℕ} (hv : 0 < v) (hH : 0 < H) (hab : a * u = b * v + 1)
    (t : ℕ) (L : ℝ)
    (hg : ∀ x : ℝ, g x ≠ 0 → 0 ≤ x ∧ x ≤ 1 / 4)
    (hf : ∀ z : ℤ, f (L⁻¹ * z) ≠ 0 → 0 < z ∧
      (t : ℝ) + (u : ℝ) * H / 4 ≤ (z : ℝ) ^ 2 ∧
      (z : ℝ) ^ 2 ≤ (t : ℝ) + (v : ℝ) * J)
    (hcount : weightedSquareCount f g a v t L (((v : ℝ) / H)⁻¹) ≠ 0) :
    ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨z, x, hfz, hgx, hcong⟩ := weightedSquareCount_ne_zero_witness f g hv hH hab t L hcount
  obtain ⟨hzpos, hzlo, hzhi⟩ := hf z hfz
  obtain ⟨hx0, hx1⟩ := hg ((x : ℝ) / H) hgx
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hxR : 0 ≤ (x : ℝ) := by
    simpa only [zero_mul] using (le_div_iff₀ hHR).mp hx0
  have hxH : (x : ℝ) ≤ (H : ℝ) / 4 := by
    have hh := (div_le_iff₀ hHR).mp hx1
    linarith
  let X := x.toNat
  let Z := z.toNat
  have hX : (X : ℤ) = x := Int.toNat_of_nonneg (by exact_mod_cast hxR)
  have hZ : (Z : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hXR : (X : ℝ) = x := by exact_mod_cast hX
  have hZR : (Z : ℝ) = z := by exact_mod_cast hZ
  have hXH : X ≤ H := by
    have hh : (X : ℝ) ≤ H := by rw [hXR]; nlinarith
    exact_mod_cast hh
  have hZpos : 0 < Z := by
    have hh : (0 : ℤ) < (Z : ℤ) := by rwa [hZ]
    exact_mod_cast hh
  have hlo : t + u * X ≤ Z ^ 2 := by
    have hh : (t : ℝ) + u * X ≤ (Z : ℝ) ^ 2 := by
      rw [hXR, hZR]
      apply le_trans _ hzlo
      have hh := mul_le_mul_of_nonneg_left hxH (Nat.cast_nonneg u)
      linarith
    exact_mod_cast hh
  have hhi : Z ^ 2 ≤ t + u * X + v * J := by
    have hh : (Z : ℝ) ^ 2 ≤ t + u * X + v * J := by
      rw [hZR]
      have hux : (0 : ℝ) ≤ u * X := by positivity
      linarith
    exact_mod_cast hh
  have hcongZ : (Z : ℤ) ^ 2 ≡ (t : ℤ) + u * (X : ℤ) [ZMOD v] := by
    simpa only [hZ, hX] using hcong
  have hcongN : Z ^ 2 ≡ t + u * X [MOD v] := by exact_mod_cast hcongZ
  obtain ⟨y, hy, heq⟩ := exists_progression_coordinate_of_square_congruence hv hcongN hlo hhi
  exact ⟨X, hXH, y, hy, Z, hZpos, heq⟩

end Erdos587
