import ErdosProblems.Erdos941.ModularRotations

/-! # Homogeneity reduces finite plane certificates to projective charts -/

namespace Erdos941

def heightLinear {R : Type*} [CommRing R] (a b c : R) : (R × R × R) →ₗ[R] R where
  toFun v := a * v.1 + b * v.2.1 + c * v.2.2
  map_add' _ _ := by dsimp; ring
  map_smul' _ _ := by dsimp; ring

theorem exists_word_kill_of_smul {R : Type*} [CommRing R] (t : R)
    (L : (R × R × R) →ₗ[R] R) {v u : R × R × R} (r : R) (hv : v = r • u)
    (h : ∃ w : List Axis, L (linearWord t w u) = 0) :
    ∃ w : List Axis, L (linearWord t w v) = 0 := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  rw [hv, map_smul, map_smul, hw, smul_zero]

theorem exists_word_kill_of_normalized {K : Type*} [Field K] (t : K)
    (L : (K × K × K) →ₗ[K] K)
    (h1 : ∀ x z : K, ∃ w : List Axis, L (linearWord t w (x, 1, z)) = 0)
    (h2 : ∀ x : K, ∃ w : List Axis, L (linearWord t w (x, 0, 1)) = 0)
    (h0 : ∃ w : List Axis, L (linearWord t w (1, 0, 0)) = 0)
    (v : K × K × K) : ∃ w : List Axis, L (linearWord t w v) = 0 := by
  by_cases hy : v.2.1 = 0
  · by_cases hz : v.2.2 = 0
    · apply exists_word_kill_of_smul t L v.1 _ h0
      ext <;> simp [hy, hz]
    · apply exists_word_kill_of_smul t L v.2.2 _ (h2 (v.1 / v.2.2))
      ext <;> simp [hy, hz, mul_div_cancel₀]
  · apply exists_word_kill_of_smul t L v.2.1 _ (h1 (v.1 / v.2.1) (v.2.2 / v.2.1))
    ext <;> simp [hy, mul_div_cancel₀]

end Erdos941
