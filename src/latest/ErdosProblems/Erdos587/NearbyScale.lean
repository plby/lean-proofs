import ErdosProblems.Erdos587.NearbyAssembly

/-!
# Simple global hypotheses for the nearby mean

Rounding the physical width and the low-frequency cutoff supplies the finite
conditions of the combined estimate. The fourth-root condition follows from
the simple scale inequality `u * L^3 <= v^3`.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma mul_sqrt_sqrt_le_of_pow_four_le_cube {u X : ℕ} (hu : u ^ 4 ≤ X ^ 3) :
    u * Nat.sqrt (Nat.sqrt X) ≤ X := by
  let D := Nat.sqrt (Nat.sqrt X)
  have hD₂ : D ^ 2 ≤ Nat.sqrt X := Nat.sqrt_le' _
  have hD₄ : D ^ 4 ≤ X := by
    calc
      D ^ 4 = (D ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt X) ^ 2 := Nat.pow_le_pow_left hD₂ 2
      _ ≤ X := Nat.sqrt_le' X
  have hprod : (u * D) ^ 4 ≤ X ^ 4 := by
    calc
      (u * D) ^ 4 = u ^ 4 * D ^ 4 := mul_pow _ _ _
      _ ≤ X ^ 3 * X := Nat.mul_le_mul hu hD₄
      _ = X ^ 4 := by ring
  have hsq : (u * D) ^ 2 ≤ X ^ 2 := by
    apply (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp
    simpa only [← pow_mul] using hprod
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hsq

lemma rounded_physical_width_bounds {L : ℝ} (hL : 1 ≤ L) :
    let K := ⌊L⌋₊ + 1
    0 < K ∧ L ≤ (K : ℝ) ∧ (K : ℝ) ≤ 2 * L ∧ 1 / 2 ≤ L⁻¹ * K ∧ L⁻¹ * K ≤ 2 := by
  dsimp only
  have hLpos : 0 < L := by linarith
  have hlo : L ≤ ((⌊L⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one L).le
  have hhi : ((⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * L := by
    have hh := Nat.floor_le hLpos.le
    push_cast
    linarith
  refine ⟨by omega, hlo, hhi, ?_, ?_⟩
  · rw [show L⁻¹ * ((⌊L⌋₊ + 1 : ℕ) : ℝ) = ((⌊L⌋₊ + 1 : ℕ) : ℝ) / L by ring]
    apply (le_div_iff₀ hLpos).mpr
    linarith
  · rw [show L⁻¹ * ((⌊L⌋₊ + 1 : ℕ) : ℝ) = ((⌊L⌋₊ + 1 : ℕ) : ℝ) / L by ring]
    exact (div_le_iff₀ hLpos).mpr hhi

lemma rounded_low_frequency_conditions (u v : ℕ) {L : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hL : 81 ≤ L) (hLv : L ≤ v)
    (hpower : (u : ℝ) * L ^ 3 ≤ (v : ℝ) ^ 3) :
    let K := ⌊L⌋₊ + 1
    let M₀ := ⌊(u : ℝ) * v / L ^ 2⌋₊
    let X := 2 * M₀ * K
    M₀ = 0 ∨ (3 ≤ Nat.sqrt (Nat.sqrt X) ∧ u - 1 ≤ X ∧ u * Nat.sqrt (Nat.sqrt X) ≤ X) := by
  dsimp only
  let K := ⌊L⌋₊ + 1
  let M₀ := ⌊(u : ℝ) * v / L ^ 2⌋₊
  let X := 2 * M₀ * K
  have hLpos : 0 < L := by linarith
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hround := rounded_physical_width_bounds (show 1 ≤ L by linarith)
  have hLK : L ≤ (K : ℝ) := hround.2.1
  by_cases hM₀ : M₀ = 0
  · exact Or.inl hM₀
  right
  have hM₀pos : 0 < M₀ := Nat.pos_of_ne_zero hM₀
  have hM₀real : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀pos
  have hfrac : (u : ℝ) * v / L ^ 2 ≤ 2 * M₀ := by
    have hh := Nat.lt_floor_add_one ((u : ℝ) * v / L ^ 2)
    change (u : ℝ) * v / L ^ 2 < (M₀ : ℝ) + 1 at hh
    linarith
  have hfracprod := (div_le_iff₀ (pow_pos hLpos 2)).mp hfrac
  have hXL : (u : ℝ) * v ≤ (X : ℝ) * L := by
    calc
      _ ≤ (2 * (M₀ : ℝ)) * L ^ 2 := hfracprod
      _ = (2 * (M₀ : ℝ) * L) * L := by ring
      _ ≤ (2 * (M₀ : ℝ) * L) * K := mul_le_mul_of_nonneg_left hLK (by positivity)
      _ = (X : ℝ) * L := by dsimp [X]; push_cast; ring
  have huXreal : (u : ℝ) ≤ X := by
    apply (mul_le_mul_iff_left₀ hLpos).mp
    exact (mul_le_mul_of_nonneg_left hLv huR.le).trans hXL
  have huX : u ≤ X := by exact_mod_cast huXreal
  have hK81 : 81 ≤ K := by exact_mod_cast hL.trans hLK
  have hX81 : 81 ≤ X := by
    have hKX : K ≤ X := by
      change K ≤ (2 * M₀) * K
      simpa only [one_mul] using Nat.mul_le_mul_right K (show 1 ≤ 2 * M₀ by omega)
    exact hK81.trans hKX
  have hD : 3 ≤ Nat.sqrt (Nat.sqrt X) :=
    le_sqrt_sqrt_of_pow_four_le (by norm_num; exact hX81)
  have hXL₃ := pow_le_pow_left₀ (by positivity : 0 ≤ (u : ℝ) * v) hXL 3
  rw [mul_pow, mul_pow] at hXL₃
  have hu₄L : (u : ℝ) ^ 4 * L ^ 3 ≤ (X : ℝ) ^ 3 * L ^ 3 := by
    calc
      _ = (u : ℝ) ^ 3 * ((u : ℝ) * L ^ 3) := by ring
      _ ≤ (u : ℝ) ^ 3 * (v : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := hXL₃
  have hu₄real : (u : ℝ) ^ 4 ≤ (X : ℝ) ^ 3 :=
    (mul_le_mul_iff_left₀ (pow_pos hLpos 3)).mp hu₄L
  have hu₄ : u ^ 4 ≤ X ^ 3 := by exact_mod_cast hu₄real
  exact ⟨hD, (Nat.sub_le u 1).trans huX, mul_sqrt_sqrt_le_of_pow_four_le_cube hu₄⟩

theorem exists_nearby_mean_bound_of_global_scales (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a u v M Y : ℕ),
      0 < u → 0 < v → 0 < M → 1 ≤ Y → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      ∀ L : ℝ, 81 ≤ L → (u : ℝ) * L ^ 3 ≤ (v : ℝ) ^ 3 → (u : ℝ) * v / L ^ 2 ≤ M →
        4 * (Y : ℝ) * L ≤ v → 64 * (M : ℝ) * L ≤ u * v →
        64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ j) →
        (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
          C * M * Real.sqrt L * (1 + Real.log u) *
            Real.log ((35 * M * (⌊L⌋₊ + 1) : ℕ) : ℝ) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_combined_nearby_mean_bound j f
  refine ⟨C, hC, O, hO, ?_⟩
  intro a u v M Y hu hv hM hY ha huv hav L hL hpower hMlower hYv hglobal hsize
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  let K := ⌊L⌋₊ + 1
  let M₀ := ⌊(u : ℝ) * v / L ^ 2⌋₊
  have hfrac0 : 0 ≤ (u : ℝ) * v / L ^ 2 := by positivity
  have hcutlo : (M₀ : ℝ) ≤ (u : ℝ) * v / L ^ 2 := Nat.floor_le hfrac0
  have hcuthi : (u : ℝ) * v / L ^ 2 < (M₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hM₀ : M₀ ≤ M := by exact_mod_cast hcutlo.trans hMlower
  have hLv : L ≤ v := by
    have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    have hYL := mul_le_mul_of_nonneg_right hYR hLpos.le
    nlinarith
  have hsizes := rounded_low_frequency_conditions u v hu hv hL hLv hpower
  obtain ⟨hK, hLK, hKL, hlo, hhi⟩ := rounded_physical_width_bounds hLone
  exact hmean a u v M M₀ K Y hu hv hM hK hY ha huv hav hM₀ hsizes L hLone hlo hhi
    hcutlo hcuthi hYv hglobal hsize

end Erdos587
