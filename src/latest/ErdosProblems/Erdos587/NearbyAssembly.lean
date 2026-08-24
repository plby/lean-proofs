import ErdosProblems.Erdos587.NearbyPartition

/-!
# The combined nearby-rational mean

This combines the low-frequency, small-dual-width, and large-block estimates.
All global scale hypotheses are explicit, to be checked at the terminal GAP
parameters separately from the analytic proof.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

/-- The complete nearby-rational mean with a logarithmic loss, retaining its
integral main term. The hypotheses are finite inequalities, not asymptotic
error assumptions. -/
theorem exists_combined_nearby_mean_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a u v M M₀ K Y : ℕ),
      let X₀ := 2 * M₀ * K
      let D₀ := Nat.sqrt (Nat.sqrt X₀)
      let Z := 35 * M * K
      0 < u → 0 < v → 0 < M → 0 < K → 1 ≤ Y →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 → M₀ ≤ M →
        (M₀ = 0 ∨ (3 ≤ D₀ ∧ u - 1 ≤ X₀ ∧ u * D₀ ≤ X₀)) →
        ∀ L : ℝ, 1 ≤ L → 1 / 2 ≤ L⁻¹ * K → L⁻¹ * K ≤ 2 →
          (M₀ : ℝ) ≤ (u : ℝ) * v / L ^ 2 → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
          4 * (Y : ℝ) * L ≤ v → 64 * (M : ℝ) * L ≤ u * v →
          64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ j) →
          (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
            C * M * Real.sqrt L * (1 + Real.log u) * Real.log (Z : ℝ) ^ O := by
  obtain ⟨C₀, hC₀, O₀, hO₀, hlow⟩ := exists_nearby_low_frequency_mean_bound f
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_nearby_small_frequency_sum_bound f
  obtain ⟨C₂, hC₂, O₂, hO₂, hlarge⟩ := exists_nearby_large_frequency_sum_bound j f
  refine ⟨C₀ + C₁ + C₂, by positivity, O₀ + O₂, by omega, ?_⟩
  intro a u v M M₀ K Y
  dsimp only
  let X₀ := 2 * M₀ * K
  let D₀ := Nat.sqrt (Nat.sqrt X₀)
  let Z := 35 * M * K
  intro hu hv hM hK hY ha huv hav hM₀M hsizes L hL hlo hhi hcutlo hcuthi hYv hglobal hsize
  have hLpos : 0 < L := by linarith
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hu0 : 0 ≤ Real.log u := Real.log_nonneg huR
  let H := 1 + Real.log u
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hMK : 0 < M * K := Nat.mul_pos hM hK
  have hZthree : 3 ≤ Z := by dsimp [Z]; nlinarith
  let F := Real.log (Z : ℝ)
  have hF : 1 ≤ F := one_le_log_nat_of_three_le hZthree
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  let B := (M : ℝ) * Real.sqrt L * H * F ^ (O₀ + O₂)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hHF : F ^ (O₀ + O₂) ≤ H * F ^ (O₀ + O₂) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH (pow_nonneg hF0 _)
  have hHFone : 1 ≤ H * F ^ (O₀ + O₂) :=
    one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hF)
  have hpowlo {x : ℝ} (hx : 0 ≤ x) (hxF : x ≤ F) : x ^ O₀ ≤ F ^ (O₀ + O₂) := by
    calc
      _ ≤ F ^ O₀ := pow_le_pow_left₀ hx hxF O₀
      _ ≤ F ^ O₀ * F ^ O₂ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hF)
      _ = _ := (pow_add F O₀ O₂).symm
  have hpowhi {x : ℝ} (hx : 0 ≤ x) (hxF : x ≤ F) : x ^ O₂ ≤ F ^ (O₀ + O₂) := by
    calc
      _ ≤ F ^ O₂ := pow_le_pow_left₀ hx hxF O₂
      _ = 1 * F ^ O₂ := by ring
      _ ≤ F ^ O₀ * F ^ O₂ := mul_le_mul_of_nonneg_right (one_le_pow₀ hF) (by positivity)
      _ = _ := (pow_add F O₀ O₂).symm
  have hlow' : (∑ m ∈ Finset.Icc 1 M₀, ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C₀ * B := by
    rcases hsizes with hz | ⟨hD₀, huX, huD⟩
    · simpa [hz] using (show (0 : ℝ) ≤ C₀ * B by positivity)
    have huPos : 0 < (u : ℝ) := by exact_mod_cast hu
    have hvPos : 0 < (v : ℝ) := by exact_mod_cast hv
    have hA : ∀ m ∈ Finset.Icc 1 M₀, ((m : ℝ) / (u * v)) * L ^ 2 ≤ 1 := by
      intro m hm
      have hmM : (m : ℝ) ≤ M₀ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have hprod := (le_div_iff₀ (pow_pos hLpos 2)).mp hcutlo
      have hmprod := mul_le_mul_of_nonneg_right hmM (sq_nonneg L)
      rw [show ((m : ℝ) / (u * v)) * L ^ 2 = ((m : ℝ) * L ^ 2) / (u * v) by ring]
      exact (div_le_one₀ (mul_pos huPos hvPos)).mpr (hmprod.trans hprod)
    have hh := hlow a u v M₀ K ha hu hv hK hD₀ huX huD L hL hlo hhi hA
    have hXthree : 3 ≤ X₀ := hD₀.trans ((Nat.sqrt_le_self (Nat.sqrt X₀)).trans (Nat.sqrt_le_self X₀))
    have hXZ : X₀ ≤ Z := Nat.mul_le_mul_right K (Nat.mul_le_mul (by norm_num : 2 ≤ 35) hM₀M)
    have hlogX : Real.log (X₀ : ℝ) ≤ F :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < X₀)) (by exact_mod_cast hXZ)
    have hlogX0 : 0 ≤ Real.log (X₀ : ℝ) :=
      zero_le_one.trans (one_le_log_nat_of_three_le hXthree)
    have hp := hpowlo hlogX0 hlogX
    apply hh.trans
    calc
      _ ≤ C₀ * M * Real.sqrt L * F ^ (O₀ + O₂) := by gcongr
      _ ≤ (C₀ * M * Real.sqrt L) * (H * F ^ (O₀ + O₂)) :=
        mul_le_mul_of_nonneg_left hHF (by positivity)
      _ = C₀ * B := by dsimp [B]; ring
  have hsmall' : (∑ m ∈ nearbySmallFrequencies u v M M₀ L,
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C₁ * B := by
    apply (hsmall a u v M M₀ hu hv ha L hLpos hcuthi).trans
    have hh := le_mul_of_one_le_right (show 0 ≤ C₁ * M * Real.sqrt L by positivity) hHFone
    convert hh using 1
    dsimp [B]
    ring
  have hlarge' : (∑ m ∈ nearbyLargeFrequencies u v M M₀ L,
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C₂ * B := by
    have hh := hlarge a u v M M₀ Y hu hv hM hY ha huv hav L hLpos hcuthi hYv hglobal hsize
    have hMZ : 35 * M ≤ Z := by
      change 35 * M ≤ (35 * M) * K
      simpa only [mul_one] using Nat.mul_le_mul_left (35 * M) (show 1 ≤ K by omega)
    have hlogM0 : 0 ≤ Real.log (35 * (M : ℝ)) := Real.log_nonneg (by linarith)
    have hlogM : Real.log (35 * (M : ℝ)) ≤ F :=
      Real.log_le_log (by positivity) (by exact_mod_cast hMZ)
    have hp := hpowhi hlogM0 hlogM
    apply hh.trans
    calc
      _ ≤ C₂ * M * Real.sqrt L * H * F ^ (O₀ + O₂) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = C₂ * B := by dsimp [B]; ring
  apply (nearby_frequency_cover u v M M₀ L
    (fun m => ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) (fun _ => norm_nonneg _)).trans
  calc
    _ ≤ C₀ * B + C₁ * B + C₂ * B := add_le_add (add_le_add hlow' hsmall') hlarge'
    _ = _ := by dsimp [B, H, F, Z]; ring

end Erdos587
