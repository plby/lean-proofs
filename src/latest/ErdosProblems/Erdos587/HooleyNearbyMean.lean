import ErdosProblems.Erdos587.HooleyNearbyLarge
import ErdosProblems.Erdos587.HooleyNearbyLow

/-!
# The complete nearby-rational mean with a log-log loss

The low frequencies, bounded dual widths, and all gcd/dyadic blocks cover
the full sum. All margins below are finite scale inequalities.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_nearby_low_power_margin {u v M₀ X : ℕ} (hM₀ : 0 < M₀)
    {L κ : ℝ} (hL : 0 < L) (hcutoff : (u : ℝ) * v / L ^ 2 < M₀ + 1)
    (hsep : 4 * L * (X : ℝ) ^ κ ≤ v) :
    (u : ℝ) * (X : ℝ) ^ κ ≤ M₀ * L := by
  have hMone : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀
  have hcut := (div_lt_iff₀ (pow_pos hL 2)).mp hcutoff
  have hcut' : (u : ℝ) * v ≤ 2 * M₀ * L ^ 2 := by
    apply hcut.le.trans
    exact mul_le_mul_of_nonneg_right (by linarith : (M₀ : ℝ) + 1 ≤ 2 * M₀) (sq_nonneg L)
  have hstep := (mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg u)).trans hcut'
  apply (mul_le_mul_iff_left₀ hL).mp
  calc
    ((u : ℝ) * (X : ℝ) ^ κ) * L = ((u : ℝ) * (4 * L * (X : ℝ) ^ κ)) / 4 := by ring
    _ ≤ (2 * (M₀ : ℝ) * L ^ 2) / 4 :=
      div_le_div_of_nonneg_right hstep (by norm_num)
    _ ≤ ((M₀ : ℝ) * L) * L := by
      nlinarith [show 0 ≤ (M₀ : ℝ) * L ^ 2 by positivity]

theorem exists_delta_nearby_mean (f : 𝓢(ℝ, ℂ)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u v M M₀ X : ℕ,
      0 < u → 0 < v → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      M₀ ≤ M → 2 ≤ X → u ≤ X → ∀ L : ℝ, 1 ≤ L →
      (M₀ : ℝ) ≤ (u : ℝ) * v / L ^ 2 → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
      4 * L * (X : ℝ) ^ κ ≤ v → 4 * (M : ℝ) * L ≤ u * v →
      (4 * L + 16 * u) * M ≤ X →
      (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
        C * M * Real.sqrt L * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C₀, hC₀, hlow⟩ := exists_delta_nearby_low_frequency_mean f hκ
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_nearby_small_frequency_sum_bound f
  obtain ⟨C₂, hC₂, hlarge⟩ := exists_delta_nearby_large_frequency_mean f hκ
  refine ⟨C₀ + C₁ + C₂, by positivity, ?_⟩
  intro a u v M M₀ X hu hv ha huv hav hM₀M hX huX L hL hcutlo hcuthi hsep hglobal hsize
  have hLpos : 0 < L := by linarith
  let F := max 1 (Real.log (Real.log (X : ℝ)))
  have hF : 1 ≤ F := le_max_left _ _
  have hFpow : 1 ≤ F ^ (9 / 2 : ℝ) := Real.one_le_rpow hF (by norm_num)
  have hFcompare : F ^ (7 / 2 : ℝ) ≤ F ^ (9 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hF (by norm_num)
  let B := (M : ℝ) * Real.sqrt L * F ^ (9 / 2 : ℝ)
  have hlow' : (∑ m ∈ Finset.Icc 1 M₀, ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤
      C₀ * B := by
    by_cases hz : M₀ = 0
    · simp only [hz, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty]
      dsimp [B]
      positivity
    have hM₀ : 0 < M₀ := Nat.pos_of_ne_zero hz
    have hM₀MR : (M₀ : ℝ) ≤ M := by exact_mod_cast hM₀M
    have hsize₀ : 2 * (M₀ : ℝ) * L ≤ X := by
      have ht : 2 * (M₀ : ℝ) * L ≤ 2 * M * L := by gcongr
      have hML : 0 ≤ (M : ℝ) * L := by positivity
      have huM : 0 ≤ (u : ℝ) * M := by positivity
      nlinarith [ht]
    have hsep₀ := delta_nearby_low_power_margin hM₀ hLpos hcuthi hsep
    have huR : 0 < (u : ℝ) := by exact_mod_cast hu
    have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
    have hA : ∀ m ∈ Finset.Icc 1 M₀, ((m : ℝ) / (u * v)) * L ^ 2 ≤ 1 := by
      intro m hm
      have hmM : (m : ℝ) ≤ M₀ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have ht := (le_div_iff₀ (pow_pos hLpos 2)).mp hcutlo
      have hmprod := mul_le_mul_of_nonneg_right hmM (sq_nonneg L)
      rw [show ((m : ℝ) / (u * v)) * L ^ 2 = ((m : ℝ) * L ^ 2) / (u * v) by ring]
      exact (div_le_one₀ (mul_pos huR hvR)).mpr (hmprod.trans ht)
    have hh := hlow a u v M₀ X ha hu hM₀ L hL hsize₀ hsep₀ hA
    apply hh.trans
    change C₀ * M₀ * Real.sqrt L * F ^ (7 / 2 : ℝ) ≤ C₀ * B
    calc
      _ ≤ C₀ * M * Real.sqrt L * F ^ (9 / 2 : ℝ) := by gcongr
      _ = _ := by dsimp [B]; ring
  have hsmall' : (∑ m ∈ nearbySmallFrequencies u v M M₀ L,
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C₁ * B := by
    apply (hsmall a u v M M₀ hu hv ha L hLpos hcuthi).trans
    have hh := le_mul_of_one_le_right (show 0 ≤ C₁ * M * Real.sqrt L by positivity) hFpow
    exact hh.trans_eq (by dsimp [B]; ring)
  have hlarge' : (∑ m ∈ nearbyLargeFrequencies u v M M₀ L,
      ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) ≤ C₂ * B := by
    have hh := hlarge a u v M M₀ X hu hv ha huv hav hX huX L hLpos hcuthi hsep hglobal hsize
    exact hh.trans_eq (by dsimp [B, F]; ring)
  apply (nearby_frequency_cover u v M M₀ L
    (fun m => ‖nearbyQuadraticRemainder f u m v (a : ℤ) L‖) (fun _ => norm_nonneg _)).trans
  calc
    _ ≤ C₀ * B + C₁ * B + C₂ * B := add_le_add (add_le_add hlow' hsmall') hlarge'
    _ = _ := by dsimp [B, F]; ring

end Erdos587
