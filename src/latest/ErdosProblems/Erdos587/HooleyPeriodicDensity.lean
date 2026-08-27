import ErdosProblems.Erdos587.HooleyPeriodicRoots
import ErdosProblems.Erdos587.HooleyCompleteRootDensity
import ErdosProblems.Erdos587.AlternativeLower

/-! # A one-log-log lower bound for the periodic physical main term -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_periodic_density_block_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (a u b q H t Y M X : ℕ), 0 < q → 0 < H →
      a * u = b * q + 1 → u.Coprime q → q ≤ X → A * Real.sqrt q ≤ M →
      (∀ x : ℝ, 0 ≤ (g x).re) →
      (∀ x ∈ Finset.Ico Y (Y + M), 1 ≤ (g ((x : ℝ) / H)).re) →
      (M : ℝ) / (C * q * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        (deltaPeriodicSquareDensity g a q t (((q : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, hden⟩ := exists_delta_complete_root_density
  refine ⟨A, hA, C, hC, ?_⟩
  intro g a u b q H t Y M X hq hH hab hu hqX hM hg hplateau
  have hroot := hden q (t + u * Y) u M X hq hu hM hqX
  rw [← sum_complete_roots_Ico] at hroot
  have hmain := delta_complete_roots_le_periodic_density g hq hH hab hg t (Finset.Ico Y (Y + M))
  calc
    _ = (q : ℝ)⁻¹ * ((M : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ))))) := by ring
    _ ≤ (q : ℝ)⁻¹ * ∑ x ∈ Finset.Ico Y (Y + M), (squareRootCount q (t + u * x) : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ (q : ℝ)⁻¹ * ∑ x ∈ Finset.Ico Y (Y + M),
        (squareRootCount q (t + u * x) : ℝ) * (g ((x : ℝ) / H)).re := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro x hx
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (hplateau x hx)
    _ ≤ _ := hmain

lemma delta_physical_plateau_block {H x : ℕ} (hH : 128 ≤ H)
    (hx : x ∈ Finset.Ico (H / 6) (H / 6 + H / 32)) :
    (x : ℝ) / H ∈ Set.Icc (5 / 32 : ℝ) (7 / 32) := by
  have hHR : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hH128 : (128 : ℝ) ≤ H := by exact_mod_cast hH
  have hxlo : ((H / 6 : ℕ) : ℝ) ≤ x := by exact_mod_cast (Finset.mem_Ico.mp hx).1
  have hxhi : (x : ℝ) < ((H / 6 : ℕ) : ℝ) + ((H / 32 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hx).2
  have hfloor : (H : ℝ) < ((H / 6 : ℕ) : ℝ) * 6 + 6 := by
    exact_mod_cast (show H < (H / 6) * 6 + 6 by omega)
  have hsix : ((H / 6 : ℕ) : ℝ) * 6 ≤ H := by exact_mod_cast Nat.div_mul_le_self H 6
  have hthirty : ((H / 32 : ℕ) : ℝ) * 32 ≤ H := by exact_mod_cast Nat.div_mul_le_self H 32
  constructor
  · apply (le_div_iff₀ hHR).mpr
    linarith
  · apply (div_le_iff₀ hHR).mpr
    linarith

theorem exists_delta_periodic_density_plateau_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (a u b q H t X : ℕ), 0 < q →
      a * u = b * q + 1 → u.Coprime q → q ≤ X → A * Real.sqrt q ≤ H →
      (∀ x : ℝ, 0 ≤ (g x).re) →
      (∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (g x).re) →
      (H : ℝ) / (C * q * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        (deltaPeriodicSquareDensity g a q t (((q : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, hden⟩ := exists_delta_periodic_density_block_bound
  refine ⟨128 * A + 128, by positivity, 64 * C, by positivity, ?_⟩
  intro g a u b q H t X hq hab hu hqX hscale hg hplateau
  have hsqrt : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hq)
  have hH128 : 128 ≤ H := by
    have hh : (128 : ℝ) ≤ H := by nlinarith
    exact_mod_cast hh
  have hH : 0 < H := by omega
  have hhalf : (H : ℝ) / 64 ≤ ((H / 32 : ℕ) : ℝ) := by
    have hh := half_div_le_nat_div 32 H (by norm_num) (show 32 ≤ H by omega)
    norm_num at hh
    exact hh
  have hM : A * Real.sqrt (q : ℝ) ≤ ((H / 32 : ℕ) : ℝ) := by
    apply le_trans _ hhalf
    nlinarith
  have hh := hden g a u b q H t (H / 6) (H / 32) X hq hH hab hu hqX hM hg
    (fun x hx => hplateau _ (delta_physical_plateau_block hH128 hx))
  apply le_trans _ hh
  calc
    _ = ((H : ℝ) / 64) / (C * q * max 1 (Real.log (Real.log (X : ℝ)))) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hhalf (by positivity)

end Erdos587
