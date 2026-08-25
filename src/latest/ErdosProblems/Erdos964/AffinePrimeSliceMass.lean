import ErdosProblems.Erdos964.AffinePrimeSlicePNT
import ErdosProblems.Erdos964.PrimeReciprocalMass

/-!
# Total prime-slice mass on the square scale
-/

namespace Erdos964

theorem exists_affine_primeSlice_pointwise_upper (m c : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ t p L U : ℕ, T₀ ≤ t → 0 < p → p ≤ t →
      p * L ≤ m * t ^ 2 + c - 1 → m * (2 * t ^ 2) + c - 1 ≤ p * U →
      ((primeSlice ((Finset.Ioc L U).filter Nat.Prime) p
          (m * t ^ 2 + c - 1) (m * (2 * t ^ 2) + c - 1)).card : ℝ) ≤
        (((m : ℝ) + 1) * (t : ℝ) ^ 2 / Real.log t) * (1 / (p : ℝ)) := by
  obtain ⟨Y₀, hY₀, herror⟩ := exists_affine_primeSlice_error m c hm hc 1 (by norm_num)
  refine ⟨max ⌈Y₀⌉₊ 2, le_max_right _ _, ?_⟩
  intro t p L U ht hp hpt hlo hhi
  have ht2 : 2 ≤ t := (le_max_right ⌈Y₀⌉₊ 2).trans ht
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hptR : (p : ℝ) ≤ t := by exact_mod_cast hpt
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  let Y := ((t ^ 2 : ℕ) : ℝ) / p
  have htY : (t : ℝ) ≤ Y := by
    apply (le_div_iff₀ hpR).mpr
    push_cast
    nlinarith
  have hY : Y₀ ≤ Y := by
    calc
      Y₀ ≤ (⌈Y₀⌉₊ : ℝ) := Nat.le_ceil Y₀
      _ ≤ (t : ℝ) := by exact_mod_cast (le_max_left ⌈Y₀⌉₊ 2).trans ht
      _ ≤ Y := htY
  have hLY : Real.log t ≤ Real.log Y := Real.log_le_log htR htY
  have he := (abs_le.mp (herror (t ^ 2) p L U (by nlinarith) hp hY hlo hhi)).2
  change _ - (m : ℝ) * Y / Real.log Y ≤ 1 * (Y / Real.log Y) at he
  have hYnonneg : 0 ≤ Y := htR.le.trans htY
  calc
    _ ≤ (m : ℝ) * Y / Real.log Y + Y / Real.log Y := by linarith
    _ = ((m : ℝ) + 1) * Y / Real.log Y := by ring
    _ ≤ ((m : ℝ) + 1) * Y / Real.log t :=
      div_le_div_of_nonneg_left (by positivity) hlogt hLY
    _ = _ := by dsimp only [Y]; push_cast; ring

theorem exists_affine_primeSlice_total_mass_bound (m c : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ (t L U : ℕ) (P : Finset ℕ), T₀ ≤ t →
      (∀ p ∈ P, p.Prime ∧ p ≤ t ∧ η * Real.log t ≤ Real.log p) →
      (∀ p ∈ P, p * L ≤ m * t ^ 2 + c - 1 ∧ m * (2 * t ^ 2) + c - 1 ≤ p * U) →
      (∑ p ∈ P, ((primeSlice ((Finset.Ioc L U).filter Nat.Prime) p
          (m * t ^ 2 + c - 1) (m * (2 * t ^ 2) + c - 1)).card : ℝ)) ≤
        (2 * ((m : ℝ) + 1) / η) * ((t : ℝ) ^ 2 / Real.log t) := by
  obtain ⟨T₁, hT₁, hpoint⟩ := exists_affine_primeSlice_pointwise_upper m c hm hc
  obtain ⟨T₂, hT₂, hmass⟩ := exists_primeReciprocalMass_uniform_bound η hη
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro t L U P ht hP hsupport
  have ht₁ : T₁ ≤ t := (le_max_left T₁ T₂).trans ht
  have ht₂ : T₂ ≤ t := (le_max_right T₁ T₂).trans ht
  have hlog : 0 < Real.log t := Real.log_pos
    (by exact_mod_cast (show 1 < t by omega))
  calc
    _ ≤ ∑ p ∈ P, (((m : ℝ) + 1) * (t : ℝ) ^ 2 / Real.log t) * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint t p L U ht₁ (hP p hp).1.pos (hP p hp).2.1
        (hsupport p hp).1 (hsupport p hp).2
    _ = (((m : ℝ) + 1) * (t : ℝ) ^ 2 / Real.log t) * (∑ p ∈ P, (1 : ℝ) / p) := by
      rw [Finset.mul_sum]
    _ ≤ (((m : ℝ) + 1) * (t : ℝ) ^ 2 / Real.log t) * (2 / η) :=
      mul_le_mul_of_nonneg_left (hmass t P ht₂ hP) (by positivity)
    _ = _ := by ring

end Erdos964
