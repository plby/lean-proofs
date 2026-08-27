import ErdosProblems.Erdos587.HooleyPeriodicMain
import ErdosProblems.Erdos587.AlternativeRoots

/-! # Complete roots retained in the periodic square density -/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_exists_periodic_root_index {a u b q : ℕ}
    (hab : a * u = b * q + 1) (t x : ℕ) (r : ℤ)
    (hroot : r ^ 2 ≡ (t : ℤ) + u * x [ZMOD q]) :
    ∃ k : ℤ, (a : ℤ) * (r ^ 2 - t) + q * k = x := by
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hroot
  have habZ : (a : ℤ) * u = b * q + 1 := by exact_mod_cast hab
  refine ⟨(a : ℤ) * d - b * x, ?_⟩
  linear_combination -(a : ℤ) * hd + (x : ℤ) * habZ

lemma delta_periodic_root_index_argument {a q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (t x : ℕ) (r k : ℤ) (hk : (a : ℤ) * (r ^ 2 - t) + q * k = x) :
    (((q : ℝ) / H)⁻¹)⁻¹ * ((a : ℝ) * ((r : ℝ) ^ 2 - t) / q + k) = (x : ℝ) / H := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hkR : (a : ℝ) * ((r : ℝ) ^ 2 - t) + q * k = x := by exact_mod_cast hk
  rw [inv_inv]
  field_simp
  linear_combination hkR

theorem delta_selected_roots_le_periodized_weight (g : 𝓢(ℝ, ℂ))
    {a u b q H : ℕ} (hq : 0 < q) (hH : 0 < H) (hab : a * u = b * q + 1)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℕ) (Y : Finset ℕ) (r : ℤ) :
    (∑ x ∈ Y.filter (fun x : ℕ => r ^ 2 ≡ (t : ℤ) + u * (x : ℤ) [ZMOD q]),
      (g ((x : ℝ) / H)).re) ≤
      (periodizedSchwartz g (((q : ℝ) / H)⁻¹)
        ((a : ℝ) * ((r : ℝ) ^ 2 - t) / q)).re := by
  classical
  let S := Y.filter (fun x : ℕ => r ^ 2 ≡ (t : ℤ) + u * (x : ℤ) [ZMOD q])
  have hex (x : ℕ) : ∃ k : ℤ, x ∈ S → (a : ℤ) * (r ^ 2 - t) + q * k = x := by
    by_cases hx : x ∈ S
    · obtain ⟨k, hk⟩ := delta_exists_periodic_root_index hab t x r (Finset.mem_filter.mp hx).2
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose k hk using hex
  have hinj : Set.InjOn k (S : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := hk x hx
    have hy' := hk y hy
    rw [hxy] at hx'
    have heq : (x : ℤ) = y := by linarith
    exact_mod_cast heq
  have hσ : 0 < ((q : ℝ) / H)⁻¹ :=
    inv_pos.mpr (div_pos (by exact_mod_cast hq) (by exact_mod_cast hH))
  calc
    _ = ∑ x ∈ S, (g ((((q : ℝ) / H)⁻¹)⁻¹ *
        ((a : ℝ) * ((r : ℝ) ^ 2 - t) / q + k x))).re := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [delta_periodic_root_index_argument hq hH t x r (k x) (hk x hx)]
    _ ≤ _ := sum_periodized_samples_le_re g hσ hg _ S k hinj

lemma deltaPeriodicSquareDensity_re (g : 𝓢(ℝ, ℂ)) (a q t : ℕ) (σ : ℝ) :
    (deltaPeriodicSquareDensity g a q t σ).re =
      (q : ℝ)⁻¹ * ∑ r : Fin q, (periodizedSchwartz g σ
        ((a : ℝ) * (((r : ℕ) : ℝ) ^ 2 - t) / q)).re := by
  have hcoeff : (q : ℂ)⁻¹ = (((q : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  unfold deltaPeriodicSquareDensity
  rw [hcoeff, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact map_sum Complex.reCLM _ Finset.univ

theorem delta_complete_roots_le_periodic_density (g : 𝓢(ℝ, ℂ))
    {a u b q H : ℕ} (hq : 0 < q) (hH : 0 < H) (hab : a * u = b * q + 1)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℕ) (Y : Finset ℕ) :
    (q : ℝ)⁻¹ * (∑ x ∈ Y, (squareRootCount q (t + u * x) : ℝ) * (g ((x : ℝ) / H)).re) ≤
      (deltaPeriodicSquareDensity g a q t (((q : ℝ) / H)⁻¹)).re := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [deltaPeriodicSquareDensity_re, root_count_weighted_sum_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro r hr
  simpa only [Int.cast_natCast] using
    delta_selected_roots_le_periodized_weight g hq hH hab hg t Y (r : ℕ)

end Erdos587
