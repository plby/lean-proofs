import ErdosProblems.Erdos587.AlternativeMain
import ErdosProblems.Erdos587.PeriodizedPositivity

/-!
# Complete roots inside the alternative main term

Each selected root congruence supplies a distinct periodization index.
Nonnegative weights allow these terms to be retained as a lower bound.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma exists_period_index_of_square_congruence {a u b v : ℕ}
    (hab : a * u = b * v + 1) (t y : ℕ) (r : ℤ)
    (hroot : r ^ 2 ≡ (t : ℤ) + v * y [ZMOD u]) :
    ∃ k : ℤ, (y : ℤ) + b * (r ^ 2 - t) + u * k = 0 := by
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hroot
  have habZ : (a : ℤ) * u = b * v + 1 := by exact_mod_cast hab
  refine ⟨(b : ℤ) * d - a * y, ?_⟩
  linear_combination -(b : ℤ) * hd - (y : ℤ) * habZ

lemma alternative_period_index_argument {a u b v H : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hH : 0 < H) (hab : a * u = b * v + 1)
    (t y : ℕ) (r k : ℤ) (z : ℝ)
    (hk : (y : ℤ) + b * (r ^ 2 - t) + u * k = 0) :
    (((v : ℝ) / H)⁻¹)⁻¹ * (alternativeRootArgument a u b v t r z + k) =
      (z ^ 2 - t - (v : ℝ) * y) / (u * H) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have habR : (a : ℝ) * u = b * v + 1 := by exact_mod_cast hab
  have hkR : (y : ℝ) + b * ((r : ℝ) ^ 2 - t) + u * k = 0 := by exact_mod_cast hk
  have harg : alternativeRootArgument a u b v t r z + k =
      (z ^ 2 - t - (v : ℝ) * y) / (u * v) := by
    unfold alternativeRootArgument
    field_simp
    linear_combination (v : ℝ) * hkR - (t : ℝ) * habR
  rw [harg, inv_inv]
  field_simp

theorem selected_roots_le_periodized_weight (g : 𝓢(ℝ, ℂ))
    {a u b v H : ℕ} (hu : 0 < u) (hv : 0 < v) (hH : 0 < H) (hab : a * u = b * v + 1)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℕ) (Y : Finset ℕ) (r : ℤ) (z : ℝ) :
    (∑ y ∈ Y.filter (fun y : ℕ => r ^ 2 ≡ (t : ℤ) + v * (y : ℤ) [ZMOD u]),
      (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) ≤
      (periodizedSchwartz g (((v : ℝ) / H)⁻¹) (alternativeRootArgument a u b v t r z)).re := by
  classical
  let S := Y.filter (fun y : ℕ => r ^ 2 ≡ (t : ℤ) + v * (y : ℤ) [ZMOD u])
  have hex (y : ℕ) : ∃ k : ℤ, y ∈ S → (y : ℤ) + b * (r ^ 2 - t) + u * k = 0 := by
    by_cases hy : y ∈ S
    · obtain ⟨k, hk⟩ := exists_period_index_of_square_congruence hab t y r (Finset.mem_filter.mp hy).2
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  choose k hk using hex
  have hinj : Set.InjOn k (S : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := hk x hx
    have hy' := hk y hy
    rw [hxy] at hx'
    have heq : (x : ℤ) = y := by linarith
    exact_mod_cast heq
  have hσ : 0 < ((v : ℝ) / H)⁻¹ :=
    inv_pos.mpr (div_pos (by exact_mod_cast hv) (by exact_mod_cast hH))
  calc
    _ = ∑ y ∈ S, (g ((((v : ℝ) / H)⁻¹)⁻¹ *
        (alternativeRootArgument a u b v t r z + k y))).re := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [alternative_period_index_argument hu hv hH hab t y r (k y) z (hk y hy)]
    _ ≤ _ := sum_periodized_samples_le_re g hσ hg _ S k hinj

lemma squareRootCount_eq_sum_fin_modEq (u n : ℕ) [NeZero u] :
    squareRootCount u n = ∑ r : Fin u,
      if ((r : ℕ) : ℤ) ^ 2 ≡ (n : ℤ) [ZMOD u] then (1 : ℕ) else 0 := by
  classical
  rw [squareRootCount_eq_card, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => if (r : ℤ) ^ 2 ≡ (n : ℤ) [ZMOD u] then (1 : ℕ) else 0)]
  calc
    _ = ∑ r ∈ Finset.range u, if (r : ZMod u) ^ 2 = (n : ZMod u) then (1 : ℕ) else 0 :=
      (sum_range_natCast_zmod u (fun z => if z ^ 2 = (n : ZMod u) then (1 : ℕ) else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hiff : ((r : ZMod u) ^ 2 = (n : ZMod u)) ↔ ((r : ℤ) ^ 2 ≡ (n : ℤ) [ZMOD u]) := by
        have h := ZMod.intCast_eq_intCast_iff ((r : ℤ) ^ 2) (n : ℤ) u
        norm_cast at h ⊢
      simp only [hiff]

lemma squareRootCount_eq_sum_fin_modEq_real (u n : ℕ) [NeZero u] :
    (squareRootCount u n : ℝ) = ∑ r : Fin u,
      if ((r : ℕ) : ℤ) ^ 2 ≡ (n : ℤ) [ZMOD u] then (1 : ℝ) else 0 := by
  exact_mod_cast squareRootCount_eq_sum_fin_modEq u n

lemma root_count_weighted_sum_eq (u v t : ℕ) [NeZero u] (Y : Finset ℕ) (w : ℕ → ℝ) :
    (∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) * w y) =
      ∑ r : Fin u, ∑ y ∈ Y.filter
        (fun y : ℕ => ((r : ℕ) : ℤ) ^ 2 ≡ (t : ℤ) + v * (y : ℤ) [ZMOD u]), w y := by
  classical
  simp_rw [squareRootCount_eq_sum_fin_modEq_real, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Nat.cast_add, Nat.cast_mul, ite_mul, one_mul, zero_mul]

theorem complete_roots_le_alternative_periods (g : 𝓢(ℝ, ℂ))
    {a u b v H : ℕ} (hu : 0 < u) (hv : 0 < v) (hH : 0 < H) (hab : a * u = b * v + 1)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℕ) (Y : Finset ℕ) (z : ℝ) :
    (∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) *
      (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) ≤
      ∑ r : Fin u, (periodizedSchwartz g (((v : ℝ) / H)⁻¹)
        (alternativeRootArgument a u b v t (r : ℕ) z)).re := by
  letI : NeZero u := ⟨hu.ne'⟩
  rw [root_count_weighted_sum_eq]
  apply Finset.sum_le_sum
  intro r hr
  exact selected_roots_le_periodized_weight g hu hv hH hab hg t Y (r : ℕ) z

end Erdos587
