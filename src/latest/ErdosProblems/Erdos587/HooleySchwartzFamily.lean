import ErdosProblems.Erdos587.HooleyChirpDecay

/-!
# Uniform chirp estimates for bounded Schwartz families

The product derivative estimate depends on finitely many input seminorms.
Consequently the bounded quadratic multipliers preserve bounded families,
and continuous Fourier operators preserve the resulting bounds.
-/

open scoped FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_family_chirp_seminorm_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ S, ∀ u : ℝ, |u| ≤ 1 →
      SchwartzMap.seminorm ℝ k n (quadraticChirpMul u f) ≤ M := by
  obtain ⟨l, C, hC, hgrowth⟩ := exists_uniform_quadratic_chirp_derivative_bound n
  let P : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (Finset.Iic (l + k, n)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2)
  obtain ⟨M₀, hM₀, hP⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_finset_seminorm_bounded.mp hS
      (Finset.Iic (l + k, n))
  let M : ℝ := 2 ^ (l + k) * M₀
  let B := ContinuousLinearMap.mul ℝ ℂ
  have hM : 0 ≤ M := mul_nonneg (by positivity) hM₀.le
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C * M), by positivity, ?_⟩
  intro f hfS u hu
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  have hcoef : (quadraticChirpMul u f : ℝ → ℂ) =
      fun x : ℝ => B (phase (u * x ^ 2)) (f x) := by
    funext x
    exact quadraticChirpMul_apply u f x
  rw [hcoef]
  have hprod := B.norm_iteratedFDeriv_le_of_bilinear
    (hasTemperateGrowth_quadratic_chirp u).1 (f.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ C * M := by
    intro i hi
    have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
    have hg := hgrowth u hu i hin x
    have hf := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (l + k, n)) (k := l + k) (n := n - i) le_rfl (Nat.sub_le _ _) f x
    have hf' : (1 + ‖x‖) ^ (l + k) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ M := by
      apply hf.trans
      exact mul_le_mul_of_nonneg_left (hP f hfS).le (by positivity)
    have hx : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
    have hg' : ‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ ≤
        C * (1 + ‖x‖) ^ l := by simpa only [Real.norm_eq_abs] using hg
    calc
      ‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
          (1 + ‖x‖) ^ k * ((C * (1 + ‖x‖) ^ l) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        gcongr
      _ = C * ((1 + ‖x‖) ^ (l + k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [pow_add]
        ring
      _ ≤ C * M := mul_le_mul_of_nonneg_left hf' hC
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ => B (phase (u * x ^ 2)) (f x)) x‖ ≤
        ‖x‖ ^ k * (‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) f x‖) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)) := by
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C * M) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _))

theorem delta_bounded_chirps {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) :
    Bornology.IsVonNBounded ℝ (Set.image2 quadraticChirpMul {u : ℝ | |u| ≤ 1} S) := by
  apply (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨k, n⟩
  obtain ⟨M, hM, hbound⟩ := exists_delta_family_chirp_seminorm_bound hS k n
  refine ⟨M + 1, by linarith, ?_⟩
  rintro g ⟨u, hu, f, hf, rfl⟩
  exact (hbound f hf u hu).trans_lt (by linarith)

theorem exists_delta_family_linear_chirp_seminorm_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ S, ∀ u : ℝ, |u| ≤ 1 →
      SchwartzMap.seminorm ℝ k n (T (quadraticChirpMul u f)) ≤ M := by
  obtain ⟨M, hM, hbound⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp
      ((delta_bounded_chirps hS).image T) (k, n)
  refine ⟨M, hM.le, ?_⟩
  intro f hf u hu
  exact (hbound _ ⟨quadraticChirpMul u f, ⟨u, hu, f, hf, rfl⟩, rfl⟩).le

theorem exists_delta_family_fresnelProfile_derivative_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ S, ∀ A : ℝ, 1 ≤ A → ∀ s : ℝ,
      (1 + |s|) ^ k * ‖iteratedDeriv n (fresnelProfile f A) s‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℝ 𝓢(ℝ, ℂ)
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierInvCLM ℝ 𝓢(ℝ, ℂ)
  obtain ⟨M₀, hM₀, hbound₀⟩ := exists_delta_family_linear_chirp_seminorm_bound (hS.image F) T 0 n
  obtain ⟨Mₖ, hMₖ, hboundₖ⟩ := exists_delta_family_linear_chirp_seminorm_bound (hS.image F) T k n
  refine ⟨2 ^ k * (M₀ + Mₖ), by positivity, ?_⟩
  intro f hf A hA s
  have hu : |-1 / (4 * A)| ≤ 1 := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith : 0 < 4 * A)]
    exact (div_le_one₀ (by linarith : 0 < 4 * A)).mpr (by linarith)
  have hfF : 𝓕 f ∈ F '' S := ⟨f, hf, rfl⟩
  let g : 𝓢(ℝ, ℂ) := T (quadraticChirpMul (-1 / (4 * A)) (𝓕 f))
  have hcoef : fresnelProfile f A = (g : ℝ → ℂ) := by
    funext s
    exact fresnelProfile_eq_inverse_fourier f A s
  rw [hcoef]
  have hzero : ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤ M₀ := by
    have h := SchwartzMap.le_seminorm' ℝ 0 n g s
    simp only [pow_zero, one_mul] at h
    exact h.trans (hbound₀ _ hfF _ hu)
  have hpow : |s| ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤ Mₖ :=
    (SchwartzMap.le_seminorm' ℝ k n g s).trans (hboundₖ _ hfF _ hu)
  by_cases hs : |s| ≤ 1
  · calc
      (1 + |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤
          2 ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ := by
        gcongr
        linarith
      _ ≤ 2 ^ k * M₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ 2 ^ k * (M₀ + Mₖ) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hMₖ) (by positivity)
  · have hs' : 1 ≤ |s| := (lt_of_not_ge hs).le
    calc
      (1 + |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤
          (2 * |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ := by
        gcongr
        linarith
      _ = 2 ^ k * (|s| ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ k * Mₖ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 2 ^ k * (M₀ + Mₖ) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM₀) (by positivity)

end Erdos587
