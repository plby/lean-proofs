import ErdosProblems.Erdos587.HooleySchwartzFamily

/-!
# Bounded affine families of Schwartz functions

Translations in a fixed compact interval and dilations bounded away from zero
preserve bounded Schwartz families. The proof gives a uniform bound for each
seminorm; it does not choose a separate major-arc constant for each weight.
-/

open scoped SchwartzMap FourierTransform

namespace Erdos587

noncomputable def deltaAffineSchwartz (f : 𝓢(ℝ, ℂ)) (s δ : ℝ) : 𝓢(ℝ, ℂ) :=
  if h : δ = 0 then 0 else dilateSchwartz (f.compSubConstCLM ℂ (-s)) δ h

lemma deltaAffineSchwartz_apply (f : 𝓢(ℝ, ℂ)) (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    (x : ℝ) : deltaAffineSchwartz f s δ x = f (s + δ * x) := by
  simp only [deltaAffineSchwartz, dif_neg hδ, dilateSchwartz_apply,
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, add_comm]

lemma deltaAffineSchwartz_iteratedDeriv (f : 𝓢(ℝ, ℂ)) (s : ℝ) {δ : ℝ}
    (hδ : δ ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (deltaAffineSchwartz f s δ : ℝ → ℂ) x =
      δ ^ n • iteratedDeriv n (f : ℝ → ℂ) (s + δ * x) := by
  have hcoe : (deltaAffineSchwartz f s δ : ℝ → ℂ) =
      fun x : ℝ => (fun y : ℝ => f (s + y)) (δ * x) := by
    funext x
    exact deltaAffineSchwartz_apply f s hδ x
  rw [hcoe, iteratedDeriv_comp_const_smul (n := n)
    (f := fun y : ℝ => f (s + y))
      ((f.smooth _).comp (contDiff_const.add contDiff_id)) δ,
    iteratedDeriv_comp_const_add]

theorem exists_delta_family_affine_seminorm_bound {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ S, ∀ s δ : ℝ, |s| ≤ 1 →
      1 / 2 ≤ δ → δ ≤ 2 → SchwartzMap.seminorm ℝ k n (deltaAffineSchwartz f s δ) ≤ C := by
  obtain ⟨M, hM, hbound⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_finset_seminorm_bounded.mp hS
      (Finset.Iic (k, n))
  refine ⟨2 ^ k * 2 ^ n * (2 ^ k * M), by positivity, ?_⟩
  intro f hf s δ hs hδlo hδhi
  have hδ : 0 < δ := by linarith
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  rw [deltaAffineSchwartz_iteratedDeriv f s hδ.ne', norm_smul, Real.norm_eq_abs,
    abs_pow, abs_of_pos hδ]
  have hx : |x| ≤ 2 * (1 + |s + δ * x|) := by
    have ht : |δ * x| ≤ |s + δ * x| + |s| := by
      have ht := abs_sub (s + δ * x) s
      simpa only [add_sub_cancel_left] using ht
    rw [abs_mul, abs_of_pos hδ] at ht
    nlinarith [abs_nonneg x]
  have hp : (1 + |s + δ * x|) ^ k *
      ‖iteratedDeriv n (f : ℝ → ℂ) (s + δ * x)‖ ≤ 2 ^ k * M := by
    have ht := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (k, n)) (k := k) (n := n) le_rfl le_rfl f (s + δ * x)
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (hbound f hf).le (by positivity))
  calc
    _ ≤ (2 * (1 + |s + δ * x|)) ^ k *
        (2 ^ n * ‖iteratedDeriv n (f : ℝ → ℂ) (s + δ * x)‖) := by
      gcongr
    _ = (2 ^ k * 2 ^ n) * ((1 + |s + δ * x|) ^ k *
        ‖iteratedDeriv n (f : ℝ → ℂ) (s + δ * x)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

def deltaAffineSchwartzFamily (S : Set 𝓢(ℝ, ℂ)) : Set 𝓢(ℝ, ℂ) :=
  {g | ∃ f ∈ S, ∃ s δ : ℝ, |s| ≤ 1 ∧ 1 / 2 ≤ δ ∧ δ ≤ 2 ∧
    g = deltaAffineSchwartz f s δ}

theorem delta_bounded_affineSchwartzFamily {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) :
    Bornology.IsVonNBounded ℝ (deltaAffineSchwartzFamily S) := by
  apply (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨k, n⟩
  obtain ⟨C, hC, hbound⟩ := exists_delta_family_affine_seminorm_bound hS k n
  refine ⟨C + 1, by linarith, ?_⟩
  rintro g ⟨f, hf, s, δ, hs, hlo, hhi, rfl⟩
  exact (hbound f hf s δ hs hlo hhi).trans_lt (by linarith)

noncomputable def deltaFresnelSchwartz (f : 𝓢(ℝ, ℂ)) (A : ℝ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (quadraticChirpMul (-1 / (4 * A)) (𝓕 f))

lemma deltaFresnelSchwartz_apply (f : 𝓢(ℝ, ℂ)) (A x : ℝ) :
    deltaFresnelSchwartz f A x = fresnelProfile f A x :=
  (fresnelProfile_eq_inverse_fourier f A x).symm

theorem delta_bounded_fresnelProfiles {S : Set 𝓢(ℝ, ℂ)}
    (hS : Bornology.IsVonNBounded ℝ S) :
    Bornology.IsVonNBounded ℝ (Set.image2 deltaFresnelSchwartz S (Set.Ici 1)) := by
  let F : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℝ 𝓢(ℝ, ℂ)
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierInvCLM ℝ 𝓢(ℝ, ℂ)
  apply ((delta_bounded_chirps (hS.image F)).image T).subset
  rintro g ⟨f, hf, A, hA, rfl⟩
  refine ⟨quadraticChirpMul (-1 / (4 * A)) (𝓕 f), ?_, rfl⟩
  refine ⟨-1 / (4 * A), ?_, 𝓕 f, ⟨f, hf, rfl⟩, rfl⟩
  change |-1 / (4 * A)| ≤ 1
  have hA' : 1 ≤ A := hA
  rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith : 0 < 4 * A)]
  exact (div_le_one₀ (by linarith : 0 < 4 * A)).mpr (by linarith)

end Erdos587
