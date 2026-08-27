import ErdosProblems.Erdos587.HooleyAffineSchwartz
import ErdosProblems.Erdos587.HooleySmoothConjugate
import ErdosProblems.Erdos587.HooleyReciprocalMean

/-!
# Full reciprocal means for varying Fresnel profiles

Compact affine changes of the uniformly Schwartz profiles permit direct use
of the smooth mean, with no partial summation or additional logarithm.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_fresnel_affine_quadratic_sum (f : 𝓢(ℝ, ℂ)) (P u α θ : ℝ)
    {δ K : ℝ} (hδ : δ ≠ 0) (hK : K ≠ 0) :
    deltaSmoothQuadraticSum (deltaAffineSchwartz (deltaFresnelSchwartz f P) u (δ * K))
        K α θ =
      ∑' n : ℤ, fresnelProfile f P (u + δ * n) *
        phase (α * (n : ℝ) ^ 2 + θ * n) := by
  unfold deltaSmoothQuadraticSum
  apply tsum_congr
  intro n
  rw [deltaAffineSchwartz_apply _ _ (mul_ne_zero hδ hK), deltaFresnelSchwartz_apply]
  have heq : u + δ * K * (K⁻¹ * (n : ℝ)) = u + δ * n := by field_simp
  rw [heq, mul_comm]

theorem exists_delta_fresnel_reciprocal_sq_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q v X : ℕ, 0 < q → q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ (A : ℕ → ℤ) (K R : ℝ), 1 ≤ K → 0 < R → 2 * K ≤ X →
      (a : ℝ) * K < q → (a : ℝ) * v * K + 16 * c * q * R ≤ X →
      K * (X : ℝ) ^ κ ≤ R →
      ∀ I : Finset ℕ, (∀ m ∈ I, R < m ∧ (m : ℝ) ≤ 2 * R) →
      (∀ m ∈ I, ((c * m : ℕ) : ℤ) ∣ (q : ℤ) * A m - (a : ℤ) * v) →
      ∀ (f : ℕ → 𝓢(ℝ, ℂ)) (P u δ θ : ℕ → ℝ), (∀ m ∈ I, f m ∈ W) →
      (∀ m ∈ I, 1 ≤ P m) → (∀ m ∈ I, |u m| ≤ 1) →
      (∀ m ∈ I, 1 / 2 ≤ δ m * K ∧ δ m * K ≤ 2) →
      (∑ m ∈ I, ‖∑' n : ℤ, fresnelProfile (f m) (P m) (u m + δ m * n) *
        phase (-((A m : ℝ) / (c * m : ℕ)) * (n : ℝ) ^ 2 + θ m * n)‖ ^ 2) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  let V := deltaAffineSchwartzFamily (Set.image2 deltaFresnelSchwartz W (Set.Ici 1))
  have hV : Bornology.IsVonNBounded ℝ V :=
    delta_bounded_affineSchwartzFamily (delta_bounded_fresnelProfiles hW)
  obtain ⟨C, hC, hmean⟩ :=
    exists_delta_smooth_reciprocal_mean (delta_bounded_conjugates hV) a c ha hc hκ
  refine ⟨C, hC, ?_⟩
  intro q v X hq hcop hX hqX A K R hK hR hKX hqa hvalue hsep I hI hrel
    f P u δ θ hf hP hu hscale
  have hKpos : 0 < K := by linarith
  let g (m : ℕ) := deltaAffineSchwartz (deltaFresnelSchwartz (f m) (P m)) (u m) (δ m * K)
  have hg (m : ℕ) (hm : m ∈ I) : g m ∈ V := by
    refine ⟨deltaFresnelSchwartz (f m) (P m), ⟨f m, hf m hm, P m, hP m hm, rfl⟩,
      u m, δ m * K, hu m hm, (hscale m hm).1, (hscale m hm).2, rfl⟩
  have h := hmean q v X hq hcop hX hqX A K R hK hR hKX hqa hvalue hsep I hI hrel
    (fun m => conjugateSchwartz (g m)) (fun m => -θ m)
    (fun m hm => ⟨g m, hg m hm, rfl⟩)
  apply le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro m hm
  have hδ : δ m ≠ 0 := by
    intro hz
    have ht := (hscale m hm).1
    rw [hz, zero_mul] at ht
    norm_num at ht
  rw [← delta_fresnel_affine_quadratic_sum (f m) (P m) (u m) _ _ hδ hKpos.ne',
    deltaSmoothQuadraticSum_norm_negative]

end Erdos587
