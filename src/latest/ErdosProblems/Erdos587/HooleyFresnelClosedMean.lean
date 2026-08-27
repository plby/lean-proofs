import ErdosProblems.Erdos587.HooleyFresnelMean

/-! # Reciprocal profile means on closed denominator blocks -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_fresnel_reciprocal_closed_sq_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q v X : ℕ, 0 < q → q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ (A : ℕ → ℤ) (K R : ℝ), 1 ≤ K → 0 < R → 2 * K ≤ X →
      (a : ℝ) * K < q → (a : ℝ) * v * K + 16 * c * q * R ≤ X →
      2 * K * (X : ℝ) ^ κ ≤ R →
      ∀ I : Finset ℕ, (∀ m ∈ I, R ≤ m ∧ (m : ℝ) ≤ 2 * R) →
      (∀ m ∈ I, ((c * m : ℕ) : ℤ) ∣ (q : ℤ) * A m - (a : ℤ) * v) →
      ∀ (f : ℕ → 𝓢(ℝ, ℂ)) (P u δ θ : ℕ → ℝ), (∀ m ∈ I, f m ∈ W) →
      (∀ m ∈ I, 1 ≤ P m) → (∀ m ∈ I, |u m| ≤ 1) →
      (∀ m ∈ I, 1 / 2 ≤ δ m * K ∧ δ m * K ≤ 2) →
      (∑ m ∈ I, ‖∑' n : ℤ, fresnelProfile (f m) (P m) (u m + δ m * n) *
        phase (-((A m : ℝ) / (c * m : ℕ)) * (n : ℝ) ^ 2 + θ m * n)‖ ^ 2) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_delta_fresnel_reciprocal_sq_mean hW a c ha hc hκ
  refine ⟨2 * C, by positivity, ?_⟩
  intro q v X hq hcop hX hqX A K R hK hR hKX hqa hvalue hsep I hI hrel
    f P u δ θ hf hP hu hscale
  let I₀ := I.filter fun m : ℕ => (m : ℝ) ≤ R
  let I₁ := I.filter fun m : ℕ => ¬(m : ℝ) ≤ R
  have hsub₀ : I₀ ⊆ I := Finset.filter_subset _ _
  have hsub₁ : I₁ ⊆ I := Finset.filter_subset _ _
  have hI₀ : ∀ m ∈ I₀, R / 2 < m ∧ (m : ℝ) ≤ 2 * (R / 2) := by
    intro m hm
    have hb := (hI m (hsub₀ hm)).1
    have ht := (Finset.mem_filter.mp hm).2
    constructor <;> linarith
  have hI₁ : ∀ m ∈ I₁, R < m ∧ (m : ℝ) ≤ 2 * R := by
    intro m hm
    exact ⟨lt_of_not_ge (Finset.mem_filter.mp hm).2, (hI m (hsub₁ hm)).2⟩
  have hvalue₀ : (a : ℝ) * v * K + 16 * c * q * (R / 2) ≤ X := by
    apply le_trans _ hvalue
    gcongr
    linarith
  have hsep₀ : K * (X : ℝ) ^ κ ≤ R / 2 := by linarith
  have hsep₁ : K * (X : ℝ) ^ κ ≤ R := by linarith
  have h₀ := hmean q v X hq hcop hX hqX A K (R / 2) hK (by positivity)
    hKX hqa hvalue₀ hsep₀ I₀ hI₀ (fun m hm => hrel m (hsub₀ hm))
    f P u δ θ (fun m hm => hf m (hsub₀ hm)) (fun m hm => hP m (hsub₀ hm))
    (fun m hm => hu m (hsub₀ hm)) (fun m hm => hscale m (hsub₀ hm))
  have h₁ := hmean q v X hq hcop hX hqX A K R hK hR
    hKX hqa hvalue hsep₁ I₁ hI₁ (fun m hm => hrel m (hsub₁ hm))
    f P u δ θ (fun m hm => hf m (hsub₁ hm)) (fun m hm => hP m (hsub₁ hm))
    (fun m hm => hu m (hsub₁ hm)) (fun m hm => hscale m (hsub₁ hm))
  have hsum := add_le_add h₀ h₁
  rw [Finset.sum_filter_add_sum_filter_not] at hsum
  apply hsum.trans
  have hz : 0 ≤ C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by positivity
  nlinarith

end Erdos587
