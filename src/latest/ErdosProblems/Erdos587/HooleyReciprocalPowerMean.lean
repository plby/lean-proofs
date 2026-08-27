import ErdosProblems.Erdos587.HooleyReciprocalGoodDenominators
import ErdosProblems.Erdos587.HooleyReciprocalSmallDenominators
import ErdosProblems.Erdos587.HooleyReciprocalMargin

/-! # The reciprocal arithmetic mean in the power-separated range -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_reciprocal_majorant_power_mean (a c r : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q v X D : ℕ, 0 < q → q.Coprime v → 2 ≤ X → q ≤ X → 2 ^ D ≤ X →
      ∀ (A : ℕ → ℤ) (K R : ℝ),
      1 ≤ K → 0 < R → K ≤ 2 ^ D → (2 : ℝ) ^ D ≤ 2 * K → (a : ℝ) * K < q →
      (a : ℝ) * v * K + 16 * c * q * R ≤ X → K * (X : ℝ) ^ (3 / (r : ℝ)) ≤ R →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - (a : ℤ) * v) →
      (∀ x ∈ S, |deltaReciprocalFrequencyError c A x| ≤ 2 / ((x.denominator : ℝ) * K)) →
      (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨C₀, hC₀, hlarge⟩ := exists_delta_reciprocal_good_denominators_bound a c r ha hc hr
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_delta_reciprocal_small_denominators_bound (inv_pos.mpr hrR)
  obtain ⟨C₂, hC₂, hmargin⟩ := exists_delta_reciprocal_margin_bound r hr
  refine ⟨C₀ + C₁ * C₂, by positivity, ?_⟩
  intro q v X D hq hcop hX hqX hDX A K R hK hR hKD hDK hqa hvalue hsep
    S hlow hupp hden hrel herror
  let Y := deltaProgressionCutoff r X
  let F := (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7
  let G := S.filter (fun x => (Y : ℝ) ≤ 2 * c * R * x.denominator / K ^ 2)
  let T := S.filter (fun x => ¬(Y : ℝ) ≤ 2 * c * R * x.denominator / K ^ 2)
  have hG := hlarge q v X D Y hq hcop hX hqX
    (deltaProgressionCutoff_ge_sixteen r X) (deltaProgressionCutoff_power hr X)
    A K R hK hR hKD hDK hqa hvalue G
    (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
    (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
    (fun x hx => hden x (Finset.mem_filter.mp hx).1)
    (fun x hx => hrel x (Finset.mem_filter.mp hx).1)
    (fun x hx => herror x (Finset.mem_filter.mp hx).1) (fun x hx => (Finset.mem_filter.mp hx).2)
  have hT := hsmall a c q v X D Y ha hc hcop A K R hK hR hKD hDK hqa hvalue T
    (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
    (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
    (fun x hx => hden x (Finset.mem_filter.mp hx).1)
    (fun x hx => hrel x (Finset.mem_filter.mp hx).1)
    (fun x hx => herror x (Finset.mem_filter.mp hx).1)
    (fun x hx => lt_of_not_ge (Finset.mem_filter.mp hx).2)
  have hE := hmargin X D (by omega) hDX K R (by linarith) hsep
  have hF : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
  have hT' : (∑ x ∈ T, deltaReciprocalMajorant K c A x) ≤ C₁ * C₂ * R * K * F := by
    calc
      _ ≤ C₁ * (K ^ 2 * (Y + 2) * (D + 3) * (X : ℝ) ^ (r : ℝ)⁻¹) :=
        hT.trans_eq (by ring)
      _ ≤ C₁ * (C₂ * R * K) := mul_le_mul_of_nonneg_left hE hC₁.le
      _ = C₁ * C₂ * R * K := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hF
  calc
    _ = (∑ x ∈ G, deltaReciprocalMajorant K c A x) +
        ∑ x ∈ T, deltaReciprocalMajorant K c A x := by
      dsimp only [G, T]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ C₀ * R * K * F + C₁ * C₂ * R * K * F := add_le_add hG hT'
    _ = _ := by dsimp only [F]; ring

end Erdos587
