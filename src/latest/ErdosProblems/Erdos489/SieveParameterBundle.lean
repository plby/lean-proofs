import ErdosProblems.Erdos489.PositiveSieveProduct
import ErdosProblems.Erdos489.ParameterSelection
import ErdosProblems.Erdos489.TailMass
import ErdosProblems.Erdos489.QuantitativeCandidateSupply

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators

namespace Erdos489

lemma list_range_prod_eq_finset_prod (f : ℕ → ℝ) (R : ℕ) :
    ((List.range R).map f).prod = ∏ n ∈ Finset.range R, f n := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.map_append, List.prod_append,
      Finset.prod_range_succ, ih]
    simp

lemma sieveDensity_map_range (a : ℕ → ℕ) (R : ℕ) :
    sieveDensity ((List.range R).map a) =
      ∏ n ∈ Finset.range R, (1 - (a n : ℝ)⁻¹) := by
  induction R with
  | zero => simp [sieveDensity]
  | succ R ih =>
    rw [List.range_succ, List.map_append, Finset.prod_range_succ]
    simp only [List.map_singleton]
    rw [show sieveDensity (List.map a (List.range R) ++ [a R]) =
      sieveDensity (List.map a (List.range R)) * (1 - (a R : ℝ)⁻¹) by
        simp [sieveDensity]]
    rw [ih]

/-- All fixed parameters needed by the affine-gap argument can be selected
from positivity and reciprocal summability alone. -/
theorem exists_sieve_parameter_bundle
    (a : ℕ → ℕ) (ha2 : ∀ n, 2 ≤ a n)
    (hs : Summable fun n => ((a n : ℝ)⁻¹)) :
    ∃ ρ : ℝ, ∃ Y Q C R : ℕ,
      0 < ρ ∧ ρ ≤ 1 ∧ 0 < Y ∧ 1 < Q ∧ 0 < C ∧
      (∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) ∧
      (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) ∧
      64 * C ^ 2 ≤ Q ^ 2 * Y ∧
      ρ ≤ sieveDensity ((List.range R).map a) ∧
      (∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
        (∑ r ∈ T, ((a r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) := by
  obtain ⟨ρ, hρpos, hprod⟩ :=
    eventually_pos_le_reciprocal_sieve_product a ha2 hs
  have hρ1 : ρ ≤ 1 := by
    obtain ⟨N, hN⟩ := hprod.exists
    have hle : (∏ n ∈ Finset.range N, (1 - (a n : ℝ)⁻¹)) ≤ 1 := by
      apply Finset.prod_le_one
      · intro n hn
        exact sieveFactor_nonneg (ha2 n)
      · intro n hn
        exact sieveFactor_le_one (a n)
    exact hN.trans hle
  obtain ⟨Y, Q, C, hY, hQ, hC, hsmall, hdensity, hCY⟩ :=
    exists_affine_sieve_parameters ρ hρpos hρ1
  have htailEv := eventually_finset_tail_sum_le_of_summable
    (fun n => ((a n : ℝ)⁻¹)) hs (fun n => by positivity)
    (1 / (C : ℝ)) (by positivity)
  have hboth : ∀ᶠ R : ℕ in atTop,
      ρ ≤ sieveDensity ((List.range R).map a) ∧
      (∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
        (∑ r ∈ T, ((a r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) := by
    filter_upwards [hprod, htailEv] with R hRprod hRtail
    exact ⟨by simpa [sieveDensity_map_range] using hRprod, hRtail⟩
  obtain ⟨R, hRdensity, hRtail⟩ := hboth.exists
  exact ⟨ρ, Y, Q, C, R, hρpos, hρ1, hY, hQ, hC, hsmall,
    hdensity, hCY, hRdensity, hRtail⟩

end Erdos489
