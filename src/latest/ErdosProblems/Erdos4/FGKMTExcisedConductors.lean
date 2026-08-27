import ErdosProblems.Erdos4.FGKMTUniformMaxima
import BoundedGaps.BombieriVinogradov.Analytic.SmallConductorMassBound
import BoundedGaps.BombieriVinogradov.Analytic.LargeConductorMassBound

/-! Conductor decomposition with the exceptional prime omitted. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem weighted_character_mass_reindex (x Q : ℕ) (w : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMaximum x q χ) =
    ∑ p ∈ (positiveFactorPairs Q).filter (fun p => p.1 ≠ 1),
      w (p.1 * p.2) * ∑ ψ : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 ψ := by
  classical
  have hindex : Finset.Icc 1 Q = Finset.Ioc 0 Q := by ext q; simp; omega
  let F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → ℝ :=
    fun {q d} _ ψ => w q * primitiveCenteredEndpointMaximum x d ψ
  let G : ℕ × ℕ → ℝ := fun p => w (p.1 * p.2) *
    ∑ ψ : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 ψ
  have hleft : (∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMaximum x q χ) =
      ∑ q ∈ Finset.Ioc 0 Q, ∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1,
        F (Nat.dvd_of_mem_divisors d.2) ψ := by
    rw [hindex]
    apply Finset.sum_congr rfl
    intro q hq
    rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors (Finset.mem_Ioc.mp hq).1]
    simp only [F, Finset.mul_sum]
  have hreindex := sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs (Q := Q) F
  have hright : (∑ p ∈ positiveFactorPairs Q,
      ∑ ψ : primitiveCharacters p.1, F (Nat.dvd_mul_right p.1 p.2) ψ) =
      ∑ p ∈ positiveFactorPairs Q, G p := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (Finset.mul_sum _ _ _).symm
  have hfilter : (∑ p ∈ (positiveFactorPairs Q).filter (fun p => p.1 ≠ 1), G p) =
      ∑ p ∈ positiveFactorPairs Q, G p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hp1 : p.1 = 1 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hp, hne⟩)
    unfold G
    rw [hp1, sum_primitiveCenteredEndpointMaximum_one, mul_zero]
  exact hleft.trans (hreindex.trans (hright.trans hfilter.symm))

noncomputable def excisedCharacterMass (x Q B : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B), (q.totient : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMaximum x q χ

noncomputable def excisedSmallMass (x Q R B : ℕ) : ℝ :=
  ∑ p ∈ (positiveFactorPairs Q).filter (fun p => p.1 ≠ 1 ∧ p.1 ≤ R ∧ p.1.Coprime B),
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 ψ

theorem excisedCharacterMass_reindex (x Q B : ℕ) :
    excisedCharacterMass x Q B =
      ∑ p ∈ (positiveFactorPairs Q).filter (fun p => p.1 ≠ 1),
        (if (p.1 * p.2).Coprime B then ((p.1 * p.2).totient : ℝ)⁻¹ else 0) *
          ∑ ψ : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 ψ := by
  classical
  rw [← weighted_character_mass_reindex x Q
    (fun q => if q.Coprime B then (q.totient : ℝ)⁻¹ else 0)]
  unfold excisedCharacterMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hc : q.Coprime B
  · simp only [if_pos hc]
  · simp only [if_neg hc, zero_mul]

theorem excisedCharacterMass_le_split (x Q R B : ℕ) :
    excisedCharacterMass x Q B ≤ excisedSmallMass x Q R B + largeConductorCenteredMass x Q R := by
  classical
  rw [excisedCharacterMass_reindex]
  unfold excisedSmallMass largeConductorCenteredMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _hp
  have hn : 0 ≤ ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 ψ :=
    mul_nonneg (by positivity) (sum_primitiveCenteredEndpointMaximum_nonneg x p.1)
  by_cases hd : p.1 ≠ 1
  · by_cases hc : (p.1 * p.2).Coprime B
    · have hdc : p.1.Coprime B := Nat.Coprime.of_dvd_left (Nat.dvd_mul_right _ _) hc
      by_cases hR : p.1 ≤ R
      · have hlo : p.1 ≠ 1 ∧ p.1 ≤ R ∧ p.1.Coprime B := ⟨hd, hR, hdc⟩
        have hhi : ¬(p.1 ≠ 1 ∧ R < p.1) := fun hh => (not_lt_of_ge hR) hh.2
        simp only [if_pos hd, if_pos hc, if_pos hlo, if_neg hhi, add_zero, le_refl]
      · have hlt : R < p.1 := lt_of_not_ge hR
        have hlo : ¬(p.1 ≠ 1 ∧ p.1 ≤ R ∧ p.1.Coprime B) := fun hh => hR hh.2.1
        have hhi : p.1 ≠ 1 ∧ R < p.1 := ⟨hd, hlt⟩
        simp only [if_pos hd, if_pos hc, if_neg hlo, if_pos hhi, zero_add, le_refl]
    · simp only [if_pos hd, if_neg hc, zero_mul]
      split_ifs <;> linarith
  · have hlo : ¬(p.1 ≠ 1 ∧ p.1 ≤ R ∧ p.1.Coprime B) := fun hh => hd hh.1
    have hhi : ¬(p.1 ≠ 1 ∧ R < p.1) := fun hh => hd hh.1
    simp only [if_neg hd, if_neg hlo, if_neg hhi, zero_add, le_refl]

end Erdos4.FGKMT
