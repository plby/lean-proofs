import ErdosProblems.Erdos4.FGKMTExcisedConductors

/-! Summing the uniform small-conductor bound while keeping prime excision. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem excisedSmallMass_eq_sum_multipliers (x Q R B : ℕ) :
    excisedSmallMass x Q R B =
      ∑ d ∈ (Finset.Ioc 1 (min R Q)).filter (fun d => d.Coprime B),
        (∑ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d), ((d * k).totient : ℝ)⁻¹ := by
  classical
  unfold excisedSmallMass
  have hreindex := sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
    (Q := Q) (fun d => d ≠ 1 ∧ d ≤ R ∧ d.Coprime B)
    (fun d k => ((d * k).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ)
  rw [hreindex]
  have hindex : (Finset.Ioc 0 Q).filter (fun d => d ≠ 1 ∧ d ≤ R ∧ d.Coprime B) =
      (Finset.Ioc 1 (min R Q)).filter (fun d => d.Coprime B) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
    omega
  rw [hindex]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [mul_comm]

theorem conductor_multiplier_mass_le (x Q d : ℕ) (hd : 0 < d) (hdQ : d ≤ Q)
    {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ ≤ E) :
    (∑ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ) *
        (∑ k ∈ Finset.Ioc 0 (Q / d), ((d * k).totient : ℝ)⁻¹) ≤
      4 * (1 + Real.log (Q : ℝ)) * E := by
  have hφ : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hQdiv : 0 < Q / d := Nat.div_pos hdQ hd
  have hmass : (∑ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ) ≤
      (d.totient : ℝ) * E := by
    calc
      _ ≤ ∑ _ψ : primitiveCharacters d, E := Finset.sum_le_sum (fun ψ _hψ => hpoint ψ)
      _ = (Fintype.card (primitiveCharacters d) : ℝ) * E := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitiveCharacters_le_totient hd) hE
  have hprefix : (∑ k ∈ Finset.Ioc 0 (Q / d), (k.totient : ℝ)⁻¹) ≤
      4 * (1 + Real.log ((Q / d : ℕ) : ℝ)) := by
    simpa [reciprocalTotientPrefix] using reciprocalTotientPrefix_le_four_mul_one_add_log hQdiv
  have hlogDiv : Real.log ((Q / d : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hQdiv) (by exact_mod_cast Nat.div_le_self Q d)
  have hweight : (∑ k ∈ Finset.Ioc 0 (Q / d), ((d * k).totient : ℝ)⁻¹) ≤
      (d.totient : ℝ)⁻¹ * (4 * (1 + Real.log (Q : ℝ))) := by
    apply (sum_inv_totient_mul_le_inv_totient_mul_sum Q d hd).trans
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hφ.le)
    exact hprefix.trans (by linarith)
  calc
    _ ≤ ((d.totient : ℝ) * E) * ((d.totient : ℝ)⁻¹ * (4 * (1 + Real.log (Q : ℝ)))) :=
      mul_le_mul hmass hweight
        (Finset.sum_nonneg (fun k _hk => inv_nonneg.mpr (Nat.cast_nonneg _)))
        (mul_nonneg hφ.le hE)
    _ = _ := by field_simp

theorem excisedSmallMass_le_of_endpoint (x Q R B : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ d : ℕ, 1 < d → d ≤ min R Q → d.Coprime B →
      ∀ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ ≤ E) :
    excisedSmallMass x Q R B ≤ 4 * (R : ℝ) * (1 + Real.log (Q : ℝ)) * E := by
  rw [excisedSmallMass_eq_sum_multipliers]
  have hbound : 0 ≤ 4 * (1 + Real.log (Q : ℝ)) * E := by
    have hh := Real.log_natCast_nonneg Q
    positivity
  calc
    _ ≤ ∑ _d ∈ (Finset.Ioc 1 (min R Q)).filter (fun d => d.Coprime B),
        4 * (1 + Real.log (Q : ℝ)) * E := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdI, hdB⟩ := Finset.mem_filter.mp hd
      have hd' := Finset.mem_Ioc.mp hdI
      exact conductor_multiplier_mass_le x Q d (by omega) (hd'.2.trans (min_le_right _ _)) hE
        (hpoint d hd'.1 hd'.2 hdB)
    _ ≤ (R : ℝ) * (4 * (1 + Real.log (Q : ℝ)) * E) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hbound
      have hc := Finset.card_filter_le (Finset.Ioc 1 (min R Q)) (fun d => d.Coprime B)
      rw [Nat.card_Ioc] at hc
      have hm := min_le_left R Q
      exact_mod_cast (show ((Finset.Ioc 1 (min R Q)).filter (fun d => d.Coprime B)).card ≤ R by omega)
    _ = _ := by ring

end Erdos4.FGKMT
