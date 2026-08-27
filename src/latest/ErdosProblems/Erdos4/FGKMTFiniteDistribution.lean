import ErdosProblems.Erdos4.FGKMTExcisedSmallMass

/-! A finite averaged progression bound, with all three error terms explicit. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

noncomputable def excisedCenteredSum (x Q B : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B), maxCenteredProgressionDiscrepancyUpTo x q

theorem excisedCenteredSum_le_character_mass (x Q B : ℕ) (hx : 2 ≤ x) :
    excisedCenteredSum x Q B ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 + excisedCharacterMass x Q B := by
  unfold excisedCenteredSum
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B),
        (Real.log ((q * x : ℕ) : ℝ) ^ 2 + (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMaximum x q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive hx
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    _ = (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B),
        Real.log ((q * x : ℕ) : ℝ) ^ 2) + excisedCharacterMass x Q B := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ (∑ q ∈ Finset.Icc 1 Q, Real.log ((q * x : ℕ) : ℝ) ^ 2) + excisedCharacterMass x Q B :=
      add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun q _hq _hnot => sq_nonneg _)) le_rfl
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      have hpoint : ∀ q ∈ Finset.Icc 1 Q,
          Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤ Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
        intro q hq
        have hqb := Finset.mem_Icc.mp hq
        have hqxp : 0 < q * x := Nat.mul_pos (by omega) (by omega)
        have hlog0 := Real.log_natCast_nonneg (q * x)
        have hlog : Real.log ((q * x : ℕ) : ℝ) ≤ Real.log ((Q * x : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hqxp)
          (by exact_mod_cast Nat.mul_le_mul_right x hqb.2)
        exact pow_le_pow_left₀ hlog0 hlog 2
      calc
        _ ≤ ∑ _q ∈ Finset.Icc 1 Q, Real.log ((Q * x : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hpoint
        _ = _ := by simp [nsmul_eq_mul]

theorem excised_distribution_bound (x Q R B : ℕ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ d : ℕ, 1 < d → d ≤ R → d.Coprime B →
      ∀ ψ : primitiveCharacters d, primitiveCenteredEndpointMaximum x d ψ ≤ E) :
    excisedCenteredSum x Q B ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        4 * (R : ℝ) * (1 + Real.log (Q : ℝ)) * E +
        (5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)) *
          vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
            vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  have hfirst := excisedCenteredSum_le_character_mass x Q B (by omega)
  have hsplit := excisedCharacterMass_le_split x Q R B
  have hsmall := excisedSmallMass_le_of_endpoint x Q R B hE
    (fun d hd hdR hdB => hpoint d hd (hdR.trans (min_le_left _ _)) hdB)
  have hlarge := largeConductorCenteredMass_le_abelEnvelope x Q R hx hQsqrt hR hRQ
  linarith

/-- The omitted prime is selected before the endpoint. This form is ready
for an exponential conductor cutoff and a fixed power level of distribution. -/
theorem exists_excised_distribution_envelope :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
      ∀ R : ℕ, 2 ≤ R → ∃ B : ℕ, B ≤ R ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x Q : ℕ, X₀ ≤ x → R ≤ Q → (Q : ℝ) ≤ Real.sqrt (x : ℝ) →
          (R : ℝ) ≤ Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) →
          excisedCenteredSum x Q B ≤
            (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
              4 * (R : ℝ) * (1 + Real.log (Q : ℝ)) *
                (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) +
              (5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)) *
                vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
                  vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  obtain ⟨C, c, hC, hc, X₀, hX₀, hmax⟩ := exists_uniform_primitive_maximum
  refine ⟨C, c, hC, hc, X₀, hX₀, ?_⟩
  intro R hR
  obtain ⟨B, hBR, hB, hbound⟩ := hmax R hR
  refine ⟨B, hBR, hB, ?_⟩
  intro x Q hx hRQ hQsqrt hRheight
  exact excised_distribution_bound x Q R B (hX₀.trans hx) hQsqrt (by omega) hRQ
    (by positivity) (hbound x hx hRheight)

end Erdos4.FGKMT
