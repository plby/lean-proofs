/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTEffectiveEndpointMaximum

/-!
# The retained small-conductor mass has an effective exponential saving

Primitive-character counting cancels the conductor totient. The conductor
cutoff grows exponentially in the square root of the endpoint logarithm,
with one excluded prime chosen before all eligible endpoints.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def coprimePrimitiveCenteredMass (B Q x : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Ioc 1 Q).filter (fun d => d.Coprime B), (d.totient : ℝ)⁻¹ *
    ∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi

theorem coprimePrimitiveCenteredMass_nonneg (B Q x : ℕ) :
    0 ≤ coprimePrimitiveCenteredMass B Q x := by
  exact Finset.sum_nonneg fun d _ => mul_nonneg (by positivity)
    (sum_primitiveCenteredEndpointMaximum_nonneg x d)

theorem coprimePrimitiveCenteredMass_le_of_endpoint {B Q x : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ d : ℕ, 1 < d → d ≤ Q → d.Coprime B →
      ∀ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi ≤ H) :
    coprimePrimitiveCenteredMass B Q x ≤ (Q : ℝ) * H := by
  have hterm (d : ℕ) (hd : d ∈ (Finset.Ioc 1 Q).filter (fun d => d.Coprime B)) :
      (d.totient : ℝ)⁻¹ *
        (∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi) ≤ H := by
    obtain ⟨hdI, hcop⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdQ⟩ := Finset.mem_Ioc.mp hdI
    have hdpos : 0 < d := by omega
    have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hdpos
    have hmass : (∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi) ≤
        (d.totient : ℝ) * H := by
      calc
        _ ≤ ∑ _psi : primitiveCharacters d, H :=
          Finset.sum_le_sum fun psi _ => hbound d hd1 hdQ hcop psi
        _ = (Fintype.card (primitiveCharacters d) : ℝ) * H := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_primitiveCharacters_le_totient hdpos) hH
    calc
      _ ≤ (d.totient : ℝ)⁻¹ * ((d.totient : ℝ) * H) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := inv_mul_cancel_left₀ hphi.ne' H
  have hcard : ((Finset.Ioc 1 Q).filter (fun d => d.Coprime B)).card ≤ Q :=
    (Finset.card_filter_le _ _).trans (by simp only [Nat.card_Ioc]; omega)
  calc
    _ ≤ ∑ _d ∈ (Finset.Ioc 1 Q).filter (fun d => d.Coprime B), H :=
      Finset.sum_le_sum hterm
    _ = (((Finset.Ioc 1 Q).filter (fun d => d.Coprime B)).card : ℝ) * H := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hH

theorem exists_exceptionalPrime_smallConductorMass_bound :
    ∃ C a c : ℝ, 0 < C ∧ 0 < a ∧ 0 < c ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ Q : ℕ, 2 ≤ Q → ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x → (Q : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
          coprimePrimitiveCenteredMass B Q x ≤
            C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C, c0, hC, hc0, X0, hX0, hendpoint⟩ :=
    exists_exceptionalPrime_effective_endpointMaximum_bound
  let a : ℝ := min (1 / 4) (c0 / 2)
  let c : ℝ := c0 / 2
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hac : a ≤ c0 / 2 := min_le_right _ _
  have haQuarter : a ≤ (1 / 4 : ℝ) := min_le_left _ _
  refine ⟨C, a, c, hC, ha, by dsimp [c]; positivity, X0, hX0, ?_⟩
  intro Q hQ
  obtain ⟨B, hBpos, hBQ, hB, hbound⟩ := hendpoint Q hQ
  refine ⟨B, hBpos, hBQ, hB, ?_⟩
  intro x hx hQexp
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hQheight : (Q : ℝ) ^ 2 ≤ Real.exp (u / 2) := by
    calc
      _ ≤ (Real.exp (a * u)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQexp 2
      _ = Real.exp (2 * a * u) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_monotone (by nlinarith)
  have hmass := coprimePrimitiveCenteredMass_le_of_endpoint (by positivity)
    (hbound x hx hQheight)
  have hdecay : Real.exp (a * u) * Real.exp (-c0 * u) ≤ Real.exp (-c * u) := by
    rw [← Real.exp_add]
    apply Real.exp_monotone
    dsimp [c]
    nlinarith
  calc
    _ ≤ (Q : ℝ) * (C * ((x : ℝ) * Real.exp (-c0 * u))) := hmass
    _ ≤ Real.exp (a * u) * (C * ((x : ℝ) * Real.exp (-c0 * u))) :=
      mul_le_mul_of_nonneg_right hQexp (by positivity)
    _ = C * ((x : ℝ) * (Real.exp (a * u) * Real.exp (-c0 * u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg x)) hC.le

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.coprimePrimitiveCenteredMass_le_of_endpoint
#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_smallConductorMass_bound
