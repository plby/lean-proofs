/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoprimeConductorSplit
import BoundedGaps.BombieriVinogradov.Analytic.LargeConductorMassBound

/-!
# Effective centered progression envelope on the retained moduli

The exact character reduction, coprime conductor split, and unconditional
large-conductor Vaughan estimate are composed before selecting their scales.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def coprimeCenteredDiscrepancySum (B L x : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B),
    maxCenteredProgressionDiscrepancyUpTo x q

theorem sum_coprime_moduli_logSq_le (B L x : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B),
      Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤
      (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 := by
  let S := (Finset.Icc 1 L).filter (fun q => q.Coprime B)
  have hpoint (q : ℕ) (hq : q ∈ S) :
      Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤ Real.log ((L * x : ℕ) : ℝ) ^ 2 := by
    have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    have hprod : 0 < q * x := Nat.mul_pos hqI.1 (by omega)
    have hlog : Real.log ((q * x : ℕ) : ℝ) ≤ Real.log ((L * x : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hprod)
      (by exact_mod_cast Nat.mul_le_mul_right x hqI.2)
    exact pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog 2
  have hcard : S.card ≤ L := (Finset.card_filter_le _ _).trans (by simp)
  calc
    _ ≤ ∑ _q ∈ S, Real.log ((L * x : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

theorem coprimeCenteredDiscrepancySum_le_log_add_inducing
    (B L x : ℕ) (hx : 2 ≤ x) :
    coprimeCenteredDiscrepancySum B L x ≤
      (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 + coprimeInducingCenteredMass B L x := by
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B),
        (Real.log ((q * x : ℕ) : ℝ) ^ 2 + (q.totient : ℝ)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMaximum x q chi) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive hx
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (sum_coprime_moduli_logSq_le B L x hx) le_rfl

theorem coprimeCenteredDiscrepancySum_le_small_add_large (B L R x : ℕ) (hx : 2 ≤ x) :
    coprimeCenteredDiscrepancySum B L x ≤
      (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
        (4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x +
          largeConductorCenteredMass x L R := by
  calc
    _ ≤ _ := coprimeCenteredDiscrepancySum_le_log_add_inducing B L x hx
    _ ≤ (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
        ((4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x +
          largeConductorCenteredMass x L R) :=
      add_le_add le_rfl (coprimeInducingCenteredMass_le_log_small_add_large B L R x)
    _ = _ := by ring

theorem coprimeCenteredDiscrepancySum_le_vaughan (B L R x : ℕ) (hx : 4 ≤ x)
    (hL : (L : ℝ) ≤ Real.sqrt (x : ℝ)) (hR : 1 ≤ R) (hRL : R ≤ L) :
    coprimeCenteredDiscrepancySum B L x ≤
      (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
        (4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x +
          (5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)) *
            vaughanPrimitiveMeanAbelEnvelope x R L *
              vaughanPrimitiveMeanEquationOneTwoLogPower x :=
  (coprimeCenteredDiscrepancySum_le_small_add_large B L R x (by omega)).trans
    (add_le_add le_rfl (largeConductorCenteredMass_le_abelEnvelope x L R hx hL hR hRL))

theorem exists_exceptionalPrime_centeredEnvelope_bound :
    ∃ C a c : ℝ, 0 < C ∧ 0 < a ∧ 0 < c ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ R : ℕ, 2 ≤ R → ∃ B : ℕ, 1 ≤ B ∧ B ≤ R ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x → (R : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
          ∀ L : ℕ, R ≤ L → (L : ℝ) ≤ Real.sqrt (x : ℝ) →
            coprimeCenteredDiscrepancySum B L x ≤
              (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
                (4 * (1 + Real.log (L : ℝ))) *
                  (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) +
                    (5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)) *
                      vaughanPrimitiveMeanAbelEnvelope x R L *
                        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  obtain ⟨C, a, c, hC, ha, hc, X0, hX0, hsmall⟩ :=
    exists_exceptionalPrime_smallConductorMass_bound
  refine ⟨C, a, c, hC, ha, hc, X0, hX0, ?_⟩
  intro R hR
  obtain ⟨B, hBpos, hBR, hB, hmass⟩ := hsmall R hR
  refine ⟨B, hBpos, hBR, hB, ?_⟩
  intro x hx hRexp L hRL hL
  have hlogL := Real.log_natCast_nonneg L
  apply (coprimeCenteredDiscrepancySum_le_vaughan B L R x (hX0.trans hx) hL
    (by omega) hRL).trans
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hmass x hx hRexp) (by positivity))) le_rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.coprimeCenteredDiscrepancySum_le_vaughan
#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_centeredEnvelope_bound
