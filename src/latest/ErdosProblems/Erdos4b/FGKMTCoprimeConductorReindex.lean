/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSmallConductorMass
import BoundedGaps.BombieriVinogradov.Analytic.AllModulusConductorSplit

/-!
# Exact conductor reindexing on moduli coprime to the excluded prime

The coprimality condition remains on the full product modulus. Only the
proved-zero centered conductor-one fiber is removed from the finite identity.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def coprimeInducingCenteredMass (B L x : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B), (q.totient : ℝ)⁻¹ *
    ∑ chi : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMaximum x q chi

theorem coprimeInducingCenteredMass_eq_factorPairs (B L x : ℕ) :
    coprimeInducingCenteredMass B L x =
      ∑ p ∈ (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B ∧ p.1 ≠ 1),
        ((p.1 * p.2).totient : ℝ)⁻¹ *
          ∑ psi : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 psi := by
  classical
  have hindex : Finset.Icc 1 L = Finset.Ioc 0 L := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  let F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → ℝ :=
    fun {q d} _ psi => (q.totient : ℝ)⁻¹ * primitiveCenteredEndpointMaximum x d psi
  let G : ℕ × ℕ → ℝ := fun p => ((p.1 * p.2).totient : ℝ)⁻¹ *
    ∑ psi : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 psi
  have hleft : coprimeInducingCenteredMass B L x =
      ∑ q ∈ (Finset.Ioc 0 L).filter (fun q => q.Coprime B),
        ∑ d : q.divisors, ∑ psi : primitiveCharacters d.1,
          F (Nat.dvd_of_mem_divisors d.2) psi := by
    rw [coprimeInducingCenteredMass, hindex]
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
    rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors hqpos, Finset.mul_sum]
    apply Fintype.sum_congr
    intro d
    rw [Finset.mul_sum]
  have hreindex := sum_primitive_conductors_up_to_filter_eq_sum_positiveFactorPairs
    (Q := L) (fun q => q.Coprime B) F
  have hright :
      (∑ p ∈ (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B),
        ∑ psi : primitiveCharacters p.1, F (Nat.dvd_mul_right p.1 p.2) psi) =
      ∑ p ∈ (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B), G p := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (Finset.mul_sum _ _ _).symm
  have hfilter :
      (∑ p ∈ (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B ∧ p.1 ≠ 1),
        G p) =
      ∑ p ∈ (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B), G p := by
    apply Finset.sum_subset
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2.1⟩
    · intro p hp hnot
      have hp1 : p.1 = 1 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
          (Finset.mem_filter.mp hp).2, hne⟩)
      dsimp [G]
      rw [hp1, sum_primitiveCenteredEndpointMaximum_one, mul_zero]
  exact hleft.trans (hreindex.trans (hright.trans hfilter.symm))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.coprimeInducingCenteredMass_eq_factorPairs
