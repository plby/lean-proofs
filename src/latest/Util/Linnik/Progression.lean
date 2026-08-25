import ErdosProblems.Erdos48.EndpointMass
import Util.Linnik.Basic

/-!
# From primitive endpoint mass to a prime in the class one

This finite reduction retains the global Chebyshev main term and removes
higher prime powers.  The analytic estimates are supplied separately.
-/

namespace Linnik

open Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

theorem inducingEndpointMass_le_fullFamily
    {x q : ℕ} (hq : 0 < q) :
    (∑ chi : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMass x q chi) ≤
      ∑ d ∈ Finset.Ioc 1 q, primitiveEndpointMass x d := by
  apply (inducingPrimitiveEndpointMass_le_divisorMass x hq).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hd, hd₁⟩ := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_mem_divisors hd
    exact Finset.mem_Ioc.mpr ⟨by omega, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  · intro d _ _
    exact primitiveEndpointMass_nonneg x d

theorem totient_mul_thetaProgression_lower
    {x q a : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) (ha : a.Coprime q) :
    Chebyshev.psi (x : ℝ) - (∑ d ∈ Finset.Ioc 1 q, primitiveEndpointMass x d) -
      (q : ℝ) * (Real.log ((q * x : ℕ) : ℝ) ^ 2 +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) ≤
      (q.totient : ℝ) * thetaProgressionSum x q a := by
  have hphi : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hdisc := abs_chebyshevProgressionSum_sub_global_le_log_sq_add_primitive_average hx hq ha
  have hmass := inducingEndpointMass_le_fullFamily (x := x) (by omega : 0 < q)
  have hlower := (abs_le.mp hdisc).1
  have hmul := mul_le_mul_of_nonneg_left hlower hphi.le
  have hcancel : (q.totient : ℝ) * (Chebyshev.psi (x : ℝ) / q.totient) =
      Chebyshev.psi (x : ℝ) := by field_simp
  have hcancel' : (q.totient : ℝ) * ((q.totient : ℝ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMass x q chi) =
      ∑ chi : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMass x q chi := by field_simp
  change (∑ chi : DirichletCharacter ℂ q,
    ‖centeredTwistedChebyshevSum x chi.conductor chi.primitiveCharacter‖) ≤ _ at hmass
  have hpp := progressionPrimePowerRemainder_le_psi_sub_theta x q a
  have hppmul := mul_le_mul_of_nonneg_left hpp hphi.le
  have hsplit := chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder x q a
  have hphiq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have herr₀ : 0 ≤ Real.log ((q * x : ℕ) : ℝ) ^ 2 +
      (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
    exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
  have hphibound := mul_le_mul_of_nonneg_right hphiq herr₀
  dsimp [inducingPrimitiveCenteredEndpointMass] at hcancel'
  nlinarith

theorem exists_prime_of_thetaProgression_pos {x q : ℕ}
    (hpos : 0 < thetaProgressionSum x q 1) :
    ∃ p : ℕ, p.Prime ∧ q ∣ p - 1 ∧ p ≤ x := by
  have hex : ∃ p ∈ primesInProgression x q 1, 0 < Real.log (p : ℝ) := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_nonpos h
    exact not_le_of_gt hpos hsum
  obtain ⟨p, hp, _⟩ := hex
  obtain ⟨hpx, hp, hmod⟩ := mem_primesInProgression.mp hp
  have hcong : Nat.ModEq q p 1 := hmod
  exact ⟨p, hp, hcong.symm.dvd', hpx⟩

end Linnik
