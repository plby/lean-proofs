/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoprimeConductorReindex
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientPrefix

/-!
# Coprime small-conductor lift and unrestricted large-conductor remainder

Only nonnegative summation ranges are enlarged. The small branch retains
conductor coprimality with the excluded prime; the large branch can forget it.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def coprimeSmallConductorLift (B L R x : ℕ) : ℝ :=
  ∑ p ∈ (positiveFactorPairs L).filter (fun p => p.1 ≠ 1 ∧ p.1 ≤ R ∧ p.1.Coprime B),
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ psi : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 psi

theorem coprimeInducingCenteredMass_le_small_add_large (B L R x : ℕ) :
    coprimeInducingCenteredMass B L x ≤
      coprimeSmallConductorLift B L R x + largeConductorCenteredMass x L R := by
  let S := (positiveFactorPairs L).filter (fun p => (p.1 * p.2).Coprime B ∧ p.1 ≠ 1)
  let G : ℕ × ℕ → ℝ := fun p => ((p.1 * p.2).totient : ℝ)⁻¹ *
    ∑ psi : primitiveCharacters p.1, primitiveCenteredEndpointMaximum x p.1 psi
  have hG (p : ℕ × ℕ) : 0 ≤ G p :=
    mul_nonneg (by positivity) (sum_primitiveCenteredEndpointMaximum_nonneg x p.1)
  rw [coprimeInducingCenteredMass_eq_factorPairs]
  change (∑ p ∈ S, G p) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.1 ≤ R) G]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpPairs, hcop, hp1⟩ := Finset.mem_filter.mp hpS
      exact Finset.mem_filter.mpr ⟨hpPairs, hp1, hpR,
        (Nat.coprime_mul_iff_left.mp hcop).1⟩
    · intro p _hp _hnot
      exact hG p
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpPairs, _hcop, hp1⟩ := Finset.mem_filter.mp hpS
      exact Finset.mem_filter.mpr ⟨hpPairs, hp1, lt_of_not_ge hpR⟩
    · intro p _hp _hnot
      exact hG p

theorem coprimeSmallConductorLift_eq_sum_multipliers (B L R x : ℕ) :
    coprimeSmallConductorLift B L R x =
      ∑ d ∈ (Finset.Ioc 1 (min R L)).filter (fun d => d.Coprime B),
        (∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi) *
          ∑ k ∈ Finset.Ioc 0 (L / d), ((d * k).totient : ℝ)⁻¹ := by
  have hreindex := sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
    (Q := L) (fun d => d ≠ 1 ∧ d ≤ R ∧ d.Coprime B)
    (fun d k => ((d * k).totient : ℝ)⁻¹ *
      ∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi)
  have hindex : (Finset.Ioc 0 L).filter (fun d => d ≠ 1 ∧ d ≤ R ∧ d.Coprime B) =
      (Finset.Ioc 1 (min R L)).filter (fun d => d.Coprime B) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [coprimeSmallConductorLift, hreindex, hindex]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact mul_comm _ _

theorem invTotient_multiplierPrefix_le_log {L d : ℕ} (hd : 0 < d) (hdL : d ≤ L) :
    (∑ k ∈ Finset.Ioc 0 (L / d), ((d * k).totient : ℝ)⁻¹) ≤
      (d.totient : ℝ)⁻¹ * (4 * (1 + Real.log (L : ℝ))) := by
  have hdiv := Nat.div_pos hdL hd
  have hprefix := reciprocalTotientPrefix_le_four_mul_one_add_log hdiv
  have hlogDiv : Real.log ((L / d : ℕ) : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdiv) (by exact_mod_cast Nat.div_le_self L d)
  calc
    _ ≤ (d.totient : ℝ)⁻¹ * ∑ k ∈ Finset.Ioc 0 (L / d), (k.totient : ℝ)⁻¹ :=
      sum_inv_totient_mul_le_inv_totient_mul_sum L d hd
    _ ≤ (d.totient : ℝ)⁻¹ * (4 * (1 + Real.log ((L / d : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hprefix (by positivity)
    _ ≤ _ := by gcongr

theorem coprimeSmallConductorLift_le_log_mass (B L R x : ℕ) :
    coprimeSmallConductorLift B L R x ≤
      (4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x := by
  let S := (Finset.Ioc 1 (min R L)).filter (fun d => d.Coprime B)
  have hlogL := Real.log_natCast_nonneg L
  have hsubset : S ⊆ (Finset.Ioc 1 R).filter (fun d => d.Coprime B) := by
    intro d hd
    obtain ⟨hdI, hcop⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdmax⟩ := Finset.mem_Ioc.mp hdI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨hd1, hdmax.trans (min_le_left _ _)⟩, hcop⟩
  rw [coprimeSmallConductorLift_eq_sum_multipliers]
  calc
    _ ≤ ∑ d ∈ S, (4 * (1 + Real.log (L : ℝ))) * ((d.totient : ℝ)⁻¹ *
        ∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      have hweight := invTotient_multiplierPrefix_le_log (by omega : 0 < d)
        (hdI.2.trans (min_le_right _ _))
      calc
        _ ≤ (∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi) *
            ((d.totient : ℝ)⁻¹ * (4 * (1 + Real.log (L : ℝ)))) :=
          mul_le_mul_of_nonneg_left hweight (sum_primitiveCenteredEndpointMaximum_nonneg x d)
        _ = _ := by ring
    _ = (4 * (1 + Real.log (L : ℝ))) *
        ∑ d ∈ S, (d.totient : ℝ)⁻¹ *
          ∑ psi : primitiveCharacters d, primitiveCenteredEndpointMaximum x d psi :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _hd _hnot =>
        mul_nonneg (by positivity) (sum_primitiveCenteredEndpointMaximum_nonneg x d)))
      (by positivity)

theorem coprimeInducingCenteredMass_le_log_small_add_large (B L R x : ℕ) :
    coprimeInducingCenteredMass B L x ≤
      (4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x +
        largeConductorCenteredMass x L R :=
  (coprimeInducingCenteredMass_le_small_add_large B L R x).trans
    (add_le_add (coprimeSmallConductorLift_le_log_mass B L R x) le_rfl)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.coprimeSmallConductorLift_eq_sum_multipliers
#print axioms Erdos4b.FGKMT.coprimeInducingCenteredMass_le_log_small_add_large
