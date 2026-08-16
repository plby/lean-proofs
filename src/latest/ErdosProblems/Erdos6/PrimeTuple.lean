import ErdosProblems.Erdos6.LargeKCandidate
import BoundedGaps.Maynard.Distribution

/-!
# The large powers-of-two tuple

This file transports the explicit variational candidate to the subtype of a
finite prime-shift tuple and selects an unconditional distribution level with
positive threshold-`3` Maynard main term.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def largePowerTuple : Finset ℕ :=
  (Finset.range largeK).image fun j => 2 ^ (j + 1)

theorem mem_largePowerTuple {h : ℕ} :
    h ∈ largePowerTuple ↔ ∃ j < largeK, h = 2 ^ (j + 1) := by
  simp [largePowerTuple, eq_comm]

theorem largePowerTuple_card : largePowerTuple.card = largeK := by
  rw [largePowerTuple, Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have hp := Nat.pow_right_injective (a := 2) (by omega) hab
  omega

theorem largePowerTuple_admissible :
    BoundedGaps.IsAdmissible largePowerTuple := by
  rw [BoundedGaps.isAdmissible_iff_avoids_residue]
  intro p hp
  by_cases hpTwo : p = 2
  · subst p
    refine ⟨1, by omega, ?_⟩
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    simp [pow_succ]
  · refine ⟨0, hp.pos, ?_⟩
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    intro hmod
    have hdvd : p ∣ 2 ^ (j + 1) := Nat.dvd_of_mod_eq_zero hmod
    have hpDvdTwo : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    exact hpTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpDvdTwo)

noncomputable def largeTupleIndexEquiv :
    largePowerTuple ≃ Fin largeK :=
  Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using largePowerTuple_card)

noncomputable def largeTupleCandidate
    (t : largePowerTuple → ℝ) : ℝ :=
  largeCandidate (fun i => t (largeTupleIndexEquiv.symm i))

theorem largeTupleCandidate_norm_le_one
    (t : largePowerTuple → ℝ) :
    ‖largeTupleCandidate t‖ ≤ 1 := by
  exact largeCandidate_norm_le_one _

theorem largeTupleCandidate_abs_le_one
    (t : largePowerTuple → ℝ) :
    |largeTupleCandidate t| ≤ 1 := by
  simpa only [Real.norm_eq_abs] using largeTupleCandidate_norm_le_one t

theorem exists_largeCandidate_level_delta_with_positive_mainTerm
    (hBV : BoundedGaps.Maynard.bombieriVinogradov) :
    ∃ theta delta : ℝ,
      0 < theta ∧ theta < 1 / 2 ∧
      BoundedGaps.Maynard.hasPrimeLevel theta ∧
      0 < delta ∧ delta < theta / 2 ∧
      0 < (theta / 2 - delta) *
          (∑ m : Fin largeK,
            BoundedGaps.Maynard.maynardJ largeK m largeCandidate) -
        3 * BoundedGaps.Maynard.maynardI largeK largeCandidate := by
  let Q := BoundedGaps.Maynard.maynardRatio largeK largeCandidate
  let S := ∑ m : Fin largeK,
    BoundedGaps.Maynard.maynardJ largeK m largeCandidate
  let I := BoundedGaps.Maynard.maynardI largeK largeCandidate
  have hQ : (12 : ℝ) < Q := maynardRatio_largeCandidate_gt_twelve
  have hQpos : 0 < Q := by linarith
  have hI : 0 < I := maynardI_largeCandidate_pos
  have hS : S = Q * I := by
    change S = (S / I) * I
    exact (div_mul_cancel₀ S hI.ne').symm
  have hSpos : 0 < S := by rw [hS]; positivity
  let theta : ℝ := 1 / 4 + 3 / Q
  have htheta0 : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaHalf : theta < 1 / 2 := by
    have hinv : Q⁻¹ < (12 : ℝ)⁻¹ := by
      exact (inv_lt_inv₀ hQpos (by norm_num)).2 hQ
    have hthree : 3 / Q < (1 : ℝ) / 4 := by
      rw [div_eq_mul_inv]
      norm_num at hinv ⊢
      nlinarith
    dsimp [theta]
    linarith
  have hlevel : BoundedGaps.Maynard.hasPrimeLevel theta :=
    hBV theta htheta0 hthetaHalf
  have hthreshold : 3 < theta * Q / 2 := by
    dsimp [theta]
    field_simp [hQpos.ne']
    nlinarith
  have hgap : 0 < (theta / 2) * S - 3 * I := by
    rw [hS]
    nlinarith [mul_pos (sub_pos.mpr hthreshold) hI]
  let gap := (theta / 2) * S - 3 * I
  let delta := gap / (2 * S)
  have hdelta0 : 0 < delta := by
    exact div_pos hgap (mul_pos (by norm_num) hSpos)
  have hdeltaTheta : delta < theta / 2 := by
    dsimp [delta, gap]
    rw [div_lt_iff₀ (mul_pos (by norm_num) hSpos)]
    nlinarith
  refine ⟨theta, delta, htheta0, hthetaHalf, hlevel,
    hdelta0, hdeltaTheta, ?_⟩
  have heq : (theta / 2 - delta) * S - 3 * I = gap / 2 := by
    dsimp [delta]
    field_simp [hSpos.ne']
    ring
  rw [show (∑ m : Fin largeK,
      BoundedGaps.Maynard.maynardJ largeK m largeCandidate) = S by rfl,
    show BoundedGaps.Maynard.maynardI largeK largeCandidate = I by rfl,
    heq]
  exact div_pos hgap (by norm_num)

end

end Erdos6.Maynard
