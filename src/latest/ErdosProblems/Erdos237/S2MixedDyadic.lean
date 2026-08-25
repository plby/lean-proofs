import ErdosProblems.Erdos237.MixedProductWeights
import ErdosProblems.Erdos237.DyadicBox
import ErdosProblems.Erdos237.S2ExtraCoordinate

/-!
# The finite mixed product model for the S2 lower bound

The two inner coordinates have linear dyadic masses. The other coordinates
have square masses and their total upper endpoint is cut off at one half.
-/

namespace Erdos237

open Finset
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def s2IsInner {H K : Finset ℕ} (e : K ≃ Option H) (m : H) (i : K) : Prop :=
  e i = none ∨ e i = some m

noncomputable def s2MixedMass {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (L k : ℕ) (i : K) (a : Fin L) : ℝ :=
  if s2IsInner e m i then dyadicLinearMass L k a else dyadicSquareMass L k a

noncomputable def s2MixedCost {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (L k : ℕ) (i : K) (a : Fin L) : ℝ :=
  if s2IsInner e m i then 0 else dyadicUpper L k a

theorem sum_extraCoordinate {H K : Finset ℕ} (e : K ≃ Option H) (f : K → ℝ) :
    (∑ i : K, f i) = f (e.symm none) + ∑ h : H, f (e.symm (some h)) := by
  rw [← e.symm.sum_comp f, univ_option, sum_insertNone]

theorem sum_s2Outer_constant {H K : Finset ℕ} (e : K ≃ Option H) (m : H) (c : ℝ) :
    (∑ i : K, if s2IsInner e m i then 0 else c) = ((univ.erase m).card : ℝ) * c := by
  classical
  rw [sum_extraCoordinate e]
  simp only [s2IsInner, Equiv.apply_symm_apply, true_or, ↓reduceIte,
    Option.some_ne_none, false_or, Option.some.injEq, zero_add]
  rw [← sum_erase_add _ _ (mem_univ m)]
  simp only [↓reduceIte, add_zero]
  calc
    _ = ∑ _h ∈ univ.erase m, c := by
      apply sum_congr rfl
      intro h hh
      exact if_neg (mem_erase.mp hh).1
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem prod_s2Inner_constant {H K : Finset ℕ} (e : K ≃ Option H) (m : H) (a b : ℝ) :
    (∏ i : K, if s2IsInner e m i then a else b) = a ^ 2 * b ^ (univ.erase m).card := by
  classical
  rw [← e.symm.prod_comp (fun i => if s2IsInner e m i then a else b),
    univ_option, prod_insertNone]
  simp only [s2IsInner, Equiv.apply_symm_apply, true_or, ↓reduceIte,
    Option.some_ne_none, false_or, Option.some.injEq]
  have hp : (∏ h : H, if h = m then a else b) = a * b ^ (univ.erase m).card := by
    rw [← mul_prod_erase _ _ (mem_univ m)]
    simp only [↓reduceIte]
    congr 1
    calc
      _ = ∏ _h ∈ univ.erase m, b := by
        apply prod_congr rfl
        intro h hh
        exact if_neg (mem_erase.mp hh).1
      _ = _ := prod_const _
  rw [hp]
  ring

theorem s2MixedMass_nonneg {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (L k : ℕ) (i : K) (a : Fin L) : 0 ≤ s2MixedMass e m L k i a := by
  unfold s2MixedMass dyadicLinearMass dyadicSquareMass dyadicHeight dyadicLength
  split_ifs <;> positivity

theorem s2MixedCost_nonneg {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    (L k : ℕ) (i : K) (a : Fin L) : 0 ≤ s2MixedCost e m L k i a := by
  unfold s2MixedCost
  split_ifs
  · rfl
  · exact dyadicUpper_nonneg L k a

theorem s2MixedMass_normalizer_pos {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {L k : ℕ} (hL : 0 < L) (hk : 0 < k) (i : K) :
    0 < ∑ a, s2MixedMass e m L k i a := by
  by_cases hi : s2IsInner e m i
  · simp only [s2MixedMass, if_pos hi, dyadicLinearMass]
    rw [sum_dyadicHeight_mul_length hL hk]
    positivity
  · simpa only [s2MixedMass, if_neg hi] using sum_dyadicSquareMass_pos hL hk

theorem s2MixedCost_mean {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    (∑ i, ∑ a, s2MixedCost e m L k i a *
      (s2MixedMass e m L k i a / ∑ b, s2MixedMass e m L k i b)) =
      ((univ.erase m).card : ℝ) * ∑ a, dyadicUpper L k a * dyadicProbability L a := by
  have hlocal (i : K) :
      (∑ a, s2MixedCost e m L k i a *
        (s2MixedMass e m L k i a / ∑ b, s2MixedMass e m L k i b)) =
      if s2IsInner e m i then 0 else ∑ a, dyadicUpper L k a * dyadicProbability L a := by
    by_cases hi : s2IsInner e m i
    · simp [s2MixedCost, hi]
    · simp only [s2MixedCost, s2MixedMass, if_neg hi, dyadicSquareMass_normalized hL hk]
  simp_rw [hlocal]
  exact sum_s2Outer_constant e m _

theorem dyadic_mixed_mass_lower_bound {H K : Finset ℕ} (e : K ≃ Option H) (m : H)
    {L k : ℕ} (hL : 0 < L) (hk : 0 < k) (hcard : Fintype.card H ≤ k) :
    (∑ a, dyadicLinearMass L k a) ^ 2 *
        (∑ a, dyadicSquareMass L k a) ^ (univ.erase m).card / 2 ≤
      ∑ x : K → Fin L,
        if (∑ i, s2MixedCost e m L k i (x i)) ≤ 1 / 2
        then ∏ i, s2MixedMass e m L k i (x i) else 0 := by
  have hmean : (∑ i, ∑ a, s2MixedCost e m L k i a *
      (s2MixedMass e m L k i a / ∑ b, s2MixedMass e m L k i b)) ≤ 1 / 4 := by
    rw [s2MixedCost_mean e m hL hk]
    exact dyadic_mean_le_quarter hL hk ((card_erase_le).trans (by simpa using hcard))
  have h := mixed_product_mass_lower_bound (s2MixedMass e m L k) (s2MixedCost e m L k)
    (s2MixedMass_nonneg e m L k) (s2MixedCost_nonneg e m L k)
    (s2MixedMass_normalizer_pos e m hL hk) hmean
  have hnorm (i : K) : (∑ a, s2MixedMass e m L k i a) =
      if s2IsInner e m i then ∑ a, dyadicLinearMass L k a else ∑ a, dyadicSquareMass L k a := by
    by_cases hi : s2IsInner e m i <;> simp [s2MixedMass, hi]
  simp_rw [hnorm] at h
  rwa [prod_s2Inner_constant e m] at h

end Erdos237
