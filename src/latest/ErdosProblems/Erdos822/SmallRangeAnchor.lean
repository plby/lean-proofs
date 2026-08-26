/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallAnchorDivisorMass

/-! # Summing all small rough divisors around one GIL anchor -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def smallRoughDivisors (N m' : ℕ) : Finset ℕ :=
  (roughPart (shiftedTotient m') (b1Cutoff N)).divisors.filter (fun h ↦ h ≤ N ^ 3)

noncomputable def smallGcdSingularAnchorTerm (N m m' U : ℕ) : ℝ :=
  if m ≠ m' ∧ (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      shiftedCoefficientGcd m m' ≤ N ^ 3 then
    ((shiftedCoefficientGcd m m' : ℝ) / m) *
      Erdos851.singularFactor (reducedTotientDet m m') 2 U else 0

theorem smallGcdSingularAnchorTerm_nonneg (N m m' U : ℕ) :
    0 ≤ smallGcdSingularAnchorTerm N m m' U := by
  unfold smallGcdSingularAnchorTerm
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · rfl

theorem smallGcdSingularAnchorTerm_le_divisor_sum {N S m m' U : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ gilCofactors N S C) (hm' : m' ∈ gilCofactors N S C) :
    smallGcdSingularAnchorTerm N m m' U ≤
      ∑ h ∈ smallRoughDivisors N m', ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
        (if m ∈ smallSupportedDivisorCofactors N S C m' h then
          ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U else 0) := by
  have hnonneg (h : ℕ) : 0 ≤ ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
      (if m ∈ smallSupportedDivisorCofactors N S C m' h then
        ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U else 0) := by
    split_ifs
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (singularFactor_nonneg _ _ _))
    · simp
  unfold smallGcdSingularAnchorTerm
  split_ifs with hcond
  · let g := shiftedCoefficientGcd m m'
    let h := roughPart g (b1Cutoff N)
    have hmpos' := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm')
    have hsne : shiftedTotient m' ≠ 0 := by dsimp [shiftedTotient]; omega
    have hgdiv : g ∣ shiftedTotient m' := Nat.gcd_dvd_right _ _
    have hgpos : 0 < g := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right hsne)
    have hhmem : h ∈ smallRoughDivisors N m' := Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨roughPart_dvd_roughPart_of_dvd hsne hgdiv, roughPart_ne_zero _ _⟩,
        (Nat.le_of_dvd hgpos (roughPart_dvd g (b1Cutoff N))).trans hcond.2.2⟩
    have hmfiber : m ∈ smallSupportedDivisorCofactors N S C m' h :=
      Finset.mem_filter.mpr ⟨hm, hcond.1, hcond.2.1, roughPart_dvd g (b1Cutoff N)⟩
    have heq := gil_gcd_eq_anchor_smooth_mul_rough hN hm hm' hcond.2.1
    have hsingle := Finset.single_le_sum (s := smallRoughDivisors N m')
      (f := fun j ↦ ((smoothPart m' (b1Cutoff N) : ℝ) * j) *
        (if m ∈ smallSupportedDivisorCofactors N S C m' j then
          ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U else 0))
      (fun j hj ↦ hnonneg j) hhmem
    rw [if_pos hmfiber] at hsingle
    calc
      _ = ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
          (((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U) := by
        conv_lhs => rw [heq]
        push_cast
        ring
      _ ≤ _ := hsingle
  · exact Finset.sum_nonneg fun h hh ↦ hnonneg h

theorem exists_eventually_smallGcdSingularAnchor_sum_bound {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ m' U : ℕ,
      m' ∈ gilCofactors N S C → Nat.log 2 N ≤ U →
      (∑ m ∈ gilCofactors N S C, smallGcdSingularAnchorTerm N m m' U) ≤ K * Real.log (N : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_small_anchor_divisor_mass_bound hS C
  let E := Real.exp (4 * (C + 2))
  refine ⟨K * E, by dsimp [E]; positivity, ?_⟩
  filter_upwards [hbound, eventually_gilCofactors_rough_divisor_euler_bound hS C,
    eventually_ge_atTop 2] with N hbound hEuler hN
  intro m' U hm' hLU
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hmass : (∑ h ∈ smallRoughDivisors N m', (4 : ℝ) ^ h.primeFactors.card / h) ≤ E := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h hh hnot ↦ by positivity)).trans (hEuler m' hm' (shiftedTotient m') (dvd_refl _))
  calc
    _ ≤ ∑ m ∈ gilCofactors N S C, ∑ h ∈ smallRoughDivisors N m',
        ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
          (if m ∈ smallSupportedDivisorCofactors N S C m' h then
            ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U else 0) :=
      Finset.sum_le_sum fun m hm ↦ smallGcdSingularAnchorTerm_le_divisor_sum hN hm hm'
    _ = ∑ h ∈ smallRoughDivisors N m', ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
        (∑ m ∈ smallSupportedDivisorCofactors N S C m' h,
          ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.mul_sum, ← Finset.sum_filter]
      congr 2
      ext m
      simp only [Finset.mem_filter, smallSupportedDivisorCofactors]
      tauto
    _ ≤ ∑ h ∈ smallRoughDivisors N m', K * Real.log (N : ℝ) * (4 : ℝ) ^ h.primeFactors.card / h := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨hhdiv, hhN⟩ := Finset.mem_filter.mp hh
      have hhpos := Nat.pos_of_mem_divisors hhdiv
      have hhR := (Nat.mem_divisors.mp hhdiv).1
      exact hbound m' h U hm' hhpos hhN (hhR.trans (roughPart_dvd _ _))
        (roughPart_eq_self_of_dvd_roughPart hhR) hLU
    _ = (K * Real.log (N : ℝ)) * ∑ h ∈ smallRoughDivisors N m', (4 : ℝ) ^ h.primeFactors.card / h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ (K * Real.log (N : ℝ)) * E := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_smallGcdSingularAnchor_sum_bound

end Erdos822
