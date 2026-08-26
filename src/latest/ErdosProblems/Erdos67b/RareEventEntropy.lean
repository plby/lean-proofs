import ErdosProblems.Erdos67b.Entropy

/-!
# Entropy control of exponentially rare events

The entropy decrement gives information small relative to the number of
primes, not necessarily small in absolute value.  A Pinsker error therefore
does not suffice.  Exponential tilting instead bounds the probability of
a rare event by the entropy deficit divided by its logarithmic rarity.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.FiniteEntropy

theorem negMulLog_le_crossEntropy {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -(x * Real.log y) - x + y := by
  by_cases hx0 : x = 0
  · simp [hx0, hy.le]
  · have hkl := correctedKLTerm_nonneg hx hy.le (fun _ ↦ hy)
    rw [correctedKLTerm, Real.log_div hx0 hy.ne'] at hkl
    unfold Real.negMulLog
    nlinarith

/-- The logarithmic cardinality bound, needed to make block entropy grow
linearly with block length rather than with the size of its full range. -/
theorem entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : FinProb α) : entropy p ≤ Real.log (Fintype.card α) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦
    negMulLog_le_crossEntropy (prob_nonneg p a) (one_div_pos.mpr hN))
  change entropy p ≤ _ at hsum
  simpa [Real.log_inv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, stdSimplex.sum_eq_one, hN.ne'] using hsum

/-- The entropy-deficit bound with a harmless constant `1`.  The hypothesis
is an exponential cardinality bound, and the conclusion remains useful
even when the entropy deficit itself tends to infinity. -/
theorem rare_event_mass_mul_le_entropy_deficit
    {α : Type*} [Fintype α] [Nonempty α]
    (p : FinProb α) (E : Finset α) (L : ℝ)
    (hrare : (E.card : ℝ) * Real.exp L ≤ Fintype.card α) :
    (∑ a ∈ E, p a) * L ≤
      Real.log (Fintype.card α) - entropy p + 1 := by
  classical
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let w : α → ℝ := fun a ↦
    (if a ∈ E then Real.exp L else 1) / N
  have hw (a : α) : 0 < w a := by
    dsimp [w]
    split_ifs <;> positivity
  have hlog (a : α) :
      Real.log (w a) = (if a ∈ E then L else 0) - Real.log N := by
    by_cases ha : a ∈ E
    · simp [w, ha, Real.log_div (Real.exp_ne_zero L) hN.ne']
    · simp [w, ha]
  have hweight : ∑ a, w a ≤ 2 := by
    have hpoint (a : α) :
        w a ≤ 1 / N + if a ∈ E then Real.exp L / N else 0 := by
      by_cases ha : a ∈ E
      · simp only [w, if_pos ha]
        linarith [one_div_pos.mpr hN]
      · simp [w, ha]
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ hpoint a)
    have hsum' : ∑ a, w a ≤ 1 + (E.card : ℝ) * Real.exp L / N := by
      simpa [Finset.sum_add_distrib, N, mul_div_assoc, hN.ne'] using hsum
    have hratio : (E.card : ℝ) * Real.exp L / N ≤ 1 :=
      (div_le_one hN).2 hrare
    linarith
  have hcross : entropy p ≤
      ∑ a, (-(p a * Real.log (w a)) - p a + w a) := by
    apply Finset.sum_le_sum
    intro a _
    exact negMulLog_le_crossEntropy (prob_nonneg p a) (hw a)
  have hpoint (a : α) :
      -(p a * Real.log (w a)) - p a + w a =
        p a * Real.log N -
          (if a ∈ E then p a * L else 0) - p a + w a := by
    rw [hlog]
    split_ifs <;> ring
  simp_rw [hpoint] at hcross
  have hcross' : entropy p ≤
      Real.log N - (∑ a ∈ E, p a) * L - 1 + ∑ a, w a := by
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, stdSimplex.sum_eq_one] using hcross
  dsimp only [N] at hcross'
  linarith

theorem mul_negMulLog_div {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 < y) :
    y * Real.negMulLog (x / y) = Real.negMulLog x + x * Real.log y := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [Real.negMulLog, Real.log_div hx0 hy.ne', Real.negMulLog]
    field_simp
    ring

/-- The rowwise form does not need a conditional law at a zero-mass row. -/
theorem rare_joint_row_mass_mul_le
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : FinProb (α × β)) (a : α) (E : Finset β) (L : ℝ)
    (hrare : (E.card : ℝ) * Real.exp L ≤ Fintype.card β) :
    (∑ b ∈ E, p (a, b)) * L ≤
      fstMarginal p a * Real.log (Fintype.card β) -
        (∑ b, Real.negMulLog (p (a, b))) +
        Real.negMulLog (fstMarginal p a) + fstMarginal p a := by
  classical
  let r := fstMarginal p a
  have hr : 0 ≤ r := prob_nonneg (fstMarginal p) a
  by_cases hr0 : r = 0
  · have hzero (b : β) : p (a, b) = 0 := by
      have hle := joint_le_fstMarginal p a b
      change p (a, b) ≤ r at hle
      exact le_antisymm (hr0 ▸ hle) (prob_nonneg p (a, b))
    change _ ≤ r * _ - _ + Real.negMulLog r + r
    simp [hzero, hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let q : FinProb β := ⟨fun b ↦ p (a, b) / r, by
      constructor
      · intro b
        exact div_nonneg (prob_nonneg p (a, b)) hr
      · rw [← Finset.sum_div, ← fstMarginal_apply]
        exact div_self hr0⟩
    have hbound := rare_event_mass_mul_le_entropy_deficit q E L hrare
    have hscaled := mul_le_mul_of_nonneg_left hbound hr
    have hmass : r * (∑ b ∈ E, q b) = ∑ b ∈ E, p (a, b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_div_cancel₀ _ hr0
    have hentropy : r * entropy q =
        (∑ b, Real.negMulLog (p (a, b))) - Real.negMulLog r := by
      unfold entropy
      rw [Finset.mul_sum]
      change (∑ b, r * Real.negMulLog (p (a, b) / r)) = _
      simp_rw [mul_negMulLog_div (prob_nonneg p _) hrpos]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← fstMarginal_apply]
      change _ + r * Real.log r = _ - Real.negMulLog r
      simp [Real.negMulLog]
    change _ ≤ r * _ - _ + Real.negMulLog r + r
    rw [← mul_assoc, hmass] at hscaled
    nlinarith

/-- Adaptive exponentially rare events are controlled by mutual
information and the entropy deficit of the second marginal.  This is the
scale-compatible replacement for applying Pinsker to the joint law. -/
theorem rare_joint_event_mass_mul_le_mutualInfo
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : FinProb (α × β)) (E : α → Finset β) (L : ℝ)
    (hrare : ∀ a, ((E a).card : ℝ) * Real.exp L ≤ Fintype.card β) :
    (∑ a, ∑ b ∈ E a, p (a, b)) * L ≤
      mutualInfo p + Real.log (Fintype.card β) -
        entropy (sndMarginal p) + 1 := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦
    rare_joint_row_mass_mul_le p a (E a) L (hrare a))
  have htotal : (∑ a, ∑ b, p (a, b)) = 1 := by
    rw [← Fintype.sum_prod_type]
    exact stdSimplex.sum_eq_one p
  have hsum' : (∑ a, ∑ b ∈ E a, p (a, b)) * L ≤
      Real.log (Fintype.card β) - entropy p + entropy (fstMarginal p) + 1 := by
    simpa [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      stdSimplex.sum_eq_one, entropy, Fintype.sum_prod_type, htotal] using hsum
  unfold mutualInfo
  linarith

end Erdos67b.FiniteEntropy
