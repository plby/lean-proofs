import ErdosProblems.Erdos1161.CycleRecursion

/-!
# Exact distinguished-cycle recurrence for Erdős Problem 1161

`CycleRecursion` proves the pointed-partition identity.  This file identifies
that identity with the actual uniform order distribution on permutations and
packages the residual event used by the analytic estimates.
-/

open scoped BigOperators Finset

namespace Erdos1161

open Equiv

theorem lcm_completeCycleType {n : ℕ} {mu : Multiset ℕ}
    (_hmu : mu ∈ cycleTypes n) :
    (completeCycleType n mu).lcm = mu.lcm := by
  rw [completeCycleType, Multiset.lcm_add]
  have hones : (Multiset.replicate (n - mu.sum) 1).lcm = 1 := by
    induction n - mu.sum with
    | zero => simp
    | succ k ih => simp [Multiset.replicate_succ, ih]
  rw [hones]
  simp

/-- Number of residual permutations whose order, combined with an exposed
cycle of length `j`, is exactly `m`. -/
def residualOrderCount (r j m : ℕ) : ℕ :=
  cycleTypeEventCount r (fun mu ↦ Nat.lcm mu.lcm j = m)

/-- Exact rational probability of the residual success event. -/
def residualOrderProbability (r j m : ℕ) : ℚ :=
  (residualOrderCount r j m : ℚ) / (r.factorial : ℚ)

theorem residualOrderProbability_eq_completeCycleTypeMass
    (r j m : ℕ) :
    residualOrderProbability r j m =
      completeCycleTypeMass r (fun mu ↦ (j ::ₘ mu).lcm = m) := by
  rw [completeCycleTypeMass_eq_cycleTypeEventProbability]
  unfold residualOrderProbability residualOrderCount
  congr 2
  unfold cycleTypeEventCount
  apply congrArg Finset.card
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Multiset.lcm_cons]
  rw [lcm_completeCycleType (show σ.cycleType ∈ cycleTypes r by
    rw [mem_cycleTypes]
    exact ⟨by simpa using σ.sum_cycleType_le,
      fun a ha ↦ Equiv.Perm.two_le_of_mem_cycleType ha⟩)]
  rw [Equiv.Perm.lcm_cycleType, Nat.lcm_comm]
  change Nat.lcm j (orderOf σ) = m ↔ Nat.lcm j (orderOf σ) = m
  rfl

theorem orderRationalProbability_eq_completeCycleTypeMass (n m : ℕ) :
    (orderCount n m : ℚ) / (n.factorial : ℚ) =
      completeCycleTypeMass n (fun mu ↦ mu.lcm = m) := by
  rw [completeCycleTypeMass_eq_sum_cycleTypes,
    orderCountRationalProbability_eq_sum_cycleWeight]
  have hsets :
      (cycleTypes n).filter
          (fun mu ↦ (completeCycleType n mu).lcm = m) =
        orderCycleTypes n m := by
    ext mu
    rw [mem_orderCycleTypes]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmu, hm⟩
      exact ⟨hmu, by rwa [lcm_completeCycleType hmu] at hm⟩
    · rintro ⟨hmu, hm⟩
      exact ⟨hmu, by rwa [lcm_completeCycleType hmu]⟩
  rw [← Finset.sum_filter]
  rw [hsets]

/-- Exact rational distinguished-cycle recurrence.  The summand indexed by
`r` is the residual event after exposing a cycle of length `n-r`. -/
theorem orderRationalProbability_recursion {n m : ℕ} (hn : 0 < n) :
    (orderCount n m : ℚ) / (n.factorial : ℚ) =
      (1 / n : ℚ) * ∑ r ∈ Finset.range n,
        residualOrderProbability r (n - r) m := by
  rw [orderRationalProbability_eq_completeCycleTypeMass]
  have hrec := completeCycleTypeMass_recursion n (fun mu ↦ mu.lcm = m)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [one_div, inv_mul_eq_div, eq_div_iff hnq]
  rw [mul_comm, hrec]
  apply Finset.sum_bij (fun j _ ↦ n - j)
  · intro j hj
    rw [Finset.mem_range]
    exact Nat.sub_lt (by omega) (Finset.mem_Icc.mp hj).1
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := Finset.mem_Icc.mp hj₁
    have h₂ := Finset.mem_Icc.mp hj₂
    omega
  · intro r hr
    have hrn := Finset.mem_range.mp hr
    refine ⟨n - r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rw [residualOrderProbability_eq_completeCycleTypeMass]
    have hjle := (Finset.mem_Icc.mp hj).2
    simp only [Nat.sub_sub_self hjle]
    rfl

theorem residualOrderProbability_eq_zero_of_not_dvd
    {r j m : ℕ} (hjd : ¬j ∣ m) :
    residualOrderProbability r j m = 0 := by
  have hcount : residualOrderCount r j m = 0 := by
    unfold residualOrderCount cycleTypeEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    apply hjd
    rw [← hσ]
    exact Nat.dvd_lcm_right _ _
  rw [residualOrderProbability, hcount]
  simp

/-- The same recurrence with the automatic condition `n-r ∣ m` made
explicit. -/
theorem orderRationalProbability_recursion_filtered {n m : ℕ} (hn : 0 < n) :
    (orderCount n m : ℚ) / (n.factorial : ℚ) =
      (1 / n : ℚ) * ∑ r ∈ (Finset.range n).filter (fun r ↦ n - r ∣ m),
        residualOrderProbability r (n - r) m := by
  rw [orderRationalProbability_recursion hn]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hrange hrnot
  apply residualOrderProbability_eq_zero_of_not_dvd
  intro hdvd
  apply hrnot
  simp [hrange, hdvd]

/-! ## The residual divisibility bound -/

/-- Number of permutations on `r` letters whose order divides `m`. -/
def orderDvdCount (r m : ℕ) : ℕ :=
  cycleTypeEventCount r (fun mu ↦ mu.lcm ∣ m)

/-- Rational probability that the order of a uniform permutation on `r`
letters divides `m`. -/
def orderDvdProbability (r m : ℕ) : ℚ :=
  (orderDvdCount r m : ℚ) / (r.factorial : ℚ)

theorem orderDvdProbability_eq_completeCycleTypeMass (r m : ℕ) :
    orderDvdProbability r m =
      completeCycleTypeMass r (fun mu ↦ mu.lcm ∣ m) := by
  rw [completeCycleTypeMass_eq_cycleTypeEventProbability]
  unfold orderDvdProbability orderDvdCount
  congr 2
  unfold cycleTypeEventCount
  apply congrArg Finset.card
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lcm_completeCycleType (show σ.cycleType ∈ cycleTypes r by
    rw [mem_cycleTypes]
    exact ⟨by simpa using σ.sum_cycleType_le,
      fun a ha ↦ Equiv.Perm.two_le_of_mem_cycleType ha⟩)]

theorem orderDvdProbability_nonneg (r m : ℕ) :
    0 ≤ orderDvdProbability r m := by
  unfold orderDvdProbability
  positivity

theorem orderDvdProbability_le_one (r m : ℕ) :
    orderDvdProbability r m ≤ 1 := by
  unfold orderDvdProbability orderDvdCount cycleTypeEventCount
  rw [div_le_one (by positivity : (0 : ℚ) < r.factorial)]
  exact_mod_cast (by
    simpa [Fintype.card_perm] using
      Finset.card_filter_le
        (Finset.univ : Finset (Perm (Fin r)))
        (fun σ : Perm (Fin r) ↦ orderOf σ ∣ m))

theorem residualOrderProbability_nonneg (r j m : ℕ) :
    0 ≤ residualOrderProbability r j m := by
  unfold residualOrderProbability
  positivity

theorem residualOrderProbability_le_orderDvdProbability
    (r j m : ℕ) :
    residualOrderProbability r j m ≤ orderDvdProbability r m := by
  unfold residualOrderProbability orderDvdProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (show residualOrderCount r j m ≤ orderDvdCount r m by
      unfold residualOrderCount orderDvdCount cycleTypeEventCount
      apply Finset.card_le_card
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hσ]
      exact Nat.dvd_lcm_left _ _)
  · positivity

theorem orderDvdProbability_mul_eq_sum {r m : ℕ} :
    (r : ℚ) * orderDvdProbability r m =
      ∑ j ∈ Finset.Icc 1 r,
        if j ∣ m then orderDvdProbability (r - j) m else 0 := by
  rw [orderDvdProbability_eq_completeCycleTypeMass]
  rw [completeCycleTypeMass_recursion]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjm : j ∣ m
  · simp only [hjm, if_true]
    rw [orderDvdProbability_eq_completeCycleTypeMass]
    unfold completeCycleTypeMass
    apply Finset.sum_congr rfl
    intro q _
    rw [Multiset.lcm_cons]
    rw [lcm_eq_nat_lcm]
    by_cases hq : q.parts.lcm ∣ m
    · have hlcm : j.lcm q.parts.lcm ∣ m :=
        Nat.lcm_dvd_iff.mpr ⟨hjm, hq⟩
      simp only [hlcm, hq, if_true]
    · have hlcm : ¬j.lcm q.parts.lcm ∣ m := by
        intro h
        exact hq (Nat.lcm_dvd_iff.mp h).2
      simp only [hlcm, hq, if_false]
  · simp only [hjm, if_false]
    apply Finset.sum_eq_zero
    intro q _
    rw [Multiset.lcm_cons]
    rw [lcm_eq_nat_lcm]
    have hlcm : ¬j.lcm q.parts.lcm ∣ m := by
      intro h
      exact hjm (Nat.lcm_dvd_iff.mp h).1
    simp only [hlcm, if_false]

private theorem card_Icc_divisors_le_divisors {r m : ℕ} (hm : 0 < m) :
    #((Finset.Icc 1 r).filter fun j ↦ j ∣ m) ≤ #m.divisors := by
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [Nat.mem_divisors]
  exact ⟨hj.2, hm.ne'⟩

/-- The standard bound obtained from the first-cycle recurrence:
`P(order(τ) ∣ m) ≤ τ(m)/r`. -/
theorem orderDvdProbability_le_divisors_card_div
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    orderDvdProbability r m ≤ (#m.divisors : ℚ) / r := by
  rw [le_div_iff₀ (by exact_mod_cast hr : (0 : ℚ) < r)]
  have hrec := orderDvdProbability_mul_eq_sum (r := r) (m := m)
  calc
    orderDvdProbability r m * (r : ℚ) =
        (r : ℚ) * orderDvdProbability r m := by ring
    _ =
        ∑ j ∈ Finset.Icc 1 r,
          if j ∣ m then orderDvdProbability (r - j) m else 0 := hrec
    _ ≤ ∑ j ∈ Finset.Icc 1 r, if j ∣ m then (1 : ℚ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hjm : j ∣ m
      · simp [hjm, orderDvdProbability_le_one]
      · simp [hjm]
    _ = (#((Finset.Icc 1 r).filter fun j ↦ j ∣ m) : ℕ) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (#m.divisors : ℕ) := by
      exact_mod_cast card_Icc_divisors_le_divisors (r := r) (m := m) hm

/-- Consumer-shaped residual bound. -/
theorem residualOrderProbability_le_divisors_card_div
    {r j m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    residualOrderProbability r j m ≤ (#m.divisors : ℚ) / r :=
  (residualOrderProbability_le_orderDvdProbability r j m).trans
    (orderDvdProbability_le_divisors_card_div hr hm)

end Erdos1161
