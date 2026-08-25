import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

open Filter Finset Real Asymptotics Topology

/-- Mertens' product asymptotic, in reciprocal-product form. -/
theorem mertens_product :
    Tendsto
      (fun y : ℝ =>
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊y⌋₊), ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))
      atTop (𝓝 1) := by
  have hprod (y : ℝ) :
      (∏ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime, ((p : ℝ) / (p - 1))) =
        (∏ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr (by congr 1)
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    field_simp
  have heq :
      (fun y : ℝ => ∏ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime,
        ((p : ℝ) / (p - 1))) ~[atTop]
      (fun y : ℝ => Real.exp Real.eulerMascheroniConstant * Real.log y) := by
    convert Mertens.E₃.bound''.inv using 1
    · ext y
      exact hprod y
    · ext y
      simp [Real.exp_neg, div_eq_mul_inv, mul_comm]
  apply (isEquivalent_iff_tendsto_one ?_).mp heq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  exact mul_ne_zero (Real.exp_ne_zero _) (Real.log_pos hy).ne'
