import ErdosProblems.Erdos4.CenterChoice

/-!
# Deterministic choices from the two-stage random construction

The joint finite distribution consists of the preliminary residues and
the independently selected surviving centers. Its uncovered-set average
is bounded by the single-point survival density times the sum of the
checked conditional noncoverage bounds. A deterministic outcome therefore
satisfies the same cardinality bound.
-/

open scoped BigOperators

namespace Erdos4.TwoStageSelection

open AffineTuples ConditionalTupleMoments

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def jointWeight (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y))) : ℝ :=
  RandomResidueSieve.weight ell o.1 * CenterChoice.assignmentWeight ell h sources Y μ hY o.1 o.2

theorem jointWeight_nonneg (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y))) :
    0 ≤ jointWeight ell h sources Y μ hY o :=
  mul_nonneg (RandomResidueSieve.weight_nonneg ell o.1)
    (CenterChoice.assignmentWeight_nonneg ell h sources Y μ hY hμ o.1 o.2)

theorem sum_jointWeight (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y) :
    (∑ o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y)),
      jointWeight ell h sources Y μ hY o) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [jointWeight, ← Finset.mul_sum, CenterChoice.sum_assignmentWeight, mul_one]
  exact RandomResidueSieve.sum_weight ell

open Classical in
theorem surviving_mean (q : ℕ) (f : (∀ l, ZMod (ell l)) → ℝ) :
    (∑ a : ∀ l, ZMod (ell l), if RandomResidueSieve.Survives ell a {q} then
      RandomResidueSieve.weight ell a * f a else 0) =
      UnitFourier.unitDensity ell * mean ell q f := by
  classical
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold RandomResidueSieve.conditionalWeight
  have hV := UnitFourier.unitDensity_pos ell
  by_cases hq : RandomResidueSieve.Survives ell a {q}
  · simp only [if_pos hq]
    field_simp
  · simp only [if_neg hq, zero_mul, mul_zero]

noncomputable def uncovered (h : Fin k → ℕ) (sources targets : Finset ℕ) (Y : ℕ)
    (o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y))) : Finset ℕ := by
  classical
  exact targets.filter (fun q => RandomResidueSieve.Survives ell o.1 {q} ∧
    ∀ p : sources, q ∉ tuple h p (o.2 p))

open Classical in
theorem source_choice_bound (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (q : ℕ) (a : ∀ l, ZMod (ell l)) :
    (∑ choice : sources → ↥(Finset.Icc 1 Y),
      if RandomResidueSieve.Survives ell a {q} ∧ ∀ p : sources, q ∉ tuple h p (choice p)
      then jointWeight ell h sources Y μ hY (a, choice) else 0) ≤
      if RandomResidueSieve.Survives ell a {q} then
        RandomResidueSieve.weight ell a * ConditionalCovering.miss ell h sources Y μ q a else 0 := by
  classical
  by_cases hs : RandomResidueSieve.Survives ell a {q}
  · rw [if_pos hs]
    calc
      _ = RandomResidueSieve.weight ell a *
          ∑ choice : sources → ↥(Finset.Icc 1 Y),
            if ∀ p : sources, q ∉ tuple h p (choice p)
            then CenterChoice.assignmentWeight ell h sources Y μ hY a choice else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro choice _hc
        by_cases hc : ∀ p : sources, q ∉ tuple h p (choice p) <;> simp [hs, hc, jointWeight]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (CenterChoice.assignment_miss_mass_le ell h sources Y μ hY hμ q a)
        (RandomResidueSieve.weight_nonneg ell a)
  · simp [hs]

theorem average_uncovered_le (h : Fin k → ℕ) (sources targets : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n) :
    (∑ o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y)),
      jointWeight ell h sources Y μ hY o * (uncovered ell h sources targets Y o).card) ≤
      UnitFourier.unitDensity ell * ∑ q ∈ targets, mean ell q (ConditionalCovering.miss ell h sources Y μ q) := by
  classical
  have hcard (o : (∀ l, ZMod (ell l)) × (sources → ↥(Finset.Icc 1 Y))) :
      jointWeight ell h sources Y μ hY o * (uncovered ell h sources targets Y o).card =
        ∑ q ∈ targets, if RandomResidueSieve.Survives ell o.1 {q} ∧
          ∀ p : sources, q ∉ tuple h p (o.2 p) then jointWeight ell h sources Y μ hY o else 0 := by
    simp only [uncovered, Finset.card_filter, Nat.cast_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    split_ifs <;> simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  calc
    _ = ∑ q ∈ targets, ∑ a : ∀ l, ZMod (ell l), ∑ choice : sources → ↥(Finset.Icc 1 Y),
        if RandomResidueSieve.Survives ell a {q} ∧ ∀ p : sources, q ∉ tuple h p (choice p)
        then jointWeight ell h sources Y μ hY (a, choice) else 0 := by
      exact Finset.sum_congr rfl (fun q _hq => Fintype.sum_prod_type _)
    _ ≤ ∑ q ∈ targets, ∑ a : ∀ l, ZMod (ell l),
        if RandomResidueSieve.Survives ell a {q} then
          RandomResidueSieve.weight ell a * ConditionalCovering.miss ell h sources Y μ q a else 0 := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Finset.sum_le_sum (fun a _ha => source_choice_bound ell h sources Y μ hY hμ q a)
    _ = _ := by
      simp only [surviving_mean]
      exact (Finset.mul_sum _ _ _).symm

theorem exists_choices (h : Fin k → ℕ) (sources targets : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n) :
    ∃ (a : ∀ l, ZMod (ell l)) (choice : sources → ↥(Finset.Icc 1 Y)),
      ((uncovered ell h sources targets Y (a, choice)).card : ℝ) ≤
        UnitFourier.unitDensity ell * ∑ q ∈ targets, mean ell q (ConditionalCovering.miss ell h sources Y μ q) := by
  let : Nonempty (↥(Finset.Icc 1 Y)) := ⟨CenterChoice.fallback Y hY⟩
  obtain ⟨o, ho⟩ := Erdos4.expectation_to_deterministic_cover
    (jointWeight ell h sources Y μ hY) (uncovered ell h sources targets Y)
    (jointWeight_nonneg ell h sources Y μ hY hμ) (sum_jointWeight ell h sources Y μ hY) _
    (average_uncovered_le ell h sources targets Y μ hY hμ)
  exact ⟨o.1, o.2, ho⟩

end Erdos4.TwoStageSelection
