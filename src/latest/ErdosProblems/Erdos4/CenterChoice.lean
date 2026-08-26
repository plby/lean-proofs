import ErdosProblems.Erdos4.ProbabilityFallback

/-!
# Actual center choices after the preliminary sieve

Surviving center weights are normalized separately for each source. A
fixed center is used when their total mass is zero. The resulting
independent choices miss a target with probability at most the product
appearing in the checked conditional covering estimate.
-/

open scoped BigOperators

namespace Erdos4.CenterChoice

open AffineTuples ConditionalTupleMoments

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

def fallback (Y : ℕ) (hY : 1 ≤ Y) : ↥(Finset.Icc 1 Y) :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hY⟩⟩

noncomputable def raw (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ)
    (a : ∀ l, ZMod (ell l)) (n : ↥(Finset.Icc 1 Y)) : ℝ :=
  μ n * indicator ell a (tuple h p n)

theorem raw_nonneg (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (a : ∀ l, ZMod (ell l)) (n : ↥(Finset.Icc 1 Y)) : 0 ≤ raw ell h p Y μ a n :=
  mul_nonneg (hμ n n.property) (indicator_nonneg ell a _)

theorem sum_raw (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (a : ∀ l, ZMod (ell l)) :
    (∑ n : ↥(Finset.Icc 1 Y), raw ell h p Y μ a n) = tupleMass ell h p Y μ a := by
  exact Finset.sum_coe_sort (Finset.Icc 1 Y) (fun n : ℕ => μ n * indicator ell a (tuple h p n))

noncomputable def probability (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (hY : 1 ≤ Y)
    (a : ∀ l, ZMod (ell l)) (n : ↥(Finset.Icc 1 Y)) : ℝ :=
  ProbabilityFallback.probability (raw ell h p Y μ a) (fallback Y hY) n

theorem probability_nonneg (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (a : ∀ l, ZMod (ell l)) (n : ↥(Finset.Icc 1 Y)) : 0 ≤ probability ell h p Y μ hY a n :=
  ProbabilityFallback.probability_nonneg _ (raw_nonneg ell h p Y μ hμ a) _ _

theorem sum_probability (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (hY : 1 ≤ Y)
    (a : ∀ l, ZMod (ell l)) :
    (∑ n : ↥(Finset.Icc 1 Y), probability ell h p Y μ hY a n) = 1 :=
  ProbabilityFallback.sum_probability _ _

theorem miss_mass_le (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (q : ℕ) (a : ∀ l, ZMod (ell l)) :
    (∑ n : ↥(Finset.Icc 1 Y), if q ∉ tuple h p n then probability ell h p Y μ hY a n else 0) ≤
      1 - hittingMass ell h p Y μ q a / tupleMass ell h p Y μ a := by
  have hh := ProbabilityFallback.miss_mass_le (raw ell h p Y μ a)
    (raw_nonneg ell h p Y μ hμ a) (fallback Y hY) (fun n => q ∈ tuple h p n)
  have hhit : (∑ n : ↥(Finset.Icc 1 Y), if q ∈ tuple h p n then raw ell h p Y μ a n else 0) =
      hittingMass ell h p Y μ q a := by
    unfold raw
    rw [Finset.sum_coe_sort (Finset.Icc 1 Y) (fun n : ℕ =>
      if q ∈ tuple h p n then μ n * indicator ell a (tuple h p n) else 0)]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hq : q ∈ tuple h p n <;> simp [hq]
  rw [sum_raw, hhit] at hh
  exact hh

noncomputable def assignmentWeight (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y) (a : ∀ l, ZMod (ell l))
    (choice : sources → ↥(Finset.Icc 1 Y)) : ℝ :=
  ∏ p : sources, probability ell h p Y (μ p) hY a (choice p)

theorem assignmentWeight_nonneg (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (a : ∀ l, ZMod (ell l)) (choice : sources → ↥(Finset.Icc 1 Y)) :
    0 ≤ assignmentWeight ell h sources Y μ hY a choice :=
  Finset.prod_nonneg (fun p _hp => probability_nonneg ell h p Y (μ p) hY (hμ p p.property) a _)

theorem sum_assignmentWeight (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y) (a : ∀ l, ZMod (ell l)) :
    (∑ choice : sources → ↥(Finset.Icc 1 Y), assignmentWeight ell h sources Y μ hY a choice) = 1 :=
  Erdos4.assignmentWeight_sum (fun p : sources => probability ell h p Y (μ p) hY a)
    (fun p => sum_probability ell h p Y (μ p) hY a)

open Classical in
theorem assignment_miss_mass_le (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (q : ℕ) (a : ∀ l, ZMod (ell l)) :
    (∑ choice : sources → ↥(Finset.Icc 1 Y),
      if ∀ p : sources, q ∉ tuple h p (choice p) then assignmentWeight ell h sources Y μ hY a choice else 0) ≤
        ConditionalCovering.miss ell h sources Y μ q a := by
  classical
  have hi := Erdos4.independent_assignment_miss_mass
    (fun p : sources => probability ell h p Y (μ p) hY a)
    (fun (p : sources) (n : ↥(Finset.Icc 1 Y)) => q ∉ tuple h p n)
  have heq : (∑ choice : sources → ↥(Finset.Icc 1 Y),
      if ∀ p : sources, q ∉ tuple h p (choice p) then assignmentWeight ell h sources Y μ hY a choice else 0) =
      ∏ p : sources, ∑ n : ↥(Finset.Icc 1 Y),
        if q ∉ tuple h p n then probability ell h p Y (μ p) hY a n else 0 := by
    convert hi using 1
    apply Finset.sum_congr rfl
    intro choice _hc
    by_cases hc : ∀ p : sources, q ∉ tuple h p (choice p) <;> simp [hc, assignmentWeight]
  rw [heq]
  apply Finset.prod_le_prod
  · intro p _hp
    apply Finset.sum_nonneg
    intro n _hn
    by_cases hq : q ∉ tuple h p n
    · rw [if_pos hq]
      exact probability_nonneg ell h p Y (μ p) hY (hμ p p.property) a n
    · rw [if_neg hq]
  · intro p _hp
    exact miss_mass_le ell h p Y (μ p) hY (hμ p p.property) q a

end Erdos4.CenterChoice
