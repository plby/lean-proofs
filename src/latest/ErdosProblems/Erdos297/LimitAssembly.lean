/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement

/-!
# Erdős Problem 297: assembling the asymptotic limit

This file contains the purely order-theoretic last step of the proof.  The
number-theoretic upper bound and the Fourier-analytic lower bound naturally
produce estimates with an arbitrary positive error in the exponent.  The
lemmas below turn those estimates into convergence of the normalized
logarithm.

The generic statements are deliberately separated from `Erdos297.count`.
Thus the deep estimates remain ordinary theorem arguments: no arithmetic or
Fourier assertion is postulated in this module.
-/

open Filter
open scoped Topology

namespace Erdos297

noncomputable section

/-- A real-valued net converges when, for every positive error, it is
eventually trapped between the corresponding lower and upper barriers.

The hypotheses use weak inequalities, as is convenient for asymptotic
estimates.  Applying them with half of the requested metric radius supplies
the strict inequalities required by `Metric.tendsto_nhds`. -/
theorem tendsto_of_eventually_between
    {α : Type*} {f : Filter α} {u : α → ℝ} {c : ℝ}
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in f, c - ε ≤ u x)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in f, u x ≤ c + ε) :
    Tendsto u f (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hlower (ε / 2) hhalf, hupper (ε / 2) hhalf] with x hxlow hxhigh
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- Bundled version of `tendsto_of_eventually_between`, useful when an upper
and lower argument have already been combined into one eventual statement. -/
theorem tendsto_of_eventually_mem_closed_interval
    {α : Type*} {f : Filter α} {u : α → ℝ} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in f, u x ∈ Set.Icc (c - ε) (c + ε)) :
    Tendsto u f (𝓝 c) := by
  apply tendsto_of_eventually_between
  · intro ε hε
    exact (h ε hε).mono fun _ hx ↦ hx.1
  · intro ε hε
    exact (h ε hε).mono fun _ hx ↦ hx.2

/-- Liminf/limsup assembly for a real-valued net.  Conditional completeness
requires the explicit eventual upper- and lower-boundedness hypotheses. -/
theorem tendsto_of_liminf_limsup_bounds
    {α : Type*} {f : Filter α} {u : α → ℝ} {c : ℝ}
    (hliminf : c ≤ liminf u f)
    (hlimsup : limsup u f ≤ c)
    (hboundedAbove : f.IsBoundedUnder (· ≤ ·) u)
    (hboundedBelow : f.IsBoundedUnder (· ≥ ·) u) :
    Tendsto u f (𝓝 c) :=
  tendsto_of_le_liminf_of_limsup_le hliminf hlimsup hboundedAbove hboundedBelow

/-- Eventual exponential bounds imply convergence of normalized logarithms.

No separate positivity assumption on `a` is needed: the lower exponential
bound makes `a N` positive on the tail on which logarithmic monotonicity is
used. -/
theorem tendsto_normalizedLog_of_eventually_exp_bounds
    (a : ℕ → ℝ) (c : ℝ)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        Real.exp ((c - ε) * (N : ℝ)) ≤ a N)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        a N ≤ Real.exp ((c + ε) * (N : ℝ))) :
    Tendsto (fun N : ℕ ↦ Real.log (a N) / (N : ℝ)) atTop (𝓝 c) := by
  apply tendsto_of_eventually_between
  · intro ε hε
    filter_upwards [hlower ε hε, eventually_gt_atTop 0] with N hNlower hN
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hlog : (c - ε) * (N : ℝ) ≤ Real.log (a N) := by
      rw [← Real.log_exp ((c - ε) * (N : ℝ))]
      exact Real.log_le_log (Real.exp_pos _) hNlower
    exact (le_div_iff₀ hNreal).2 hlog
  · intro ε hε
    filter_upwards [hlower ε hε, hupper ε hε, eventually_gt_atTop 0] with
      N hNlower hNupper hN
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have haN : 0 < a N := (Real.exp_pos _).trans_le hNlower
    have hlog : Real.log (a N) ≤ (c + ε) * (N : ℝ) := by
      rw [← Real.log_exp ((c + ε) * (N : ℝ))]
      exact Real.log_le_log haN hNupper
    exact (div_le_iff₀ hNreal).2 hlog

/-- A version of the preceding lemma in which the exponential estimates are
already bundled into one eventual interval statement. -/
theorem tendsto_normalizedLog_of_eventually_exp_mem_Icc
    (a : ℕ → ℝ) (c : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        a N ∈ Set.Icc
          (Real.exp ((c - ε) * (N : ℝ)))
          (Real.exp ((c + ε) * (N : ℝ)))) :
    Tendsto (fun N : ℕ ↦ Real.log (a N) / (N : ℝ)) atTop (𝓝 c) := by
  apply tendsto_normalizedLog_of_eventually_exp_bounds a c
  · intro ε hε
    exact (h ε hε).mono fun _ hx ↦ hx.1
  · intro ε hε
    exact (h ε hε).mono fun _ hx ↦ hx.2

/-- The direct normalized-log interface for the two deep halves of Erdős
Problem 297. -/
theorem tendsto_logGrowth_of_eventual_bounds
    (lam : ℝ)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, gamma lam - ε ≤ logGrowth N)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, logGrowth N ≤ gamma lam + ε) :
    Tendsto logGrowth atTop (𝓝 (gamma lam)) :=
  tendsto_of_eventually_between hlower hupper

/-- The exponential-count interface for the two deep halves of Erdős Problem
297.  It is often the most convenient final theorem: the lower construction
and exponential-moment upper bound can be supplied without first taking
logarithms by hand. -/
theorem tendsto_logGrowth_of_eventually_exp_count_bounds
    (lam : ℝ)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        Real.exp ((gamma lam - ε) * (N : ℝ)) ≤ (count N : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (count N : ℝ) ≤ Real.exp ((gamma lam + ε) * (N : ℝ))) :
    Tendsto logGrowth atTop (𝓝 (gamma lam)) := by
  change Tendsto
    (fun N : ℕ ↦ Real.log (count N : ℝ) / (N : ℝ))
    atTop (𝓝 (gamma lam))
  exact tendsto_normalizedLog_of_eventually_exp_bounds
    (fun N : ℕ ↦ (count N : ℝ)) (gamma lam) hlower hupper

/-- Liminf/limsup interface specialized to the normalized logarithm in
Problem 297. -/
theorem tendsto_logGrowth_of_liminf_limsup
    (lam : ℝ)
    (hliminf : gamma lam ≤ liminf logGrowth atTop)
    (hlimsup : limsup logGrowth atTop ≤ gamma lam)
    (hboundedAbove : atTop.IsBoundedUnder (· ≤ ·) logGrowth)
    (hboundedBelow : atTop.IsBoundedUnder (· ≥ ·) logGrowth) :
    Tendsto logGrowth atTop (𝓝 (gamma lam)) :=
  tendsto_of_liminf_limsup_bounds
    hliminf hlimsup hboundedAbove hboundedBelow

end

end Erdos297

#print axioms Erdos297.tendsto_logGrowth_of_eventual_bounds
#print axioms Erdos297.tendsto_logGrowth_of_eventually_exp_count_bounds
#print axioms Erdos297.tendsto_logGrowth_of_liminf_limsup
