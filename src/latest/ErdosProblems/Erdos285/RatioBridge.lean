/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Basic
import ErdosProblems.Erdos285.Analytic
import ErdosProblems.Erdos285.UpperAssembly
import ErdosProblems.Erdos285.Erdos285Lower

/-!
# Erdős 285: bridge from finite-set witnesses to the least-denominator ratio

This file connects the finite-set output of Martin's upper-bound construction
to the indexed formulation in the formal-conjectures statement.  An upper
witness with `k + 1` elements is enumerated increasingly; minimality then puts
`f k` below its largest denominator and hence below the witness cutoff.  The
elementary lower bound and the asymptotic cutoff bound squeeze the completed
ratio to one.
-/

open Filter
open scoped BigOperators Topology Real

namespace Erdos285

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite-set upper witness gives an admissible indexed representation and
therefore an upper bound for the least final denominator. -/
theorem minimalLastDenominator_le_cutoff_of_upperWitness
    (f : ℕ → ℕ) (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧
      0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        {n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i)}
        (f k))
    {k x : ℕ} {A : Finset ℕ} (hA : UpperWitness 1 k.succ x A) :
    k ∈ S ∧ f k ≤ x := by
  have hcard : A.card = k.succ := hA.card_eq
  let n : Fin k.succ → ℕ := enumerate A hcard
  have hn : Representation k n := by
    apply representation_enumerate hcard hA.zero_not_mem
    simpa only [reciprocalSum] using hA.sum_eq
  have hkS : k ∈ S := by
    rw [hS]
    exact ⟨n, hn⟩
  refine ⟨hkS, ?_⟩
  have hnLastMem : n (Fin.last k) ∈
      {m (Fin.last k) | (m : Fin k.succ → ℕ) (_ : StrictMono m)
        (_ : 0 ∉ Set.range m) (_ : 1 = ∑ i, (1 : ℝ) / m i)} := by
    exact ⟨n, hn.1, hn.2.1, hn.2.2, rfl⟩
  have hfLast : f k ≤ n (Fin.last k) := (h k hkS).2 hnLastMem
  have hnLastA : n (Fin.last k) ∈ A := by
    dsimp only [n]
    change enumerate A hcard (Fin.last k) ∈ (A : Set ℕ)
    rw [← range_enumerate A hcard]
    exact Set.mem_range_self (Fin.last k)
  exact hfLast.trans (hA.le_cutoff _ hnLastA)

/--
If Martin's construction eventually supplies exact `k + 1`-term witnesses
whose cutoffs divided by `k + 1` tend to `e / (e - 1)`, then the completed
least-denominator ratio in `Erdos285Packaging` tends to one.
-/
theorem uniform_ratio_of_eventually_upperWitness
    (f : ℕ → ℕ) (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧
      0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        {n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i)}
        (f k))
    (cutoff : ℕ → ℕ)
    (hupper : ∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (cutoff k) A)
    (hcutoff : Tendsto
      (fun k : ℕ ↦ (cutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds (rexp 1 / (rexp 1 - 1)))) :
    Tendsto
      (fun k : ℕ ↦
        if k ∈ S then
          (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
        else 1)
      atTop (nhds 1) := by
  let C : ℝ := rexp 1 / (rexp 1 - 1)
  have hCpos : 0 < C := by
    simpa only [C, Analytic.densityConstant] using
      Analytic.densityConstant_pos
  have hCne : C ≠ 0 := hCpos.ne'
  have hbounds : ∀ᶠ k in atTop, k ∈ S ∧ f k ≤ cutoff k := by
    filter_upwards [hupper] with k hk
    rcases hk with ⟨A, hA⟩
    exact minimalLastDenominator_le_cutoff_of_upperWitness f S hS h hA
  have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℕ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlower : Tendsto
      (fun k : ℕ ↦ 1 - (1 / C) * (1 / (k + 1 : ℕ))) atTop (nhds 1) := by
    have hz : Tendsto (fun k : ℕ ↦ (1 / C) * (1 / (k + 1 : ℕ)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    simpa using (tendsto_const_nhds.sub hz)
  have hcutoffC : Tendsto
      (fun k : ℕ ↦ (cutoff k : ℝ) /
        (C * (k + 1 : ℕ))) atTop (nhds 1) := by
    have hdiv := hcutoff.div_const C
    have heq : ∀ k : ℕ,
        ((cutoff k : ℝ) / (k + 1 : ℕ)) / C =
          (cutoff k : ℝ) / (C * (k + 1 : ℕ)) := by
      intro k
      field_simp [hCne]
    have hdiv' : Tendsto
        (fun k : ℕ ↦ (cutoff k : ℝ) / (C * (k + 1 : ℕ))) atTop
        (nhds (C / C)) := hdiv.congr' (Eventually.of_forall heq)
    simpa [hCne] using hdiv'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hcutoffC
  · filter_upwards [hbounds] with k hk
    rw [if_pos hk.1]
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hdenom : 0 < C * (k + 1 : ℕ) := mul_pos hCpos hkpos
    have hpoint := Erdos285Lower.lower_bound_of_isLeast f S h k hk.1
    change C * (k + 1 : ℕ) ≤ (f k : ℝ) + 1 at hpoint
    rw [le_div_iff₀ hdenom]
    have halgebra :
        (1 - (1 / C) * (1 / (k + 1 : ℕ))) *
            (C * (k + 1 : ℕ)) = C * (k + 1 : ℕ) - 1 := by
      field_simp [hCne]
    rw [halgebra]
    linarith
  · filter_upwards [hbounds] with k hk
    rw [if_pos hk.1]
    have hdenom : 0 ≤ C * (k + 1 : ℕ) := by positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast hk.2) hdenom

end

end Erdos285

#print axioms Erdos285.minimalLastDenominator_le_cutoff_of_upperWitness
#print axioms Erdos285.uniform_ratio_of_eventually_upperWitness
