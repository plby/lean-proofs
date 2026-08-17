/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos308.CrootInterval
import ErdosProblems.Erdos308.GreedyEgyptian

/-!
# Erdős 308: completion of the represented initial interval

The analytic construction is uniform for all sufficiently large target
integers.  The finitely many earlier targets are handled by the proved greedy
Egyptian-expansion theorem; taking a finite intersection of
their denominator bounds makes this uniform in the ambient cutoff.
-/

namespace Erdos308.CrootCompletion

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos308.CrootInterval

def BoundedRepresentation (N k : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (k : ℚ)

lemma eventually_fixed_target_representable (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, BoundedRepresentation N k := by
  by_cases hk : k = 0
  · subst k
    filter_upwards with N
    exact ⟨∅, by simp, by simp [UnitFractions.rec_sum]⟩
  · have hkpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    obtain ⟨A, hApos, hAsum⟩ :=
      GreedyEgyptian.egyptian_expansion_exists (k : ℚ) hkpos 0
    filter_upwards [eventually_ge_atTop (A.sup id)] with N hN
    refine ⟨A, ?_, hAsum.symm⟩
    intro n hn
    exact Finset.mem_Icc.mpr
      ⟨hApos n hn, (Finset.le_sup (f := id) hn).trans hN⟩

lemma eventually_targets_below (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ k < K, BoundedRepresentation N k := by
  induction K with
  | zero => simp
  | succ K ih =>
      filter_upwards [ih, eventually_fixed_target_representable K] with N hN hK
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact hN k hlt
      · exact hK

/-- Every positive integer at least one below the harmonic floor is eventually
represented.  This is the exact qualitative interval consequence needed for
Problem 308. -/
theorem eventually_initial_interval :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      0 < k → k + 1 ≤ ⌊harmonicMass N⌋₊ →
      BoundedRepresentation N k := by
  obtain ⟨K, hlarge⟩ := eventually_atTop.mp eventually_large_target_representable
  filter_upwards [eventually_targets_below K] with N hsmall
  intro k hkpos hkfloor
  by_cases hk : K ≤ k
  · exact hlarge k hk N hkfloor
  · exact hsmall k (Nat.lt_of_not_ge hk)

end

end Erdos308.CrootCompletion

#print axioms Erdos308.CrootCompletion.eventually_initial_interval
