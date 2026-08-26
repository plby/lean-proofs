import Mathlib
import ErdosProblems.Erdos550.ThresholdCounting
import ErdosProblems.Erdos550.MatchingHeadDegreeTransfer

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Heavy-cluster thresholding for the direct off-Turán route

This file restates the Run-A2 counting step with the heavy family defined
explicitly at threshold `base + 80ηN`.  It also records the `77ηN` head-supply
transfer used after deleting all clusters not covered by the chosen matching.
-/

open Finset

namespace Erdos550

/-- Clusters whose cleaned degree reaches the Run-A2 heavy threshold. -/
noncomputable def heavyClusterFamily {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (D : ι → ℝ) (base η N : ℝ) : Finset ι :=
  S.filter fun i => base + 80 * η * N ≤ D i

@[simp] lemma mem_heavyClusterFamily_iff
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (D : ι → ℝ) (base η N : ℝ) (i : ι) :
    i ∈ heavyClusterFamily S D base η N ↔
      i ∈ S ∧ base + 80 * η * N ≤ D i := by
  simp [heavyClusterFamily]

/-- **Threshold counting.**  If cleaned average degree is at least
`base + 100ηN`, then at least a `20η` fraction of the cluster family has degree
at least `base + 80ηN`. -/
theorem heavyClusterFamily_card_lower
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (D : ι → ℝ) (base η N : ℝ)
    (hN : 0 < N) (hbase : 0 ≤ base + 80 * η * N)
    (hup : ∀ i ∈ S, D i ≤ N)
    (havg : (base + 100 * η * N) * (S.card : ℝ) ≤ ∑ i ∈ S, D i) :
    (20 * η) * (S.card : ℝ) ≤
      ((heavyClusterFamily S D base η N).card : ℝ) := by
  apply theta_counting S (heavyClusterFamily S D base η N) D
      (Finset.filter_subset _ _) N base η hN hbase hup
  · intro i hi hnot
    have hnot' : ¬ base + 80 * η * N ≤ D i := by
      intro h
      exact hnot (by simp [heavyClusterFamily, hi, h])
    exact le_of_lt (lt_of_not_ge hnot')
  · exact havg

/-- Removing at most `3ηN` from a heavy head leaves the `77ηN` supply required
by the dynamic engine.  This deliberately uses no per-edge load hypothesis. -/
lemma matching_head_supply_77
    (base η N full matched outside : ℝ)
    (hfull : base + 80 * η * N ≤ full)
    (hsplit : full ≤ matched + outside)
    (hout : outside ≤ 3 * η * N) :
    base + 77 * η * N ≤ matched := by
  linarith

/-- The existing sharper `2ηN` unmatched-cluster estimate immediately yields
the stated `77ηN` conclusion. -/
lemma matching_head_supply_77_of_two
    (base η N full matched outside : ℝ)
    (hη : 0 ≤ η) (hN : 0 ≤ N)
    (hfull : base + 80 * η * N ≤ full)
    (hsplit : full ≤ matched + outside)
    (hout : outside ≤ 2 * η * N) :
    base + 77 * η * N ≤ matched := by
  have h78 := matching_head_degree_lower base η N full matched outside
    hfull hsplit hout
  nlinarith

end Erdos550
