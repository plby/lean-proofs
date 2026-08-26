import Mathlib
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching-endpoint vertices retained for deferred seed contacts

For a matching endpoint assigned to a head, retain the vertices having the
standard degree lower bound into the low-bad head core.  If the endpoint is
not a positive-weight reduced neighbour of the head, its weight is at most
`ε` and the condition is automatic.  Otherwise regularity shows that fewer
than an `ε`-fraction of the endpoint is removed.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpRetainedSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (endpoint headCore : Finset V) : Finset V :=
  endpoint.filter fun v =>
    (d - ε) * (headCore.card : ℝ) ≤
      ((headCore.filter fun x => G.Adj v x).card : ℝ)

lemma hpRetainedSet_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (endpoint headCore : Finset V) :
    hpRetainedSet G ε d endpoint headCore ⊆ endpoint :=
  Finset.filter_subset _ _

lemma hpRetainedSet_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d : ℝ) (endpoint headCore : Finset V)
    {v : V} (hv : v ∈ hpRetainedSet G ε d endpoint headCore) :
    (d - ε) * (headCore.card : ℝ) ≤
      ((headCore.filter fun x => G.Adj v x).card : ℝ) :=
  (Finset.mem_filter.mp hv).2

/-- The retained set loses fewer than `ε|endpoint|` vertices.  The disjunction
is the weighted-cluster convention: zero/small weight is automatic, while a
positive weight is certified by a regular pair to the full head cluster. -/
lemma hpRetainedSet_removed_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (endpoint headBase headCore : Finset V)
    (hheadCore : headCore ⊆ headBase)
    (hheadSig : ε * (headBase.card : ℝ) ≤ (headCore.card : ℝ))
    (hcase : d ≤ ε ∨
      (G.IsUniform ε endpoint headBase ∧
        d ≤ (G.edgeDensity endpoint headBase : ℝ)))
    (hendpoint : endpoint.Nonempty) :
    (((endpoint \ hpRetainedSet G ε d endpoint headCore).card : ℕ) : ℝ) <
      ε * (endpoint.card : ℝ) := by
  rcases hcase with hsmall | ⟨huni, hdens⟩
  · have hall :
        hpRetainedSet G ε d endpoint headCore = endpoint := by
      apply Finset.Subset.antisymm
      · exact hpRetainedSet_subset G ε d endpoint headCore
      · intro v hv
        apply Finset.mem_filter.mpr
        refine ⟨hv, ?_⟩
        have hdeg :
            0 ≤ ((headCore.filter fun x => G.Adj v x).card : ℝ) :=
          Nat.cast_nonneg _
        have hcard : 0 ≤ (headCore.card : ℝ) := Nat.cast_nonneg _
        nlinarith
    rw [hall]
    simpa using! mul_pos hε0 (Nat.cast_pos.mpr hendpoint.card_pos)
  · have hbad :=
      isUniform_few_low_degree_subset G hε0 hε1 hheadCore
        hendpoint hheadSig huni
    refine lt_of_le_of_lt ?_ hbad
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hv'.1, ?_⟩
    have hnot :
        ¬ (d - ε) * (headCore.card : ℝ) ≤
          ((headCore.filter fun x => G.Adj v x).card : ℝ) := by
      intro h
      exact hv'.2 (Finset.mem_filter.mpr ⟨hv'.1, h⟩)
    have hlt := lt_of_not_ge hnot
    exact lt_of_lt_of_le hlt
      (mul_le_mul_of_nonneg_right
        (sub_le_sub_right hdens ε) (Nat.cast_nonneg _))

end Erdos550
