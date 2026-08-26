import Mathlib
import ErdosProblems.Erdos550.SkeletonLowBad

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Low-atypicality cores for the two head clusters

The direct embedding chooses seeds dynamically inside fixed head cores.  A head
core is obtained by intersecting an arbitrary structural core with the vertices
whose matching bad-count is below a threshold.  The lemmas below give the exact
Markov loss and the degree loss caused by that deletion.
-/

open Finset

namespace Erdos550

open Classical

noncomputable def hpLowBadCore
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (core : Finset V) (thr : ℝ) : Finset V :=
  core.filter fun v => (badCount G C dcap ε Tset v : ℝ) ≤ thr

lemma hpLowBadCore_subset
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (core : Finset V) (thr : ℝ) :
    hpLowBadCore G C dcap ε Tset core thr ⊆ core :=
  Finset.filter_subset _ _

@[simp] lemma mem_hpLowBadCore
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (core : Finset V) (thr : ℝ) (v : V) :
    v ∈ hpLowBadCore G C dcap ε Tset core thr ↔
      v ∈ core ∧ (badCount G C dcap ε Tset v : ℝ) ≤ thr := by
  simp [hpLowBadCore]

/-- Finite Markov inequality for the high-bad vertices of one head set. -/
lemma highBad_card_mul_threshold_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (base : Finset V) (thr : ℝ) :
    let high := base.filter fun v =>
      thr < (badCount G C dcap ε Tset v : ℝ)
    (high.card : ℝ) * thr ≤
      ∑ v ∈ base, (badCount G C dcap ε Tset v : ℝ) := by
  let high := base.filter fun v =>
    thr < (badCount G C dcap ε Tset v : ℝ)
  calc
    (high.card : ℝ) * thr = ∑ _v ∈ high, thr := by simp
    _ ≤ ∑ v ∈ high, (badCount G C dcap ε Tset v : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v ∈ base, (badCount G C dcap ε Tset v : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)

/-- The complement of the low-bad core is covered by the structural-core
deletion and the Markov high-bad deletion. -/
lemma hpLowBadCore_complement_card_upper
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (base core : Finset V) (thr coreLoss badMass : ℝ)
    (hthr : 0 < thr)
    (hcore : core ⊆ base)
    (hcoreLoss : ((base \ core).card : ℝ) ≤ coreLoss)
    (hbadMass :
      (∑ v ∈ base, (badCount G C dcap ε Tset v : ℝ)) ≤ badMass) :
    (((base \ hpLowBadCore G C dcap ε Tset core thr).card : ℕ) : ℝ) ≤
      coreLoss + badMass / thr := by
  let low := hpLowBadCore G C dcap ε Tset core thr
  let high := base.filter fun v =>
    thr < (badCount G C dcap ε Tset v : ℝ)
  have hhighMul : (high.card : ℝ) * thr ≤ badMass := by
    exact (highBad_card_mul_threshold_le
      G C dcap ε Tset base thr).trans hbadMass
  have hhigh : (high.card : ℝ) ≤ badMass / thr := by
    rwa [le_div_iff₀ hthr]
  have hcompSub :
      base \ low ⊆ (base \ core) ∪ high := by
    intro v hv
    have hvBase := (Finset.mem_sdiff.mp hv).1
    have hvNotLow := (Finset.mem_sdiff.mp hv).2
    by_cases hvCore : v ∈ core
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hvBase, ?_⟩
      have : ¬ (badCount G C dcap ε Tset v : ℝ) ≤ thr := by
        intro h
        exact hvNotLow ((mem_hpLowBadCore
          G C dcap ε Tset core thr v).2 ⟨hvCore, h⟩)
      exact lt_of_not_ge this
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hvBase, hvCore⟩)
  have hcard :
      (base \ low).card ≤ (base \ core).card + high.card :=
    (Finset.card_le_card hcompSub).trans (Finset.card_union_le _ _)
  have hcardReal :
      ((base \ low).card : ℝ) ≤
        ((base \ core).card : ℝ) + (high.card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Size lower bound after the structural-core and high-bad deletions. -/
lemma hpLowBadCore_card_lower
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι)
    (base core : Finset V) (thr coreLoss badMass : ℝ)
    (hthr : 0 < thr)
    (hcore : core ⊆ base)
    (hcoreLoss : ((base \ core).card : ℝ) ≤ coreLoss)
    (hbadMass :
      (∑ v ∈ base, (badCount G C dcap ε Tset v : ℝ)) ≤ badMass) :
    (base.card : ℝ) - coreLoss - badMass / thr ≤
      (hpLowBadCore G C dcap ε Tset core thr).card := by
  let low := hpLowBadCore G C dcap ε Tset core thr
  have hcomp :
      ((base \ low).card : ℝ) ≤ coreLoss + badMass / thr := by
    exact hpLowBadCore_complement_card_upper
      G C dcap ε Tset base core thr coreLoss badMass
      hthr hcore hcoreLoss hbadMass
  have hlowSub : low ⊆ base :=
    (hpLowBadCore_subset G C dcap ε Tset core thr).trans hcore
  have hsplit : low.card + (base \ low).card = base.card := by
    simpa [Nat.add_comm] using!
      (Finset.card_sdiff_add_card_eq_card hlowSub)
  have hsplitReal :
      (low.card : ℝ) + ((base \ low).card : ℝ) =
        (base.card : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- Deleting a small subset from a target loses at most that many neighbours
of any fixed vertex. -/
lemma filtered_degree_after_core_deletion
    {V : Type*} [DecidableEq V]
    (base core : Finset V) (adj : V → Prop) [DecidablePred adj]
    (hcore : core ⊆ base) (need loss : ℝ)
    (hdegree :
      need + loss ≤ ((base.filter adj).card : ℝ))
    (hloss : ((base \ core).card : ℝ) ≤ loss) :
    need ≤ ((core.filter adj).card : ℝ) := by
  have hsub :
      base.filter adj ⊆ core.filter adj ∪ (base \ core) := by
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    by_cases hvc : v ∈ core
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hvc, hv'.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hv'.1, hvc⟩)
  have hcard :
      (base.filter adj).card ≤
        (core.filter adj).card + (base \ core).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardReal :
      ((base.filter adj).card : ℝ) ≤
        ((core.filter adj).card : ℝ) + ((base \ core).card : ℝ) := by
    exact_mod_cast hcard
  linarith

end Erdos550
