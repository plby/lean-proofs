import Mathlib
import ErdosProblems.Erdos550.HPMatchingState

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dynamic free and root pools inside a matching endpoint

At an intermediate embedding state, an endpoint may be used only at already
embedded image vertices and at vertices deleted by the fixed retained-contact
condition.  The lemmas below charge these two losses exactly and convert the
result into the free-side and root-pool inequalities required by the
matching-wide component extension.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpFreeEndpoint
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V) : Finset V :=
  (endpoint ∩ retained) \ used

noncomputable def hpRootPool
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (anchor : V)
    (used endpoint retained : Finset V) : Finset V :=
  (hpFreeEndpoint used endpoint retained).filter fun v => G.Adj anchor v

lemma hpFreeEndpoint_subset_endpoint
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V) :
    hpFreeEndpoint used endpoint retained ⊆ endpoint :=
  (Finset.sdiff_subset).trans Finset.inter_subset_left

lemma hpFreeEndpoint_subset_retained
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V) :
    hpFreeEndpoint used endpoint retained ⊆ retained :=
  (Finset.sdiff_subset).trans Finset.inter_subset_right

lemma hpFreeEndpoint_mono_retained
    {V : Type*} [DecidableEq V]
    (used endpoint retained retained' : Finset V)
    (hret : retained ⊆ retained') :
    hpFreeEndpoint used endpoint retained ⊆
      hpFreeEndpoint used endpoint retained' := by
  intro v hv
  have hv' := Finset.mem_sdiff.mp hv
  have hvInter := Finset.mem_inter.mp hv'.1
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_inter.mpr ⟨hvInter.1, hret hvInter.2⟩, hv'.2⟩

lemma hpFreeEndpoint_disjoint_used
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V) :
    Disjoint (hpFreeEndpoint used endpoint retained) used := by
  rw [Finset.disjoint_left]
  intro v hvFree hvUsed
  exact (Finset.mem_sdiff.mp hvFree).2 hvUsed

lemma hpRootPool_subset_free
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (anchor : V)
    (used endpoint retained : Finset V) :
    hpRootPool G anchor used endpoint retained ⊆
      hpFreeEndpoint used endpoint retained :=
  Finset.filter_subset _ _

lemma hpRootPool_adj
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (anchor : V)
    (used endpoint retained : Finset V) :
    ∀ v ∈ hpRootPool G anchor used endpoint retained,
      G.Adj anchor v := by
  intro v hv
  exact (Finset.mem_filter.mp hv).2

private lemma endpoint_subset_free_union_losses
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V) :
    endpoint ⊆
      (hpFreeEndpoint used endpoint retained ∪
        (endpoint \ retained)) ∪ (used ∩ endpoint) := by
  intro v hvEndpoint
  by_cases hvRetained : v ∈ retained
  · by_cases hvUsed : v ∈ used
    · exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hvUsed, hvEndpoint⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr
            ⟨Finset.mem_inter.mpr ⟨hvEndpoint, hvRetained⟩, hvUsed⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hvEndpoint, hvRetained⟩))

/-- A uniform lower cap survives the fixed retained deletion and all currently
used vertices in the endpoint. -/
lemma hpFreeEndpoint_card_lower
    {V : Type*} [DecidableEq V]
    (used endpoint retained : Finset V)
    (cap retainedLoss : ℝ)
    (hretained :
      ((endpoint \ retained).card : ℝ) ≤ retainedLoss)
    (hcap : cap + retainedLoss ≤ (endpoint.card : ℝ)) :
    cap - ((used ∩ endpoint).card : ℝ) ≤
      (hpFreeEndpoint used endpoint retained).card := by
  have hcard :
      endpoint.card ≤
        (hpFreeEndpoint used endpoint retained).card +
          (endpoint \ retained).card + (used ∩ endpoint).card := by
    exact (Finset.card_le_card
      (endpoint_subset_free_union_losses used endpoint retained)).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcardReal :
      (endpoint.card : ℝ) ≤
        (hpFreeEndpoint used endpoint retained).card +
          ((endpoint \ retained).card : ℝ) +
          ((used ∩ endpoint).card : ℝ) := by
    exact_mod_cast hcard
  linarith

private lemma adjacent_endpoint_subset_root_union_losses
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (anchor : V)
    (used endpoint retained : Finset V) :
    endpoint.filter (fun v => G.Adj anchor v) ⊆
      (hpRootPool G anchor used endpoint retained ∪
        (endpoint \ retained)) ∪ (used ∩ endpoint) := by
  intro v hv
  have hvEndpoint := (Finset.mem_filter.mp hv).1
  have hvAdj := (Finset.mem_filter.mp hv).2
  by_cases hvRetained : v ∈ retained
  · by_cases hvUsed : v ∈ used
    · exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hvUsed, hvEndpoint⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hvEndpoint, hvRetained⟩, hvUsed⟩, hvAdj⟩
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hvEndpoint, hvRetained⟩))

/-- A typical anchor degree loses only the retained-set deletion and the exact
current endpoint load. -/
lemma hpRootPool_card_lower
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (anchor : V)
    (used endpoint retained : Finset V)
    (threshold typicalityError retainedLoss : ℝ)
    (hdegree :
      threshold - typicalityError ≤
        ((endpoint.filter fun v => G.Adj anchor v).card : ℝ))
    (hretained :
      ((endpoint \ retained).card : ℝ) ≤ retainedLoss) :
    threshold - ((used ∩ endpoint).card : ℝ) -
        (typicalityError + retainedLoss) ≤
      (hpRootPool G anchor used endpoint retained).card := by
  have hcard :
      (endpoint.filter fun v => G.Adj anchor v).card ≤
        (hpRootPool G anchor used endpoint retained).card +
          (endpoint \ retained).card + (used ∩ endpoint).card := by
    exact (Finset.card_le_card
      (adjacent_endpoint_subset_root_union_losses
        G anchor used endpoint retained)).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcardReal :
      ((endpoint.filter fun v => G.Adj anchor v).card : ℝ) ≤
        (hpRootPool G anchor used endpoint retained).card +
          ((endpoint \ retained).card : ℝ) +
          ((used ∩ endpoint).card : ℝ) := by
    exact_mod_cast hcard
  linarith

end Erdos550
