import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weighted head degrees on a reduced matching

For a reduced edge from a head cluster to a target cluster, its weight is the
actual host density times the target-cluster order; for a reduced nonedge it
is zero.  These are exactly the endpoint thresholds in Hladký--Piguet
packedness.  Whole matching-edge weights are the sums of their two endpoint
weights.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpHeadEndpointWeight
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι) : ℝ :=
  if R.Adj head target then
    (G.edgeDensity (C head) (C target) : ℝ) * (C target).card
  else 0

noncomputable def hpHeadMatchingWeight
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head : ι)
    (cL cR : κ → ι) (k : κ) : ℝ :=
  hpHeadEndpointWeight G R C head (cL k) +
    hpHeadEndpointWeight G R C head (cR k)

lemma hpHeadEndpointWeight_nonneg
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι) :
    0 ≤ hpHeadEndpointWeight G R C head target := by
  rw [hpHeadEndpointWeight]
  split
  · exact mul_nonneg
      (by exact_mod_cast G.edgeDensity_nonneg (C head) (C target))
      (Nat.cast_nonneg _)
  · exact le_rfl

lemma hpHeadEndpointWeight_le_card
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head target : ι) :
    hpHeadEndpointWeight G R C head target ≤ (C target).card := by
  rw [hpHeadEndpointWeight]
  split
  · have hd :
        (G.edgeDensity (C head) (C target) : ℝ) ≤ 1 := by
      exact_mod_cast G.edgeDensity_le_one (C head) (C target)
    simpa using! mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
  · positivity

lemma hpHeadMatchingWeight_nonneg
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head : ι)
    (cL cR : κ → ι) (k : κ) :
    0 ≤ hpHeadMatchingWeight G R C head cL cR k := by
  exact add_nonneg
    (hpHeadEndpointWeight_nonneg G R C head (cL k))
    (hpHeadEndpointWeight_nonneg G R C head (cR k))

lemma hpHeadMatchingWeight_le_two_mul
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head : ι)
    (cL cR : κ → ι) (s : ℝ)
    (hsize : ∀ i, ((C i).card : ℝ) ≤ s) (k : κ) :
    hpHeadMatchingWeight G R C head cL cR k ≤ 2 * s := by
  rw [hpHeadMatchingWeight]
  linarith [hpHeadEndpointWeight_le_card G R C head (cL k),
    hpHeadEndpointWeight_le_card G R C head (cR k),
    hsize (cL k), hsize (cR k)]

end Erdos550
