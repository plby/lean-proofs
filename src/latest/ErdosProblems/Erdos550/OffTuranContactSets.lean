import Mathlib
import ErdosProblems.Erdos550.HPRetainedSet
import ErdosProblems.Erdos550.OffTuranHeadAtypicality
import ErdosProblems.Erdos550.HPTrimmedThreshold

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# One-sided retained contact sets

A matching edge may have only one endpoint adjacent to its assigned head in
the reduced graph.  The parity-refined component is oriented so all deferred
contacts land on the chosen root side.  Accordingly, an endpoint has a contact
set only when its trimmed root threshold is positive; otherwise its contact
set is empty and it is used only as the opposite capacity side.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpHeadContactSet
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (headCore : Finset V)
    (ε : ℝ) (head target : ι) : Finset V :=
  if 0 < hpTrimmedThreshold
      (hpHeadEndpointWeight G R C head target)
      ε ((C target).card : ℝ) then
    hpRetainedSet G ε (hpHeadDensityCap G R C head target)
      (C target) headCore
  else ∅

lemma hpHeadContactSet_subset
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (headCore : Finset V)
    (ε : ℝ) (head target : ι) :
    hpHeadContactSet G R C headCore ε head target ⊆ C target := by
  unfold hpHeadContactSet
  split
  · exact hpRetainedSet_subset G ε
      (hpHeadDensityCap G R C head target) (C target) headCore
  · simp

lemma hpTrimmedThreshold_pos_raw
    (weight ε size : ℝ)
    (hpos : 0 < hpTrimmedThreshold weight ε size) :
    2 * ε * size < weight := by
  rw [hpTrimmedThreshold] at hpos
  have : 0 < weight - 2 * ε * size := by
    simpa using! hpos
  linarith

lemma hpHeadContactSet_positive_reduced_edge
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (ε : ℝ) (hε0 : 0 ≤ ε) (head target : ι)
    (hpos : 0 < hpTrimmedThreshold
      (hpHeadEndpointWeight G R C head target)
      ε ((C target).card : ℝ)) :
    R.Adj head target := by
  by_contra hR
  have hraw := hpTrimmedThreshold_pos_raw
    (hpHeadEndpointWeight G R C head target)
    ε ((C target).card : ℝ) hpos
  rw [hpHeadEndpointWeight, if_neg hR] at hraw
  have hprod : (0 : ℝ) ≤ 2 * ε * ((C target).card : ℝ) := by
    positivity
  linarith

/-- A positive-threshold contact side loses fewer than an `ε`-fraction. -/
lemma hpHeadContactSet_removed_lt
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (headCore : Finset V) (head target : ι)
    (hheadCore : headCore ⊆ C head)
    (hheadSig :
      ε * ((C head).card : ℝ) ≤ (headCore.card : ℝ))
    (htarget : (C target).Nonempty)
    (huni : R.Adj head target →
      G.IsUniform ε (C head) (C target))
    (hpos : 0 < hpTrimmedThreshold
      (hpHeadEndpointWeight G R C head target)
      ε ((C target).card : ℝ)) :
    (((C target \ hpHeadContactSet
      G R C headCore ε head target).card : ℕ) : ℝ) <
        ε * ((C target).card : ℝ) := by
  have hR :=
    hpHeadContactSet_positive_reduced_edge
      G R C ε hε0.le head target hpos
  rw [hpHeadContactSet, if_pos hpos]
  apply hpRetainedSet_removed_lt G hε0 hε1
    (C target) (C head) headCore hheadCore hheadSig
  · apply Or.inr
    refine ⟨(huni hR).symm, ?_⟩
    rw [hpHeadDensityCap, if_pos hR,
      SimpleGraph.edgeDensity_comm]
  · exact htarget

/-- Every vertex retained on a positive-threshold side has enough neighbours
back in the head core for the next seed, provided the core has an
`ε`-fraction seed reserve. -/
lemma hpHeadContactSet_seed_degree
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V)
    (ε : ℝ) (hε0 : 0 < ε)
    (headCore : Finset V) (head target : ι)
    (htarget : (C target).Nonempty)
    (seed : ℕ)
    (hseed : (seed : ℝ) < ε * (headCore.card : ℝ))
    {v : V}
    (hv : v ∈ hpHeadContactSet
      G R C headCore ε head target) :
    seed < ((headCore.filter fun x => G.Adj x v).card) := by
  have hpos :
      0 < hpTrimmedThreshold
        (hpHeadEndpointWeight G R C head target)
        ε ((C target).card : ℝ) := by
    by_contra h
    rw [hpHeadContactSet, if_neg h] at hv
    simpa using! hv
  have hR :=
    hpHeadContactSet_positive_reduced_edge
      G R C ε hε0.le head target hpos
  have hvRet :
      v ∈ hpRetainedSet G ε
        (hpHeadDensityCap G R C head target)
        (C target) headCore := by
    simpa [hpHeadContactSet, hpos] using! hv
  have hraw := hpTrimmedThreshold_pos_raw
    (hpHeadEndpointWeight G R C head target)
    ε ((C target).card : ℝ) hpos
  rw [hpHeadEndpointWeight_eq_densityCap_mul] at hraw
  have htargetPos : (0 : ℝ) < (C target).card :=
    Nat.cast_pos.mpr htarget.card_pos
  have hdcap :
      2 * ε < hpHeadDensityCap G R C head target := by
    nlinarith
  have hheadCard0 : (0 : ℝ) ≤ headCore.card := Nat.cast_nonneg _
  have hstrict :
      (seed : ℝ) <
        (hpHeadDensityCap G R C head target - ε) *
          (headCore.card : ℝ) := by
    nlinarith
  have hdegree :=
    hpRetainedSet_degree G ε
      (hpHeadDensityCap G R C head target)
      (C target) headCore hvRet
  have hdegree' :
      (hpHeadDensityCap G R C head target - ε) *
          (headCore.card : ℝ) ≤
        ((headCore.filter fun x => G.Adj x v).card : ℝ) := by
    rw [show headCore.filter (fun x => G.Adj x v) =
        headCore.filter (fun x => G.Adj v x) by
      ext x
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => G.adj_comm x v]
    exact hdegree
  exact_mod_cast hstrict.trans_le hdegree'

end Erdos550
