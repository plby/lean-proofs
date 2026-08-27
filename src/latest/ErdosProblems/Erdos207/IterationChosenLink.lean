/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualLinkTypicality

/-!
# Choosing a typical residual link from iteration typicality

This is the complete random-bisection bridge for one outer center.  Exact
iteration-typical degree/codegree windows are restricted to the residual
neighbor set, and the paired independent sampler chooses a balanced
bipartition with the two-sided bounds required by robust Hall.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The unique structural link needed when a center has no residual
neighbors. -/
def emptyBipartiteLink {V : Type*} [DecidableEq V] (center : V) :
    BipartiteLink V where
  center := center
  left := ∅
  right := ∅
  center_not_left := by simp
  center_not_right := by simp
  disjoint_sides := by simp

@[simp]
lemma emptyBipartiteLink_center
    {V : Type*} [DecidableEq V] (center : V) :
    (emptyBipartiteLink center).center = center := rfl

@[simp]
lemma emptyBipartiteLink_left
    {V : Type*} [DecidableEq V] (center : V) :
    (emptyBipartiteLink center).left = ∅ := rfl

@[simp]
lemma emptyBipartiteLink_right
    {V : Type*} [DecidableEq V] (center : V) :
    (emptyBipartiteLink center).right = ∅ := rfl

lemma emptyBipartiteLink_hasBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (d D codegree : ℕ) :
    HasLinkDegreeCodegreeBounds A (emptyBipartiteLink center)
      d D codegree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact (by simpa using a.2)
  · intro b
    exact (by simpa using b.2)
  · intro a
    exact (by simpa using a.2)
  · intro b
    exact (by simpa using b.2)

/-- Direct paired-bisection constructor from degree and codegree estimates on
the *actual* residual-neighbor set.  Unlike the iteration-typical wrappers
below, this theorem does not compare that set with the whole next vortex
layer.  This is the form needed after a sparse crossing reserve has been
exposed: concentration is first proved on the sampled spokes, and the few
additional residual spokes are then charged explicitly. -/
theorem exists_chosenResidualLink_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V} {center : V}
    (heven : Even (residualNeighbors G R center).card)
    (m d D codegree : ℕ)
    (hdegreeLower : ∀ x ∈ residualNeighbors G R center,
      m ≤ (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card)
    (hdegreeUpper : ∀ x ∈ residualNeighbors G R center,
      (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ≤ D)
    (hcodegreeUpper : ∀ x ∈ residualNeighbors G R center,
      ∀ y ∈ residualNeighbors G R center, x ≠ y →
        (ambientLinkCommonNeighborsIn center A
          (residualNeighbors G R center) x y).card ≤ codegree)
    (hbisection : ((residualNeighbors G R center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G R center K ∧
      HasLinkDegreeCodegreeBounds A K d D codegree := by
  let Wres := residualNeighbors G R center
  let B : BalancedBisection V Wres :=
    Classical.choice (BalancedBisection.nonempty_of_even Wres heven)
  obtain ⟨K, hcenter, hunion, hbalanced, hbounds⟩ :=
    B.exists_paired_goodLinkBisection_of_scalar center
      (center_not_mem_residualNeighbors G R center) A m d D codegree
      (by simpa only [Wres] using hdegreeLower)
      (by simpa only [Wres] using hdegreeUpper)
      (by simpa only [Wres] using hcodegreeUpper)
      (by simpa only [Wres] using hbisection)
  exact ⟨K, ⟨hcenter, hunion, hbalanced⟩, hbounds⟩

/-- The scalar paired-bisection inequality upgrades the residual-link bounds
from iteration typicality to a concrete chosen balanced link. -/
theorem IsIterationTypical.exists_chosenResidualLink_localized
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (center : V)
    (hcOuter : center ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (heven : Even (residualNeighbors G R center).card)
    (m d D codegree loss : ℕ)
    (hcovered :
      ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ((residualNeighbors G R center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G R center K ∧
      HasLinkDegreeCodegreeBounds A K d D codegree := by
  let Wres := residualNeighbors G R center
  let B : BalancedBisection V Wres :=
    Classical.choice (BalancedBisection.nonempty_of_even Wres heven)
  have hbounds := htyp.residualLink_degree_codegree_bounds_localized htri i hki center
    hcOuter hcInner hresInner m D codegree loss hcovered hh hlower hupper
      hcodegree
  obtain ⟨K, hcenter, hunion, hbalanced, htypK⟩ :=
    B.exists_paired_goodLinkBisection_of_scalar center
      (center_not_mem_residualNeighbors G R center) A m d D codegree
      (fun x hx ↦ (hbounds.1 x hx).1)
      (fun x hx ↦ (hbounds.1 x hx).2)
      hbounds.2 (by simpa only [Wres] using hbisection)
  exact ⟨K, ⟨hcenter, hunion, hbalanced⟩, htypK⟩

/-- Coarser form in which the full covered degree bounds the localized
next-level loss. -/
theorem IsIterationTypical.exists_chosenResidualLink
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (center : V)
    (hcOuter : center ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (heven : Even (residualNeighbors G R center).card)
    (m d D codegree loss : ℕ)
    (hcovered : (coveredGraph R).degree center ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ((residualNeighbors G R center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G R center K ∧
      HasLinkDegreeCodegreeBounds A K d D codegree := by
  apply htyp.exists_chosenResidualLink_localized htri i hki center hcOuter
    hcInner hresInner heven m d D codegree loss _ hh hlower hupper
      hcodegree hbisection
  calc
    ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤
        ((coveredGraph R).neighborFinset center).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph R).degree center := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ loss := hcovered

/-- If the current graph is supported on the outer level, the chosen-link
constructor applies to every center: a nonempty residual link certifies outer
membership through one incident graph edge, while an empty residual link is
handled by `emptyBipartiteLink`. -/
theorem IsIterationTypical.exists_chosenResidualLink_of_supported_localized
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (center : V) (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (heven : Even (residualNeighbors G R center).card)
    (m d D codegree loss : ℕ)
    (hcovered :
      ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ((residualNeighbors G R center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G R center K ∧
      HasLinkDegreeCodegreeBounds A K d D codegree := by
  by_cases hnonempty : (residualNeighbors G R center).Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    have hcxG := (mem_residualNeighbors_iff.mp hx).1
    have hcOuter := (hGsupp hcxG).1
    exact htyp.exists_chosenResidualLink_localized htri i hki center hcOuter hcInner
      hresInner heven m d D codegree loss hcovered hh hlower hupper
      hcodegree hbisection
  · have hempty : residualNeighbors G R center = ∅ := not_nonempty_iff_eq_empty.mp
      hnonempty
    refine ⟨emptyBipartiteLink center, ?_,
      emptyBipartiteLink_hasBounds center A d D codegree⟩
    exact ⟨rfl, by simpa [hempty], by simp⟩

/-- Coarser supported-center form using the full covered degree. -/
theorem IsIterationTypical.exists_chosenResidualLink_of_supported
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (center : V) (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (heven : Even (residualNeighbors G R center).card)
    (m d D codegree loss : ℕ)
    (hcovered : (coveredGraph R).degree center ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ((residualNeighbors G R center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G R center K ∧
      HasLinkDegreeCodegreeBounds A K d D codegree := by
  apply htyp.exists_chosenResidualLink_of_supported_localized htri i hki
    hGsupp center hcInner hresInner heven m d D codegree loss _ hh hlower
      hupper hcodegree hbisection
  calc
    ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤
        ((coveredGraph R).neighborFinset center).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph R).degree center := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ loss := hcovered

end

end Erdos207
