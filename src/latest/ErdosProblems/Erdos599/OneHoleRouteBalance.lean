/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleResidualExtraction

/-!
# The telescoping balance law for a marked residual route
-/

namespace Erdos599
namespace DWeb

open Set Alternating

universe u

variable {V : Type u}

private theorem oneHoleRoute_edgeBalance_difference
    {G : DWeb V} {J : Set G.DPath} {a b x : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l) :
    edgeBalance (oneHoleRouteForwardEdges G J l) x -
        edgeBalance (oneHoleRouteBackwardEdges G J l) x =
      ∑ i : Fin (l.length - 1),
        (propInt (x = (oneHoleRouteSource l i).vertex) -
          propInt (x = (oneHoleRouteTarget l i).vertex)) := by
  classical
  letI forwardFintype : Fintype (OneHoleRouteForwardIndex G J l) := by
    unfold OneHoleRouteForwardIndex
    infer_instance
  letI backwardFintype : Fintype (OneHoleRouteBackwardIndex G J l) := by
    unfold OneHoleRouteBackwardIndex
    infer_instance
  let contribution : Fin (l.length - 1) → Int := fun i ↦
    propInt (x = (oneHoleRouteSource l i).vertex) -
      propInt (x = (oneHoleRouteTarget l i).vertex)
  have hFbi : Relator.BiUnique
      (fun u v ↦ (u, v) ∈ Set.range (oneHoleRouteForwardEdge G J l)) := by
    rw [← oneHoleRouteForwardEdges_eq_range G J l]
    exact oneHoleRouteForwardEdges_biUnique hl
  have hBbi : Relator.BiUnique
      (fun u v ↦ (u, v) ∈ Set.range (oneHoleRouteBackwardEdge G J l)) := by
    rw [← oneHoleRouteBackwardEdges_eq_range hl]
    exact oneHoleRouteBackwardEdges_biUnique hJ hl
  have hF := edgeBalance_range_eq_sum
    (oneHoleRouteForwardEdge G J l)
    (oneHoleRouteForwardEdge_injective hl) hFbi x
  have hB := edgeBalance_range_eq_sum
    (oneHoleRouteBackwardEdge G J l)
    (oneHoleRouteBackwardEdge_injective hl) hBbi x
  rw [← oneHoleRouteForwardEdges_eq_range G J l] at hF
  rw [← oneHoleRouteBackwardEdges_eq_range hl] at hB
  simp only [oneHoleRouteForwardEdge, oneHoleRouteBackwardEdge] at hF hB
  rw [hF, hB]
  have hBneg :
      (∑ i : OneHoleRouteBackwardIndex G J l,
          (propInt (x = (oneHoleRouteTarget l i.1).vertex) -
            propInt (x = (oneHoleRouteSource l i.1).vertex))) =
        ∑ i : OneHoleRouteBackwardIndex G J l, - contribution i.1 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [contribution]
    omega
  rw [hBneg]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  exact Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin (l.length - 1) ↦
      OneHoleChosenForwardStep G J (oneHoleRouteSource l i)
        (oneHoleRouteTarget l i)) contribution

private theorem oneHoleRoute_contribution_telescope
    {G : DWeb V} {J : Set G.DPath} {a b x : V}
    {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    (∑ i : Fin (l.length - 1),
        (propInt (x = (oneHoleRouteSource l i).vertex) -
          propInt (x = (oneHoleRouteTarget l i).vertex))) =
      propInt (x = a) - propInt (x = b) := by
  classical
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl.1.1
  let f : Fin ((l.length - 1) + 1) → V := fun i ↦
    (l[i.1]'(by omega)).vertex
  calc
    (∑ i : Fin (l.length - 1),
        (propInt (x = (oneHoleRouteSource l i).vertex) -
          propInt (x = (oneHoleRouteTarget l i).vertex))) =
        ∑ i : Fin (l.length - 1),
          (propInt (x = f i.castSucc) - propInt (x = f i.succ)) := by
            apply Finset.sum_congr rfl
            intro i _
            rfl
    _ = propInt (x = f 0) -
          propInt (x = f (Fin.last (l.length - 1))) :=
      sum_adjacent_propInt_eq_boundary (l.length - 1) f x
    _ = propInt (x = a) - propInt (x = b) := by
      have hf0 : f 0 = a := by
        change (l[0]'(by omega)).vertex = a
        exact congrArg OneHoleResidualState.vertex (oneHoleRoute_first hl)
      have hflast : f (Fin.last (l.length - 1)) = b := by
        change (l[l.length - 1]'(by omega)).vertex = b
        exact congrArg OneHoleResidualState.vertex (oneHoleRoute_last hl)
      rw [hf0, hflast]

/-- The unconditional signed balance law of a reduced marked route. -/
theorem oneHoleRouteBalance : OneHoleRouteBalanceLaw V := by
  intro G J a b l hJ ha hl x
  have hu := oneHoleRouteToggledEdges_biUnique hJ ha hl
  have hdisj : Disjoint
      (familyEdges J \ oneHoleRouteBackwardEdges G J l)
      (oneHoleRouteForwardEdges G J l) := by
    rw [Set.disjoint_left]
    intro e heOld heForward
    exact Set.disjoint_left.1
      (oneHoleRouteForwardEdges_disjoint_familyEdges G J l)
        heForward heOld.1
  have htoggle := edgeBalance_sdiff_union_eq_add_sub
    (oneHoleRouteBackwardEdges_subset_familyEdges G J l)
    (fun _ _ _ h₁ h₂ ↦ familyEdges_out_unique hJ.isWarp h₁ h₂)
    (fun _ _ _ h₁ h₂ ↦ familyEdges_in_unique hJ.isWarp h₁ h₂)
    (fun _ _ _ h₁ h₂ ↦ hu.2 h₁ h₂)
    (fun _ _ _ h₁ h₂ ↦ hu.1 h₁ h₂)
    hdisj x
  have htoggle' :
      edgeBalance (oneHoleRouteToggledEdges G J l) x =
        edgeBalance (familyEdges J) x +
          edgeBalance (oneHoleRouteForwardEdges G J l) x -
            edgeBalance (oneHoleRouteBackwardEdges G J l) x := by
    simpa only [oneHoleRouteToggledEdges] using htoggle
  rw [htoggle']
  have hdiff := oneHoleRoute_edgeBalance_difference hJ hl (x := x)
  have htel := oneHoleRoute_contribution_telescope hl (x := x)
  omega

/-- The finite marked residual route produces an exact augmentation. -/
theorem oneHoleMarkedAugmentation : OneHoleMarkedAugmentation V :=
  oneHoleMarkedAugmentation_of_routeBalance oneHoleRouteBalance

end DWeb
end Erdos599
