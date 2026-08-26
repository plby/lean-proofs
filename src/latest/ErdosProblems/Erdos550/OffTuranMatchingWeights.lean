import Mathlib
import ErdosProblems.Erdos550.ClusterDegreeAccounting
import ErdosProblems.Erdos550.HPClusterWeights
import ErdosProblems.Erdos550.OffTuranRegularityData

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching weights from the cleaned exact reduced graph

On a fixed pair of partition classes, the regularity-reduced graph keeps
exactly the original edges when the corresponding reduced edge is present and
keeps none otherwise.  Consequently its normalized cluster contribution is
bounded by the density-times-target-size endpoint weight used by packedness.
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

lemma regularityReduced_adj_iff_fixed_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ)
    (i j : {C // C ∈ P.parts}) {x y : V}
    (hx : x ∈ i.1) (hy : y ∈ j.1) :
    (G.regularityReduced P ε d).Adj x y ↔
      G.Adj x y ∧ (offTuranReducedGraph G P ε d).Adj i j := by
  constructor
  · rintro ⟨hxy, U, hUP, W, hWP, hxU, hyW, hUW, huni, hdens⟩
    have hUi : U = i.1 :=
      P.eq_of_mem_parts hUP i.2 hxU hx
    have hWj : W = j.1 :=
      P.eq_of_mem_parts hWP j.2 hyW hy
    subst U
    subst W
    exact ⟨hxy, fun h => hUW (congrArg Subtype.val h), huni, hdens⟩
  · rintro ⟨hxy, hij, huni, hdens⟩
    exact ⟨hxy, i.1, i.2, j.1, j.2, hx, hy,
      fun h => hij (Subtype.ext h), huni, hdens⟩

lemma clusterContribution_reduced_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) (scale : ℕ)
    (i j : {C // C ∈ P.parts}) :
    clusterContribution (G.regularityReduced P ε d) P scale i j =
      if (offTuranReducedGraph G P ε d).Adj i j then
        clusterContribution G P scale i j
      else 0 := by
  by_cases hij : (offTuranReducedGraph G P ε d).Adj i j
  · rw [if_pos hij]
    unfold clusterContribution
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [show
      (j.1.filter fun w =>
        (G.regularityReduced P ε d).Adj v w) =
          (j.1.filter fun w => G.Adj v w) by
      ext w
      simp only [Finset.mem_filter]
      exact and_congr_right fun hw =>
        (regularityReduced_adj_iff_fixed_parts
          G P ε d i j hv hw).trans (and_iff_left hij)]
  · rw [if_neg hij]
    unfold clusterContribution
    have hz : ∀ v ∈ i.1,
        (j.1.filter fun w =>
          (G.regularityReduced P ε d).Adj v w) = ∅ := by
      intro v hv
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hred
      exact hij
        ((regularityReduced_adj_iff_fixed_parts
          G P ε d i j hv hw).mp hred).2
    have hsum :
        (∑ v ∈ i.1, (((j.1.filter fun w =>
          (G.regularityReduced P ε d).Adj v w).card : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz v hv]
      simp
    rw [hsum]
    simp

lemma clusterContribution_eq_density_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (hscale : 0 < scale)
    (i j : {C // C ∈ P.parts}) :
    clusterContribution G P scale i j =
      (G.edgeDensity i.1 j.1 : ℝ) *
        (i.1.card : ℝ) * (j.1.card : ℝ) / scale := by
  by_cases hi : i.1 = ∅
  · simp [hi, clusterContribution, SimpleGraph.edgeDensity_def]
  by_cases hj : j.1 = ∅
  · simp [hj, clusterContribution, SimpleGraph.edgeDensity_def]
  have hcount :
      (∑ v ∈ i.1, (j.1.filter fun w => G.Adj v w).card) =
        (G.interedges i.1 j.1).card := by
    simp +decide [SimpleGraph.interedges, Rel.interedges,
      Finset.sum_filter]
    rw [Finset.card_filter, Finset.sum_product]
    simp +decide [Finset.sum_ite]
  unfold clusterContribution
  rw [← Nat.cast_sum, hcount, SimpleGraph.edgeDensity_def]
  push_cast
  have hipos : 0 < i.1.card :=
    Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hi)
  have hjpos : 0 < j.1.card :=
    Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hj)
  have hi0 : (i.1.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hipos.ne'
  have hj0 : (j.1.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hjpos.ne'
  have hs0 : (scale : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hscale.ne'
  field_simp

/-- A cleaned normalized contribution is no larger than the corresponding
density-times-target-size endpoint weight. -/
lemma clusterContribution_reduced_le_headEndpointWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) (scale : ℕ) (hscale : 0 < scale)
    (hsize : ∀ i : {C // C ∈ P.parts}, i.1.card ≤ scale)
    (head target : {C // C ∈ P.parts}) :
    clusterContribution (G.regularityReduced P ε d) P scale head target ≤
      hpHeadEndpointWeight G (offTuranReducedGraph G P ε d)
        (fun i : {C // C ∈ P.parts} => i.1) head target := by
  rw [clusterContribution_reduced_eq]
  by_cases hR : (offTuranReducedGraph G P ε d).Adj head target
  · rw [if_pos hR, hpHeadEndpointWeight, if_pos hR,
      clusterContribution_eq_density_mul G P scale hscale]
    have hd0 : (0 : ℝ) ≤ (G.edgeDensity head.1 target.1 : ℝ) := by
      exact_mod_cast G.edgeDensity_nonneg head.1 target.1
    have hhead : (head.1.card : ℝ) ≤ scale := by
      exact_mod_cast hsize head
    have htarget : (0 : ℝ) ≤ target.1.card := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < scale)]
    nlinarith [mul_nonneg hd0 htarget]
  · rw [if_neg hR, hpHeadEndpointWeight, if_neg hR]

end Erdos550
