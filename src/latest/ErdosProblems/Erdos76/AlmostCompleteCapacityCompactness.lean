/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostCompleteCompactness
import ErdosProblems.Erdos76.FractionalTransport

/-!
# Capacity decompositions from unweighted decompositions

`AlmostCompleteCompactness.weightedReduction` retains the companion paper's
extra half-bound because its input is the strong almost-complete theorem.
For Proposition 4.2 we only need exact capacity decompositions.  The same
upper-rational-approximation and finite-cube argument works directly from
exact decompositions of the row graphs, with the compact cube `[0,1]` in
place of `[0,1/2]`.
-/

open Finset Filter Set
open scoped BigOperators Topology

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

private lemma IsFractionalDecomposition.relabel_capacity
    {B : Type*} [Fintype B] [DecidableEq B]
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalDecomposition G w) (e : A ≃ B) :
    IsFractionalDecomposition (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  refine ⟨hw.isPacking.relabel e, ?_⟩
  intro p hp
  have hp' := SimpleGraph.mem_edgeFinset.mp hp
  rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  rw [fractionalEdgeLoad_relabel]
  exact hw.edgeLoad_eq_one (SimpleGraph.mem_edgeFinset.mpr hq)

/-- Exact decompositions transport from the `Fin n` statement to an
arbitrary finite vertex type of the same cardinality. -/
theorem almostCompleteFractionalDecomposition_on_fintype
    (hAC : AlmostCompleteFractionalDecomposition)
    (G : SimpleGraph A) (hcard : 7 ≤ Fintype.card A)
    (hmissing : missingEdgeCount G ≤ Fintype.card A - 4) :
    ∃ w : Finset A → ℝ, IsFractionalDecomposition G w := by
  classical
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFinOfCardEq rfl
  let H : SimpleGraph (Fin (Fintype.card A)) := G.map e.toEmbedding
  letI : DecidableRel H.Adj := Classical.decRel _
  have hmissH : missingEdgeCount H ≤ Fintype.card A - 4 := by
    have hc : Hᶜ = Gᶜ.map e.toEmbedding := compl_map_equiv G e
    have hedge : Hᶜ.edgeFinset = (Gᶜ.map e.toEmbedding).edgeFinset := by
      ext p
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hc]
    unfold missingEdgeCount at hmissing ⊢
    calc
      Hᶜ.edgeFinset.card = (Gᶜ.map e.toEmbedding).edgeFinset.card :=
        congrArg Finset.card hedge
      _ = Gᶜ.edgeFinset.card :=
        SimpleGraph.card_edgeFinset_map e.toEmbedding Gᶜ
      _ ≤ Fintype.card A - 4 := hmissing
  obtain ⟨w, hw⟩ := hAC (Fintype.card A) hcard H hmissH
  let u : Finset A → ℝ := relabelWeight e.symm w
  have hmap : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  refine ⟨u, ?_⟩
  simpa only [u, hmap] using hw.relabel_capacity e.symm

/-- Rational capacity decomposition with a displayed common denominator. -/
theorem rationalWeightedDecomposition {r m : ℕ} (hr : 0 < r)
    (c : Sym2 A → ℝ) (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (d : CompleteEdge A → ℕ) (hrange : ∀ e, d e ≤ r)
    (hcDeficit : ∀ e : CompleteEdge A,
      c e = 1 - (d e : ℝ) / (r : ℝ))
    (hmissing : capacityMissingWeight c ≤ (m : ℝ))
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition H w) :
    ∃ w : Finset A → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph A) c w := by
  obtain ⟨S, hcard, hmult⟩ := exists_deficit_distribution r m d hrange
    (integralDeficits_total_le hr c d hcDeficit hmissing)
  apply weightedDecomposition_of_deficitRows hr S hcard c
  · exact averageGraphCapacity_deficitRows_eq hr d S hmult c
      (fun e he ↦ hc.eq_zero_of_isDiag he) hcDeficit
  · exact hgraphs

private lemma IsFractionalPacking.weight_le_one_on_triangle
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w)
    {t : Finset A} (ht : G.IsNClique 3 t) : w t ≤ 1 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
  let e : Sym2 A := s(a, b)
  have he : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ht.isClique (by simp) (by simp) hab
  have htri : {a, b, c} ∈
      (G.cliqueFinset 3).filter (fun u ↦ e ∈ u.sym2) := by
    rw [mem_filter]
    exact ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ht, by simp [e]⟩
  calc
    w {a, b, c} ≤ fractionalEdgeLoad G w e := by
      unfold fractionalEdgeLoad
      exact Finset.single_le_sum
        (fun u hu ↦ hw.nonneg_on (mem_filter.mp hu).1) htri
    _ ≤ 1 := hw.edgeLoad_le_one he

private lemma zeroExtendTriangleWeight_mem_unitCube
    (G : SimpleGraph A) (w : Finset A → ℝ)
    (hw : IsFractionalPacking G w) :
    zeroExtendTriangleWeight G w ∈
      Set.Icc (fun _ ↦ 0) (fun _ ↦ 1) := by
  constructor
  · intro t
    by_cases ht : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem ht]
      exact hw.nonneg_on ht
    · rw [zeroExtendTriangleWeight_of_not_mem ht]
  · intro t
    by_cases ht : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem ht]
      exact hw.weight_le_one_on_triangle
        (SimpleGraph.mem_cliqueFinset_iff.mp ht)
    · rw [zeroExtendTriangleWeight_of_not_mem ht]
      norm_num

/-- Compactness analogue of Corollary 2.12 which needs only exact
decompositions of the unweighted row graphs and does not retain a half-bound. -/
theorem capacityDecomposition_of_fractionalDecompositions
    {m : ℕ} (c : Sym2 A → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (hmissing : capacityMissingWeight c ≤ (m : ℝ))
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition H w) :
    ∃ w : Finset A → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph A) c w := by
  have hex : ∀ k : ℕ, ∃ w : Finset A → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph A)
        (upperCapacityApprox c k) w := by
    intro k
    exact rationalWeightedDecomposition (Nat.succ_pos k)
      (upperCapacityApprox c k) (upperCapacityApprox_isEdgeCapacity hc k)
      (upperCapacityDeficit c k) (upperCapacityDeficit_le c k)
      (upperCapacityApprox_deficit hc k)
      ((capacityMissingWeight_upperCapacityApprox_le hc k).trans hmissing)
      hgraphs
  choose w hw using hex
  let v : ℕ → Finset A → ℝ := fun k ↦
    zeroExtendTriangleWeight (⊤ : SimpleGraph A) (w k)
  have hv : ∀ k,
      IsCapacityDecomposition (⊤ : SimpleGraph A)
        (upperCapacityApprox c k) (v k) := by
    intro k
    constructor
    · constructor
      · exact zeroExtendTriangleWeight_nonneg le_rfl
          ((hw k).1.toFractionalPacking
            (upperCapacityApprox_isEdgeCapacity hc k))
      · intro e he
        rw [fractionalEdgeLoad_zeroExtend le_rfl]
        exact (hw k).1.2 e he
    · intro e he
      rw [fractionalEdgeLoad_zeroExtend le_rfl]
      exact (hw k).2 e he
  have hwPacking : ∀ k, IsFractionalPacking (⊤ : SimpleGraph A) (w k) := by
    intro k
    exact (hw k).1.toFractionalPacking
      (upperCapacityApprox_isEdgeCapacity hc k)
  let K : Set (Finset A → ℝ) :=
    Set.Icc (fun _ ↦ 0) (fun _ ↦ 1)
  have hvK : ∀ k, v k ∈ K := by
    intro k
    exact zeroExtendTriangleWeight_mem_unitCube (⊤ : SimpleGraph A)
      (w k) (hwPacking k)
  obtain ⟨wlim, hwlimK, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact K).tendsto_subseq hvK
  refine ⟨wlim, ?_, ?_⟩
  · constructor
    · intro t _ht
      exact hwlimK.1 t
    · intro e he
      have hload : Tendsto
          (fun n ↦ fractionalEdgeLoad (⊤ : SimpleGraph A) (v (φ n)) e)
          atTop (𝓝 (fractionalEdgeLoad (⊤ : SimpleGraph A) wlim e)) := by
        unfold fractionalEdgeLoad
        apply tendsto_finsetSum
        intro t ht
        simpa only [Function.comp_apply] using tendsto_pi_nhds.mp hlim t
      have hcap := (tendsto_upperCapacityApprox c hc e).comp hφ.tendsto_atTop
      exact le_of_tendsto_of_tendsto' hload hcap fun n ↦ (hv (φ n)).1.2 e he
  · intro e he
    have hload : Tendsto
        (fun n ↦ fractionalEdgeLoad (⊤ : SimpleGraph A) (v (φ n)) e)
        atTop (𝓝 (fractionalEdgeLoad (⊤ : SimpleGraph A) wlim e)) := by
      unfold fractionalEdgeLoad
      apply tendsto_finsetSum
      intro t ht
      simpa only [Function.comp_apply] using tendsto_pi_nhds.mp hlim t
    have hcap := (tendsto_upperCapacityApprox c hc e).comp hφ.tendsto_atTop
    have heq : ∀ n,
        fractionalEdgeLoad (⊤ : SimpleGraph A) (v (φ n)) e =
          upperCapacityApprox c (φ n) e := fun n ↦ (hv (φ n)).2 e he
    have hloadToCap : Tendsto
        (fun n ↦ fractionalEdgeLoad (⊤ : SimpleGraph A) (v (φ n)) e)
        atTop (𝓝 (c e)) := by
      exact hcap.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm)
    exact tendsto_nhds_unique hload hloadToCap

/-- Corollary 2.12 in the exact form needed downstream: the unweighted
almost-complete decomposition theorem implies decomposition of every real
capacity with total deficit at most `|A|-4`. -/
theorem capacityDecomposition_of_almostComplete
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcard : 7 ≤ Fintype.card A)
    (c : Sym2 A → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (hmissing : capacityMissingWeight c ≤
      ((Fintype.card A - 4 : ℕ) : ℝ)) :
    ∃ w : Finset A → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph A) c w := by
  apply capacityDecomposition_of_fractionalDecompositions c hc hmissing
  intro H hH
  exact almostCompleteFractionalDecomposition_on_fintype hAC H hcard hH

end

end Erdos76
