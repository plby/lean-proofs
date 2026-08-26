import Mathlib
import ErdosProblems.Erdos550.MatchingHeadDegreeTransfer

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cluster-degree accounting

The off--Turán proof uses the normalized number of cleaned edges incident with
a cluster, not the combinatorial degree of the reduced graph.  These lemmas
record the exact double-counting identities for a finite partition.
-/

open SimpleGraph Finset Finpartition

namespace Erdos550

open Classical

/-- Normalized edge contribution from part `i` to part `j`. -/
noncomputable def clusterContribution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (i j : {C // C ∈ P.parts}) : ℝ :=
  (∑ v ∈ i.1, (((j.1.filter fun w => G.Adj v w).card : ℕ) : ℝ)) /
    (scale : ℝ)

/-- Total normalized degree of one partition class. -/
noncomputable def clusterNormalizedDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (i : {C // C ∈ P.parts}) : ℝ :=
  ∑ j, clusterContribution G P scale i j

lemma sum_neighbor_counts_over_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (v : V) :
    ∑ j : {C // C ∈ P.parts},
        (j.1.filter fun w => G.Adj v w).card = G.degree v := by
  rw [← Finset.card_biUnion]
  · rw [show Finset.univ.biUnion
          (fun j : {C // C ∈ P.parts} =>
            j.1.filter fun w => G.Adj v w) =
        G.neighborFinset v by
      ext w
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨j, hwj, hvw⟩
        exact hvw
      · intro hvw
        obtain ⟨C, hCP, hwC⟩ := P.exists_mem (Finset.mem_univ w)
        exact ⟨⟨C, hCP⟩, hwC, hvw⟩]
    exact SimpleGraph.card_neighborFinset_eq_degree G v
  · intro i _ j _ hij
    apply Disjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
    exact P.disjoint i.2 j.2 (fun h => hij (Subtype.ext h))

lemma clusterNormalizedDegree_eq_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (i : {C // C ∈ P.parts}) :
    clusterNormalizedDegree G P scale i =
      (∑ v ∈ i.1, (G.degree v : ℝ)) / (scale : ℝ) := by
  simp only [clusterNormalizedDegree, clusterContribution]
  have hsum :
      (∑ j : {C // C ∈ P.parts},
          ∑ v ∈ i.1,
            (((j.1.filter fun w => G.Adj v w).card : ℕ) : ℝ)) =
        ∑ v ∈ i.1, (G.degree v : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Nat.cast_sum, sum_neighbor_counts_over_parts G P v]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ => x / (scale : ℝ)) hsum

/-- The normalized cluster degrees sum to the normalized host degree sum. -/
lemma sum_clusterNormalizedDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) :
    ∑ i, clusterNormalizedDegree G P scale i =
      2 * (G.edgeFinset.card : ℝ) / (scale : ℝ) := by
  simp_rw [clusterNormalizedDegree_eq_degree_sum]
  rw [← Finset.sum_div, ← Finset.sum_biUnion]
  · rw [show Finset.univ.biUnion
          (fun i : {C // C ∈ P.parts} => i.1) =
        (Finset.univ : Finset V) by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · exact fun _ => trivial
      · intro _
        obtain ⟨C, hCP, hvC⟩ := P.exists_mem (Finset.mem_univ v)
        exact ⟨⟨C, hCP⟩, hvC⟩]
    rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
    push_cast
    ring
  · intro i _ j _ hij
    exact P.disjoint i.2 j.2 (fun h => hij (Subtype.ext h))

lemma clusterContribution_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (i j : {C // C ∈ P.parts}) :
    0 ≤ clusterContribution G P scale i j := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    (Nat.cast_nonneg _)

/-- A contribution is at most the target-cluster size when both parts have
size at most the positive normalizing scale. -/
lemma clusterContribution_le_scale
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (hscale : 0 < scale)
    (hsize : ∀ i : {C // C ∈ P.parts}, i.1.card ≤ scale)
    (i j : {C // C ∈ P.parts}) :
    clusterContribution G P scale i j ≤ scale := by
  have hterm : ∀ v ∈ i.1,
      ((j.1.filter fun w => G.Adj v w).card : ℝ) ≤ scale := by
    intro v hv
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (hsize j)
  have hsum :
      (∑ v ∈ i.1,
        (((j.1.filter fun w => G.Adj v w).card : ℕ) : ℝ)) ≤
          (scale : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _v ∈ i.1, (scale : ℝ) :=
        Finset.sum_le_sum hterm
      _ = (i.1.card : ℝ) * scale := by simp
      _ ≤ (scale : ℝ) * scale := by
        gcongr
        exact_mod_cast hsize i
      _ = (scale : ℝ) ^ 2 := by ring
  rw [clusterContribution, div_le_iff₀ (by positivity : (0 : ℝ) < scale)]
  simpa [pow_two] using! hsum

/-- Every normalized cluster degree is at most the host order. -/
lemma clusterNormalizedDegree_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ) (hscale : 0 < scale)
    (hsize : ∀ i : {C // C ∈ P.parts}, i.1.card ≤ scale)
    (i : {C // C ∈ P.parts}) :
    clusterNormalizedDegree G P scale i ≤ Fintype.card V := by
  rw [clusterNormalizedDegree_eq_degree_sum]
  have hdeg : ∀ v ∈ i.1, (G.degree v : ℝ) ≤ Fintype.card V := by
    intro v hv
    exact_mod_cast (Nat.le_of_lt (G.degree_lt_card_verts v))
  have hsum :
      (∑ v ∈ i.1, (G.degree v : ℝ)) ≤
        (scale : ℝ) * Fintype.card V := by
    calc
      _ ≤ ∑ _v ∈ i.1, (Fintype.card V : ℝ) :=
        Finset.sum_le_sum hdeg
      _ = (i.1.card : ℝ) * Fintype.card V := by simp
      _ ≤ (scale : ℝ) * Fintype.card V := by
        gcongr
        exact_mod_cast hsize i
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < scale)]
  simpa [mul_comm] using! hsum

/-- Maximal-matching coverage transfers a heavy normalized cluster degree to
the union of the matching endpoints. -/
lemma matched_clusterContribution_lower
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : ι → ℝ) (scale : ℝ)
    (hfs : ∀ i, f i ≤ scale) (hscale : 0 ≤ scale)
    (X Y : ι) (cL cR : κ → ι) (U : Finset ι)
    (hU : ∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
      a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR)
    (B : ℕ) (hsmall : U.card < B) :
    (∑ i, f i) - (B + 2) * scale ≤
      ∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR), f i :=
  matching_endpoint_sum_lower X Y cL cR U hU B hsmall f scale
    hfs hscale

end Erdos550
