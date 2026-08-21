/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos88.StructuredClaimUpper
import ErdosProblems.Erdos88.SwitchingLower

/-!
# Conditioning the structured decomposition

This file identifies a subset of the canonically relabelled covered
coordinates with its subset of the original vertex set.  It then records the
exact polynomial identity obtained after fixing a subset of the small RLCD
remainder.
-/

namespace Erdos88.RLCD.BucketDecomposition

attribute [local instance] Classical.propDecidable

/-- A subset of the standard finite model of the covered coordinates,
regarded as a subset of the original coordinate type. -/
noncomputable def finCoveredSubsetImage
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (S : Finset (Fin (Fintype.card D.Covered))) : Finset (Fin n) :=
  BoundedWindow.subtypeSubsetImage (D.blocks.biUnion id)
    (Switching.equivFinsetImage D.finCoveredEquiv S)

lemma finCoveredSubsetImage_subset
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    D.finCoveredSubsetImage S ⊆ D.blocks.biUnion id := by
  exact BoundedWindow.subtypeSubsetImage_subset _ _

lemma subtypeSubsetImage_finCoveredEquiv
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    BoundedWindow.subtypeSubsetImage (D.blocks.biUnion id)
        (Equiv.finsetCongr D.finCoveredEquiv S) =
      D.finCoveredSubsetImage S := by
  rfl

/-- Exact two-stage disintegration of the unbiased Boolean cube into a
remainder subset and a canonically relabelled covered subset. -/
lemma expectation_half_remainder_covered_fubini
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (f : Finset (Fin n) → ℝ) :
    Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          Probability.expectation (1 / 2 : ℝ)
            (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
              f (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                D.finCoveredSubsetImage S))) =
      Probability.expectation (1 / 2 : ℝ) f := by
  classical
  let eCovered : Finset (Fin (Fintype.card D.Covered)) ≃
      Finset (D.Covered) := Equiv.finsetCongr D.finCoveredEquiv
  have hcovered (R : Finset (D.remainder : Set (Fin n))) :
      Probability.expectation (1 / 2 : ℝ)
          (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
            f (BoundedWindow.subtypeSubsetImage D.remainder R ∪
              D.finCoveredSubsetImage S)) =
        Probability.expectation (1 / 2 : ℝ)
          (fun T : Finset (D.Covered) ↦
            f (BoundedWindow.subtypeSubsetImage D.remainder R ∪
              BoundedWindow.subtypeSubsetImage
                (D.blocks.biUnion id) T)) := by
    rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite,
      ← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
    apply Switching.uniformExpectation_equiv eCovered
    intro S
    rw [subtypeSubsetImage_finCoveredEquiv]
  simp_rw [hcovered]
  have hFub := Switching.expectation_half_disjoint_union_fubini
    D.remainder (D.blocks.biUnion id) D.remainder_disjoint f
  change
    (Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          Probability.expectation (1 / 2 : ℝ)
            (fun T : Finset D.Covered ↦
              f (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                BoundedWindow.subtypeSubsetImage
                  (D.blocks.biUnion id) T)))) = _ at hFub
  rw [hFub]
  let eVertex : ((Finset.univ : Finset (Fin n)) : Set (Fin n)) ≃
      Fin n :=
    { toFun := Subtype.val
      invFun := fun v ↦ ⟨v, Finset.mem_univ v⟩
      left_inv := fun v ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  let eUniv : Finset ((Finset.univ : Finset (Fin n)) : Set (Fin n)) ≃
      Finset (Fin n) := Equiv.finsetCongr eVertex
  rw [D.remainder_union_covered]
  rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite,
    ← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  apply Switching.uniformExpectation_equiv eUniv
  intro S
  congr 1
  ext v
  simp [eUniv, eVertex, BoundedWindow.subtypeSubsetImage]

/-- Event form of `expectation_half_remainder_covered_fubini`. -/
lemma eventProbability_half_remainder_covered_fubini
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (E : Finset (Fin n) → Prop) :
    Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          Probability.eventProbability (1 / 2 : ℝ)
            (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
              E (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                D.finCoveredSubsetImage S))) =
      Probability.eventProbability (1 / 2 : ℝ) E := by
  classical
  exact D.expectation_half_remainder_covered_fubini
    (fun U ↦ if E U then 1 else 0)

lemma disjoint_finCoveredSubsetImage_of_subset_remainder
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    Disjoint O (D.finCoveredSubsetImage S) := by
  exact D.remainder_disjoint.mono hO (D.finCoveredSubsetImage_subset S)

/-- The perturbed edge polynomial on the relabelled covered graph is the
ambient polynomial evaluated on the corresponding covered subset. -/
lemma perturbedEdgePolynomial_finCoveredGraph
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n))
    (e0 : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    Probability.perturbedEdgePolynomial (D.finCoveredGraph G) e0
        (fun i ↦ c (D.finCoveredEquiv i).1) S =
      Probability.perturbedEdgePolynomial G e0 c
        (D.finCoveredSubsetImage S) := by
  calc
    Probability.perturbedEdgePolynomial (D.finCoveredGraph G) e0
        (fun i ↦ c (D.finCoveredEquiv i).1) S =
      Probability.perturbedEdgePolynomial
        (G.induce (D.blocks.biUnion id : Set (Fin n))) e0
        (fun v ↦ c v.1)
        (Switching.equivFinsetImage D.finCoveredEquiv S) := by
          exact Switching.perturbedEdgePolynomial_comap_equiv
            (G.induce (D.blocks.biUnion id : Set (Fin n)))
              D.finCoveredEquiv e0 (fun v ↦ c v.1) S
    _ = Probability.perturbedEdgePolynomial G e0 c
        (D.finCoveredSubsetImage S) := by
          exact BoundedWindow.perturbedEdgePolynomial_induce_subtypeSubsetImage
            G (D.blocks.biUnion id) e0 c
              (Switching.equivFinsetImage D.finCoveredEquiv S)

/-- Fixing any subset of the RLCD remainder only changes the constant and
linear coefficients of the polynomial on the covered induced graph. -/
lemma perturbedEdgePolynomial_union_finCoveredSubsetImage
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n))
    (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    Probability.perturbedEdgePolynomial G e0 c
        (O ∪ D.finCoveredSubsetImage S) =
      Probability.perturbedEdgePolynomial (D.finCoveredGraph G)
        (Probability.perturbedEdgePolynomial G e0 c O)
        (fun i ↦ c (D.finCoveredEquiv i).1 +
          AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O) S := by
  have hdisjoint := D.disjoint_finCoveredSubsetImage_of_subset_remainder hO S
  have hunion := Switching.perturbedEdgePolynomial_union_of_disjoint
    G e0 c hdisjoint
  have hreindex := D.perturbedEdgePolynomial_finCoveredGraph G
    (Probability.perturbedEdgePolynomial G e0 c O)
    (fun v ↦ c v + AKSGraph.degreeInto G v O) S
  exact hunion.trans hreindex.symm

/-- The linear perturbation induced on the covered graph after fixing the
outside set `O`. -/
noncomputable def conditionedCoveredCoefficient
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n)) (i : Fin (Fintype.card D.Covered)) : ℝ :=
  c (D.finCoveredEquiv i).1 +
    AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O

/-- The degree in the canonically relabelled covered graph is the ambient
degree into the union of the RLCD blocks. -/
lemma degree_finCoveredGraph
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (i : Fin (Fintype.card D.Covered)) :
    (D.finCoveredGraph G).degree i =
      AKSGraph.degreeInto G (D.finCoveredEquiv i).1
        (D.blocks.biUnion id) := by
  let iso : D.finCoveredGraph G ≃g
      G.induce (D.blocks.biUnion id : Set (Fin n)) :=
    { toEquiv := D.finCoveredEquiv
      map_rel_iff' := by intro u v; rfl }
  have hiso := iso.degree_eq i
  have hinduce (v : (D.blocks.biUnion id : Set (Fin n))) :
      (G.induce (D.blocks.biUnion id : Set (Fin n))).degree v =
        AKSGraph.degreeInto G v.1 (D.blocks.biUnion id) := by
    let e : (G.induce (D.blocks.biUnion id : Set (Fin n))).neighborSet v ≃
        {x : Fin n // x ∈ G.neighborFinset v.1 ∩ D.blocks.biUnion id} :=
      { toFun := fun x ↦ ⟨x.1.1, by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨x.2, x.1.2⟩⟩
        invFun := fun x ↦ ⟨⟨x.1, (Finset.mem_inter.mp x.2).2⟩, by
          change G.Adj v.1 x.1
          simpa only [SimpleGraph.mem_neighborFinset] using
            (Finset.mem_inter.mp x.2).1⟩
        left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := by intro x; apply Subtype.ext; rfl }
    calc
      (G.induce (D.blocks.biUnion id : Set (Fin n))).degree v =
          Fintype.card
            ((G.induce (D.blocks.biUnion id : Set (Fin n))).neighborSet v) :=
        (SimpleGraph.card_neighborSet_eq_degree
          (G := G.induce (D.blocks.biUnion id : Set (Fin n))) v).symm
      _ = Fintype.card
          {x : Fin n // x ∈ G.neighborFinset v.1 ∩ D.blocks.biUnion id} :=
        Fintype.card_congr e
      _ = (G.neighborFinset v.1 ∩ D.blocks.biUnion id).card :=
        Fintype.card_coe _
      _ = AKSGraph.degreeInto G v.1 (D.blocks.biUnion id) := rfl
  calc
    (D.finCoveredGraph G).degree i =
        (G.induce (D.blocks.biUnion id : Set (Fin n))).degree (iso i) :=
      hiso.symm
    _ = AKSGraph.degreeInto G (iso i).1 (D.blocks.biUnion id) :=
      hinduce (iso i)
    _ = AKSGraph.degreeInto G (D.finCoveredEquiv i).1
        (D.blocks.biUnion id) := rfl

/-- The conditioned effective coefficient differs from the original one by
the centered number of selected remainder-neighbours.  This is the exact
deterministic identity behind the typical-remainder event in Section 12. -/
lemma graphEffectiveLinear_conditionedCoveredCoefficient
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n)) (i : Fin (Fintype.card D.Covered)) :
    GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
        (D.conditionedCoveredCoefficient G c O) i =
      GraphQuadratic.graphEffectiveLinear G c (D.finCoveredEquiv i).1 +
        ((AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2) := by
  let v : Fin n := (D.finCoveredEquiv i).1
  have hsplitNat : G.degree v =
      AKSGraph.degreeInto G v D.remainder +
        AKSGraph.degreeInto G v (D.blocks.biUnion id) := by
    calc
      G.degree v = AKSGraph.degreeInto G v (Finset.univ : Finset (Fin n)) := by
        simp only [AKSGraph.degreeInto, Finset.inter_univ,
          SimpleGraph.card_neighborFinset_eq_degree]
      _ = AKSGraph.degreeInto G v
          (D.remainder ∪ D.blocks.biUnion id) := by
            rw [D.remainder_union_covered]
      _ = AKSGraph.degreeInto G v D.remainder +
          AKSGraph.degreeInto G v (D.blocks.biUnion id) :=
            Switching.degreeInto_union_of_disjoint G v D.remainder_disjoint
  have hsplit : (G.degree v : ℝ) =
      (AKSGraph.degreeInto G v D.remainder : ℝ) +
        (AKSGraph.degreeInto G v (D.blocks.biUnion id) : ℝ) := by
    exact_mod_cast hsplitNat
  have hdegree : ((D.finCoveredGraph G).degree i : ℝ) =
      (AKSGraph.degreeInto G v (D.blocks.biUnion id) : ℝ) := by
    exact_mod_cast D.degree_finCoveredGraph G i
  rw [GraphQuadratic.graphEffectiveLinear,
    GraphQuadratic.graphEffectiveLinear, conditionedCoveredCoefficient]
  change c v + (AKSGraph.degreeInto G v O : ℝ) +
      ((D.finCoveredGraph G).degree i : ℝ) / 2 =
    c v + (G.degree v : ℝ) / 2 +
      ((AKSGraph.degreeInto G v O : ℝ) -
        (AKSGraph.degreeInto G v D.remainder : ℝ) / 2)
  rw [hdegree, hsplit]
  ring

/-- A typical half-sample of the remainder preserves closeness to the RLCD
block center on every covered coordinate. -/
lemma conditionedCovered_close_to_blockCenter
    {n k : ℕ} {d : Fin n → ℝ} {rho t : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (hd : d = GraphQuadratic.graphEffectiveLinear G c)
    (O : Finset (Fin n))
    (htypical : ∀ i : Fin (Fintype.card D.Covered),
      |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
        (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| ≤ t)
    (i : Fin (Fintype.card D.Covered)) :
    |GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O) i -
        D.blockCenter
          (D.finBlockEquiv (D.finCoveredPartition.bucket i))| ≤ rho + t := by
  rw [D.graphEffectiveLinear_conditionedCoveredCoefficient G c O i]
  have hblock := D.finCovered_close_to_blockCenter i
  have hdi : d (D.finCoveredEquiv i).1 =
      GraphQuadratic.graphEffectiveLinear G c (D.finCoveredEquiv i).1 :=
    congrFun hd (D.finCoveredEquiv i).1
  rw [hdi] at hblock
  calc
    |GraphQuadratic.graphEffectiveLinear G (c := c) (D.finCoveredEquiv i).1 +
          ((AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
            (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2) -
        D.blockCenter (D.finBlockEquiv (D.finCoveredPartition.bucket i))| ≤
      |GraphQuadratic.graphEffectiveLinear G c (D.finCoveredEquiv i).1 -
          D.blockCenter (D.finBlockEquiv (D.finCoveredPartition.bucket i))| +
        |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| := by
            have hrearrange :
                GraphQuadratic.graphEffectiveLinear G c
                    (D.finCoveredEquiv i).1 +
                    ((AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
                      (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                        D.remainder : ℝ) / 2) -
                  D.blockCenter
                    (D.finBlockEquiv (D.finCoveredPartition.bucket i)) =
                (GraphQuadratic.graphEffectiveLinear G c
                    (D.finCoveredEquiv i).1 -
                  D.blockCenter
                    (D.finBlockEquiv (D.finCoveredPartition.bucket i))) +
                  ((AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
                    (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                      D.remainder : ℝ) / 2) := by ring
            rw [hrearrange]
            exact abs_add_le _ _
    _ ≤ rho + t := add_le_add hblock (htypical i)

/-- After fixing the remainder assignment, the graph-slice polynomial on the
covered graph is pointwise the original ambient perturbed edge polynomial.
This is the exact finite conditioning bridge into the product-slice model. -/
lemma sliceQuadratic_conditionedCovered_eq
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (S : Finset (Fin (Fintype.card D.Covered))) :
    BooleanSlices.sliceQuadratic
        (GraphQuadratic.graphSliceConstant (D.finCoveredGraph G)
          (Probability.perturbedEdgePolynomial G e0 c O)
          (D.conditionedCoveredCoefficient G c O))
        (GraphQuadratic.graphSliceLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O))
        (GraphQuadratic.graphSliceMatrix (D.finCoveredGraph G)) S =
      Probability.perturbedEdgePolynomial G e0 c
        (O ∪ D.finCoveredSubsetImage S) := by
  calc
    BooleanSlices.sliceQuadratic
        (GraphQuadratic.graphSliceConstant (D.finCoveredGraph G)
          (Probability.perturbedEdgePolynomial G e0 c O)
          (D.conditionedCoveredCoefficient G c O))
        (GraphQuadratic.graphSliceLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O))
        (GraphQuadratic.graphSliceMatrix (D.finCoveredGraph G)) S =
      Probability.perturbedEdgePolynomial (D.finCoveredGraph G)
        (Probability.perturbedEdgePolynomial G e0 c O)
        (D.conditionedCoveredCoefficient G c O) S :=
      GraphQuadratic.sliceQuadratic_graph_coefficients
        (D.finCoveredGraph G) _ _ S
    _ = Probability.perturbedEdgePolynomial G e0 c
        (O ∪ D.finCoveredSubsetImage S) :=
      (D.perturbedEdgePolynomial_union_finCoveredSubsetImage
        G e0 c hO S).symm

end Erdos88.RLCD.BucketDecomposition
