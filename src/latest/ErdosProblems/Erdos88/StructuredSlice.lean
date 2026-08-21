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

import ErdosProblems.Erdos88.StructuredConditioning

/-!
# The structured polynomial on a fixed product slice

This file reconciles the graph-Walsh normalization with the matrix notation
of Section 12 and records the exact shift on a fixed bucket-count vector.
-/

open scoped BigOperators Matrix

namespace Erdos88

attribute [local instance] Classical.propDecidable

namespace GraphQuadratic

/-- The graph slice polynomial is exactly the Section 12 structured
quadratic, with `y` equal to the graph effective linear coefficient. -/
lemma sliceQuadratic_graph_eq_structuredQuadratic
    {n : ℕ} (G : SimpleGraph (Fin n)) (e0 : ℝ)
    (c x : Fin n → ℝ) :
    BooleanSlices.quadraticPolynomial (graphSliceConstant G e0 c)
        (graphSliceLinear G c) (graphSliceMatrix G) x =
      Structured.structuredQuadratic (graphSliceConstant G e0 c)
        (RobustRank.graphAdjacencyMatrix G) (graphEffectiveLinear G c) x := by
  have hlinear :
      BooleanSlices.linearPart (graphSliceLinear G c) x =
        (1 / 2 : ℝ) * (graphEffectiveLinear G c ⬝ᵥ x) := by
    rw [BooleanSlices.linearPart, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [graphSliceLinear_eq_half_effective]
    ring
  have hquadratic :
      BooleanSlices.quadraticPart (graphSliceMatrix G) x =
        (1 / 8 : ℝ) *
          (x ⬝ᵥ (RobustRank.graphAdjacencyMatrix G *ᵥ x)) := by
    rw [BooleanSlices.quadraticPart]
    change (∑ i, ∑ j, x i * graphSliceMatrix G i j * x j) =
      (1 / 8 : ℝ) *
        ∑ i, x i * ∑ j, RobustRank.graphAdjacencyMatrix G i j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [graphSliceMatrix]
    ring
  rw [BooleanSlices.quadraticPolynomial, Structured.structuredQuadratic,
    hlinear, hquadratic]

end GraphQuadratic

namespace GaussianQuadratic

open BooleanSlices

/-- The sum of a sign vector on a finite coordinate set is twice the
number of positive coordinates there, minus the size of the set. -/
lemma sum_signOfSet_on_finset {n : ℕ} (S I : Finset (Fin n)) :
    (∑ i ∈ I, signOfSet S i) =
      2 * ((S ∩ I).card : ℝ) - (I.card : ℝ) := by
  classical
  have hpoint (i : Fin n) :
      signOfSet S i = 2 * (if i ∈ S then (1 : ℝ) else 0) - 1 := by
    by_cases hi : i ∈ S <;> simp [signOfSet, hi] <;> norm_num
  calc
    (∑ i ∈ I, signOfSet S i) =
        ∑ i ∈ I, (2 * (if i ∈ S then (1 : ℝ) else 0) - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = 2 * ((S ∩ I).card : ℝ) - (I.card : ℝ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      rw [← Finset.mul_sum]
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      have hfilter : I.filter (fun i ↦ i ∈ S) = S ∩ I := by
        ext i
        simp [and_comm]
      rw [hfilter]

/-- The bucket-average sign vector prescribed by product-slice counts. -/
noncomputable def productSliceDelta {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (s : ℕ)
    (ell : Fin m → ℕ) : Fin n → ℝ :=
  fun i ↦ (s : ℝ)⁻¹ * (2 * (ell (P.bucket i) : ℝ) - (s : ℝ))

/-- Every point of a fixed product slice has the same bucket projection. -/
lemma delta_signOfSet_eq_productSliceDelta
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (ell : Fin m → ℕ) (S : ProductSlicePoint P ell) :
    Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose)
        (signOfSet S.1) =
      productSliceDelta P hbucket.choose ell := by
  classical
  let s := hbucket.choose
  have hcard (k : Fin m) : (P.fiber k).card = s := by
    change (RobustRank.bucketFiber P.bucket k).card = s
    exact hbucket.choose_spec.2 k
  have hcount (k : Fin m) : (S.1 ∩ P.fiber k).card = ell k :=
    (mem_productBooleanSlice P ell S.1).mp S.2 k
  funext i
  rw [Structured.delta]
  change (∑ j, (if P.bucket i = P.bucket j then (s : ℝ)⁻¹ else 0) *
      signOfSet S.1 j) =
    (s : ℝ)⁻¹ * (2 * (ell (P.bucket i) : ℝ) - (s : ℝ))
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfiber :
      (Finset.univ.filter fun j ↦ P.bucket i = P.bucket j) =
        P.fiber (P.bucket i) := by
    ext j
    simp [eq_comm]
  rw [hfiber]
  rw [← Finset.mul_sum]
  rw [sum_signOfSet_on_finset, hcount, hcard]

/-- Once the bucket-average vector is fixed, the original graph polynomial
is a translate of the centered product-slice polynomial used in Claim 12.1.
The extra `trace F` exactly compensates for the public `-trace F` convention. -/
lemma sliceQuadratic_graph_eq_shift_add_productSlice
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (ell : Fin m → ℕ) (G : SimpleGraph (Fin n))
    (e0 : ℝ) (c : Fin n → ℝ) (d : Fin n → ℝ)
    (hdelta : ∀ S : ProductSlicePoint P ell,
      Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose)
          (signOfSet S.1) = d)
    (S : ProductSlicePoint P ell) :
    BooleanSlices.sliceQuadratic (GraphQuadratic.graphSliceConstant G e0 c)
        (GraphQuadratic.graphSliceLinear G c)
        (GraphQuadratic.graphSliceMatrix G) S.1 =
      Structured.conditionalShift (GraphQuadratic.graphSliceConstant G e0 c)
          (RobustRank.graphAdjacencyMatrix G)
          (GraphQuadratic.graphEffectiveLinear G c) d +
        trace (bucketCenteredAdjacency P.bucket hbucket.choose G) +
          productSliceQuadratic P ell
            (-trace (bucketCenteredAdjacency P.bucket hbucket.choose G))
            (Structured.wStar
              (bucketProjectionMatrix P.bucket hbucket.choose)
              (RobustRank.graphAdjacencyMatrix G)
              (GraphQuadratic.graphEffectiveLinear G c) d)
            (bucketCenteredAdjacency P.bucket hbucket.choose G) S := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  let E := GraphQuadratic.graphSliceConstant G e0 c
  let y := GraphQuadratic.graphEffectiveLinear G c
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  let f := Structured.wStar Q M y d
  let x := signOfSet S.1
  have hgraph :
      BooleanSlices.sliceQuadratic E (GraphQuadratic.graphSliceLinear G c)
          (GraphQuadratic.graphSliceMatrix G) S.1 =
        Structured.structuredQuadratic E M y x := by
    exact GraphQuadratic.sliceQuadratic_graph_eq_structuredQuadratic
      G e0 c x
  have hstructured := graph_structured_decomposition
    P.bucket hbucket G E y x
  rw [hdelta S] at hstructured
  change Structured.structuredQuadratic E M y x =
      Structured.conditionalShift E M y d + f ⬝ᵥ x +
        x ⬝ᵥ (F *ᵥ x) at hstructured
  have hlinear : f ⬝ᵥ x = linearPart f x := rfl
  have hquadratic : x ⬝ᵥ (F *ᵥ x) = quadraticPart F x := by
    change (∑ i, x i * ∑ j, F i j * x j) =
      ∑ i, ∑ j, x i * F i j * x j
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hgraph, hstructured]
  rw [hlinear, hquadratic]
  dsimp only [F, f, productSliceQuadratic, sliceQuadratic,
    quadraticPolynomial]
  ring

/-- Count-specialized form of the structured graph decomposition.  The
bucket-average vector is forced by `ell`, so no separate projection
hypothesis remains. -/
lemma sliceQuadratic_graph_eq_shift_add_productSlice_counts
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (ell : Fin m → ℕ) (G : SimpleGraph (Fin n))
    (e0 : ℝ) (c : Fin n → ℝ) (S : ProductSlicePoint P ell) :
    BooleanSlices.sliceQuadratic (GraphQuadratic.graphSliceConstant G e0 c)
        (GraphQuadratic.graphSliceLinear G c)
        (GraphQuadratic.graphSliceMatrix G) S.1 =
      Structured.conditionalShift (GraphQuadratic.graphSliceConstant G e0 c)
          (RobustRank.graphAdjacencyMatrix G)
          (GraphQuadratic.graphEffectiveLinear G c)
          (productSliceDelta P hbucket.choose ell) +
        trace (bucketCenteredAdjacency P.bucket hbucket.choose G) +
          productSliceQuadratic P ell
            (-trace (bucketCenteredAdjacency P.bucket hbucket.choose G))
            (Structured.wStar
              (bucketProjectionMatrix P.bucket hbucket.choose)
              (RobustRank.graphAdjacencyMatrix G)
              (GraphQuadratic.graphEffectiveLinear G c)
              (productSliceDelta P hbucket.choose ell))
            (bucketCenteredAdjacency P.bucket hbucket.choose G) S := by
  apply sliceQuadratic_graph_eq_shift_add_productSlice P hbucket ell G e0 c
    (productSliceDelta P hbucket.choose ell)
  intro T
  exact delta_signOfSet_eq_productSliceDelta P hbucket ell T

end GaussianQuadratic
end Erdos88
