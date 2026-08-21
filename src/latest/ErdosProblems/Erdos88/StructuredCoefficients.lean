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

import ErdosProblems.Erdos88.StructuredSlice

/-!
# Coefficient conditions in the structured branch

This file discharges the algebraic parts of the KSSS balanced-coefficient
condition for the centered graph matrix.  The only inputs left explicit are
the two quantitative entry bounds.
-/

open scoped BigOperators Matrix

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

/-- The indicator of one bucket, viewed as a real coordinate vector. -/
noncomputable def bucketIndicator {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (k : Fin m) : Fin n → ℝ :=
  fun i ↦ if P.bucket i = k then 1 else 0

/-- Equal-bucket averaging fixes the indicator of each bucket. -/
lemma delta_bucketIndicator {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket) (k : Fin m) :
    Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose)
        (bucketIndicator P k) = bucketIndicator P k := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hcard : (P.fiber k).card = s := by
    change (RobustRank.bucketFiber P.bucket k).card = s
    exact hbucket.choose_spec.2 k
  funext i
  rw [Structured.delta]
  change (∑ j, (if P.bucket i = P.bucket j then (s : ℝ)⁻¹ else 0) *
      (if P.bucket j = k then 1 else 0)) =
    if P.bucket i = k then 1 else 0
  by_cases hik : P.bucket i = k
  · rw [if_pos hik]
    have hsum :
        (∑ j, (if P.bucket i = P.bucket j then (s : ℝ)⁻¹ else 0) *
            (if P.bucket j = k then 1 else 0)) =
          ∑ j ∈ P.fiber k, (s : ℝ)⁻¹ := by
      rw [BucketPartition.fiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjk : P.bucket j = k
      · have hij : P.bucket i = P.bucket j := hik.trans hjk.symm
        rw [if_pos hij, if_pos hjk, mul_one, if_pos hjk]
      · have hij : P.bucket i ≠ P.bucket j := by
          intro hij
          exact hjk (hij.symm.trans hik)
        rw [if_neg hij, zero_mul, if_neg hjk]
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hcard]
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  · rw [if_neg hik]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hij : P.bucket i = P.bucket j
    · have hjk : P.bucket j ≠ k := by
        intro hjk
        exact hik (hij.trans hjk)
      rw [if_pos hij, if_neg hjk, mul_zero]
    · rw [if_neg hij, zero_mul]

/-- A vector killed by the equal-bucket averaging projection has zero sum
on every bucket. -/
lemma sum_fiber_eq_zero_of_bucketProjection_mulVec_eq_zero
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket) (f : Fin n → ℝ)
    (hf : bucketProjectionMatrix P.bucket hbucket.choose *ᵥ f = 0)
    (k : Fin m) :
    ∑ i ∈ P.fiber k, f i = 0 := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hcard : (P.fiber k).card = s := by
    change (RobustRank.bucketFiber P.bucket k).card = s
    exact hbucket.choose_spec.2 k
  have hnonempty : (P.fiber k).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; exact hs)
  let r : Fin n := hnonempty.choose
  have hr : P.bucket r = k :=
    (P.mem_fiber k r).mp hnonempty.choose_spec
  have hcoord := congrFun hf r
  change (∑ j, (if P.bucket r = P.bucket j then (s : ℝ)⁻¹ else 0) * f j) =
    0 at hcoord
  simp only [ite_mul, zero_mul] at hcoord
  rw [← Finset.sum_filter] at hcoord
  have hfiber :
      (Finset.univ.filter fun j ↦ P.bucket r = P.bucket j) = P.fiber k := by
    ext j
    simp [hr, eq_comm]
  rw [hfiber, ← Finset.mul_sum] at hcoord
  have hsInv : (s : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hs.ne')
  exact (mul_eq_zero.mp hcoord).resolve_left hsInv

/-- Right multiplication by equal-bucket averaging preserves an entrywise
absolute bound of one. -/
lemma abs_matrix_mul_bucketProjection_le_one
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : Fin n) :
    |(A * bucketProjectionMatrix P.bucket hbucket.choose) i j| ≤ 1 := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hsNonneg : 0 ≤ (s : ℝ) := by positivity
  have hcard : (P.fiber (P.bucket j)).card = s := by
    change (RobustRank.bucketFiber P.bucket (P.bucket j)).card = s
    exact hbucket.choose_spec.2 (P.bucket j)
  change |∑ x, A i x *
      (if P.bucket x = P.bucket j then (s : ℝ)⁻¹ else 0)| ≤ 1
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  change |∑ x ∈ P.fiber (P.bucket j), A i x * (s : ℝ)⁻¹| ≤ 1
  rw [← Finset.sum_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hsNonneg)]
  have hsum : |∑ x ∈ P.fiber (P.bucket j), A i x| ≤ (s : ℝ) := by
    calc
      |∑ x ∈ P.fiber (P.bucket j), A i x| ≤
          ∑ x ∈ P.fiber (P.bucket j), |A i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ P.fiber (P.bucket j), (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx ↦ hA i x
      _ = (s : ℝ) := by simp [hcard]
  calc
    |∑ x ∈ P.fiber (P.bucket j), A i x| * (s : ℝ)⁻¹ ≤
        (s : ℝ) * (s : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hsNonneg)
    _ = 1 := by
      field_simp [show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne']

/-- Left multiplication by equal-bucket averaging preserves an entrywise
absolute bound of one. -/
lemma abs_bucketProjection_mul_matrix_le_one
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : Fin n) :
    |(bucketProjectionMatrix P.bucket hbucket.choose * A) i j| ≤ 1 := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hsNonneg : 0 ≤ (s : ℝ) := by positivity
  have hcard : (P.fiber (P.bucket i)).card = s := by
    change (RobustRank.bucketFiber P.bucket (P.bucket i)).card = s
    exact hbucket.choose_spec.2 (P.bucket i)
  change |∑ x, (if P.bucket i = P.bucket x then (s : ℝ)⁻¹ else 0) *
      A x j| ≤ 1
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfiber :
      (Finset.univ.filter fun x ↦ P.bucket i = P.bucket x) =
        P.fiber (P.bucket i) := by
    ext x
    simp [eq_comm]
  rw [hfiber, ← Finset.mul_sum, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hsNonneg)]
  have hsum : |∑ x ∈ P.fiber (P.bucket i), A x j| ≤ (s : ℝ) := by
    calc
      |∑ x ∈ P.fiber (P.bucket i), A x j| ≤
          ∑ x ∈ P.fiber (P.bucket i), |A x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ P.fiber (P.bucket i), (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx ↦ hA x j
      _ = (s : ℝ) := by simp [hcard]
  calc
    (s : ℝ)⁻¹ * |∑ x ∈ P.fiber (P.bucket i), A x j| ≤
        (s : ℝ)⁻¹ * (s : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hsNonneg)
    _ = 1 := by
      field_simp [show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne']

/-- Equal-bucket averaging is an `L∞` contraction. -/
lemma abs_bucketProjection_mulVec_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (z : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ i, |z i| ≤ B) (i : Fin n) :
    |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ z) i| ≤ B := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hsNonneg : 0 ≤ (s : ℝ) := by positivity
  have hcard : (P.fiber (P.bucket i)).card = s := by
    change (RobustRank.bucketFiber P.bucket (P.bucket i)).card = s
    exact hbucket.choose_spec.2 (P.bucket i)
  change |∑ x, (if P.bucket i = P.bucket x then (s : ℝ)⁻¹ else 0) * z x| ≤ B
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfiber :
      (Finset.univ.filter fun x ↦ P.bucket i = P.bucket x) =
        P.fiber (P.bucket i) := by
    ext x
    simp [eq_comm]
  rw [hfiber, ← Finset.mul_sum, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hsNonneg)]
  have hsum : |∑ x ∈ P.fiber (P.bucket i), z x| ≤ (s : ℝ) * B := by
    calc
      |∑ x ∈ P.fiber (P.bucket i), z x| ≤
          ∑ x ∈ P.fiber (P.bucket i), |z x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ P.fiber (P.bucket i), B := by
        exact Finset.sum_le_sum fun x hx ↦ hz x
      _ = (s : ℝ) * B := by simp [hcard]
  calc
    (s : ℝ)⁻¹ * |∑ x ∈ P.fiber (P.bucket i), z x| ≤
        (s : ℝ)⁻¹ * ((s : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hsNonneg)
    _ = B := by
      field_simp [show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne']

/-- The bucket-centered projection has `L∞` norm at most two. -/
lemma abs_centeredProjection_mulVec_le_two
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (z : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ i, |z i| ≤ B) (i : Fin n) :
    |(Structured.centeredProjection
        (bucketProjectionMatrix P.bucket hbucket.choose) *ᵥ z) i| ≤ 2 * B := by
  rw [show Structured.centeredProjection
      (bucketProjectionMatrix P.bucket hbucket.choose) *ᵥ z =
        Structured.residual
          (bucketProjectionMatrix P.bucket hbucket.choose) z by rfl,
    Structured.residual_eq_sub]
  change |z i -
      (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ z) i| ≤ 2 * B
  calc
    |z i - (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ z) i| ≤
        |z i| + |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ z) i| :=
      abs_sub _ _
    _ ≤ B + B := add_le_add (hz i)
      (abs_bucketProjection_mulVec_le P hbucket z hB hz i)
    _ = 2 * B := by ring

/-- Multiplication by a matrix with entries bounded by one costs at most
the ambient dimension in `L∞`. -/
lemma abs_matrix_mulVec_le_card_mul
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hM : ∀ i j, |M i j| ≤ 1)
    (hz : ∀ j, |z j| ≤ B) (i : Fin n) :
    |(M *ᵥ z) i| ≤ (n : ℝ) * B := by
  change |∑ j, M i j * z j| ≤ (n : ℝ) * B
  calc
    |∑ j, M i j * z j| ≤ ∑ j, |M i j * z j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      calc
        |M i j| * |z j| ≤ 1 * B :=
          mul_le_mul (hM i j) (hz j) (abs_nonneg _) (by norm_num)
        _ = B := one_mul B
    _ = (n : ℝ) * B := by simp

/-- A vector which is constant on each bucket is fixed by bucket averaging. -/
lemma delta_bucketConstant {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (a : Fin m → ℝ) :
    Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose)
        (fun i ↦ a (P.bucket i)) = fun i ↦ a (P.bucket i) := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hcard (k : Fin m) : (P.fiber k).card = s := by
    change (RobustRank.bucketFiber P.bucket k).card = s
    exact hbucket.choose_spec.2 k
  funext i
  rw [Structured.delta]
  change (∑ j, (if P.bucket i = P.bucket j then (s : ℝ)⁻¹ else 0) *
      a (P.bucket j)) = a (P.bucket i)
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfiber :
      (Finset.univ.filter fun j ↦ P.bucket i = P.bucket j) =
        P.fiber (P.bucket i) := by
    ext j
    simp [eq_comm]
  rw [hfiber]
  have hconst :
      (∑ j ∈ P.fiber (P.bucket i), (s : ℝ)⁻¹ * a (P.bucket j)) =
        ∑ _j ∈ P.fiber (P.bucket i), (s : ℝ)⁻¹ * a (P.bucket i) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [(P.mem_fiber (P.bucket i) j).mp hj]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

/-- Deterministic `L∞` estimate for `w*`.  Closeness to a bucket-constant
vector contributes `R`; a perturbation `d` contributes at most `nD/2`. -/
lemma abs_wStar_le_of_close_bucketConstant
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (M : Matrix (Fin n) (Fin n) ℝ) (y d : Fin n → ℝ)
    (a : Fin m → ℝ) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hM : ∀ i j, |M i j| ≤ 1)
    (hy : ∀ i, |y i - a (P.bucket i)| ≤ R)
    (hd : ∀ i, |d i| ≤ D) (i : Fin n) :
    |Structured.wStar
        (bucketProjectionMatrix P.bucket hbucket.choose) M y d i| ≤
      R + (n : ℝ) * D / 2 := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let avec : Fin n → ℝ := fun j ↦ a (P.bucket j)
  let err : Fin n → ℝ := y - avec
  let md : Fin n → ℝ := M *ᵥ d
  let z : Fin n → ℝ := err + (1 / 2 : ℝ) • md
  have ha : Q *ᵥ avec = avec := by
    simpa only [Q, avec, Structured.delta] using
      delta_bucketConstant P hbucket a
  have herr : ∀ j, |err j| ≤ R := by
    intro j
    simpa only [err, avec, Pi.sub_apply] using hy j
  have hmd : ∀ j, |md j| ≤ (n : ℝ) * D := by
    intro j
    exact abs_matrix_mulVec_le_card_mul M d hD hM hd j
  have hB : 0 ≤ R + (n : ℝ) * D / 2 := by positivity
  have hz : ∀ j, |z j| ≤ R + (n : ℝ) * D / 2 := by
    intro j
    dsimp only [z]
    calc
      |(err + (1 / 2 : ℝ) • md) j| ≤
          |err j| + |((1 / 2 : ℝ) • md) j| := by
        rw [Pi.add_apply]
        exact abs_add_le _ _
      _ = |err j| + 1 / 2 * |md j| := by
        rw [Pi.smul_apply, abs_smul]
        norm_num [smul_eq_mul]
      |err j| + 1 / 2 * |md j| ≤ R + 1 / 2 * ((n : ℝ) * D) :=
        add_le_add (herr j) (mul_le_mul_of_nonneg_left (hmd j) (by norm_num))
      _ = R + (n : ℝ) * D / 2 := by ring
  have hres :
      Structured.centeredProjection Q *ᵥ
          (y + (1 / 2 : ℝ) • (M *ᵥ d)) =
        Structured.centeredProjection Q *ᵥ z := by
    funext j
    simp only [Structured.centeredProjection, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      z, err, avec, md, ha]
    ring
  rw [Structured.wStar]
  change |(1 / 2 : ℝ) *
      (Structured.centeredProjection Q *ᵥ
        (y + (1 / 2 : ℝ) • (M *ᵥ d))) i| ≤ _
  rw [hres, abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hcenter := abs_centeredProjection_mulVec_le_two P hbucket z hB hz i
  nlinarith

/-- Near-balanced bucket counts give the expected uniform bound on the
bucket-average sign vector. -/
lemma abs_productSliceDelta_le
    {n m : ℕ} {delta : ℝ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (ell : Fin m → ℕ) (hbalanced : IsNearBalanced delta P ell)
    (i : Fin n) :
    |productSliceDelta P hbucket.choose ell i| ≤
      (hbucket.choose : ℝ)⁻¹ *
        (2 * (scale n ((1 - delta) / 2) * Real.log n)) := by
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hsNonneg : 0 ≤ (s : ℝ) := by positivity
  have hcard : (P.fiber (P.bucket i)).card = s := by
    change (RobustRank.bucketFiber P.bucket (P.bucket i)).card = s
    exact hbucket.choose_spec.2 (P.bucket i)
  have hnear := hbalanced (P.bucket i)
  rw [hcard] at hnear
  have hnum :
      |2 * (ell (P.bucket i) : ℝ) - (s : ℝ)| =
        2 * |(ell (P.bucket i) : ℝ) - (s : ℝ) / 2| := by
    rw [show 2 * (ell (P.bucket i) : ℝ) - (s : ℝ) =
      2 * ((ell (P.bucket i) : ℝ) - (s : ℝ) / 2) by ring,
      abs_mul]
    norm_num
  rw [productSliceDelta, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hsNonneg), hnum]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hnear (by norm_num))
    (inv_nonneg.mpr hsNonneg)

/-- Exact deterministic coefficient bound after conditioning the RLCD
remainder and fixing a near-balanced product slice. -/
lemma abs_conditionedCovered_wStar_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho t delta : ℝ}
    (D0 : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (hd0 : d0 = GraphQuadratic.graphEffectiveLinear G c)
    (O : Finset (Fin n))
    (htypical : ∀ i : Fin (Fintype.card D0.Covered),
      |(AKSGraph.degreeInto G (D0.finCoveredEquiv i).1 O : ℝ) -
        (AKSGraph.degreeInto G (D0.finCoveredEquiv i).1 D0.remainder : ℝ) / 2| ≤ t)
    (hrho : 0 ≤ rho) (ht : 0 ≤ t)
    (hbucket : RobustRank.HasEqualBuckets D0.finCoveredPartition.bucket)
    (ell : Fin (Fintype.card D0.BlockIndex) → ℕ)
    (hbalanced : IsNearBalanced delta D0.finCoveredPartition ell)
    (i : Fin (Fintype.card D0.Covered)) :
    |Structured.wStar
        (bucketProjectionMatrix D0.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D0.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D0.finCoveredGraph G)
          (D0.conditionedCoveredCoefficient G c O))
        (productSliceDelta D0.finCoveredPartition hbucket.choose ell) i| ≤
      (rho + t) + (Fintype.card D0.Covered : ℝ) *
        ((hbucket.choose : ℝ)⁻¹ *
          (2 * (scale (Fintype.card D0.Covered) ((1 - delta) / 2) *
            Real.log (Fintype.card D0.Covered)))) / 2 := by
  let P := D0.finCoveredPartition
  let M := RobustRank.graphAdjacencyMatrix (D0.finCoveredGraph G)
  let y := GraphQuadratic.graphEffectiveLinear (D0.finCoveredGraph G)
    (D0.conditionedCoveredCoefficient G c O)
  let d := productSliceDelta P hbucket.choose ell
  let a : Fin (Fintype.card D0.BlockIndex) → ℝ :=
    fun j ↦ D0.blockCenter (D0.finBlockEquiv j)
  have hq : 1 ≤ Fintype.card D0.Covered := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      have := i.isLt
      omega)
  have hlog : 0 ≤ Real.log (Fintype.card D0.Covered : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hDvec : 0 ≤ (hbucket.choose : ℝ)⁻¹ *
      (2 * (scale (Fintype.card D0.Covered) ((1 - delta) / 2) *
        Real.log (Fintype.card D0.Covered))) :=
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (mul_nonneg (by norm_num) (mul_nonneg (scale_nonneg _ _) hlog))
  apply abs_wStar_le_of_close_bucketConstant P hbucket M y d a
    (add_nonneg hrho ht) hDvec
  · intro u v
    classical
    simp only [M, RobustRank.graphAdjacencyMatrix]
    split <;> norm_num
  · intro u
    exact D0.conditionedCovered_close_to_blockCenter G c hd0 O htypical u
  · intro u
    exact abs_productSliceDelta_le P hbucket ell hbalanced u

/-- The centered graph matrix has uniformly bounded entries; the generous
bound one is the normalization required by KSSS Lemma 11.1. -/
lemma abs_bucketCenteredAdjacency_le_one {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    |bucketCenteredAdjacency P.bucket hbucket.choose G i j| ≤ 1 := by
  let M := RobustRank.graphAdjacencyMatrix G
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  have hM : ∀ a b, |M a b| ≤ 1 := by
    intro a b
    classical
    by_cases hab : G.Adj a b <;>
      simp [M, RobustRank.graphAdjacencyMatrix, hab]
  have hMQ : ∀ a b, |(M * Q) a b| ≤ 1 :=
    abs_matrix_mul_bucketProjection_le_one P hbucket M hM
  have hQM : ∀ a b, |(Q * M) a b| ≤ 1 :=
    abs_bucketProjection_mul_matrix_le_one P hbucket M hM
  have hQMQ : ∀ a b, |(Q * M * Q) a b| ≤ 1 :=
    abs_matrix_mul_bucketProjection_le_one P hbucket (Q * M) hQM
  have hmatrix : (1 - Q) * M * (1 - Q) =
      M - M * Q - Q * M + Q * M * Q := by
    noncomm_ring
  have hentry :
      bucketCenteredAdjacency P.bucket hbucket.choose G i j =
        (1 / 8 : ℝ) *
          (M i j - (M * Q) i j - (Q * M) i j + (Q * M * Q) i j) := by
    rw [bucketCenteredAdjacency_eq_mStar]
    simp only [Structured.mStar, Structured.centeredProjection,
      smul_apply, smul_eq_mul]
    rw [hmatrix]
    rfl
  rw [hentry, abs_mul]
  have hfour :
      |M i j - (M * Q) i j - (Q * M) i j + (Q * M * Q) i j| ≤ 4 := by
    calc
      |M i j - (M * Q) i j - (Q * M) i j + (Q * M * Q) i j| ≤
          |M i j| + |(M * Q) i j| + |(Q * M) i j| +
            |(Q * M * Q) i j| := by
        calc
          |_ + _| ≤ |M i j - (M * Q) i j - (Q * M) i j| +
              |(Q * M * Q) i j| := abs_add_le _ _
          _ ≤ (|M i j - (M * Q) i j| + |(Q * M) i j|) +
              |(Q * M * Q) i j| := by gcongr; exact abs_sub _ _
          _ ≤ ((|M i j| + |(M * Q) i j|) + |(Q * M) i j|) +
              |(Q * M * Q) i j| := by gcongr; exact abs_sub _ _
          _ = _ := by ring
      _ ≤ 4 := by linarith [hM i j, hMQ i j, hQM i j, hQMQ i j]
  norm_num at ⊢
  nlinarith

/-- The centered graph matrix is symmetric over the reals. -/
lemma bucketCenteredAdjacency_symmetric {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (s : ℕ)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    bucketCenteredAdjacency P.bucket s G i j =
      bucketCenteredAdjacency P.bucket s G j i := by
  have h := bucketCenteredAdjacency_isHermitian P.bucket s G
  have hij := congrArg
    (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) h.eq
  simpa only [Matrix.conjTranspose_apply, starRingEnd_apply, star_id_of_comm]
    using hij.symm

/-- Every row of the centered graph matrix sums to zero on every bucket. -/
lemma sum_bucketCenteredAdjacency_row_eq_zero {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i : Fin n) (k : Fin m) :
    ∑ j ∈ P.fiber k,
      bucketCenteredAdjacency P.bucket hbucket.choose G i j = 0 := by
  classical
  have hzero := bucketCenteredAdjacency_delta_eq_zero P.bucket hbucket G
    (bucketIndicator P k)
  rw [delta_bucketIndicator P hbucket k] at hzero
  have hcoord := congrFun hzero i
  change (∑ j, bucketCenteredAdjacency P.bucket hbucket.choose G i j *
      bucketIndicator P k j) = 0 at hcoord
  have hsum :
      (∑ j, bucketCenteredAdjacency P.bucket hbucket.choose G i j *
          bucketIndicator P k j) =
        ∑ j ∈ P.fiber k,
          bucketCenteredAdjacency P.bucket hbucket.choose G i j := by
    rw [BucketPartition.fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : P.bucket j = k <;>
      simp [bucketIndicator, hjk]
  rw [hsum] at hcoord
  exact hcoord

/-- Every column of the centered graph matrix sums to zero on every bucket. -/
lemma sum_bucketCenteredAdjacency_col_eq_zero {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (j : Fin n) (k : Fin m) :
    ∑ i ∈ P.fiber k,
      bucketCenteredAdjacency P.bucket hbucket.choose G i j = 0 := by
  calc
    (∑ i ∈ P.fiber k,
        bucketCenteredAdjacency P.bucket hbucket.choose G i j) =
        ∑ i ∈ P.fiber k,
          bucketCenteredAdjacency P.bucket hbucket.choose G j i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact bucketCenteredAdjacency_symmetric P hbucket.choose G i j
    _ = 0 := sum_bucketCenteredAdjacency_row_eq_zero P hbucket G j k

/-- The graph-structured coefficients satisfy all KSSS conditions once the
two quantitative coordinate bounds are supplied. -/
lemma hasKSSSBalancedCoefficients_wStar_of_bounds
    {n m : ℕ} (delta : ℝ)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y d : Fin n → ℝ)
    (hw : ∀ i, |Structured.wStar
        (bucketProjectionMatrix P.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix G) y d i| ≤
          scale n (1 / 2 + 3 * delta)) :
    HasKSSSBalancedCoefficients delta P
      (Structured.wStar
        (bucketProjectionMatrix P.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix G) y d)
      (bucketCenteredAdjacency P.bucket hbucket.choose G) := by
  let f := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix G) y d
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  refine ⟨?_, hw, abs_bucketCenteredAdjacency_le_one P hbucket G, ?_, ?_, ?_⟩
  · intro i j
    exact bucketCenteredAdjacency_symmetric P hbucket.choose G i j
  · intro k
    apply sum_fiber_eq_zero_of_bucketProjection_mulVec_eq_zero P hbucket f
    exact bucket_wStar_delta_eq_zero P.bucket hbucket G y d
  · intro k h i hi
    exact sum_bucketCenteredAdjacency_row_eq_zero P hbucket G i h
  · intro k h j hj
    exact sum_bucketCenteredAdjacency_col_eq_zero P hbucket G j k

/-- The conditioned graph coefficients satisfy the full KSSS certificate as
soon as the explicit deterministic upper bound is absorbed by the target
power scale.  This isolates the remaining asymptotic arithmetic from all
matrix and bucket identities. -/
lemma hasKSSSBalancedCoefficients_conditionedCovered
    {n k : ℕ} {d0 : Fin n → ℝ} {rho t delta : ℝ}
    (D0 : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (hd0 : d0 = GraphQuadratic.graphEffectiveLinear G c)
    (O : Finset (Fin n))
    (htypical : ∀ i : Fin (Fintype.card D0.Covered),
      |(AKSGraph.degreeInto G (D0.finCoveredEquiv i).1 O : ℝ) -
        (AKSGraph.degreeInto G (D0.finCoveredEquiv i).1 D0.remainder : ℝ) / 2| ≤ t)
    (hrho : 0 ≤ rho) (ht : 0 ≤ t)
    (hbucket : RobustRank.HasEqualBuckets D0.finCoveredPartition.bucket)
    (ell : Fin (Fintype.card D0.BlockIndex) → ℕ)
    (hbalanced : IsNearBalanced delta D0.finCoveredPartition ell)
    (hbound :
      (rho + t) + (Fintype.card D0.Covered : ℝ) *
          ((hbucket.choose : ℝ)⁻¹ *
            (2 * (scale (Fintype.card D0.Covered) ((1 - delta) / 2) *
              Real.log (Fintype.card D0.Covered)))) / 2 ≤
        scale (Fintype.card D0.Covered) (1 / 2 + 3 * delta)) :
    HasKSSSBalancedCoefficients delta D0.finCoveredPartition
      (Structured.wStar
        (bucketProjectionMatrix D0.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D0.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D0.finCoveredGraph G)
          (D0.conditionedCoveredCoefficient G c O))
        (productSliceDelta D0.finCoveredPartition hbucket.choose ell))
      (bucketCenteredAdjacency D0.finCoveredPartition.bucket hbucket.choose
        (D0.finCoveredGraph G)) := by
  apply hasKSSSBalancedCoefficients_wStar_of_bounds delta
    D0.finCoveredPartition hbucket (D0.finCoveredGraph G)
  intro i
  exact (abs_conditionedCovered_wStar_le D0 G c hd0 O htypical
    hrho ht hbucket ell hbalanced i).trans hbound

end Erdos88.GaussianQuadratic
