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

import ErdosProblems.Erdos88.StructuredCoefficients

/-!
# Typical remainder conditionings in the structured branch

The generic cross-term estimate in `LinearLCDCancellation` uses the ambient
number of vertices.  In the structured branch the random coordinates are
only the small RLCD remainder.  This file records the sharper version with
the actual complement cardinality in the exponent.
-/

open scoped BigOperators

namespace Erdos88.LinearLCDCancellation

attribute [local instance] Classical.propDecidable

/-- The squared graph cross coefficients are controlled by the actual
number of outside coordinates, rather than by the ambient cardinality. -/
lemma graphCrossCoefficient_sq_sum_le_compl {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I) :
    (∑ j : {v : Fin n // v ∉ I}, graphCrossCoefficient G I i j ^ 2) ≤
      (Fintype.card {v : Fin n // v ∉ I} : ℝ) / 16 := by
  classical
  calc
    (∑ j : {v : Fin n // v ∉ I}, graphCrossCoefficient G I i j ^ 2) ≤
        ∑ _j : {v : Fin n // v ∉ I}, (1 / 16 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : G.Adj i.1 j.1 <;>
        simp [graphCrossCoefficient,
          RobustRank.graphAdjacencyMatrix, hij] <;> norm_num
    _ = (Fintype.card {v : Fin n // v ∉ I} : ℝ) / 16 := by
      simp
      ring

/-- Hoeffding for one graph cross coefficient with the true complement
cardinality in the exponent. -/
theorem graphCrossLinear_tail_compl_uniform {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I)
    (u : ℝ) (hcompl : 0 < Fintype.card {v : Fin n // v ∉ I})
    (hu : 0 < u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      2 * (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
        Real.exp (-8 * u ^ 2 /
          Fintype.card {v : Fin n // v ∉ I}) := by
  let S := ∑ j : {v : Fin n // v ∉ I},
    graphCrossCoefficient G I i j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hSr : S ≤ (Fintype.card {v : Fin n // v ∉ I} : ℝ) / 16 :=
    graphCrossCoefficient_sq_sum_le_compl G I i
  by_cases hS0 : S = 0
  · have hcoeff : ∀ j : {v : Fin n // v ∉ I},
        graphCrossCoefficient G I i j = 0 := by
      intro j
      have hsq : graphCrossCoefficient G I i j ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg (graphCrossCoefficient G I i j))).mp hS0
            j (Finset.mem_univ j)
      nlinarith [sq_nonneg (graphCrossCoefficient G I i j)]
    have hlinear : ∀ z, graphCrossLinear G I i z = 0 := by
      intro z
      simp [graphCrossLinear, hcoeff]
    have hempty :
        (Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
          u ≤ |graphCrossLinear G I i z|) = ∅ := by
      ext z
      simp [hlinear, not_le_of_gt hu]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hr : (0 : ℝ) < Fintype.card {v : Fin n // v ∉ I} := by
      exact_mod_cast hcompl
    have hratio :
        8 * u ^ 2 / (Fintype.card {v : Fin n // v ∉ I} : ℝ) ≤
          u ^ 2 / (2 * S) := by
      apply (div_le_div_iff₀ hr (mul_pos (by norm_num) hSpos)).2
      have h16 : 16 * S ≤ (Fintype.card {v : Fin n // v ∉ I} : ℝ) := by
        linarith
      nlinarith [sq_nonneg u]
    have hexp : Real.exp (-u ^ 2 / (2 * S)) ≤
        Real.exp (-8 * u ^ 2 /
          Fintype.card {v : Fin n // v ∉ I}) := by
      apply Real.exp_le_exp.mpr
      rw [show -u ^ 2 / (2 * S) = -(u ^ 2 / (2 * S)) by ring,
        show -8 * u ^ 2 /
            (Fintype.card {v : Fin n // v ∉ I} : ℝ) =
          -(8 * u ^ 2 /
            (Fintype.card {v : Fin n // v ∉ I} : ℝ)) by ring]
      exact neg_le_neg hratio
    have htail := graphCrossLinear_tail G I i u hu.le
    exact htail.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Union bound for all inside vertices, retaining the true outside
cardinality in the exponential decay. -/
theorem graphCrossLinear_exists_tail_compl_uniform {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (u : ℝ) (hcompl : 0 < Fintype.card {v : Fin n // v ∉ I})
    (hu : 0 < u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      ∃ i : I, u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      2 * (I.card : ℝ) *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 /
            Fintype.card {v : Fin n // v ∉ I}) := by
  classical
  let bad : I → Finset ({v : Fin n // v ∉ I} → Bool) := fun i ↦
    Finset.univ.filter fun z ↦ u ≤ |graphCrossLinear G I i z|
  have hset :
      (Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
        ∃ i : I, u ≤ |graphCrossLinear G I i z|) =
        (Finset.univ : Finset I).biUnion bad := by
    ext z
    simp [bad]
  rw [hset]
  calc
    (((Finset.univ : Finset I).biUnion bad).card : ℝ) ≤
        ∑ i : I, ((bad i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 2 *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 /
            Fintype.card {v : Fin n // v ∉ I}) := by
      apply Finset.sum_le_sum
      intro i hi
      exact graphCrossLinear_tail_compl_uniform G I i u hcompl hu
    _ = 2 * (I.card : ℝ) *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 /
            Fintype.card {v : Fin n // v ∉ I}) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
      ring

/-- The ambient subset selected by a Boolean assignment on the complement
of `I`. -/
noncomputable def outsideAssignmentSet {n : ℕ} (I : Finset (Fin n))
    (z : {v : Fin n // v ∉ I} → Bool) : Finset (Fin n) :=
  (Finset.univ.filter fun j : {v : Fin n // v ∉ I} ↦ z j = true).image
    Subtype.val

lemma outsideAssignmentSet_subset_compl {n : ℕ} (I : Finset (Fin n))
    (z : {v : Fin n // v ∉ I} → Bool) :
    outsideAssignmentSet I z ⊆ Finset.univ \ I := by
  intro v hv
  rw [outsideAssignmentSet, Finset.mem_image] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact j.2

lemma sum_graphAdjacencyMatrix_compl {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I) :
    (∑ j : {v : Fin n // v ∉ I},
        RobustRank.graphAdjacencyMatrix G i.1 j.1) =
      (AKSGraph.degreeInto G i.1 (Finset.univ \ I) : ℝ) := by
  classical
  let R := Finset.univ \ I
  let e : {v : Fin n // v ∉ I} ≃ R :=
    { toFun := fun v ↦ ⟨v.1, by simp only [R, Finset.mem_sdiff,
          Finset.mem_univ, true_and]; exact v.2⟩
      invFun := fun v ↦ ⟨v.1, by
        have hv := v.2
        simpa only [R, Finset.mem_sdiff, Finset.mem_univ, true_and] using hv⟩
      left_inv := by intro v; exact Subtype.ext rfl
      right_inv := by intro v; exact Subtype.ext rfl }
  calc
    (∑ j : {v : Fin n // v ∉ I},
        RobustRank.graphAdjacencyMatrix G i.1 j.1) =
        ∑ j : R, RobustRank.graphAdjacencyMatrix G i.1 j.1 := by
      convert e.sum_comp (fun j : R ↦
        RobustRank.graphAdjacencyMatrix G i.1 j.1) using 1 <;> rfl
    _ = ∑ j ∈ R, RobustRank.graphAdjacencyMatrix G i.1 j := by
      exact (Finset.sum_subtype R (fun _ ↦ Iff.rfl)
        (fun j ↦ RobustRank.graphAdjacencyMatrix G i.1 j)).symm
    _ = (AKSGraph.degreeInto G i.1 R : ℝ) := by
      rw [AKSGraph.degreeInto_eq_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : G.Adj i.1 j <;>
        simp [RobustRank.graphAdjacencyMatrix, hij]

lemma sum_graphAdjacencyMatrix_selected {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I)
    (z : {v : Fin n // v ∉ I} → Bool) :
    (∑ j : {v : Fin n // v ∉ I},
        if z j = true then RobustRank.graphAdjacencyMatrix G i.1 j.1 else 0) =
      (AKSGraph.degreeInto G i.1 (outsideAssignmentSet I z) : ℝ) := by
  classical
  let T := Finset.univ.filter fun j : {v : Fin n // v ∉ I} ↦ z j = true
  calc
    (∑ j : {v : Fin n // v ∉ I},
        if z j = true then RobustRank.graphAdjacencyMatrix G i.1 j.1 else 0) =
        ∑ j ∈ T, RobustRank.graphAdjacencyMatrix G i.1 j.1 := by
      change (∑ j, if z j = true then
          RobustRank.graphAdjacencyMatrix G i.1 j.1 else 0) =
        ∑ j ∈ (Finset.univ.filter fun j : {v : Fin n // v ∉ I} ↦
          z j = true), RobustRank.graphAdjacencyMatrix G i.1 j.1
      rw [Finset.sum_filter]
    _ = ∑ v ∈ outsideAssignmentSet I z,
        RobustRank.graphAdjacencyMatrix G i.1 v := by
      rw [outsideAssignmentSet]
      exact (Finset.sum_image
        (f := fun v ↦ RobustRank.graphAdjacencyMatrix G i.1 v)
        (g := fun j : {v : Fin n // v ∉ I} ↦ j.1)
        (s := T) (fun a ha b hb hab ↦ Subtype.ext hab)).symm
    _ = (AKSGraph.degreeInto G i.1 (outsideAssignmentSet I z) : ℝ) := by
      rw [AKSGraph.degreeInto_eq_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : G.Adj i.1 j <;>
        simp [RobustRank.graphAdjacencyMatrix, hij]

/-- Exact conversion between the graph cross linear form and the centered
remainder-neighbour count used after conditioning. -/
lemma degreeInto_outsideAssignmentSet_sub_half_eq_two_mul_graphCrossLinear
    {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I)
    (z : {v : Fin n // v ∉ I} → Bool) :
    (AKSGraph.degreeInto G i.1 (outsideAssignmentSet I z) : ℝ) -
        (AKSGraph.degreeInto G i.1 (Finset.univ \ I) : ℝ) / 2 =
      2 * graphCrossLinear G I i z := by
  classical
  let A : {v : Fin n // v ∉ I} → ℝ := fun j ↦
    RobustRank.graphAdjacencyMatrix G i.1 j.1
  have hsign :
      (∑ j, A j * Fourier.rademacherSign (z j)) =
        2 * (∑ j, if z j = true then A j else 0) - ∑ j, A j := by
    calc
      (∑ j, A j * Fourier.rademacherSign (z j)) =
          ∑ j, (2 * (if z j = true then A j else 0) - A j) := by
        apply Finset.sum_congr rfl
        intro j hj
        cases hz : z j <;>
          simp [Fourier.rademacherSign, hz] <;> ring
      _ = 2 * (∑ j, if z j = true then A j else 0) - ∑ j, A j := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hcross : graphCrossLinear G I i z =
      (1 / 4 : ℝ) * ∑ j, A j * Fourier.rademacherSign (z j) := by
    rw [graphCrossLinear, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [graphCrossCoefficient, A]
    ring
  have hselected : (∑ j, if z j = true then A j else 0) =
      (AKSGraph.degreeInto G i.1 (outsideAssignmentSet I z) : ℝ) := by
    exact sum_graphAdjacencyMatrix_selected G I i z
  have hcomplement : (∑ j, A j) =
      (AKSGraph.degreeInto G i.1 (Finset.univ \ I) : ℝ) := by
    exact sum_graphAdjacencyMatrix_compl G I i
  rw [hcross, hsign, hselected, hcomplement]
  ring

end Erdos88.LinearLCDCancellation

namespace Erdos88.RLCD.BucketDecomposition

attribute [local instance] Classical.propDecidable

/-- A `sqrt n` deviation on at most `n^(1-gamma)` remainder coordinates has
exceptional factor smaller than the final `n^(-3/2)` scale, uniformly in
the number `q ≤ n` of covered coordinates. -/
lemma eventually_remainder_exceptional_factor_le
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ q r : ℕ, q ≤ n → 0 < r →
        (r : ℝ) ≤ BooleanSlices.scale n (1 - gamma) →
        2 * (q : ℝ) *
            Real.exp (-2 * (Real.sqrt n) ^ 2 / r) ≤
          BooleanSlices.scale n (-3 / 2) := by
  have hdecay :=
    QuadraticCancellation.eventually_const_mul_exp_neg_const_rpow_le_rpow
      2 2 gamma (5 / 2) (by norm_num) (by norm_num) hgamma (by norm_num)
  filter_upwards [hdecay, Filter.eventually_ge_atTop 1] with n hdecayN hn
  intro q r hq hr hrem
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmul :
      BooleanSlices.scale n gamma * (r : ℝ) ≤ (n : ℝ) := by
    calc
      BooleanSlices.scale n gamma * (r : ℝ) ≤
          BooleanSlices.scale n gamma *
            BooleanSlices.scale n (1 - gamma) :=
        mul_le_mul_of_nonneg_left hrem
          (BooleanSlices.scale_nonneg n gamma)
      _ = BooleanSlices.scale n gamma *
          BooleanSlices.scale n (1 - gamma) := rfl
      _ = BooleanSlices.scale n (gamma + (1 - gamma)) :=
        BooleanSlices.scale_mul hnpos gamma (1 - gamma)
      _ = (n : ℝ) := by
        rw [show gamma + (1 - gamma) = (1 : ℝ) by ring]
        exact Real.rpow_one _
  have hratio : BooleanSlices.scale n gamma ≤ (n : ℝ) / r :=
    (le_div_iff₀ hrR).2 hmul
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hexponent :
      -2 * Real.sqrt (n : ℝ) ^ 2 / (r : ℝ) ≤
        -2 * BooleanSlices.scale n gamma := by
    rw [hsqrt]
    calc
      -2 * (n : ℝ) / (r : ℝ) =
          -2 * ((n : ℝ) / (r : ℝ)) := by ring
      _ ≤ -2 * BooleanSlices.scale n gamma :=
        mul_le_mul_of_nonpos_left hratio (by norm_num)
  have hexp :
      Real.exp (-2 * Real.sqrt (n : ℝ) ^ 2 / (r : ℝ)) ≤
        Real.exp (-2 * BooleanSlices.scale n gamma) :=
    Real.exp_le_exp.mpr hexponent
  have hdecayN' :
      2 * Real.exp (-2 * BooleanSlices.scale n gamma) ≤
        BooleanSlices.scale n (-5 / 2) := by
    simpa only [BooleanSlices.scale, Real.rpow_eq_pow,
      show -(5 / 2 : ℝ) = -5 / 2 by ring] using hdecayN
  have hqR : (q : ℝ) ≤ n := by exact_mod_cast hq
  calc
    2 * (q : ℝ) * Real.exp (-2 * Real.sqrt n ^ 2 / r) =
        (q : ℝ) * (2 * Real.exp (-2 * Real.sqrt n ^ 2 / r)) := by ring
    _ ≤ (q : ℝ) *
        (2 * Real.exp (-2 * BooleanSlices.scale n gamma)) := by
      gcongr
    _ ≤ (q : ℝ) * BooleanSlices.scale n (-5 / 2) := by
      exact mul_le_mul_of_nonneg_left hdecayN' (by positivity)
    _ ≤ (n : ℝ) * BooleanSlices.scale n (-5 / 2) := by
      exact mul_le_mul_of_nonneg_right hqR
        (BooleanSlices.scale_nonneg n (-5 / 2))
    _ = BooleanSlices.scale n (-3 / 2) := by
      rw [show (n : ℝ) = BooleanSlices.scale n 1 by
        exact (Real.rpow_one _).symm,
        BooleanSlices.scale_mul hnpos]
      congr 1
      ring

/-- Boolean assignments on the complement of the covered coordinates are
canonically the Boolean coordinates of the RLCD remainder. -/
noncomputable def outsideEquivRemainder
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) :
    {v : Fin n // v ∉ D.blocks.biUnion id} ≃ D.remainder :=
  { toFun := fun v ↦ ⟨v.1, by
      rw [D.remainder_eq]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, v.2⟩⟩
    invFun := fun v ↦ ⟨v.1, by
      exact fun hv ↦
        (Finset.disjoint_left.mp D.remainder_disjoint) v.2 hv⟩
    left_inv := by intro v; exact Subtype.ext rfl
    right_inv := by intro v; exact Subtype.ext rfl }

lemma card_outside_eq_remainder
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) :
    Fintype.card {v : Fin n // v ∉ D.blocks.biUnion id} = D.remainder.card := by
  rw [Fintype.card_congr D.outsideEquivRemainder]
  exact Fintype.card_coe D.remainder

lemma outsideAssignmentSet_subset_remainder
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (z : {v : Fin n // v ∉ D.blocks.biUnion id} → Bool) :
    LinearLCDCancellation.outsideAssignmentSet (D.blocks.biUnion id) z ⊆
      D.remainder := by
  rw [D.remainder_eq]
  exact LinearLCDCancellation.outsideAssignmentSet_subset_compl
    (D.blocks.biUnion id) z

/-- The centered neighbour fluctuation on a decoded remainder assignment is
exactly twice the graph cross linear form. -/
lemma degreeInto_outsideAssignmentSet_sub_half_remainder
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n))
    (i : Fin (Fintype.card D.Covered))
    (z : {v : Fin n // v ∉ D.blocks.biUnion id} → Bool) :
    (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
          (LinearLCDCancellation.outsideAssignmentSet
            (D.blocks.biUnion id) z) : ℝ) -
        (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2 =
      2 * LinearLCDCancellation.graphCrossLinear G
        (D.blocks.biUnion id) (D.finCoveredEquiv i) z := by
  rw [D.remainder_eq]
  exact
    LinearLCDCancellation.degreeInto_outsideAssignmentSet_sub_half_eq_two_mul_graphCrossLinear
      G (D.blocks.biUnion id) (D.finCoveredEquiv i) z

/-- The finite set of remainder assignments on which at least one covered
degree has a centered fluctuation of size at least `t`. -/
noncomputable def badRemainderConditionings
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n)) (t : ℝ) :
    Finset ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) :=
  Finset.univ.filter fun z ↦
    ∃ i : Fin (Fintype.card D.Covered),
      t ≤ |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1
            (LinearLCDCancellation.outsideAssignmentSet
              (D.blocks.biUnion id) z) : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
            D.remainder : ℝ) / 2|

/-- The exceptional remainder assignments have exponentially small count
with exponent governed by the remainder cardinality.  The good complement
therefore gives the simultaneous `sqrt n`-scale degree control needed by
the conditioned coefficient certificate. -/
theorem card_bad_remainder_conditionings_le
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n))
    (t : ℝ) (hrem : 0 < D.remainder.card) (ht : 0 < t) :
    ((Finset.univ.filter fun
        z : {v : Fin n // v ∉ D.blocks.biUnion id} → Bool ↦
      ∃ i : Fin (Fintype.card D.Covered),
        t ≤ |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1
              (LinearLCDCancellation.outsideAssignmentSet
                (D.blocks.biUnion id) z) : ℝ) -
            (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
              D.remainder : ℝ) / 2|).card : ℝ) ≤
      2 * (Fintype.card D.Covered : ℝ) *
        (Fintype.card
          ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) *
          Real.exp (-2 * t ^ 2 / D.remainder.card) := by
  classical
  let I := D.blocks.biUnion id
  let badDegree : ({v : Fin n // v ∉ I} → Bool) → Prop := fun z ↦
    ∃ i : Fin (Fintype.card D.Covered),
      t ≤ |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1
            (LinearLCDCancellation.outsideAssignmentSet I z) : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
            D.remainder : ℝ) / 2|
  let badCross : ({v : Fin n // v ∉ I} → Bool) → Prop := fun z ↦
    ∃ i : D.Covered,
      t / 2 ≤ |LinearLCDCancellation.graphCrossLinear G I i z|
  have hbad : (Finset.univ.filter badDegree) =
      Finset.univ.filter badCross := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨D.finCoveredEquiv i, ?_⟩
      have hid := D.degreeInto_outsideAssignmentSet_sub_half_remainder G i z
      have habs :
          |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                (LinearLCDCancellation.outsideAssignmentSet I z) : ℝ) -
              (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                D.remainder : ℝ) / 2| =
            2 * |LinearLCDCancellation.graphCrossLinear G I
              (D.finCoveredEquiv i) z| := by
        rw [hid, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [habs] at hi
      linarith
    · rintro ⟨i, hi⟩
      refine ⟨D.finCoveredEquiv.symm i, ?_⟩
      have hid := D.degreeInto_outsideAssignmentSet_sub_half_remainder G
        (D.finCoveredEquiv.symm i) z
      simp only [Equiv.apply_symm_apply] at hid
      have habs :
          |(AKSGraph.degreeInto G i.1
                (LinearLCDCancellation.outsideAssignmentSet I z) : ℝ) -
              (AKSGraph.degreeInto G i.1 D.remainder : ℝ) / 2| =
            2 * |LinearLCDCancellation.graphCrossLinear G I i z| := by
        rw [hid, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hgoal :
          t ≤ |(AKSGraph.degreeInto G i.1
                (LinearLCDCancellation.outsideAssignmentSet I z) : ℝ) -
              (AKSGraph.degreeInto G i.1 D.remainder : ℝ) / 2| := by
        rw [habs]
        linarith
      simpa only [Equiv.apply_symm_apply] using hgoal
  have hcompl : 0 < Fintype.card {v : Fin n // v ∉ I} := by
    rw [show Fintype.card {v : Fin n // v ∉ I} = D.remainder.card by
      simpa only [I] using D.card_outside_eq_remainder]
    exact hrem
  have htail :=
    LinearLCDCancellation.graphCrossLinear_exists_tail_compl_uniform
      G I (t / 2) hcompl (by positivity)
  have hIcard : I.card = Fintype.card D.Covered := by
    exact (Fintype.card_ofFinset I (fun _ ↦ Iff.rfl)).symm
  have houtcard :
      Fintype.card {v : Fin n // v ∉ I} = D.remainder.card := by
    simpa only [I] using D.card_outside_eq_remainder
  change ((Finset.univ.filter badDegree).card : ℝ) ≤ _
  rw [hbad]
  change ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
    ∃ i : I, t / 2 ≤
      |LinearLCDCancellation.graphCrossLinear G I i z|).card : ℝ) ≤ _
  rw [houtcard] at htail
  rw [hIcard] at htail
  have hexp :
      -8 * (t / 2) ^ 2 / (D.remainder.card : ℝ) =
        -2 * t ^ 2 / (D.remainder.card : ℝ) := by ring
  rw [hexp] at htail
  simpa only [I] using htail

lemma card_badRemainderConditionings_le
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n))
    (t : ℝ) (hrem : 0 < D.remainder.card) (ht : 0 < t) :
    ((D.badRemainderConditionings G t).card : ℝ) ≤
      2 * (Fintype.card D.Covered : ℝ) *
        (Fintype.card
          ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) *
          Real.exp (-2 * t ^ 2 / D.remainder.card) := by
  simpa only [badRemainderConditionings] using
    D.card_bad_remainder_conditionings_le G t hrem ht

/-- For a structured decomposition with remainder at most `n^(1-gamma)`,
the simultaneous `sqrt n`-atypical conditionings occupy at most an
`n^(-3/2)` fraction of the outside cube. -/
theorem eventually_card_badRemainderConditionings_sqrt_le
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ {k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
        (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n)),
        (D.remainder.card : ℝ) ≤
            BooleanSlices.scale n (1 - gamma) →
        ((D.badRemainderConditionings G (Real.sqrt n)).card : ℝ) ≤
          BooleanSlices.scale n (-3 / 2) *
            (Fintype.card
              ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) := by
  have hfactor := eventually_remainder_exceptional_factor_le gamma hgamma
  filter_upwards [hfactor, Filter.eventually_ge_atTop 1] with n hfactorN hn
  intro k d rho D G hremBound
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  by_cases hrem : 0 < D.remainder.card
  · have hcard :
        D.remainder.card + Fintype.card D.Covered = n := by
      simpa only [Fintype.card_fin] using D.remainder_card_add_card_covered
    have hq : Fintype.card D.Covered ≤ n := by
      omega
    have htail := D.card_badRemainderConditionings_le G
      (Real.sqrt n) hrem hsqrt
    have hsmall := hfactorN (Fintype.card D.Covered) D.remainder.card
      hq hrem hremBound
    calc
      ((D.badRemainderConditionings G (Real.sqrt n)).card : ℝ) ≤
          2 * (Fintype.card D.Covered : ℝ) *
            (Fintype.card
              ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) *
              Real.exp (-2 * (Real.sqrt n) ^ 2 / D.remainder.card) := htail
      _ = (2 * (Fintype.card D.Covered : ℝ) *
              Real.exp (-2 * (Real.sqrt n) ^ 2 / D.remainder.card)) *
            (Fintype.card
              ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) := by
        ring
      _ ≤ BooleanSlices.scale n (-3 / 2) *
            (Fintype.card
              ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
  · have hremZero : D.remainder.card = 0 := Nat.eq_zero_of_not_pos hrem
    have hremEmpty : D.remainder = ∅ := Finset.card_eq_zero.mp hremZero
    have hbadEmpty : D.badRemainderConditionings G (Real.sqrt n) = ∅ := by
      ext z
      constructor
      · intro hz
        have hbad := (Finset.mem_filter.mp hz).2
        obtain ⟨i, hi⟩ := hbad
        have hOsub := D.outsideAssignmentSet_subset_remainder z
        have hOempty :
            LinearLCDCancellation.outsideAssignmentSet
                (D.blocks.biUnion id) z = ∅ := by
          ext v
          constructor
          · intro hv
            have := hOsub hv
            simpa [hremEmpty] using this
          · intro hv
            simp at hv
        rw [hOempty, hremEmpty] at hi
        simp only [AKSGraph.degreeInto_empty, Nat.cast_zero, zero_div,
          sub_zero, abs_zero] at hi
        exact ((not_le_of_gt hsqrt) hi).elim
      · intro hz
        simp at hz
    rw [hbadEmpty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (BooleanSlices.scale_nonneg n (-3 / 2)) (by positivity)

end Erdos88.RLCD.BucketDecomposition

namespace Erdos88.GaussianQuadratic

open BooleanSlices

/-- Uniform asymptotic absorption of the three terms in the conditioned
`wStar` estimate.  The exact identity `q = m*s` is what replaces the
apparently dangerous factor `q/s` by the bucket count `m`. -/
lemma eventually_conditionedCoefficient_numeric
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ q m s : ℕ, q ≤ n → n ≤ 2 * q → 0 < s → q = m * s →
        (m : ℝ) ≤ 2 * scale q (2 * gamma) →
        (scale n (1 / 2 + 4 * gamma) + Real.sqrt n) +
            (q : ℝ) *
              ((s : ℝ)⁻¹ *
                (2 * (scale q ((1 - 2 * gamma) / 2) * Real.log q))) / 2 ≤
          scale q (1 / 2 + 6 * gamma) := by
  let a : ℝ := 1 / 2 + 4 * gamma
  let b : ℝ := 1 / 2 + 6 * gamma
  let K : ℝ := 3 * scale 2 a
  have ha : 0 < a := by dsimp only [a]; linarith
  have hab : a < b := by dsimp only [a, b]; linarith
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num) (scale_nonneg 2 a)
  have habsorbEvent :=
    QuadraticCancellation.eventually_const_mul_rpow_le_rpow K a b hK hab
  have hlogEvent :=
    QuadraticCancellation.eventually_const_mul_log_le_rpow
      6 (5 * gamma) (by norm_num) (by positivity)
  obtain ⟨Nabsorb, hNabsorb⟩ := Filter.eventually_atTop.1 habsorbEvent
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.1 hlogEvent
  let N := max 1 (max Nabsorb Nlog)
  filter_upwards [Filter.eventually_ge_atTop (2 * N)] with n hn
  intro q m s hqn hnq hs hqms hm
  have hNq : N ≤ q := by
    dsimp only [N] at hn ⊢
    omega
  have hqOne : 1 ≤ q := (le_max_left 1 (max Nabsorb Nlog)).trans hNq
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hqOne
  have hnOne : 1 ≤ n := by omega
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnOne
  have habsorbRaw := hNabsorb q
    ((le_max_left Nabsorb Nlog).trans
      ((le_max_right 1 (max Nabsorb Nlog)).trans hNq))
  have habsorb : K * scale q a ≤ scale q b := by
    simpa only [scale, Real.rpow_eq_pow] using habsorbRaw
  have hlogRaw := hNlog q
    ((le_max_right Nabsorb Nlog).trans
      ((le_max_right 1 (max Nabsorb Nlog)).trans hNq))
  have hlog : 6 * Real.log q ≤ scale q (5 * gamma) := by
    simpa only [scale, Real.rpow_eq_pow] using hlogRaw
  have hbase : scale n a ≤ scale (2 * q) a := by
    have hcast : (n : ℝ) ≤ (2 * q : ℕ) := by exact_mod_cast hnq
    simpa only [scale, Real.rpow_eq_pow] using
      Real.rpow_le_rpow (show (0 : ℝ) ≤ n by positivity) hcast ha.le
  have hscaleTwo : scale (2 * q) a = scale 2 a * scale q a := by
    unfold scale
    rw [show (((2 * q : ℕ) : ℝ)) = 2 * (q : ℝ) by norm_num,
      Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow]
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ q)
  have hrhoThree : 3 * scale n a ≤ scale q b := by
    calc
      3 * scale n a ≤ 3 * scale (2 * q) a :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = K * scale q a := by rw [hscaleTwo]; dsimp only [K]; ring
      _ ≤ scale q b := habsorb
  have hrho : scale n a ≤ scale q b / 3 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
      simpa only [mul_comm] using hrhoThree)
  have hsqrtScale : Real.sqrt (n : ℝ) ≤ scale n a := by
    rw [Real.sqrt_eq_rpow]
    exact scale_mono_exponent hnOne (by dsimp only [a]; linarith)
  have hsqrt : Real.sqrt (n : ℝ) ≤ scale q b / 3 :=
    hsqrtScale.trans hrho
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqmsR : (q : ℝ) = (m : ℝ) * (s : ℝ) := by
    exact_mod_cast hqms
  have hqs : (q : ℝ) * (s : ℝ)⁻¹ = (m : ℝ) := by
    rw [hqmsR]
    field_simp
  let A := scale q ((1 - 2 * gamma) / 2) * Real.log q
  have hlogNonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqOne)
  have hANonneg : 0 ≤ A :=
    mul_nonneg (scale_nonneg q _) hlogNonneg
  have hcountEq :
      (q : ℝ) * ((s : ℝ)⁻¹ * (2 * A)) / 2 = (m : ℝ) * A := by
    rw [show (q : ℝ) * ((s : ℝ)⁻¹ * (2 * A)) / 2 =
      ((q : ℝ) * (s : ℝ)⁻¹) * A by ring, hqs]
  have hcountThree : 3 * ((m : ℝ) * A) ≤ scale q b := by
    calc
      3 * ((m : ℝ) * A) ≤
          3 * (2 * scale q (2 * gamma) * A) := by
        gcongr
      _ = (6 * Real.log q) *
          (scale q (2 * gamma) * scale q ((1 - 2 * gamma) / 2)) := by
        dsimp only [A]
        ring
      _ ≤ scale q (5 * gamma) *
          (scale q (2 * gamma) * scale q ((1 - 2 * gamma) / 2)) := by
        exact mul_le_mul_of_nonneg_right hlog
          (mul_nonneg (scale_nonneg q _) (scale_nonneg q _))
      _ = scale q b := by
        rw [scale_mul hqpos, scale_mul hqpos]
        congr 1
        dsimp only [b]
        ring
  have hcount : (m : ℝ) * A ≤ scale q b / 3 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
      simpa only [mul_comm] using hcountThree)
  dsimp only [a, b] at hrho hsqrt ⊢
  rw [show (q : ℝ) *
      ((s : ℝ)⁻¹ *
        (2 * (scale q ((1 - 2 * gamma) / 2) * Real.log q))) / 2 =
      (m : ℝ) * A by simpa only [A] using hcountEq]
  linarith

/-- Every typical remainder conditioning and every near-balanced covered
product slice satisfy the coefficient hypotheses of Claim 12.1. -/
theorem eventually_conditionedCovered_hasKSSSBalancedCoefficients
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
        (D : RLCD.BucketDecomposition
          (GraphQuadratic.graphEffectiveLinear G c)
          (RLCD.smallRLCDBucketCard n gamma)
          ((n : ℝ) ^ (1 / 2 + 4 * gamma))),
        (D.remainder.card : ℝ) ≤ (n : ℝ) / 2 →
        IsKSSSPartition (2 * gamma) D.finCoveredPartition →
        ∀ (hbucket : RobustRank.HasEqualBuckets
            D.finCoveredPartition.bucket)
          (ell : Fin (Fintype.card D.BlockIndex) → ℕ),
          IsNearBalanced (2 * gamma) D.finCoveredPartition ell →
          ∀ (O : Finset (Fin n)),
            (∀ i : Fin (Fintype.card D.Covered),
              |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
                (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                  D.remainder : ℝ) / 2| ≤ Real.sqrt n) →
            HasKSSSBalancedCoefficients (2 * gamma)
              D.finCoveredPartition
              (Structured.wStar
                (bucketProjectionMatrix D.finCoveredPartition.bucket
                  hbucket.choose)
                (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
                (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                  (D.conditionedCoveredCoefficient G c O))
                (productSliceDelta D.finCoveredPartition hbucket.choose ell))
              (bucketCenteredAdjacency D.finCoveredPartition.bucket
                hbucket.choose (D.finCoveredGraph G)) := by
  have hnumeric := eventually_conditionedCoefficient_numeric gamma hgamma
  filter_upwards [hnumeric] with n hnumericN
  intro G c D hremHalf hpart hbucket ell hbalanced O htypical
  let q := Fintype.card D.Covered
  let m := Fintype.card D.BlockIndex
  let s := hbucket.choose
  have hcard : D.remainder.card + q = n := by
    simpa only [q, Fintype.card_fin] using D.remainder_card_add_card_covered
  have hq : q ≤ n := by omega
  have hcardR : (D.remainder.card : ℝ) + (q : ℝ) = (n : ℝ) := by
    exact_mod_cast hcard
  have hnqR : (n : ℝ) ≤ 2 * (q : ℝ) := by linarith
  have hnq : n ≤ 2 * q := by exact_mod_cast hnqR
  have hs : 0 < s := hbucket.choose_spec.1
  have hqms : q = m * s := by
    exact RobustRank.card_eq_bucketCount_mul_bucketSize
      D.finCoveredPartition.bucket
        (fun j ↦ hbucket.choose_spec.2 j)
  have hm : (m : ℝ) ≤ 2 * scale q (2 * gamma) := by
    simpa only [m, q] using hpart.2.2
  have hbound := hnumericN q m s hq hnq hs hqms hm
  apply hasKSSSBalancedCoefficients_conditionedCovered D G c rfl O
    htypical (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)
    hbucket ell hbalanced
  simpa only [q, s, scale, Real.rpow_eq_pow,
    show 1 / 2 + 3 * (2 * gamma) = 1 / 2 + 6 * gamma by ring,
    show (1 - 2 * gamma) / 2 = (1 - (2 * gamma)) / 2 by ring]
    using hbound

end Erdos88.GaussianQuadratic
