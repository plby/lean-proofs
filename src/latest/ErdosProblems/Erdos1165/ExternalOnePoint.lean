/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos1165.ExternalWalk
import ErdosProblems.Erdos1165.FourierReturn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The external walk: exact one-point finite-dimensional formulae

Hao--Li--Okada--Zheng's estimate (7.4) is a sharp upper tail for the local
time at the origin of the external walk.  This file establishes, from the
actual retained-block product law, the finite-dimensional identities that
precede the analytic local central limit theorem:

* the exact real Fourier transform of one external increment;
* the uniform law of a finite external block;
* the exact counting formula for the probability of return at time `n`;
* comparison with the number of ordinary planar `2n`-step returns.

The last comparison is deliberately recorded with its exact conditioning
factor.  It is not strong enough for (7.4): obtaining the sharp constant
`15 / (16 * π)` requires Fourier inversion and a uniform local central limit
estimate for the transform computed below.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalOnePoint

open ExternalWalk LazyDecomposition

/-! ## Exact Fourier transform of one retained increment -/

/-- The (real) cosine transform of the external increment law.  Symmetry of
the displacement multiset makes this the real-valued characteristic
function. -/
noncomputable def externalCosTransform (o : Orientation) (x y : ℝ) : ℝ :=
  (∑ b : RetainedBlock o,
    Real.cos (x * (retainedDisplacement o b).1 +
      y * (retainedDisplacement o b).2)) / 15

private def externalSupport : Finset Point :=
  {(0, 0), (2, 0), (-2, 0), (0, 2), (0, -2),
    (1, 1), (1, -1), (-1, 1), (-1, -1)}

private lemma retainedDisplacement_mem_externalSupport (o : Orientation)
    (b : RetainedBlock o) : retainedDisplacement o b ∈ externalSupport := by
  rcases b with ⟨⟨d₁, d₂⟩, hb⟩
  cases o <;> fin_cases d₁ <;> fin_cases d₂ <;>
    norm_num [externalSupport, retainedDisplacement,
      ExternalWalk.blockDisplacement, directionVector]

private lemma exact_multiplicities (o : Orientation) :
    displacementMultiplicity o (0, 0) = 3 ∧
    displacementMultiplicity o (2, 0) = 1 ∧
    displacementMultiplicity o (-2, 0) = 1 ∧
    displacementMultiplicity o (0, 2) = 1 ∧
    displacementMultiplicity o (0, -2) = 1 ∧
    displacementMultiplicity o (1, 1) = 2 ∧
    displacementMultiplicity o (1, -1) = 2 ∧
    displacementMultiplicity o (-1, 1) = 2 ∧
    displacementMultiplicity o (-1, -1) = 2 := by
  cases o <;> decide

private theorem sum_retainedDisplacement (o : Orientation) (f : Point → ℝ) :
    (∑ b : RetainedBlock o, f (retainedDisplacement o b)) =
      ∑ z ∈ externalSupport, (displacementMultiplicity o z : ℝ) * f z := by
  symm
  calc
    (∑ z ∈ externalSupport, (displacementMultiplicity o z : ℝ) * f z) =
        ∑ z ∈ externalSupport,
          ∑ b ∈ (Finset.univ : Finset (RetainedBlock o)) with
            retainedDisplacement o b = z, f z := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [displacementMultiplicity]
    _ = ∑ b ∈ (Finset.univ : Finset (RetainedBlock o)) with
          retainedDisplacement o b ∈ externalSupport,
          f (retainedDisplacement o b) :=
      Finset.sum_fiberwise_eq_sum_filter' _ _ _ _
    _ = ∑ b : RetainedBlock o, f (retainedDisplacement o b) := by
      simp [retainedDisplacement_mem_externalSupport]

/-- Exact Fourier polynomial of one external step.  In particular this is
independent of the deletion orientation. -/
theorem externalCosTransform_eq (o : Orientation) (x y : ℝ) :
    externalCosTransform o x y =
      (3 + 2 * Real.cos (2 * x) + 2 * Real.cos (2 * y) +
        8 * Real.cos x * Real.cos y) / 15 := by
  unfold externalCosTransform
  change (∑ b : RetainedBlock o,
    (fun z : Point ↦ Real.cos (x * (z.1 : ℝ) + y * (z.2 : ℝ)))
      (retainedDisplacement o b)) / 15 = _
  rw [sum_retainedDisplacement o
    (fun z : Point ↦ Real.cos (x * (z.1 : ℝ) + y * (z.2 : ℝ)))]
  obtain ⟨h0, h20, hm20, h02, h0m2, h11, h1m1, hm11, hm1m1⟩ :=
    exact_multiplicities o
  simp [externalSupport, h0, h20, hm20, h02, h0m2, h11, h1m1, hm11, hm1m1,
    Real.cos_neg, Real.cos_add]
  ring_nf

/-- Equivalent square form, exhibiting the external transform as the affine
image of the two-step simple-random-walk transform. -/
theorem externalCosTransform_eq_square (o : Orientation) (x y : ℝ) :
    externalCosTransform o x y =
      ((2 * Real.cos x + 2 * Real.cos y) ^ 2 - 1) / 15 := by
  rw [externalCosTransform_eq]
  rw [Real.cos_two_mul, Real.cos_two_mul]
  ring

@[simp] theorem externalCosTransform_zero (o : Orientation) :
    externalCosTransform o 0 0 = 1 := by
  rw [externalCosTransform_eq_square]
  norm_num

/-- The second unit-modulus saddle reflects that every external displacement
lies in the index-two sublattice `{z | z.1 + z.2 is even}`.  Both saddles
contribute to the sharp local-CLT constant `15 / (16 * π)`. -/
theorem externalCosTransform_pi_pi (o : Orientation) :
    externalCosTransform o Real.pi Real.pi = 1 := by
  rw [externalCosTransform_eq_square, Real.cos_pi]
  norm_num

/-! ## Finite external words and their exact law -/

/-- A finite prefix of retained blocks. -/
def externalPrefix (o : Orientation) (n : ℕ)
    (η : ℕ → RetainedBlock o) : Fin n → RetainedBlock o :=
  fun i ↦ η i

/-- Product law of `n` retained blocks. -/
noncomputable def externalBlockLaw (o : Orientation) (n : ℕ) :
    Measure (Fin n → RetainedBlock o) :=
  Measure.infinitePi fun _ : Fin n ↦ retainedBlockLaw o

noncomputable instance (o : Orientation) (n : ℕ) :
    IsProbabilityMeasure (externalBlockLaw o n) := by
  unfold externalBlockLaw
  infer_instance

lemma measurable_externalPrefix (o : Orientation) (n : ℕ) :
    Measurable (externalPrefix o n) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)

/-- Every finite prefix has the finite product law. -/
theorem externalBlocks_map_externalPrefix (o : Orientation) (n : ℕ) :
    (externalBlocks o).map (externalPrefix o n) = externalBlockLaw o n := by
  unfold externalBlocks externalBlockLaw externalPrefix
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ retainedBlockLaw o)
    (f := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective

/-- The finite external-block law is uniform on the `15^n` retained words. -/
theorem externalBlockLaw_eq_uniform (o : Orientation) (n : ℕ) :
    externalBlockLaw o n =
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin n → RetainedBlock o)) := by
  rw [externalBlockLaw, Measure.infinitePi_eq_pi]
  symm
  simpa [retainedBlockLaw] using
    (ProbabilityTheory.uniformOn_pi
      (f := fun _ : Fin n ↦ (Set.univ : Set (RetainedBlock o))))

/-- Displacement of a finite retained-block word. -/
def externalWordDisplacement (o : Orientation) {n : ℕ}
    (u : Fin n → RetainedBlock o) : Point :=
  ∑ i, retainedDisplacement o (u i)

/-- Finite set of retained-block words which return to the origin. -/
def externalReturningWords (o : Orientation) (n : ℕ) :
    Finset (Fin n → RetainedBlock o) :=
  Finset.univ.filter fun u ↦ externalWordDisplacement o u = 0

@[simp] lemma mem_externalReturningWords {o : Orientation} {n : ℕ}
    {u : Fin n → RetainedBlock o} :
    u ∈ externalReturningWords o n ↔ externalWordDisplacement o u = 0 := by
  simp [externalReturningWords]

lemma externalPosition_eq_externalWordDisplacement (o : Orientation)
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    externalPosition o η n = externalWordDisplacement o (externalPrefix o n η) := by
  rw [externalPosition, externalWordDisplacement]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

/-- Exact finite-time return probability on the IID retained-block space. -/
theorem externalBlocks_return_probability (o : Orientation) (n : ℕ) :
    externalBlocks o {η | externalPosition o η n = 0} =
      (externalReturningWords o n).card * (1 / 15) ^ n := by
  have hset : {η | externalPosition o η n = 0} =
      externalPrefix o n ⁻¹' (externalReturningWords o n :
        Set (Fin n → RetainedBlock o)) := by
    ext η
    simp only [mem_ofPred_eq, Finset.mem_coe, mem_externalReturningWords, mem_preimage]
    rw [externalPosition_eq_externalWordDisplacement]
  rw [hset, ← Measure.map_apply (measurable_externalPrefix o n) (by measurability),
    externalBlocks_map_externalPrefix, externalBlockLaw_eq_uniform,
    ProbabilityTheory.uniformOn_univ, MeasureTheory.Measure.count_apply_finset]
  simp only [Fintype.card_fun, Fintype.card_fin, card_retainedBlock]
  rw [div_eq_mul_inv, Nat.cast_pow]
  congr 1
  calc
    ((15 : ℝ≥0∞) ^ n)⁻¹ = ((15 : ℝ≥0∞)⁻¹) ^ n := ENNReal.inv_pow
    _ = (1 / 15 : ℝ≥0∞) ^ n := by norm_num

/-- The same exact return probability on external path space. -/
theorem externalWalkLaw_return_probability (o : Orientation) (n : ℕ) :
    externalWalkLaw o {s | s n = 0} =
      (externalReturningWords o n).card * (1 / 15) ^ n := by
  rw [externalWalkLaw, Measure.map_apply (measurable_externalPosition o)
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)]
  exact externalBlocks_return_probability o n

/-! ## Exact comparison with ordinary two-step words -/

/-- Flatten `n` ordered two-step blocks into a direction word of length
`n * 2`. -/
def blockWordEquivDirectionWord (n : ℕ) :
    (Fin n → Block) ≃ (Fin (n * 2) → Direction) :=
  (Equiv.piCongrRight fun _ : Fin n ↦ (finTwoArrowEquiv Direction).symm).trans <|
    (Equiv.curry (Fin n) (Fin 2) Direction).symm |>.trans <|
      finProdFinEquiv.piCongrLeft (fun _ : Fin (n * 2) ↦ Direction)

lemma blockWordEquivDirectionWord_displacement (n : ℕ) (u : Fin n → Block) :
    Erdos1165.blockDisplacement (blockWordEquivDirectionWord n u) =
      ∑ i, ExternalWalk.blockDisplacement (u i) := by
  rw [Erdos1165.blockDisplacement]
  calc
    (∑ k, directionVector (blockWordEquivDirectionWord n u k)) =
        ∑ ij : Fin n × Fin 2,
          directionVector (blockWordEquivDirectionWord n u (finProdFinEquiv ij)) := by
      symm
      exact Equiv.sum_comp finProdFinEquiv
        (fun k ↦ directionVector (blockWordEquivDirectionWord n u k))
    _ = ∑ i : Fin n, ∑ j : Fin 2,
          directionVector (blockWordEquivDirectionWord n u (finProdFinEquiv (i, j))) :=
      Fintype.sum_prod_type _
    _ = ∑ i : Fin n, ExternalWalk.blockDisplacement (u i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [blockWordEquivDirectionWord, ExternalWalk.blockDisplacement]

/-- Reindex a direction word from `n * 2` to the conventional `2 * n`. -/
def reindexTwoMul (n : ℕ) :
    (Fin (n * 2) → Direction) ≃ (Fin (2 * n) → Direction) :=
  (finCongr (Nat.mul_comm n 2)).piCongrLeft
    (fun _ : Fin (2 * n) ↦ Direction)

lemma reindexTwoMul_displacement (n : ℕ) (u : Fin (n * 2) → Direction) :
    Erdos1165.blockDisplacement (reindexTwoMul n u) =
      Erdos1165.blockDisplacement u := by
  unfold Erdos1165.blockDisplacement
  calc
    (∑ j, directionVector (reindexTwoMul n u j)) =
        ∑ i, directionVector
          (reindexTwoMul n u ((finCongr (Nat.mul_comm n 2)) i)) := by
      symm
      exact Equiv.sum_comp (finCongr (Nat.mul_comm n 2))
        (fun j ↦ directionVector (reindexTwoMul n u j))
    _ = ∑ i, directionVector (u i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg directionVector <|
        Equiv.piCongrLeft_apply_apply
          (fun _ : Fin (2 * n) ↦ Direction)
          (finCongr (Nat.mul_comm n 2)) u i

/-- Ordinary direction words, indexed as `n` consecutive pairs, that return
to the origin. -/
def pairedReturningWords (n : ℕ) : Finset (Fin (n * 2) → Direction) :=
  Finset.univ.filter fun u ↦ Erdos1165.blockDisplacement u = 0

@[simp] lemma mem_pairedReturningWords {n : ℕ} {u : Fin (n * 2) → Direction} :
    u ∈ pairedReturningWords n ↔ Erdos1165.blockDisplacement u = 0 := by
  simp [pairedReturningWords]

private def pairedReturnEquivStandard (n : ℕ) :
    {u : Fin (n * 2) → Direction // Erdos1165.blockDisplacement u = 0} ≃
      {u : Fin (2 * n) → Direction // Erdos1165.blockDisplacement u = 0} :=
  Equiv.subtypeEquiv (reindexTwoMul n) fun u ↦ by
    rw [reindexTwoMul_displacement]

/-- The paired indexing does not change the classical exact return count. -/
theorem card_pairedReturningWords (n : ℕ) :
    (pairedReturningWords n).card = Nat.centralBinom n ^ 2 := by
  calc
    (pairedReturningWords n).card =
        Fintype.card {u : Fin (n * 2) → Direction //
          Erdos1165.blockDisplacement u = 0} := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card {u : Fin (2 * n) → Direction //
          Erdos1165.blockDisplacement u = 0} :=
      Fintype.card_congr (pairedReturnEquivStandard n)
    _ = Nat.centralBinom n ^ 2 := Erdos1165.card_returning_blocks n

/-- Forget retention and flatten an external word into its underlying
ordinary direction word. -/
def expandExternalWord (o : Orientation) (n : ℕ)
    (u : Fin n → RetainedBlock o) : Fin (n * 2) → Direction :=
  blockWordEquivDirectionWord n fun i ↦ (u i : Block)

lemma expandExternalWord_injective (o : Orientation) (n : ℕ) :
    Function.Injective (expandExternalWord o n) := by
  intro u v huv
  have hblocks : (fun i ↦ (u i : Block)) = (fun i ↦ (v i : Block)) :=
    (blockWordEquivDirectionWord n).injective huv
  funext i
  exact Subtype.ext (congrFun hblocks i)

lemma expandExternalWord_displacement (o : Orientation) (n : ℕ)
    (u : Fin n → RetainedBlock o) :
    Erdos1165.blockDisplacement (expandExternalWord o n u) =
      externalWordDisplacement o u := by
  rw [expandExternalWord, blockWordEquivDirectionWord_displacement]
  rfl

/-- Every retained returning word is an ordinary returning word.  This is an
actual finite combinatorial bound; no local central limit theorem is used. -/
theorem card_externalReturningWords_le (o : Orientation) (n : ℕ) :
    (externalReturningWords o n).card ≤ Nat.centralBinom n ^ 2 := by
  rw [← card_pairedReturningWords n]
  apply Finset.card_le_card_of_injOn (expandExternalWord o n)
  · intro u hu
    rw [Finset.mem_coe, mem_pairedReturningWords,
      expandExternalWord_displacement]
    exact (mem_externalReturningWords.mp hu)
  · exact (expandExternalWord_injective o n).injOn

/-- The resulting exact finite upper bound on the one-point return
probability.  Its factor `15^{-n}` displays why the naive conditioning
comparison is exponentially too weak for HLOZ (7.4). -/
theorem externalWalkLaw_return_probability_le (o : Orientation) (n : ℕ) :
    externalWalkLaw o {s | s n = 0} ≤
      (Nat.centralBinom n ^ 2 : ℝ≥0∞) * (1 / 15) ^ n := by
  rw [externalWalkLaw_return_probability]
  gcongr
  exact_mod_cast card_externalReturningWords_le o n

/-! ## A checked finite first-moment local-time tail -/

/-- Number of visits of the external chain to the origin through external
time `n`, including time zero. -/
def externalOriginLocalTime (o : Orientation)
    (η : ℕ → RetainedBlock o) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun j ↦ externalPosition o η j = 0).card

lemma measurableSet_externalPosition_eq_zero (o : Orientation) (n : ℕ) :
    MeasurableSet {η : ℕ → RetainedBlock o | externalPosition o η n = 0} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply n).comp (measurable_externalPosition o)) measurable_const

lemma externalOriginLocalTime_eq_sum_indicators (o : Orientation)
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    (externalOriginLocalTime o η n : ℝ≥0∞) =
      ∑ j ∈ Finset.range (n + 1),
        ({η : ℕ → RetainedBlock o | externalPosition o η j = 0}.indicator
          (fun _ ↦ (1 : ℝ≥0∞))) η := by
  rw [externalOriginLocalTime, Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hreturn : externalPosition o η j = 0 <;> simp [hreturn]

lemma measurable_externalOriginLocalTime_ennreal (o : Orientation) (n : ℕ) :
    Measurable fun η : ℕ → RetainedBlock o ↦
      (externalOriginLocalTime o η n : ℝ≥0∞) := by
  rw [show (fun η : ℕ → RetainedBlock o ↦
      (externalOriginLocalTime o η n : ℝ≥0∞)) =
      (fun η ↦ ∑ j ∈ Finset.range (n + 1),
        ({η : ℕ → RetainedBlock o | externalPosition o η j = 0}.indicator
          (fun _ ↦ (1 : ℝ≥0∞))) η) by
        funext η
        exact externalOriginLocalTime_eq_sum_indicators o η n]
  exact (Finset.range (n + 1)).measurable_fun_sum fun j hj ↦
    measurable_const.indicator (measurableSet_externalPosition_eq_zero o j)

/-- Exact expectation of the finite external local time, expressed solely in
terms of the checked finite return counts. -/
theorem lintegral_externalOriginLocalTime (o : Orientation) (n : ℕ) :
    ∫⁻ η, (externalOriginLocalTime o η n : ℝ≥0∞) ∂externalBlocks o =
      ∑ j ∈ Finset.range (n + 1),
        ((externalReturningWords o j).card : ℝ≥0∞) * (1 / 15) ^ j := by
  calc
    (∫⁻ η, (externalOriginLocalTime o η n : ℝ≥0∞) ∂externalBlocks o) =
        ∫⁻ η, ∑ j ∈ Finset.range (n + 1),
          ({η : ℕ → RetainedBlock o | externalPosition o η j = 0}.indicator
            (fun _ ↦ (1 : ℝ≥0∞))) η ∂externalBlocks o := by
      apply lintegral_congr
      exact fun η ↦ externalOriginLocalTime_eq_sum_indicators o η n
    _ = ∑ j ∈ Finset.range (n + 1),
        ∫⁻ η, ({η : ℕ → RetainedBlock o | externalPosition o η j = 0}.indicator
          (fun _ ↦ (1 : ℝ≥0∞))) η ∂externalBlocks o := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro j hj
      exact measurable_const.indicator (measurableSet_externalPosition_eq_zero o j)
    _ = ∑ j ∈ Finset.range (n + 1),
        externalBlocks o {η | externalPosition o η j = 0} := by
      apply Finset.sum_congr rfl
      intro j hj
      exact MeasureTheory.lintegral_indicator_one
        (measurableSet_externalPosition_eq_zero o j)
    _ = ∑ j ∈ Finset.range (n + 1),
        ((externalReturningWords o j).card : ℝ≥0∞) * (1 / 15) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact externalBlocks_return_probability o j

/-- Honest finite first-moment upper tail for the external local time.  This
is much weaker than HLOZ (7.4), but unlike (7.4) it follows without a renewal
argument or a local central limit theorem. -/
theorem externalOriginLocalTime_tail_le (o : Orientation) (n k : ℕ)
    (hk : 0 < k) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤
      (∑ j ∈ Finset.range (n + 1),
        ((externalReturningWords o j).card : ℝ≥0∞) * (1 / 15) ^ j) / k := by
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div
    (μ := externalBlocks o)
    (measurable_externalOriginLocalTime_ennreal o n).aemeasurable
    (ε := (k : ℝ≥0∞)) (by exact_mod_cast hk.ne') (by finiteness)
  rw [lintegral_externalOriginLocalTime] at hmarkov
  have hset : {η : ℕ → RetainedBlock o |
      (k : ℝ≥0∞) ≤ (externalOriginLocalTime o η n : ℝ≥0∞)} =
      {η | k ≤ externalOriginLocalTime o η n} := by
    ext η
    norm_cast
  rw [hset] at hmarkov
  exact hmarkov

/-- Fully explicit version of the first-moment tail, using the ordinary
central-binomial return count as a rigorous upper bound. -/
theorem externalOriginLocalTime_tail_le_centralBinom (o : Orientation) (n k : ℕ)
    (hk : 0 < k) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤
      (∑ j ∈ Finset.range (n + 1),
        (Nat.centralBinom j ^ 2 : ℝ≥0∞) * (1 / 15) ^ j) / k := by
  refine (externalOriginLocalTime_tail_le o n k hk).trans ?_
  gcongr
  exact_mod_cast card_externalReturningWords_le o _

end Erdos1165.ExternalOnePoint
