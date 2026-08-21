/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos88.RLCD
import ErdosProblems.Erdos88.BooleanSlices

/-!
# Equal partitions from the small-RLCD decomposition

This file turns the disjoint equal-size blocks supplied by KSSS Lemma 4.12
into the exact finite bucket-partition interface used in Section 11.  The
small remainder stays outside the covered coordinate subtype.
-/

open scoped BigOperators

namespace Erdos88
namespace RLCD
namespace BucketDecomposition

open BooleanSlices

variable {α : Type*} [Fintype α] [DecidableEq α]
  {d : α → ℝ} {k : ℕ} {ρ : ℝ}

/-- The coordinates covered by the equal-size blocks of a bucket decomposition. -/
def Covered (D : BucketDecomposition d k ρ) :=
  {i : α // i ∈ D.blocks.biUnion id}

/-- The finite type indexing the blocks of a bucket decomposition. -/
def BlockIndex (D : BucketDecomposition d k ρ) :=
  {I : Finset α // I ∈ D.blocks}

noncomputable instance (D : BucketDecomposition d k ρ) : Fintype D.Covered :=
  Fintype.ofFinset (D.blocks.biUnion id) fun _ ↦ Iff.rfl

noncomputable instance (D : BucketDecomposition d k ρ) : Fintype D.BlockIndex :=
  Fintype.ofFinset D.blocks fun _ ↦ Iff.rfl

noncomputable instance (D : BucketDecomposition d k ρ) : DecidableEq D.Covered :=
  Classical.decEq _

noncomputable instance (D : BucketDecomposition d k ρ) : DecidableEq D.BlockIndex :=
  Classical.decEq _

private lemma blocks_disjoint_coe (D : BucketDecomposition d k ρ) :
    ((D.blocks : Set (Finset α))).PairwiseDisjoint fun I ↦ (I : Set α) := by
  intro I hI J hJ hIJ
  simpa only [Function.onFun, id_eq, Finset.disjoint_coe] using
    D.blocks_disjoint hI hJ hIJ

/-- A covered coordinate is equivalently a block together with a coordinate in it. -/
noncomputable def coveredEquivSigma (D : BucketDecomposition d k ρ) :
    D.Covered ≃ Σ I : D.BlockIndex, {i : α // i ∈ I.1} :=
  (Equiv.setCongr Finset.coe_biUnion).trans
    (Set.biUnionEqSigmaOfDisjoint D.blocks_disjoint_coe)

@[simp] lemma coveredEquivSigma_snd_val (D : BucketDecomposition d k ρ)
    (x : D.Covered) :
    ((D.coveredEquivSigma x).2 : α) = x.1 := by
  exact Set.coe_snd_biUnionEqSigmaOfDisjoint D.blocks_disjoint_coe
    ((Equiv.setCongr Finset.coe_biUnion) x)

/-- The nonnegative center attached by the RLCD decomposition to a block. -/
noncomputable def blockCenter (D : BucketDecomposition d k ρ)
    (I : D.BlockIndex) : ℝ :=
  Classical.choose (D.blocks_good I.1 I.2).2

lemma blockCenter_nonneg (D : BucketDecomposition d k ρ)
    (I : D.BlockIndex) : 0 ≤ D.blockCenter I :=
  (Classical.choose_spec (D.blocks_good I.1 I.2).2).1

lemma close_to_blockCenter (D : BucketDecomposition d k ρ)
    (I : D.BlockIndex) (i : α) (hi : i ∈ I.1) :
    |d i - D.blockCenter I| ≤ ρ :=
  (Classical.choose_spec (D.blocks_good I.1 I.2).2).2 i hi

/-- The equal-block partition naturally carried by the covered coordinates. -/
noncomputable def coveredPartition (D : BucketDecomposition d k ρ) :
    BucketPartition D.Covered D.BlockIndex where
  bucket i := (D.coveredEquivSigma i).1

lemma covered_close_to_blockCenter (D : BucketDecomposition d k ρ)
    (i : D.Covered) :
    |d i.1 - D.blockCenter (D.coveredPartition.bucket i)| ≤ ρ := by
  let y := D.coveredEquivSigma i
  have hclose := D.close_to_blockCenter y.1 y.2.1 y.2.2
  simpa only [coveredPartition, y, coveredEquivSigma_snd_val] using hclose

/-- The fiber over a block is exactly that block. -/
private def sigmaFstFiberEquiv {ι : Type*} (p : ι → Type*) (i : ι) :
    {y : Σ j, p j // y.1 = i} ≃ p i where
  toFun y := by
    rcases y with ⟨⟨j, x⟩, hj⟩
    change j = i at hj
    subst j
    exact x
  invFun x := ⟨⟨i, x⟩, rfl⟩
  left_inv y := by
    rcases y with ⟨⟨j, x⟩, hj⟩
    change j = i at hj
    subst j
    rfl
  right_inv _ := rfl

noncomputable def coveredFiberEquiv (D : BucketDecomposition d k ρ)
    (I : D.BlockIndex) :
    {x : D.Covered // x ∈ D.coveredPartition.fiber I} ≃
      {i : α // i ∈ I.1} :=
  (D.coveredEquivSigma.subtypeEquiv fun x ↦ by
    rw [D.coveredPartition.mem_fiber]
    rfl).trans (sigmaFstFiberEquiv (fun J : D.BlockIndex ↦ {i : α // i ∈ J.1}) I)

@[simp] lemma card_coveredPartition_fiber (D : BucketDecomposition d k ρ)
    (I : D.BlockIndex) :
    (D.coveredPartition.fiber I).card = k := by
  rw [← Fintype.card_coe, Fintype.card_congr (D.coveredFiberEquiv I)]
  rw [Fintype.card_coe]
  exact (D.blocks_good I.1 I.2).1

lemma card_covered (D : BucketDecomposition d k ρ) :
    Fintype.card D.Covered = D.blocks.card * k := by
  rw [show Fintype.card D.Covered = (D.blocks.biUnion id).card by
    exact Fintype.card_ofFinset (D.blocks.biUnion id) fun _ ↦ Iff.rfl]
  rw [Finset.card_biUnion D.blocks_disjoint]
  calc
    ∑ I ∈ D.blocks, I.card = ∑ _I ∈ D.blocks, k := by
      apply Finset.sum_congr rfl
      intro I hI
      exact (D.blocks_good I hI).1
    _ = D.blocks.card * k := by simp

@[simp] lemma card_blockIndex (D : BucketDecomposition d k ρ) :
    Fintype.card D.BlockIndex = D.blocks.card := by
  exact Fintype.card_ofFinset D.blocks fun _ ↦ Iff.rfl

lemma remainder_card_add_card_covered (D : BucketDecomposition d k ρ) :
    D.remainder.card + Fintype.card D.Covered = Fintype.card α := by
  rw [show Fintype.card D.Covered = (D.blocks.biUnion id).card by
    exact Fintype.card_ofFinset (D.blocks.biUnion id) fun _ ↦ Iff.rfl]
  rw [← Finset.card_union_of_disjoint D.remainder_disjoint,
    D.remainder_union_covered, Finset.card_univ]

/-- Canonical finite relabeling of the covered coordinates. -/
noncomputable def finCoveredEquiv (D : BucketDecomposition d k ρ) :
    Fin (Fintype.card D.Covered) ≃ D.Covered :=
  (Fintype.equivFin D.Covered).symm

/-- Canonical finite relabeling of the blocks. -/
noncomputable def finBlockEquiv (D : BucketDecomposition d k ρ) :
    Fin (Fintype.card D.BlockIndex) ≃ D.BlockIndex :=
  (Fintype.equivFin D.BlockIndex).symm

/-- The covered equal-block partition, relabeled on standard finite types. -/
noncomputable def finCoveredPartition (D : BucketDecomposition d k ρ) :
    BucketPartition (Fin (Fintype.card D.Covered))
      (Fin (Fintype.card D.BlockIndex)) where
  bucket i := D.finBlockEquiv.symm
    (D.coveredPartition.bucket (D.finCoveredEquiv i))

/-- Relabeling preserves every bucket fiber. -/
noncomputable def finCoveredFiberEquiv (D : BucketDecomposition d k ρ)
    (j : Fin (Fintype.card D.BlockIndex)) :
    {i : Fin (Fintype.card D.Covered) // i ∈ D.finCoveredPartition.fiber j} ≃
      {i : D.Covered // i ∈ D.coveredPartition.fiber (D.finBlockEquiv j)} :=
  D.finCoveredEquiv.subtypeEquiv fun i ↦ by
    rw [D.finCoveredPartition.mem_fiber, D.coveredPartition.mem_fiber]
    exact D.finBlockEquiv.symm_apply_eq

@[simp] lemma card_finCoveredPartition_fiber (D : BucketDecomposition d k ρ)
    (j : Fin (Fintype.card D.BlockIndex)) :
    (D.finCoveredPartition.fiber j).card = k := by
  rw [← Fintype.card_coe, Fintype.card_congr (D.finCoveredFiberEquiv j),
    Fintype.card_coe, D.card_coveredPartition_fiber]

lemma isKSSSPartition_finCovered (D : BucketDecomposition d k ρ) (δ : ℝ)
    (hlower : BooleanSlices.scale (Fintype.card D.Covered) δ / 2 ≤
      (D.blocks.card : ℝ))
    (hupper : (D.blocks.card : ℝ) ≤
      2 * BooleanSlices.scale (Fintype.card D.Covered) δ) :
    BooleanSlices.IsKSSSPartition δ D.finCoveredPartition := by
  refine ⟨fun j h ↦ ?_, ?_, ?_⟩
  · rw [D.card_finCoveredPartition_fiber, D.card_finCoveredPartition_fiber]
  · simpa only [D.card_blockIndex, Nat.cast_ofNat] using hlower
  · simpa only [D.card_blockIndex, Nat.cast_ofNat] using hupper

lemma finCovered_close_to_blockCenter (D : BucketDecomposition d k ρ)
    (i : Fin (Fintype.card D.Covered)) :
    |d (D.finCoveredEquiv i).1 -
        D.blockCenter (D.finBlockEquiv (D.finCoveredPartition.bucket i))| ≤ ρ := by
  simpa only [finCoveredPartition, Equiv.apply_symm_apply] using
    D.covered_close_to_blockCenter (D.finCoveredEquiv i)

/-- Quantitative cardinal conditions ensuring that the relabeled RLCD blocks
form a KSSS partition at exponent `δ`. -/
lemma isKSSSPartition_finCovered_of_remainder_and_block_bounds
    {n : ℕ} {d : Fin n → ℝ} {k : ℕ} {ρ δ : ℝ}
    (D : BucketDecomposition d k ρ)
    (hn : 0 < n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hrem : (D.remainder.card : ℝ) ≤ (n : ℝ) / 4)
    (hkLower : BooleanSlices.scale n (1 - δ) ≤ (k : ℝ))
    (hkUpper : (k : ℝ) ≤ (3 / 2 : ℝ) *
      BooleanSlices.scale n (1 - δ)) :
    BooleanSlices.IsKSSSPartition δ D.finCoveredPartition := by
  let q := Fintype.card D.Covered
  let m := D.blocks.card
  let N : ℝ := n
  let Q : ℝ := q
  let M : ℝ := m
  let S : ℝ := BooleanSlices.scale n (1 - δ)
  let T : ℝ := BooleanSlices.scale n δ
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hS : 0 < S := by
    dsimp only [S]
    exact BooleanSlices.scale_pos hn _
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact BooleanSlices.scale_nonneg n δ
  have hQ0 : 0 ≤ Q := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hcardNat : D.remainder.card + q = n := by
    simpa only [q, Fintype.card_fin] using D.remainder_card_add_card_covered
  have hcard : (D.remainder.card : ℝ) + Q = N := by
    dsimp only [Q, N]
    exact_mod_cast hcardNat
  have hprodNat : q = m * k := by
    simpa only [q, m] using D.card_covered
  have hprod : Q = M * (k : ℝ) := by
    dsimp only [Q, M]
    exact_mod_cast hprodNat
  have hQN : Q ≤ N := by
    have hrem0 : (0 : ℝ) ≤ D.remainder.card := by positivity
    linarith
  have hQlower : 3 * N / 4 ≤ Q := by
    linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity : 0 < 3 * N / 4) hQlower
  have hNT : S * T = N := by
    dsimp only [S, T, N, BooleanSlices.scale]
    calc
      (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ =
          (n : ℝ) ^ ((1 - δ) + δ) :=
        (Real.rpow_add (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
          (1 - δ) δ).symm
      _ = (n : ℝ) ^ (1 : ℝ) := by congr 1 <;> ring
      _ = (n : ℝ) := Real.rpow_one _
  have hLowerM : T / 2 ≤ M := by
    apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < (k : ℝ) by
      exact hS.trans_le hkLower)).mp
    calc
      T / 2 * (k : ℝ) ≤ T / 2 * ((3 / 2 : ℝ) * S) := by
        gcongr
      _ = 3 * N / 4 := by rw [← hNT]; ring
      _ ≤ Q := hQlower
      _ = M * (k : ℝ) := hprod
  have hUpperM : M ≤ T := by
    apply (mul_le_mul_iff_of_pos_right hS).mp
    calc
      M * S ≤ M * (k : ℝ) := by gcongr
      _ = Q := hprod.symm
      _ ≤ N := hQN
      _ = T * S := by rw [← hNT]; ring
  have hNtwoQ : N ≤ 2 * Q := by linarith
  have hpowNQ : T ≤ (2 * Q) ^ δ := by
    dsimp only [T, BooleanSlices.scale, N, Q] at *
    exact Real.rpow_le_rpow (by positivity) hNtwoQ hδ0
  have htwoPow : (2 : ℝ) ^ δ ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ1
  have hQPow0 : 0 ≤ Q ^ δ := Real.rpow_nonneg hQ0 δ
  have hQpowT : Q ^ δ ≤ T := by
    dsimp only [T, Q, BooleanSlices.scale]
    exact Real.rpow_le_rpow hQ0 hQN hδ0
  have hUpperQ : T ≤ 2 * Q ^ δ := by
    calc
      T ≤ (2 * Q) ^ δ := hpowNQ
      _ = (2 : ℝ) ^ δ * Q ^ δ := by rw [Real.mul_rpow (by norm_num) hQ0]
      _ ≤ 2 * Q ^ δ := mul_le_mul_of_nonneg_right htwoPow hQPow0
  apply D.isKSSSPartition_finCovered δ
  · dsimp only [q, m, M] at hLowerM ⊢
    exact (div_le_div_of_nonneg_right hQpowT (by norm_num)).trans hLowerM
  · dsimp only [q, m, Q, M, T] at hUpperM hUpperQ ⊢
    exact hUpperM.trans hUpperQ

/-- The numerical output of Lemma 4.12 gives the KSSS partition exponent
`2γ` once the two elementary power-growth inequalities hold. -/
lemma isKSSSPartition_finCovered_smallRLCD
    {n : ℕ} {d : Fin n → ℝ} {ρ γ : ℝ}
    (D : BucketDecomposition d (smallRLCDBucketCard n γ) ρ)
    (hn : 0 < n) (hγ0 : 0 ≤ γ) (hγhalf : γ ≤ 1 / 2)
    (hrem : (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ))
    (hremGrowth : 4 ≤ BooleanSlices.scale n γ)
    (hblockGrowth : 2 ≤ BooleanSlices.scale n (1 - 2 * γ)) :
    BooleanSlices.IsKSSSPartition (2 * γ) D.finCoveredPartition := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hremScale : BooleanSlices.scale n (1 - γ) ≤ (n : ℝ) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    calc
      BooleanSlices.scale n (1 - γ) * 4 ≤
          BooleanSlices.scale n (1 - γ) * BooleanSlices.scale n γ :=
        mul_le_mul_of_nonneg_left hremGrowth
          (BooleanSlices.scale_nonneg n (1 - γ))
      _ = BooleanSlices.scale n ((1 - γ) + γ) :=
        BooleanSlices.scale_mul hn (1 - γ) γ
      _ = BooleanSlices.scale n 1 := by congr 1 <;> ring
      _ = (n : ℝ) := by
        unfold BooleanSlices.scale
        exact Real.rpow_one _
  have hkLower : BooleanSlices.scale n (1 - 2 * γ) ≤
      (smallRLCDBucketCard n γ : ℝ) := by
    unfold smallRLCDBucketCard BooleanSlices.scale
    exact Nat.le_ceil _
  have hkUpper : (smallRLCDBucketCard n γ : ℝ) ≤
      (3 / 2 : ℝ) * BooleanSlices.scale n (1 - 2 * γ) := by
    have hceil : (smallRLCDBucketCard n γ : ℝ) <
        BooleanSlices.scale n (1 - 2 * γ) + 1 := by
      unfold smallRLCDBucketCard BooleanSlices.scale
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg hnR.le _)
    linarith
  apply D.isKSSSPartition_finCovered_of_remainder_and_block_bounds
    hn (mul_nonneg (by norm_num) hγ0) (by linarith) (hrem.trans hremScale)
  · exact hkLower
  · exact hkUpper

/-- Eventual partition interface furnished by every small-RLCD decomposition. -/
theorem eventually_isKSSSPartition_finCovered_smallRLCD
    (γ : ℝ) (hγ : 0 < γ) (hγhalf : γ < 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (d : Fin n → ℝ) (ρ : ℝ)
        (D : BucketDecomposition d (smallRLCDBucketCard n γ) ρ),
        (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) →
          BooleanSlices.IsKSSSPartition (2 * γ) D.finCoveredPartition := by
  have hremGrowth := ((tendsto_rpow_atTop hγ).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 4)
  have hblockExp : 0 < 1 - 2 * γ := by linarith
  have hblockGrowth := ((tendsto_rpow_atTop hblockExp).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 2)
  filter_upwards [hremGrowth, hblockGrowth, Filter.eventually_ge_atTop 1] with
      n hremGrow hblockGrow hn
  intro d ρ D hrem
  apply D.isKSSSPartition_finCovered_smallRLCD (by omega) hγ.le hγhalf.le hrem
  · change 4 ≤ (n : ℝ) ^ γ
    simpa only [Function.comp_apply] using hremGrow
  · change 2 ≤ (n : ℝ) ^ (1 - 2 * γ)
    simpa only [Function.comp_apply] using hblockGrow

/-- Lemma 4.12 together with the exact standard-finite KSSS partition carried
by its covered coordinates. -/
theorem KSSS_lemma_4_12_with_partition
    (H γ L : ℝ) (hH : 0 < H) (hγ : 0 < γ)
    (hγ4 : γ < 1 / 4) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (d : Fin n → ℝ),
        (∀ i, 0 ≤ d i) →
        ‖d‖ ≤ H * n →
        (∀ S : Finset (Fin n), S.card = regularizationCard n γ →
          (n : ℝ) ^ ((3 : ℝ) / 2 - 2 * γ) ≤ euclidNorm (restrict d S)) →
        regularizedLCD L γ d ≤ Real.sqrt n →
        ∃ D : BucketDecomposition d (smallRLCDBucketCard n γ)
            ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
          (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) ∧
            BooleanSlices.IsKSSSPartition (2 * γ) D.finCoveredPartition := by
  have hdecomp := KSSS_lemma_4_12 H γ L hH hγ hγ4 hL
  have hpart := eventually_isKSSSPartition_finCovered_smallRLCD γ hγ (by linarith)
  filter_upwards [hdecomp, hpart] with n hdecompN hpartN
  intro d hd hsup hnorm hsmall
  obtain ⟨D, hrem⟩ := hdecompN d hd hsup hnorm hsmall
  have hrem' : (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) := by
    change (D.remainder.card : ℝ) ≤ (n : ℝ) ^ (1 - γ)
    exact hrem
  exact ⟨D, hrem', hpartN d _ D hrem'⟩

end BucketDecomposition
end RLCD
end Erdos88
