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

import ErdosProblems.Erdos88.StructuredGraphBucket
import ErdosProblems.Erdos88.ProductSliceFourierAssembly

/-!
# The conditional structured upper bound

This file feeds the exact partition furnished by the small-RLCD graph
decomposition into the already-proved product-slice upper half of Claim 12.1.
-/

open scoped BigOperators

namespace Erdos88.GaussianQuadratic

open Erdos88.BooleanSlices

/-- Positive-bucket-count form of the eventual Claim 12.1 upper theorem. -/
theorem exists_eventual_productSlice_claim121_upper_pos
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 < D ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {m : ℕ}, 0 < m →
          ∀ (P : BucketPartition (Fin n) (Fin m))
            (ell : Fin m → ℕ) (G : SimpleGraph (Fin n))
            (f : Fin n → ℝ)
            (hbucket : Erdos88.RobustRank.HasEqualBuckets P.bucket),
            IsKSSSPartition delta P → IsNearBalanced delta P ell →
            HasKSSSBalancedCoefficients delta P f
              (bucketCenteredAdjacency P.bucket hbucket.choose G) →
            RamseyFree C G →
            ∃ hleft : Nonempty (ProductSlicePoint P ell),
              letI := hleft
              let F := bucketCenteredAdjacency P.bucket hbucket.choose G
              ∀ x : ℝ,
                Erdos88.Esseen.smallBall
                    (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                      (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                  D * scale n (-1) := by
  obtain ⟨B, hB, D, hD, hbase⟩ :=
    exists_eventual_productSlice_claim121_upper C delta hC hdelta hdeltaSmall
  refine ⟨B, hB, D, hD, ?_⟩
  filter_upwards [hbase] with n hbaseN
  intro m hm P ell G f hbucket hpart hbalanced hcoeff hRamsey
  cases m with
  | zero => omega
  | succ K =>
      exact hbaseN P ell G f hbucket hpart hbalanced hcoeff hRamsey

/-- The low-RLCD decomposition specialized to the already-proved upper half
of Claim 12.1 on every near-balanced covered product slice. -/
theorem exists_eventual_graphEffective_smallRLCD_claim121_upper
    (C H γ L : ℝ) (hC : 0 < C) (hH : 0 < H)
    (hγ : 0 < γ) (hγSmall : γ < 3 / 800) (hL : 1 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ D0 : ℝ, 0 < D0 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          RLCD.regularizedLCD L γ
              (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n →
          ∃ D : RLCD.BucketDecomposition
              (GraphQuadratic.graphEffectiveLinear G c)
              (RLCD.smallRLCDBucketCard n γ)
              ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
            (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) ∧
              ∃ hbucket : Erdos88.RobustRank.HasEqualBuckets
                  D.finCoveredPartition.bucket,
                ∀ (ell : Fin (Fintype.card D.BlockIndex) → ℕ)
                  (f : Fin (Fintype.card D.Covered) → ℝ),
                  IsNearBalanced (2 * γ) D.finCoveredPartition ell →
                  HasKSSSBalancedCoefficients (2 * γ)
                    D.finCoveredPartition f
                    (bucketCenteredAdjacency
                      D.finCoveredPartition.bucket hbucket.choose
                      (D.finCoveredGraph G)) →
                  ∃ hleft : Nonempty
                      (ProductSlicePoint D.finCoveredPartition ell),
                    letI := hleft
                    let F := bucketCenteredAdjacency
                      D.finCoveredPartition.bucket hbucket.choose
                      (D.finCoveredGraph G)
                    ∀ x : ℝ,
                      Erdos88.Esseen.smallBall
                          (Erdos88.Esseen.finiteUniformLaw
                            (ProductSlicePoint D.finCoveredPartition ell)
                            (productSliceQuadratic D.finCoveredPartition ell
                              (-trace F) f F)) B x ≤
                        D0 * scale (Fintype.card D.Covered) (-1) := by
  have hγ4 : γ < 1 / 4 := hγSmall.trans (by norm_num)
  obtain ⟨B, hB, D0, hD0, hupperEvent⟩ :=
    exists_eventual_productSlice_claim121_upper_pos
      (2 * C) (2 * γ) (mul_pos (by norm_num) hC)
      (mul_pos (by norm_num) hγ) (by linarith)
  obtain ⟨Nupper, hupper⟩ := Filter.eventually_atTop.1 hupperEvent
  have hstruct :=
    Erdos88.LinearLCDCancellation.eventually_graphEffective_smallRLCD_structuredData
      C H γ L hC hH hγ hγ4 hL
  have hgrowth := BooleanSlices.eventually_const_le_scale 2 γ hγ
  refine ⟨B, hB, D0, hD0, ?_⟩
  filter_upwards [hstruct, hgrowth,
    Filter.eventually_ge_atTop (max 4 (2 * Nupper))] with
      n hstructN hgrowthN hn
  intro G c hG hc hsmall
  obtain ⟨D, hrem, hpart, hbucket, hRamsey⟩ :=
    hstructN G c hG hc hsmall
  have hnpos : 0 < n := by omega
  have hscaleHalf : BooleanSlices.scale n (1 - γ) ≤ (n : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      BooleanSlices.scale n (1 - γ) * 2 ≤
          BooleanSlices.scale n (1 - γ) * BooleanSlices.scale n γ :=
        mul_le_mul_of_nonneg_left hgrowthN
          (BooleanSlices.scale_nonneg n _)
      _ = BooleanSlices.scale n ((1 - γ) + γ) :=
        BooleanSlices.scale_mul hnpos _ _
      _ = (n : ℝ) := by
        rw [show (1 - γ) + γ = (1 : ℝ) by ring]
        exact Real.rpow_one _
  have hremHalf : (D.remainder.card : ℝ) ≤ (n : ℝ) / 2 :=
    hrem.trans hscaleHalf
  have hcardNat : D.remainder.card + Fintype.card D.Covered = n := by
    simpa only [Fintype.card_fin] using D.remainder_card_add_card_covered
  have hcardEq : (D.remainder.card : ℝ) +
      (Fintype.card D.Covered : ℝ) = n := by
    exact_mod_cast hcardNat
  have hNupperR : (Nupper : ℝ) ≤ (n : ℝ) / 2 := by
    have hnN : 2 * Nupper ≤ n := (le_max_right 4 (2 * Nupper)).trans hn
    have hnNR : (2 : ℝ) * (Nupper : ℝ) ≤ n := by exact_mod_cast hnN
    linarith
  have hqN : Nupper ≤ Fintype.card D.Covered := by
    have : (Nupper : ℝ) ≤ (Fintype.card D.Covered : ℝ) := by linarith
    exact_mod_cast this
  have hqpos : 0 < Fintype.card D.Covered := by
    have hqHalf : (n : ℝ) / 2 ≤ (Fintype.card D.Covered : ℝ) := by linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    exact_mod_cast (lt_of_lt_of_le (half_pos hnR) hqHalf)
  have hmpos : 0 < Fintype.card D.BlockIndex := by
    rw [D.card_covered] at hqpos
    have hblocks : 0 < D.blocks.card := Nat.pos_of_mul_pos_right hqpos
    simpa only [D.card_blockIndex] using hblocks
  refine ⟨D, hrem, hbucket, ?_⟩
  intro ell f hbalanced hcoeff
  exact hupper (Fintype.card D.Covered) hqN hmpos
    D.finCoveredPartition ell (D.finCoveredGraph G) f hbucket
    hpart hbalanced hcoeff hRamsey

end Erdos88.GaussianQuadratic
