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

import ErdosProblems.Erdos88.StructuredBucket
import ErdosProblems.Erdos88.LinearLCDCancellation

/-!
# Small-RLCD partitions for graph effective coefficients

This file supplies the graph-specific hypotheses of KSSS Lemma 4.12 from
the Ramsey density estimate in Lemma 7.3.  Thus, in the small-RLCD branch,
the equal RLCD blocks carry the exact finite partition used in Section 11.
-/

open scoped BigOperators

namespace Erdos88

namespace RLCD.BucketDecomposition

open BooleanSlices

/-- The standard finite partition carried by a nonempty equal-block
decomposition has equal nonempty fibers in the robust-rank sense. -/
lemma hasEqualBuckets_finCovered
    {n k : ℕ} {d : Fin n → ℝ} {ρ : ℝ}
    (D : BucketDecomposition d k ρ) (hk : 0 < k) :
    RobustRank.HasEqualBuckets D.finCoveredPartition.bucket := by
  refine ⟨k, hk, ?_⟩
  intro j
  simpa only [RobustRank.bucketFiber, BucketPartition.fiber] using
    D.card_finCoveredPartition_fiber j

/-- The graph induced on the covered coordinates, relabelled by the same
canonical equivalence used by `finCoveredPartition`. -/
noncomputable def finCoveredGraph
    {n k : ℕ} {d : Fin n → ℝ} {ρ : ℝ}
    (D : BucketDecomposition d k ρ) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin (Fintype.card D.Covered)) :=
  (G.induce (D.blocks.biUnion id : Set (Fin n))).comap D.finCoveredEquiv

@[simp] lemma finCoveredGraph_adj
    {n k : ℕ} {d : Fin n → ℝ} {ρ : ℝ}
    (D : BucketDecomposition d k ρ) (G : SimpleGraph (Fin n))
    (i j : Fin (Fintype.card D.Covered)) :
    (D.finCoveredGraph G).Adj i j ↔
      G.Adj (D.finCoveredEquiv i).1 (D.finCoveredEquiv j).1 := by
  rfl

/-- Ramsey-freeness passes to the covered induced graph under the exact
logarithmic threshold comparison. -/
lemma ramseyFree_finCoveredGraph
    {n k : ℕ} {d : Fin n → ℝ} {ρ C E : ℝ}
    (D : BucketDecomposition d k ρ) (G : SimpleGraph (Fin n))
    (hG : RamseyFree C G)
    (hthreshold : C * Real.logb 2 n ≤
      E * Real.logb 2 (Fintype.card D.Covered)) :
    RamseyFree E (D.finCoveredGraph G) := by
  classical
  intro T hT
  let e : Fin (Fintype.card D.Covered) ↪ Fin n :=
    ⟨fun i ↦ (D.finCoveredEquiv i).1,
      fun _ _ hij ↦ D.finCoveredEquiv.injective (Subtype.ext hij)⟩
  let S : Finset (Fin n) := T.map e
  have hcardS : S.card = T.card := by simp [S]
  have hhom : G.IsClique (S : Set (Fin n)) ∨
      G.IsIndepSet (S : Set (Fin n)) := by
    rcases hT with hclique | hindep
    · left
      intro x hx y hy hxy
      dsimp only [S] at hx hy
      simp only [Finset.coe_map, Set.mem_image] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      have huv : u ≠ v := fun h ↦ hxy (by simpa [h])
      exact (D.finCoveredGraph_adj G u v).mp
        (hclique hu hv huv)
    · right
      intro x hx y hy hxy hadj
      dsimp only [S] at hx hy
      simp only [Finset.coe_map, Set.mem_image] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      have huv : u ≠ v := fun h ↦ hxy (by simpa [h])
      exact hindep hu hv huv ((D.finCoveredGraph_adj G u v).mpr hadj)
  have hsmall := hG S hhom
  rw [hcardS] at hsmall
  exact hsmall.trans_le hthreshold

/-- A covered set of size at least `sqrt n` loses only the standard factor
two in the Ramsey parameter. -/
lemma ramseyFree_finCoveredGraph_of_sqrt
    {n k : ℕ} {d : Fin n → ℝ} {ρ C : ℝ}
    (D : BucketDecomposition d k ρ) (G : SimpleGraph (Fin n))
    (hC : 0 < C) (hn : 1 ≤ n) (hG : RamseyFree C G)
    (hcovered : Real.sqrt n ≤ (Fintype.card D.Covered : ℝ)) :
    RamseyFree (2 * C) (D.finCoveredGraph G) := by
  apply D.ramseyFree_finCoveredGraph G hG
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hlogMono : Real.logb 2 (Real.sqrt n) ≤
      Real.logb 2 (Fintype.card D.Covered : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hsqrtPos hcovered
  have hlogSqrt : Real.logb 2 (Real.sqrt n) =
      (1 / 2 : ℝ) * Real.logb 2 n := by
    rw [Real.logb, Real.logb, Real.log_sqrt hnpos.le]
    ring
  rw [hlogSqrt] at hlogMono
  nlinarith

end RLCD.BucketDecomposition

namespace LinearLCDCancellation

open GraphQuadratic

/-- The effective linear coefficient vector is bounded coordinatewise by
`(H + 1/2)n` when the perturbation coefficients lie in `[0,Hn]`. -/
theorem norm_graphEffectiveLinear_le
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hcNonneg : ∀ i, 0 ≤ c i) (hcUpper : ∀ i, c i ≤ H * n) :
    ‖graphEffectiveLinear G c‖ ≤ (H + 1 / 2) * n := by
  classical
  letI (i : Fin n) : Fintype ↑(G.neighborSet i) :=
    Subtype.fintype (Membership.mem (G.neighborSet i))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have hdegNat : G.degree i ≤ n :=
    Nat.le_of_lt (by simpa using G.degree_lt_card_verts i)
  have hdeg : (G.degree i : ℝ) ≤ n := by exact_mod_cast hdegNat
  have hd : 0 ≤ graphEffectiveLinear G c i := by
    unfold graphEffectiveLinear
    exact add_nonneg (hcNonneg i) (div_nonneg (by positivity) (by norm_num))
  rw [Real.norm_eq_abs, abs_of_nonneg hd]
  unfold graphEffectiveLinear
  have hci := hcUpper i
  nlinarith

/-- In a Ramsey-free graph, the small-RLCD output of Lemma 4.12 carries
the standard finite KSSS partition on all coordinates outside its small
remainder.  The regularized-coordinate norm hypothesis is supplied by
Lemma 7.3. -/
theorem eventually_graphEffective_smallRLCD_bucketPartition
    (C H γ L : ℝ) (hC : 0 < C) (hH : 0 < H)
    (hγ : 0 < γ) (hγ4 : γ < 1 / 4) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
        RamseyFree C G →
        (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
        RLCD.regularizedLCD L γ (graphEffectiveLinear G c) ≤ Real.sqrt n →
        ∃ D : RLCD.BucketDecomposition (graphEffectiveLinear G c)
            (RLCD.smallRLCDBucketCard n γ)
            ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
          (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) ∧
            BooleanSlices.IsKSSSPartition (2 * γ) D.finCoveredPartition := by
  obtain ⟨a, ha, N, hmass⟩ := ksssLemma73 C hC
  let H' : ℝ := H + 1 / 2
  have hH' : 0 < H' := by dsimp only [H']; linarith
  have hbucket := RLCD.BucketDecomposition.KSSS_lemma_4_12_with_partition
    H' γ L hH' hγ hγ4 hL
  have hNcard := BooleanSlices.eventually_const_le_scale (N : ℝ)
    (1 - γ) (by linarith)
  have haGrow := BooleanSlices.eventually_const_le_scale (1 / a)
    (γ / 2) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop N, hbucket, hNcard, haGrow] with
      n hn hNn hbucketN hNcardN haGrowN
  intro G c hG hc hsmall
  have hnpos : 0 < n := by omega
  have hcNonneg : ∀ i, 0 ≤ c i := fun i ↦ (hc i).1
  have hcUpper : ∀ i, c i ≤ H * n := fun i ↦ (hc i).2
  have hdNonneg : ∀ i, 0 ≤ graphEffectiveLinear G c i := by
    intro i
    unfold graphEffectiveLinear
    exact add_nonneg (hcNonneg i) (div_nonneg (by positivity) (by norm_num))
  have hsup : ‖graphEffectiveLinear G c‖ ≤ H' * n := by
    exact norm_graphEffectiveLinear_le G c H hH.le hcNonneg hcUpper
  let k : ℕ := RLCD.regularizationCard n γ
  have hkLower : BooleanSlices.scale n (1 - γ) ≤ (k : ℝ) := by
    exact regularizationCard_cast_lower γ
  have hNk : N ≤ k := by
    have hNkR : (N : ℝ) ≤ (k : ℝ) := hNcardN.trans hkLower
    exact_mod_cast hNkR
  have hsqrtK : Real.sqrt n ≤ (k : ℝ) := by
    have hscale : BooleanSlices.scale n (1 / 2) ≤
        BooleanSlices.scale n (1 - γ) :=
      BooleanSlices.scale_mono_exponent hn (by linarith)
    rw [Real.sqrt_eq_rpow]
    exact hscale.trans hkLower
  have hmassI : ∀ S : Finset (Fin n), S.card = k →
      a ^ 2 * (S.card : ℝ) ^ 3 ≤
        ∑ i : S, graphEffectiveLinear G c i.1 ^ 2 := by
    intro S hS
    exact hmass hn hNn G hG c hcNonneg S (by simpa [hS] using hNk)
      (by simpa [hS] using hsqrtK)
  have hnormLower : ∀ S : Finset (Fin n), S.card = k →
      a * (k : ℝ) ^ ((3 : ℝ) / 2) ≤
        RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) S) := by
    intro S hS
    rw [← hS]
    exact graphEffectiveLinear_restrict_norm_lower_of_sq
      G c S ha.le (hmassI S hS)
  have hscaleAbsorb : BooleanSlices.scale n ((3 : ℝ) / 2 - 2 * γ) ≤
      a * BooleanSlices.scale n (3 * (1 - γ) / 2) := by
    have haInv : 1 ≤ a * BooleanSlices.scale n (γ / 2) := by
      calc
        1 = a * (1 / a) := by field_simp [ne_of_gt ha]
        _ ≤ a * BooleanSlices.scale n (γ / 2) :=
          mul_le_mul_of_nonneg_left haGrowN ha.le
    calc
      BooleanSlices.scale n ((3 : ℝ) / 2 - 2 * γ) =
          1 * BooleanSlices.scale n ((3 : ℝ) / 2 - 2 * γ) := by ring
      _ ≤ (a * BooleanSlices.scale n (γ / 2)) *
          BooleanSlices.scale n ((3 : ℝ) / 2 - 2 * γ) :=
        mul_le_mul_of_nonneg_right haInv
          (BooleanSlices.scale_nonneg n _)
      _ = a * BooleanSlices.scale n (3 * (1 - γ) / 2) := by
        rw [mul_assoc, BooleanSlices.scale_mul hnpos]
        congr 1
        congr 1
        ring
  have hkPow : BooleanSlices.scale n (3 * (1 - γ) / 2) ≤
      (k : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← scale_rpow_three_halves hnpos]
    exact Real.rpow_le_rpow (BooleanSlices.scale_nonneg n _) hkLower (by norm_num)
  have hnorm : ∀ S : Finset (Fin n), S.card = RLCD.regularizationCard n γ →
      (n : ℝ) ^ ((3 : ℝ) / 2 - 2 * γ) ≤
        RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) S) := by
    intro S hS
    change BooleanSlices.scale n ((3 : ℝ) / 2 - 2 * γ) ≤ _
    exact hscaleAbsorb.trans
      ((mul_le_mul_of_nonneg_left hkPow ha.le).trans (hnormLower S hS))
  exact hbucketN (graphEffectiveLinear G c) hdNonneg hsup hnorm hsmall

/-- The small-RLCD branch packaged with every graph-theoretic input needed
by the product-slice Claim 12.1 machinery: an exact KSSS partition, equal
nonempty buckets, and a `2C`-Ramsey induced graph on the covered vertices. -/
theorem eventually_graphEffective_smallRLCD_structuredData
    (C H γ L : ℝ) (hC : 0 < C) (hH : 0 < H)
    (hγ : 0 < γ) (hγ4 : γ < 1 / 4) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
        RamseyFree C G →
        (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
        RLCD.regularizedLCD L γ (graphEffectiveLinear G c) ≤ Real.sqrt n →
        ∃ D : RLCD.BucketDecomposition (graphEffectiveLinear G c)
            (RLCD.smallRLCDBucketCard n γ)
            ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
          (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - γ) ∧
            BooleanSlices.IsKSSSPartition (2 * γ) D.finCoveredPartition ∧
            RobustRank.HasEqualBuckets D.finCoveredPartition.bucket ∧
            RamseyFree (2 * C) (D.finCoveredGraph G) := by
  have hbase := eventually_graphEffective_smallRLCD_bucketPartition
    C H γ L hC hH hγ hγ4 hL
  have hgrowth := BooleanSlices.eventually_const_le_scale 2 γ hγ
  filter_upwards [hbase, hgrowth, Filter.eventually_ge_atTop 4] with
      n hbaseN hgrowthN hn
  intro G c hG hc hsmall
  obtain ⟨D, hrem, hpart⟩ := hbaseN G c hG hc hsmall
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
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtHalf : Real.sqrt n ≤ (n : ℝ) / 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  have hcovered : Real.sqrt n ≤ (Fintype.card D.Covered : ℝ) := by
    linarith
  have hk : 0 < RLCD.smallRLCDBucketCard n γ := by
    rw [RLCD.smallRLCDBucketCard, Nat.ceil_pos]
    exact BooleanSlices.scale_pos hnpos _
  have hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket :=
    D.hasEqualBuckets_finCovered hk
  have hRamsey : RamseyFree (2 * C) (D.finCoveredGraph G) :=
    D.ramseyFree_finCoveredGraph_of_sqrt G hC (by omega) hG hcovered
  exact ⟨D, hrem, hpart, hbucket, hRamsey⟩

end LinearLCDCancellation
end Erdos88
