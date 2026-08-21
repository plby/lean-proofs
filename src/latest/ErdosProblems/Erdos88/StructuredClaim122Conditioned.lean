import ErdosProblems.Erdos88.StructuredClaim122Eventual

open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

/-- A remainder conditioning preserves nonnegativity of the perturbation
coefficients.  If the remainder has size at most half the ambient graph,
the conditioned coefficients are bounded by `(2H+1)` times the number of
covered vertices. -/
lemma conditionedCoveredCoefficient_bounds
    {n k : ℕ} {d0 : Fin n → ℝ} {rho H : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n)) (hH : 0 ≤ H)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hO : O ⊆ D.remainder)
    (hremHalf : (D.remainder.card : ℝ) ≤ (n : ℝ) / 2) :
    ∀ i, 0 ≤ D.conditionedCoveredCoefficient G c O i ∧
      D.conditionedCoveredCoefficient G c O i ≤
        (2 * H + 1) * (Fintype.card D.Covered : ℝ) := by
  intro i
  let v : Fin n := (D.finCoveredEquiv i).1
  have hdegNat : AKSGraph.degreeInto G v O ≤ D.remainder.card :=
    (AKSGraph.degreeInto_le_card G v O).trans (Finset.card_le_card hO)
  have hdeg : (AKSGraph.degreeInto G v O : ℝ) ≤
      (D.remainder.card : ℝ) := by exact_mod_cast hdegNat
  have hcardNat : D.remainder.card + Fintype.card D.Covered = n := by
    simpa only [Fintype.card_fin] using D.remainder_card_add_card_covered
  have hcard : (D.remainder.card : ℝ) +
      (Fintype.card D.Covered : ℝ) = (n : ℝ) := by
    exact_mod_cast hcardNat
  have hnCovered : (n : ℝ) ≤ 2 * (Fintype.card D.Covered : ℝ) := by
    linarith
  have hcovered0 : (0 : ℝ) ≤ Fintype.card D.Covered := by positivity
  have hc := hcH v
  constructor
  · dsimp only [RLCD.BucketDecomposition.conditionedCoveredCoefficient, v]
    exact add_nonneg (hc0 _) (by positivity)
  · dsimp only [RLCD.BucketDecomposition.conditionedCoveredCoefficient, v]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith

/-- Claim 12.2 on the covered graph after fixing a subset of the small-RLCD
remainder.  The interval scale is the Frobenius norm of the centered covered
adjacency matrix, exactly as in the source proof. -/
def ConditionedClaim122Bound
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (B : ℝ) : Prop :=
  ∀ a b : ℝ,
    ‖bucketCenteredAdjacency D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ b - a →
    Fourier.finExpectation (Fin (Fintype.card D.Covered) → Bool) (fun xi ↦
      let x : Fin (Fintype.card D.Covered) → ℝ :=
        fun i ↦ Fourier.rademacherSign (xi i)
      let E := (1 / 2 : ℝ) *
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O) ⬝ᵥ
          Structured.delta
            (bucketProjectionMatrix D.finCoveredPartition.bucket
              hbucket.choose) x)
      let W :=
        ((1 / 8 : ℝ) *
          (Structured.delta
              (bucketProjectionMatrix D.finCoveredPartition.bucket
                hbucket.choose) x ⬝ᵥ
            (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G) *ᵥ
              Structured.delta
                (bucketProjectionMatrix D.finCoveredPartition.bucket
                  hbucket.choose) x))) ^ 2 +
        ∑ i, ((1 / 4 : ℝ) *
          (bucketShiftResidualMatrix D.finCoveredPartition hbucket
              (D.finCoveredGraph G) *ᵥ x) i) ^ 2
      if a ≤ E ∧ E ≤ b then W else 0) ≤
      B * Real.sqrt (Fintype.card D.Covered) * (b - a)

/-- Eventual Claim 12.2 for every conditioned covered graph produced by the
small-RLCD decomposition.  All constants are uniform in the graph, its
perturbation coefficients, the decomposition, and the fixed remainder set. -/
theorem exists_eventual_graphEffective_smallRLCD_claim122
    (C H gamma L : ℝ) (hC : 0 < C) (hH : 0 < H)
    (hgamma : 0 < gamma) (hgamma4 : gamma < 1 / 4) (hL : 1 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
        RamseyFree C G →
        (∀ i, 0 ≤ c i ∧ c i ≤ H * (n : ℝ)) →
        RLCD.regularizedLCD L gamma
            (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n →
        ∃ D : RLCD.BucketDecomposition
            (GraphQuadratic.graphEffectiveLinear G c)
            (RLCD.smallRLCDBucketCard n gamma)
            ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * gamma)),
          (D.remainder.card : ℝ) ≤ scale n (1 - gamma) ∧
          IsKSSSPartition (2 * gamma) D.finCoveredPartition ∧
          ∃ hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket,
            ∀ (O : Finset (Fin n)), O ⊆ D.remainder →
              ConditionedClaim122Bound D G c O hbucket B := by
  obtain ⟨B, hB, hbaseEvent⟩ :=
    exists_eventual_bucketShiftMoment_graph_claim122
      (2 * C) (2 * H + 1) (2 * gamma)
      (mul_pos (by norm_num) hC) (by positivity)
      (mul_pos (by norm_num) hgamma) (by linarith)
  obtain ⟨Nbase, hbase⟩ := Filter.eventually_atTop.1 hbaseEvent
  have hstruct :=
    Erdos88.LinearLCDCancellation.eventually_graphEffective_smallRLCD_structuredData
      C H gamma L hC hH hgamma hgamma4 hL
  have hgrowth := eventually_const_le_scale 2 gamma hgamma
  refine ⟨B, hB, ?_⟩
  filter_upwards [hstruct, hgrowth,
      Filter.eventually_ge_atTop (max 4 (2 * Nbase))] with
      n hstructN hgrowthN hn
  intro G c hRamsey hc hsmall
  obtain ⟨D, hrem, hpart, hbucket, hcoveredRamsey⟩ :=
    hstructN G c hRamsey hc hsmall
  have hnpos : 0 < n := by omega
  have hscaleHalf : scale n (1 - gamma) ≤ (n : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      scale n (1 - gamma) * 2 ≤
          scale n (1 - gamma) * scale n gamma :=
        mul_le_mul_of_nonneg_left hgrowthN (scale_nonneg n _)
      _ = scale n ((1 - gamma) + gamma) := scale_mul hnpos _ _
      _ = (n : ℝ) := by
        rw [show (1 - gamma) + gamma = (1 : ℝ) by ring]
        exact Real.rpow_one _
  have hremHalf : (D.remainder.card : ℝ) ≤ (n : ℝ) / 2 :=
    hrem.trans hscaleHalf
  have hcardNat : D.remainder.card + Fintype.card D.Covered = n := by
    simpa only [Fintype.card_fin] using D.remainder_card_add_card_covered
  have hcard : (D.remainder.card : ℝ) +
      (Fintype.card D.Covered : ℝ) = (n : ℝ) := by exact_mod_cast hcardNat
  have hqHalf : (n : ℝ) / 2 ≤ (Fintype.card D.Covered : ℝ) := by linarith
  have hqpos : 0 < Fintype.card D.Covered := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    exact_mod_cast (lt_of_lt_of_le (half_pos hnR) hqHalf)
  have hNbase : Nbase ≤ Fintype.card D.Covered := by
    have hnN : 2 * Nbase ≤ n := (le_max_right 4 (2 * Nbase)).trans hn
    have hnNR2' : (2 * Nbase : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hnNR : (Nbase : ℝ) ≤ (n : ℝ) / 2 := by linarith
    exact_mod_cast hnNR.trans hqHalf
  have hmpos : 0 < Fintype.card D.BlockIndex := by
    rw [D.card_covered] at hqpos
    have hblocks : 0 < D.blocks.card := Nat.pos_of_mul_pos_right hqpos
    simpa only [D.card_blockIndex] using hblocks
  refine ⟨D, hrem, hpart, hbucket, ?_⟩
  intro O hO
  have hcoeff := conditionedCoveredCoefficient_bounds D G c O hH.le
    (fun i ↦ (hc i).1) (fun i ↦ (hc i).2) hO hremHalf
  have hbaseD := hbase (Fintype.card D.Covered) hNbase
    D.finCoveredPartition hbucket (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O) hmpos hpart.2.1 hpart.2.2
    hcoveredRamsey hcoeff
  intro a b hlength
  exact hbaseD a b hlength

end Erdos88.GaussianQuadratic
