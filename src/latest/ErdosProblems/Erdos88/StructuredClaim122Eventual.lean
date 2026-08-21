import ErdosProblems.Erdos88.StructuredClaim122

open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

/-- Eventual source-shaped Claim 12.2 for an equal-bucket Ramsey graph.
The positive edge-density and robust-rank constants, together with all
auxiliary numerical parameters, are chosen uniformly in the graph. -/
theorem exists_eventual_bucketShiftMoment_graph_claim122
    (C H delta : ℝ) (hC : 0 < C) (hH : 0 ≤ H)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ {m : ℕ} (P : BucketPartition (Fin n) (Fin m))
        (hbucket : RobustRank.HasEqualBuckets P.bucket)
        (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
        0 < m →
        Real.rpow (n : ℝ) delta / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta →
        RamseyFree C G →
        (∀ i, 0 ≤ c i ∧ c i ≤ H * (n : ℝ)) →
        ∀ a b : ℝ,
        ‖bucketCenteredAdjacency P.bucket hbucket.choose G‖ ≤ b - a →
        Fourier.finExpectation (Fin n → Bool) (fun xi ↦
          let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
          let E := (1 / 2 : ℝ) *
            (GraphQuadratic.graphEffectiveLinear G c ⬝ᵥ Structured.delta
              (bucketProjectionMatrix P.bucket hbucket.choose) x)
          let W :=
            ((1 / 8 : ℝ) *
              (Structured.delta
                  (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
                (RobustRank.graphAdjacencyMatrix G *ᵥ
                  Structured.delta
                    (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
            ∑ i, ((1 / 4 : ℝ) *
              (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
          if a ≤ E ∧ E ≤ b then W else 0) ≤
          D * Real.sqrt n * (b - a) := by
  obtain ⟨A, hA, NA, hDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower C hC
  obtain ⟨rho, hrho, Nrho, hRobust⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 0 hC hdelta hdelta1
  let q : ℝ := min 1 (A ^ 2 / (8 * (H + 1) ^ 2))
  let d : ℝ := Real.sqrt rho
  let Cq : ℝ :=
    (45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
      (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
      3 * (q / 32) ^ (-(3 : ℝ) / 2)
  let D : ℝ := (1 / (2 * (H + 1)) + 2 / d) * Cq
  have hH1 : 0 < H + 1 := by linarith
  have hq : 0 < q := by
    dsimp only [q]
    exact lt_min (by norm_num) (div_pos (sq_pos_of_pos hA) (by positivity))
  have hq1 : q ≤ 1 := by exact min_le_left _ _
  have hqcoef : 4 * q * (H + 1) ^ 2 ≤ A ^ 2 := by
    have hq' : q ≤ A ^ 2 / (8 * (H + 1) ^ 2) := min_le_right _ _
    have hden : 0 < 8 * (H + 1) ^ 2 := by positivity
    have hqmul := (le_div_iff₀ hden).mp hq'
    nlinarith [sq_nonneg (H + 1)]
  have hd : 0 < d := by
    dsimp only [d]
    exact Real.sqrt_pos.2 hrho
  have hCq : 0 < Cq := by
    dsimp only [Cq]
    positivity
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (add_pos (by positivity) (by positivity)) hCq
  have hgrowthEventually : ∀ᶠ n : ℕ in Filter.atTop,
      32 * (H + 1) ^ 2 ≤ A ^ 2 * (n : ℝ) := by
    have hcast : ∀ᶠ n : ℕ in Filter.atTop,
        32 * (H + 1) ^ 2 / A ^ 2 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually
        (Filter.eventually_ge_atTop (32 * (H + 1) ^ 2 / A ^ 2))
    filter_upwards [hcast] with n hn
    exact (div_le_iff₀ (sq_pos_of_pos hA)).mp hn |>.trans_eq (by ring)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hgrowthEventually,
      Filter.eventually_ge_atTop (max (max NA Nrho) 1)] with n hgrowth hn
  intro m P hbucket G c hm hmLower hmUpper hRamsey hc a b hlength
  have hnA : NA ≤ n := (le_max_left NA Nrho).trans
    ((le_max_left (max NA Nrho) 1).trans hn)
  have hnRho : Nrho ≤ n := (le_max_right NA Nrho).trans
    ((le_max_left (max NA Nrho) 1).trans hn)
  have hnOne : 1 ≤ n := (le_max_right (max NA Nrho) 1).trans hn
  have hnpos : 0 < n := by omega
  have hEdge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) :=
    hDensity n hnA G hRamsey
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  have hRobustF : RobustRankAt 0 (rho * (n : ℝ) ^ 2) F :=
    hRobust n hnRho m P.bucket G hm hmLower hmUpper hbucket hRamsey
  have hFrob : rho * (n : ℝ) ^ 2 ≤ ‖F‖ ^ 2 := by
    have hz := hRobustF (0 : Matrix (Fin n) (Fin n) ℝ) (by simp)
    simpa only [sub_zero] using hz
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdnorm : d * (n : ℝ) ≤ ‖F‖ := by
    have hnorm0 : 0 ≤ ‖F‖ := norm_nonneg _
    have hleft0 : 0 ≤ d * (n : ℝ) := (mul_pos hd hnR).le
    apply (sq_le_sq₀ hleft0 hnorm0).mp
    dsimp only [d]
    rw [mul_pow, Real.sq_sqrt hrho.le]
    exact hFrob
  have hbase := bucketShiftMoment_graph_claim122 hnpos P hbucket G c
    H A q d a b hH hA.le hd (fun i ↦ (hc i).1) (fun i ↦ (hc i).2)
    hEdge hq hq1 hqcoef hgrowth (hdnorm.trans hlength)
  simpa only [D, Cq, F] using hbase

end Erdos88.GaussianQuadratic
