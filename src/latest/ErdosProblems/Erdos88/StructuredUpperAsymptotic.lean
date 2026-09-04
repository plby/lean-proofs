import ErdosProblems.Erdos88.StructuredClaims

/-!
# Asymptotic assembly of the structured upper bound

This module absorbs the explicit Fourier-error term left by the four-way
Claim 12.1 averaging argument.  The main term is already a constant multiple
of `q⁻³⁄²`; the only calculation here is that the error term has a
strictly better exponent when `gamma < 3/800`.
-/

open scoped BigOperators

namespace Erdos88.GaussianQuadratic

open BooleanSlices

/-- The Fourier-error contribution in the normalized four-way Claim 12.1
bound is eventually at most two copies of the target `q⁻³⁄²` scale. -/
lemma eventually_claim121_fourier_error_absorption
    (gamma Cmass B : ℝ) (hgammaSmall : gamma < 3 / 800)
    (hCmass : 0 ≤ Cmass) (hB : 0 ≤ B) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ sigma0 : ℝ, 0 ≤ sigma0 →
        sigma0 ≤ 2 * scale q (1 + 6 * gamma) →
        4 * (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
              (B + sigma0 * scale q (1 / 20 : ℝ))) *
              (B * scale q (-6 / 5 : ℝ)) ≤
          2 * scale q (-(3 : ℝ) / 2) := by
  let K1 : ℝ := 8 * Cmass * B ^ 2
  let K2 : ℝ := 16 * Cmass * B
  have hK1 : 0 ≤ K1 := by dsimp only [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp only [K2]; positivity
  have hgap2 : (-33 / 20 : ℝ) + 6 * gamma < -(3 : ℝ) / 2 := by
    linarith
  have hfirst := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    K1 (-27 / 10 : ℝ) (-(3 : ℝ) / 2) hK1 (by norm_num)
  have hsecond := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    K2 ((-33 / 20 : ℝ) + 6 * gamma) (-(3 : ℝ) / 2) hK2 hgap2
  filter_upwards [hfirst, hsecond, Filter.eventually_ge_atTop 1] with
      q hfirstQ hsecondQ hq
  intro sigma0 hsigma0 hsigmaUpper
  have hqpos : 0 < q := by omega
  have hfirstQ' : K1 * scale q (-27 / 10 : ℝ) ≤
      scale q (-(3 : ℝ) / 2) := by
    simpa only [scale, Real.rpow_eq_pow] using hfirstQ
  have hsecondQ' : K2 * scale q ((-33 / 20 : ℝ) + 6 * gamma) ≤
      scale q (-(3 : ℝ) / 2) := by
    simpa only [scale, Real.rpow_eq_pow] using hsecondQ
  calc
    4 * (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
          (B + sigma0 * scale q (1 / 20 : ℝ))) *
          (B * scale q (-6 / 5 : ℝ)) ≤
        4 * (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
          (B + (2 * scale q (1 + 6 * gamma)) *
            scale q (1 / 20 : ℝ))) *
          (B * scale q (-6 / 5 : ℝ)) := by
      have hsum : B + sigma0 * scale q (1 / 20 : ℝ) ≤
          B + (2 * scale q (1 + 6 * gamma)) *
            scale q (1 / 20 : ℝ) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hsigmaUpper
            (scale_nonneg q (1 / 20 : ℝ)))
      have hcoef : 0 ≤ 2 * (Cmass * scale q (-(3 : ℝ) / 2)) :=
        mul_nonneg (by norm_num) (mul_nonneg hCmass (scale_nonneg q _))
      have hlast : 0 ≤ B * scale q (-6 / 5 : ℝ) :=
        mul_nonneg hB (scale_nonneg q _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum hcoef) (by norm_num)) hlast
    _ = K1 * (scale q (-(3 : ℝ) / 2) * scale q (-6 / 5 : ℝ)) +
        K2 * (((scale q (-(3 : ℝ) / 2) * scale q (1 + 6 * gamma)) *
          scale q (1 / 20 : ℝ)) * scale q (-6 / 5 : ℝ)) := by
      dsimp only [K1, K2]
      ring
    _ = K1 * scale q (-27 / 10 : ℝ) +
        K2 * scale q ((-33 / 20 : ℝ) + 6 * gamma) := by
      rw [scale_mul hqpos (-(3 : ℝ) / 2) (-6 / 5 : ℝ)]
      rw [scale_mul hqpos (-(3 : ℝ) / 2) (1 + 6 * gamma)]
      rw [scale_mul hqpos ((-(3 : ℝ) / 2) + (1 + 6 * gamma))
        (1 / 20 : ℝ)]
      rw [scale_mul hqpos
        (((-(3 : ℝ) / 2) + (1 + 6 * gamma)) + 1 / 20)
        (-6 / 5 : ℝ)]
      congr 2 <;> ring_nf
    _ ≤ scale q (-(3 : ℝ) / 2) + scale q (-(3 : ℝ) / 2) :=
      add_le_add hfirstQ' hsecondQ'
    _ = 2 * scale q (-(3 : ℝ) / 2) := by ring

/-- After the explicit Fourier-error absorption, the full four-way
normalized bound is eventually a fixed constant multiple of `q⁻³⁄²`. -/
lemma exists_eventual_claim121FourWayNormalizedBound_le_scale
    (gamma rho K Cmass c B eta kappa : ℝ)
    (hgammaSmall : gamma < 3 / 800) (hrho : 0 < rho)
    (hK : 0 ≤ K) (hCmass : 0 ≤ Cmass) (hc : 0 ≤ c)
    (hB : 0 ≤ B) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ q : ℕ in Filter.atTop,
        ∀ sigma0 : ℝ, 0 ≤ sigma0 →
          sigma0 ≤ 2 * scale q (1 + 6 * gamma) →
          claim121FourWayNormalizedBound q rho K Cmass c B eta kappa
              (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
                (B + sigma0 * scale q (1 / 20 : ℝ)))
              (scale q (-6 / 5 : ℝ)) ≤
            D * scale q (-(3 : ℝ) / 2) := by
  let A : ℝ :=
    4 * Cmass * (2 + kappa) *
        (∑' j, claim121ComparableCellKernel B eta kappa j) +
      200 * K / rho *
        (∑' j, claim121ComparableCellKernel B eta 1 j)
  let D : ℝ := 1 + c * (A + 2)
  have hSk : 0 ≤ ∑' j, claim121ComparableCellKernel B eta kappa j :=
    tsum_nonneg (claim121ComparableCellKernel_nonneg hB heta)
  have hS1 : 0 ≤ ∑' j, claim121ComparableCellKernel B eta 1 j :=
    tsum_nonneg (claim121ComparableCellKernel_nonneg hB heta)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg
      (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) hCmass) (by linarith)) hSk)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hK) hrho.le) hS1)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_claim121_fourier_error_absorption
      gamma Cmass B hgammaSmall hCmass hB] with q herr
  intro sigma0 hsigma0 hsigmaUpper
  have herr' := herr sigma0 hsigma0 hsigmaUpper
  have hs : 0 ≤ scale q (-(3 : ℝ) / 2) := scale_nonneg q _
  unfold claim121FourWayNormalizedBound
  change c * (A * scale q (-(3 : ℝ) / 2) +
      4 * (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
        (B + sigma0 * scale q (1 / 20 : ℝ))) *
        (B * scale q (-6 / 5 : ℝ))) ≤
    D * scale q (-(3 : ℝ) / 2)
  calc
    c * (A * scale q (-(3 : ℝ) / 2) +
        4 * (2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
          (B + sigma0 * scale q (1 / 20 : ℝ))) *
          (B * scale q (-6 / 5 : ℝ))) ≤
        c * (A * scale q (-(3 : ℝ) / 2) +
          2 * scale q (-(3 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl herr') hc
    _ = c * (A + 2) * scale q (-(3 : ℝ) / 2) := by ring
    _ ≤ D * scale q (-(3 : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_right _ hs
      dsimp only [D]
      linarith

/-- Typical remainder degree control also bounds the zero-count comparison
scale used in the residual cutoff. -/
theorem eventually_zeroCountClaim121Scale_le
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
          (O : Finset (Fin n)),
          (∀ i : Fin (Fintype.card D.Covered),
            |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
              (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                D.remainder : ℝ) / 2| ≤ Real.sqrt n) →
          zeroCountClaim121Scale D G c O hbucket ≤
            2 * scale (Fintype.card D.Covered) (1 + 6 * gamma) := by
  have hnumeric := eventually_conditionedCoefficient_numeric gamma hgamma
  filter_upwards [hnumeric, Filter.eventually_ge_atTop 2] with
      n hnumericN hn
  intro G c D hremHalf hpart hbucket O htypical
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
  have hqpos : 0 < q := by omega
  have hqOne : 1 ≤ q := hqpos
  have hs : 0 < s := hbucket.choose_spec.1
  have hqms : q = m * s := by
    exact RobustRank.card_eq_bucketCount_mul_bucketSize
      D.finCoveredPartition.bucket
        (fun j ↦ hbucket.choose_spec.2 j)
  have hm : (m : ℝ) ≤ 2 * scale q (2 * gamma) := by
    simpa only [m, q] using hpart.2.2
  have hfull := hnumericN q m s hq hnq hs hqms hm
  have hbound :
      (n : ℝ) ^ (1 / 2 + 4 * gamma) + Real.sqrt n ≤
        scale q (1 / 2 + 6 * gamma) := by
    have hcountNonneg : 0 ≤
        (q : ℝ) *
          ((s : ℝ)⁻¹ *
            (2 * (scale q ((1 - 2 * gamma) / 2) * Real.log q))) / 2 := by
      have hlog : 0 ≤ Real.log (q : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hqOne)
      exact div_nonneg
        (mul_nonneg (by positivity)
          (mul_nonneg (inv_nonneg.mpr (by positivity))
            (mul_nonneg (by norm_num)
              (mul_nonneg (scale_nonneg q _) hlog)))) (by norm_num)
    change scale n (1 / 2 + 4 * gamma) + Real.sqrt n ≤ _
    linarith
  have hcoeff :=
    hasKSSSBalancedCoefficients_conditionedCovered_zero
      (delta := 2 * gamma) (t := Real.sqrt n)
      D G c rfl O htypical
      (Real.rpow_nonneg (by positivity) _)
      (Real.sqrt_nonneg _) hbucket (by
        simpa only [q, scale, Real.rpow_eq_pow,
          show 1 / 2 + 3 * (2 * gamma) = 1 / 2 + 6 * gamma by ring]
          using hbound)
  have hscale := claim121Scale_le_of_balancedCoefficients
    (delta := 2 * gamma) hqOne (mul_nonneg (by norm_num) hgamma.le)
    D.finCoveredPartition
    (Structured.wStar
      (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
      (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
        (D.conditionedCoveredCoefficient G c O)) 0)
    (bucketCenteredAdjacency D.finCoveredPartition.bucket hbucket.choose
      (D.finCoveredGraph G)) hcoeff
  simpa only [q, zeroCountClaim121Scale,
    show 1 + 3 * (2 * gamma) = 1 + 6 * gamma by ring] using hscale

/-- A covered set of size at least half the ambient set has inverse
three-halves scale within a fixed factor of the ambient one. -/
lemma scale_neg_three_halves_le_ambient
    {n q : ℕ} (hn : 0 < n) (hnq : n ≤ 2 * q) :
    scale q (-(3 : ℝ) / 2) ≤
      (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) *
        scale n (-(3 : ℝ) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) * n := by positivity
  have hbase : (1 / 2 : ℝ) * n ≤ q := by
    have hnqR : (n : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hnq
    linarith
  calc
    scale q (-(3 : ℝ) / 2) ≤
        ((1 / 2 : ℝ) * n) ^ (-(3 : ℝ) / 2) := by
      exact Real.rpow_le_rpow_of_nonpos hhalf hbase (by norm_num)
    _ = (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) *
        scale n (-(3 : ℝ) / 2) := by
      unfold scale
      exact Real.mul_rpow (by norm_num) hnR.le

/-- Numerical conversion of the three fixed-remainder contributions to the
ambient `n⁻³⁄²` scale. -/
lemma claim121_fixed_remainder_rhs_le_ambient
    {n q : ℕ} (hn : 0 < n) (hq : 1 ≤ q) (hnq : n ≤ 2 * q)
    {D R main bad : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hmain : main ≤ D * scale q (-(3 : ℝ) / 2))
    (hbad : bad ≤ scale q (-(3 : ℝ) / 2)) :
    main + bad + R * scale q (-16 / 5 : ℝ) ≤
      ((D + R + 1) * (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)) *
        scale n (-(3 : ℝ) / 2) := by
  have hqDecay : scale q (-16 / 5 : ℝ) ≤
      scale q (-(3 : ℝ) / 2) :=
    scale_mono_exponent hq (by norm_num)
  have hlocal := scale_neg_three_halves_le_ambient hn hnq
  have hqNonneg : 0 ≤ scale q (-(3 : ℝ) / 2) := scale_nonneg q _
  have hnNonneg : 0 ≤ scale n (-(3 : ℝ) / 2) := scale_nonneg n _
  calc
    main + bad + R * scale q (-16 / 5 : ℝ) ≤
        D * scale q (-(3 : ℝ) / 2) +
          scale q (-(3 : ℝ) / 2) +
          R * scale q (-(3 : ℝ) / 2) := by
      exact add_le_add (add_le_add hmain hbad)
        (mul_le_mul_of_nonneg_left hqDecay hR)
    _ = (D + R + 1) * scale q (-(3 : ℝ) / 2) := by ring
    _ ≤ (D + R + 1) *
          ((1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) *
            scale n (-(3 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = ((D + R + 1) * (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)) *
        scale n (-(3 : ℝ) / 2) := by ring

/-- Split a Bernoulli expectation into a uniformly bounded exceptional
event and a pointwise bound on its complement. -/
lemma expectation_half_le_add_eventProbability
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℝ) (Bad : Finset V → Prop) [DecidablePred Bad]
    (A : ℝ)
    (hA : 0 ≤ A) (hgood : ∀ W, ¬ Bad W → f W ≤ A)
    (hall : ∀ W, f W ≤ 1) :
    Probability.expectation (1 / 2 : ℝ) f ≤
      A + Probability.eventProbability (1 / 2 : ℝ) Bad := by
  classical
  calc
    Probability.expectation (1 / 2 : ℝ) f ≤
        Probability.expectation (1 / 2 : ℝ)
          (fun W ↦ A + if Bad W then 1 else 0) := by
      unfold Probability.expectation
      apply Finset.sum_le_sum
      intro W hW
      apply mul_le_mul_of_nonneg_left _
        (Probability.bernoulliWeight_nonneg (by norm_num) (by norm_num) W)
      by_cases hbad : Bad W
      · simp only [hbad, if_true]
        linarith [hall W]
      · simp only [hbad, if_false, add_zero]
        exact hgood W hbad
    _ = A + Probability.eventProbability (1 / 2 : ℝ) Bad := by
      rw [Probability.expectation_add, Probability.expectation_const]
      rfl

/-- Uniform-counting version of the exceptional-event split, avoiding any
dependence on a chosen decision procedure for the predicate. -/
lemma uniformExpectation_le_add_uniformProbability
    {V : Type*} [Fintype V]
    (f : Finset V → ℝ) (Bad : Finset V → Prop) (A : ℝ)
    (hA : 0 ≤ A) (hgood : ∀ W, ¬ Bad W → f W ≤ A)
    (hall : ∀ W, f W ≤ 1) :
    Concentration.uniformExpectation f ≤
      A + Concentration.uniformProbability Bad := by
  classical
  calc
    Concentration.uniformExpectation f ≤
        Concentration.uniformExpectation
          (fun W ↦ A + if Bad W then 1 else 0) := by
      unfold Concentration.uniformExpectation
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro W hW
      by_cases hbad : Bad W
      · simp only [hbad, if_true]
        linarith [hall W]
      · simp only [hbad, if_false, add_zero]
        exact hgood W hbad
    _ = A + Concentration.uniformProbability Bad := by
      rw [Concentration.uniformExpectation_add,
        Concentration.uniformExpectation_const]
      congr 1
      rw [Concentration.uniformExpectation,
        Concentration.uniformProbability, Finset.card_filter]
      push_cast
      rfl

/-- Transfer an eventual property of the covered cardinality `q` to an
ambient index `n` whenever `q ≥ n/2`. -/
lemma eventually_of_le_two
    {P : ℕ → Prop} (hP : ∀ᶠ q : ℕ in Filter.atTop, P q) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ q : ℕ, n ≤ 2 * q → P q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hP
  filter_upwards [Filter.eventually_ge_atTop (2 * N)] with n hn
  intro q hnq
  exact hN q (by omega)

/-- Pointwise bridge between the native raw count-vector mixture and the
named conditional probability used by the structured estimates.  The
explicit decision-procedure alignment prevents a large global
definitional reduction of the whole outer expectation. -/
lemma structuredCountVectorRaw_eq_conditionedSum
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) [instAdj : DecidableRel G.Adj]
    (e0 : ℝ) (c : Fin n → ℝ)
    (R : Finset (D.remainder : Set (Fin n))) (B target : ℝ) :
    (∑ ell : BucketCountVector D.finCoveredPartition,
        (Fintype.card
            (ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val)) : ℝ) /
            Fintype.card
              (Finset (Fin (Fintype.card D.Covered))) *
          Concentration.uniformProbability
            (fun S : ProductSlicePoint D.finCoveredPartition
                (fun j ↦ (ell j).val) ↦
              |Probability.perturbedEdgePolynomial G e0 c
                  (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                    D.finCoveredSubsetImage S.1) - target| ≤ B)) =
      ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability D G e0 c
            (BoundedWindow.subtypeSubsetImage D.remainder R)
            B target ell := by
  have hinst : instAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases hinst
  apply Finset.sum_congr rfl
  intro ell hell
  rw [countVectorWeight, conditionedCountVectorWindowProbability]

/-- In the structured (small regularized-LCD) case, every sufficiently
large fixed window has probability `O(n⁻³ᐞ²)`, uniformly over the
Ramsey graph, admissible linear coefficients, constant term, and center. -/
theorem exists_eventual_graphEffective_smallRLCD_window_upper_threshold
    (C gamma L : ℝ) (hC : 0 < C)
    (hgamma : 0 < gamma) (hgammaSmall : gamma < 3 / 800)
    (hL : 1 ≤ L) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ H : ℝ, 0 < H →
      ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * (n : ℝ)) →
          RLCD.regularizedLCD L gamma
              (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n →
          ∀ e0 target : ℝ,
            Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) ≤
              K * scale n (-(3 : ℝ) / 2) := by
  obtain ⟨B0, hB0, eta, heta, hetaOne, hcommonAll⟩ :=
    exists_eventual_graphEffective_smallRLCD_common_claims_threshold
      C gamma hC hgamma hgammaSmall
  refine ⟨B0, hB0, ?_⟩
  intro B hB0B
  intro H hH
  obtain ⟨Adens, hAdens, rhoF, hrhoF, Dshift, hDshift, hcommon⟩ :=
    hcommonAll H L hH hL
  have hB : 0 < B := hB0.trans_le hB0B
  let Cmass : ℝ := 2 * Real.pi * Real.sqrt Real.pi / Adens
  let kappa : ℝ := 4 * ((2 * H + 1) + 1) /
    (Real.pi * Real.sqrt rhoF)
  let Rtail : ℝ :=
    9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
      (1 + 1 / (32 * rhoF)) ^ 32
  have hCmass : 0 < Cmass := by dsimp only [Cmass]; positivity
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hRtail : 0 < Rtail := by dsimp only [Rtail]; positivity
  obtain ⟨Dnorm, hDnorm, hnormQ⟩ :=
    exists_eventual_claim121FourWayNormalizedBound_le_scale
      gamma rhoF Dshift Cmass Esseen.relativeEsseenConstant B eta kappa
      hgammaSmall hrhoF hDshift.le hCmass.le
      Esseen.relativeEsseenConstant_nonneg hB.le heta hkappa
  let Kfixed : ℝ :=
    (Dnorm + Rtail + 1) * (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)
  let K : ℝ := Kfixed + 1
  have hKfixed : 0 < Kfixed := by dsimp only [Kfixed]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hcommonB := hcommon B hB0B
  have hcountBadQ :=
    RLCD.BucketDecomposition.eventually_countVectorMass_not_nearBalanced_le
  have houterBad :=
    RLCD.BucketDecomposition.eventually_uniformProbability_remainder_atypical_le
      gamma hgamma
  have hzero := eventually_zeroCountClaim121Scale_le gamma hgamma
  have hgrowth := eventually_const_le_scale 2 gamma hgamma
  have hnormN := eventually_of_le_two hnormQ
  have hcountBadN := eventually_of_le_two hcountBadQ
  have hwidthN := eventually_of_le_two
    (eventually_const_le_scale (kappa / 2) (1 / 20 : ℝ) (by norm_num))
  have hlargeN := eventually_of_le_two
    (eventually_const_le_scale (2 / Real.sqrt rhoF) 1 (by norm_num))
  filter_upwards [hcommonB, hcountBadN, houterBad, hzero, hgrowth,
      hnormN, hwidthN, hlargeN, Filter.eventually_ge_atTop 2] with
      n hcommonN hcountBadN houterBadN hzeroN hgrowthN hnormN' hwidthN'
        hlargeN' hn
  intro G _instAdj c hRamsey hc hsmall e0 target
  obtain ⟨D, hrem, hpart, hbucket, hcoveredRamsey, hFrob, hclaims⟩ :=
    hcommonN G c hRamsey hc hsmall
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
  let q := Fintype.card D.Covered
  have hcard : D.remainder.card + q = n := by
    simpa only [q, Fintype.card_fin] using D.remainder_card_add_card_covered
  have hqle : q ≤ n := by omega
  have hcardR : (D.remainder.card : ℝ) + (q : ℝ) = (n : ℝ) := by
    exact_mod_cast hcard
  have hnqR : (n : ℝ) ≤ 2 * (q : ℝ) := by linarith
  have hnq : n ≤ 2 * q := by exact_mod_cast hnqR
  have hqpos : 0 < q := by omega
  have hqOne : 1 ≤ q := hqpos
  have hnormAt := hnormN' q hnq
  have hwidthAt := hwidthN' q hnq
  have hlargeAt := hlargeN' q hnq
  have hlarge : 2 ≤ Real.sqrt rhoF * (q : ℝ) := by
    have hsqrt : 0 < Real.sqrt rhoF := Real.sqrt_pos.2 hrhoF
    have hlargeAt' : 2 / Real.sqrt rhoF ≤ (q : ℝ) := by
      rw [show scale q 1 = (q : ℝ) by exact Real.rpow_one _] at hlargeAt
      exact hlargeAt
    simpa only [mul_comm] using (div_le_iff₀ hsqrt).1 hlargeAt'
  let f : Finset (D.remainder : Set (Fin n)) → ℝ := fun R ↦
    ∑ ell : BucketCountVector D.finCoveredPartition,
      (Fintype.card
          (ProductSlicePoint D.finCoveredPartition
            (fun j ↦ (ell j).val)) : ℝ) /
          Fintype.card (Finset (Fin (Fintype.card D.Covered))) *
        Concentration.uniformProbability
          (fun S : ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val) ↦
            |Probability.perturbedEdgePolynomial G e0 c
                (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                  D.finCoveredSubsetImage S.1) - target| ≤ B)
  let Bad : Finset (D.remainder : Set (Fin n)) → Prop := fun R ↦
    D.remainderSubsetEquivOutsideAssignment R ∈
      D.badRemainderConditionings G (Real.sqrt n)
  have hgood : ∀ R, ¬ Bad R →
      f R ≤ Kfixed * scale n (-(3 : ℝ) / 2) := by
    intro R hRgood
    let O := BoundedWindow.subtypeSubsetImage D.remainder R
    have hO : O ⊆ D.remainder :=
      BoundedWindow.subtypeSubsetImage_subset D.remainder R
    have hdegree : ∀ i : Fin q,
        |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| ≤
            Real.sqrt n := by
      intro i
      have hnot : ¬ Real.sqrt n ≤
          |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
            (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| := by
        intro hi
        apply hRgood
        dsimp only [Bad]
        rw [RLCD.BucketDecomposition.badRemainderConditionings,
          Finset.mem_filter]
        refine ⟨Finset.mem_univ _, i, ?_⟩
        simpa only [O, D.outsideAssignmentSet_remainderSubsetEquiv R] using hi
      exact le_of_not_ge hnot
    obtain ⟨hcoeffBounds, hclaim122, hclaim121Imp, hmass⟩ := hclaims O hO
    have hclaim121 := hclaim121Imp hdegree
    have hsigmaUpper := hzeroN G c D hremHalf hpart hbucket O hdegree
    have hsigma0 : 0 ≤ zeroCountClaim121Scale D G c O hbucket := by
      unfold zeroCountClaim121Scale
      positivity
    have hwidth : kappa * zeroCountClaim121Scale D G c O hbucket ≤
        2 * (B + zeroCountClaim121Scale D G c O hbucket *
          scale q (1 / 20 : ℝ)) := by
      have hk : kappa ≤ 2 * scale q (1 / 20 : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hk hsigma0
      calc
        kappa * zeroCountClaim121Scale D G c O hbucket ≤
            2 * scale q (1 / 20 : ℝ) *
              zeroCountClaim121Scale D G c O hbucket := hmul
        _ = 2 * (0 + zeroCountClaim121Scale D G c O hbucket *
              scale q (1 / 20 : ℝ)) := by ring
        _ ≤ 2 * (B + zeroCountClaim121Scale D G c O hbucket *
              scale q (1 / 20 : ℝ)) := by gcongr
    have hraw := conditionedCountVector_window_average_le_scale_add_bad_tail
      D G e0 c hO hbucket hqpos hrhoF hH hDshift.le hCmass.le hB.le heta
      hlarge hFrob hclaim121 hclaim122
      (by simpa only [Cmass, q] using hmass)
      (by simpa only [kappa, q] using hwidth)
      (target := target)
    have hmain := hnormAt
      (zeroCountClaim121Scale D G c O hbucket) hsigma0
      (by simpa only [q] using hsigmaUpper)
    have hbad := (hcountBadN q hnq) (Fintype.card D.BlockIndex)
      D.finCoveredPartition (2 * gamma) hpart
    have hambient := claim121_fixed_remainder_rhs_le_ambient
      hnpos hqOne hnq hDnorm.le hRtail.le hmain hbad
    have hcompact :
        (∑ ell : BucketCountVector D.finCoveredPartition,
          countVectorWeight D.finCoveredPartition ell *
            conditionedCountVectorWindowProbability D G e0 c O B target ell) ≤
          Kfixed * scale n (-(3 : ℝ) / 2) :=
      hraw.trans (by
        simpa only [q, Kfixed, Rtail] using hambient)
    exact (structuredCountVectorRaw_eq_conditionedSum
      D G e0 c R B target).trans_le (by simpa only [O] using hcompact)
  have hall : ∀ R, f R ≤ 1 := by
    intro R
    dsimp only [f]
    rw [structuredCountVectorRaw_eq_conditionedSum]
    calc
      (∑ ell : BucketCountVector D.finCoveredPartition,
      countVectorWeight D.finCoveredPartition ell *
        conditionedCountVectorWindowProbability D G e0 c
          (BoundedWindow.subtypeSubsetImage D.remainder R) B target ell) ≤
          ∑ ell : BucketCountVector D.finCoveredPartition,
            countVectorWeight D.finCoveredPartition ell * 1 := by
        apply Finset.sum_le_sum
        intro ell hell
        exact mul_le_mul_of_nonneg_left
          (Concentration.uniformProbability_le_one _)
          (countVectorWeight_nonneg D.finCoveredPartition ell)
      _ = 1 := by
        simp only [mul_one]
        exact sum_countVectorWeight_eq_one D.finCoveredPartition
  have houter := houterBadN D G hrem
  have hsplit := uniformExpectation_le_add_uniformProbability f Bad
    (Kfixed * scale n (-(3 : ℝ) / 2))
    (mul_nonneg hKfixed.le (scale_nonneg n _)) hgood hall
  have hfinal : Probability.expectation (1 / 2 : ℝ) f ≤
      K * scale n (-(3 : ℝ) / 2) := by
    rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
    calc
      Concentration.uniformExpectation f ≤
          Kfixed * scale n (-(3 : ℝ) / 2) +
            Concentration.uniformProbability Bad := hsplit
      _ ≤ Kfixed * scale n (-(3 : ℝ) / 2) +
            scale n (-(3 : ℝ) / 2) := by
        exact add_le_add le_rfl (by simpa only [Bad] using houter)
      _ = K * scale n (-(3 : ℝ) / 2) := by dsimp only [K]; ring
  simpa only [f] using
    (RLCD.BucketDecomposition.eventProbability_half_eq_structured_countVector_mixture
      D (fun U ↦
        |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B)).trans_le hfinal

end Erdos88.GaussianQuadratic
