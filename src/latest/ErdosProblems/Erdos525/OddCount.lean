import ErdosProblems.Erdos525.OddProbability

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

noncomputable def localAffineOffset (n : ℕ) (e : SignVector (2 * n + 1))
    (a : Fin (localMeshSize n)) : ℝ :=
  affineClosestOffset (eval n e (localMeshPoint n a))
    (velocity n e (localMeshPoint n a))

noncomputable def localSignedHeight (n : ℕ) (e : SignVector (2 * n + 1))
    (a : Fin (localMeshSize n)) : ℝ :=
  n * ((eval n e (localMeshPoint n a) *
    conj (velocity n e (localMeshPoint n a))).im /
      ‖velocity n e (localMeshPoint n a)‖)

def IsLocalRepresentative (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n + 1)) (a : Fin (localMeshSize n)) : Prop :=
  velocity n e (localMeshPoint n a) ≠ 0 ∧
  |localAffineOffset n e a| ≤ localMeshHalfWidth n ∧
  |localSignedHeight n e a| ≤ u

def IsTruncatedLocalRepresentative
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) (a : Fin (localMeshSize n)) : Prop :=
  IsLocalRepresentative n u e a ∧
    velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖ ∧
    ‖velocity n e (localMeshPoint n a)‖ ≤ velocityUpper

def IsFactoredTruncatedLocalRepresentative
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) (a : Fin (localMeshSize n)) : Prop :=
  velocity n e (localMeshPoint n a) ≠ 0 ∧
    |localAffineOffset n e a| ≤ widthFactor * localMeshHalfWidth n ∧
    |localSignedHeight n e a| ≤ u ∧
    velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖ ∧
    ‖velocity n e (localMeshPoint n a)‖ ≤ velocityUpper

lemma phasePosition_normalizedPhaseWalk (n : ℕ)
    (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) (r : Fin m) :
    phasePosition (normalizedPhaseWalk n e points) r = eval n e (points r) := by
  rfl

lemma phaseVelocity_normalizedPhaseWalk (n : ℕ)
    (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) (r : Fin m) :
    phaseVelocity (normalizedPhaseWalk n e points) r = velocity n e (points r) := by
  rfl

lemma phaseToBlocks_normalizedPhaseEuclideanWalk
    (n : ℕ) (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) (r : Fin m) :
    phaseToBlocks (normalizedPhaseEuclideanWalk n e points) r =
      (eval n e (points r), velocity n e (points r)) := by
  rfl

lemma isPhaseRepresentative_normalized_iff
    (n : ℕ) (u halfWidth : ℝ) (e : SignVector (2 * n + 1))
    (points : Fin m → ℝ) (r : Fin m) :
    IsPhaseRepresentative n u halfWidth (normalizedPhaseWalk n e points) r ↔
      velocity n e (points r) ≠ 0 ∧
      |affineClosestOffset (eval n e (points r)) (velocity n e (points r))| ≤
        halfWidth ∧
      |n * ((eval n e (points r) * conj (velocity n e (points r))).im /
        ‖velocity n e (points r)‖)| ≤ u := by
  rw [IsPhaseRepresentative, phaseAffineOffset, phaseSignedHeight,
    phasePosition_normalizedPhaseWalk, phaseVelocity_normalizedPhaseWalk]

lemma joint_factoredTruncatedLocalRepresentatives_iff_region
    (n : ℕ) (hn : 0 < n)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hvelLower : 0 < velocityLower)
    (e : SignVector (2 * n + 1))
    (s : Finset (Fin (localMeshSize n))) :
    (∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a) ↔
      normalizedPhaseEuclideanWalk n e (localSitesPoints s) ∈
        truncatedPhaseRegion (m := s.card) n u
          (widthFactor * localMeshHalfWidth n)
          velocityLower velocityUpper := by
  rw [truncatedPhaseRegion]
  change (∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a) ↔
    phaseToBlocks (normalizedPhaseEuclideanWalk n e (localSitesPoints s)) ∈
      Set.univ.pi (fun _ : Fin s.card ↦
        truncatedBlockSet n u (widthFactor * localMeshHalfWidth n)
          velocityLower velocityUpper)
  constructor
  · intro h r _hr
    have ha := h (localSite s r) (localSite_mem s r)
    rw [truncatedBlockSet,
      mem_truncatedBlockRegion_iff n u
        (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper hvelLower]
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk]
    rw [← phasePosition_normalizedPhaseWalk n e (localSitesPoints s) r,
      ← phaseVelocity_normalizedPhaseWalk n e (localSitesPoints s) r]
    rw [isTruncatedBlockRepresentative_iff_phase
      (m := s.card) n hn u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper]
    refine ⟨?_, ?_, ?_⟩
    · rw [isPhaseRepresentative_normalized_iff]
      exact ⟨ha.1, ha.2.1, ha.2.2.1⟩
    · rw [phaseVelocity_normalizedPhaseWalk]
      exact ha.2.2.2.1
    · rw [phaseVelocity_normalizedPhaseWalk]
      exact ha.2.2.2.2
  · intro h a ha
    rcases localSite_surjective s ha with ⟨r, rfl⟩
    have hr := h r (Set.mem_univ r)
    rw [truncatedBlockSet,
      mem_truncatedBlockRegion_iff n u
        (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper hvelLower] at hr
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk] at hr
    rw [← phasePosition_normalizedPhaseWalk n e (localSitesPoints s) r,
      ← phaseVelocity_normalizedPhaseWalk n e (localSitesPoints s) r] at hr
    rw [isTruncatedBlockRepresentative_iff_phase
      (m := s.card) n hn u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper] at hr
    rw [isPhaseRepresentative_normalized_iff] at hr
    rw [phaseVelocity_normalizedPhaseWalk] at hr
    exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2.1, hr.2.2⟩

lemma joint_factoredTruncatedLocalProbability_eq_phase
    (n : ℕ) (hn : 0 < n)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hvelLower : 0 < velocityLower)
    (s : Finset (Fin (localMeshSize n))) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ∀ a ∈ s,
          IsFactoredTruncatedLocalRepresentative n widthFactor u
            velocityLower velocityUpper e a) =
      factoredTruncatedPhaseProbability s.card n (localSitesPoints s)
        widthFactor u velocityLower velocityUpper := by
  unfold factoredTruncatedPhaseProbability
  apply congrArg uniformProbability
  funext e
  exact propext (joint_factoredTruncatedLocalRepresentatives_iff_region
    n hn widthFactor u velocityLower velocityUpper hvelLower e s)

theorem eventually_uniform_scaled_good_factoredTruncatedLocalProbability
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Finset (Fin (localMeshSize n)),
      s ∈ Finset.univ.powersetCard m →
      IsGoodLocalSiteSet n s →
      |(localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            ∀ a ∈ s,
              IsFactoredTruncatedLocalRepresentative n widthFactor u
                velocityLower velocityUpper e a) -
        ((widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m)| < eps := by
  filter_upwards [Nat.eventually_pos,
      eventually_uniform_scaled_factoredTruncatedPhaseProbability
        m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower
          hvelUpper heps]
    with n hn hprob
  intro s hs hgood
  have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
  subst m
  rw [joint_factoredTruncatedLocalProbability_eq_phase
    n hn widthFactor u velocityLower velocityUpper hvelLower s]
  exact hprob (localSitesPoints s) hgood.smooth_points hgood.2

noncomputable def halfGoodFactoredTruncatedChooseContribution
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfGoodLocalSiteSets n m,
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem eventually_halfGoodFactoredTruncatedChooseContribution_close
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      |halfGoodFactoredTruncatedChooseContribution n m widthFactor u
          velocityLower velocityUpper -
        ((widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m) *
          ((halfGoodLocalSiteSets n m).card : ℝ) /
            (localMeshSize n : ℝ) ^ m| < eps := by
  have hlocal := eventually_uniform_scaled_good_factoredTruncatedLocalProbability
    m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower hvelUpper
      (half_pos heps)
  filter_upwards [hlocal] with n hn
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  let q : ℝ := (localMeshSize n : ℝ) ^ m
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_pos (by exact_mod_cast localMeshSize_pos n) m
  have hcardNat : (halfGoodLocalSiteSets n m).card ≤ localMeshSize n ^ m := by
    calc
      (halfGoodLocalSiteSets n m).card ≤
          ((halfLocalMeshSites n).powersetCard m).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (halfLocalMeshSize n).choose m := by
        rw [Finset.card_powersetCard, card_halfLocalMeshSites]
      _ ≤ (halfLocalMeshSize n) ^ m := Nat.choose_le_pow _ _
      _ ≤ (localMeshSize n) ^ m :=
        Nat.pow_le_pow_left (Nat.div_le_self _ _) m
  have hcardR : ((halfGoodLocalSiteSets n m).card : ℝ) ≤ q := by
    dsimp [q]
    exact_mod_cast hcardNat
  have hsum :
      |∑ s ∈ halfGoodLocalSiteSets n m,
          (q * uniformProbability (fun e : SignVector (2 * n + 1) ↦
              ∀ a ∈ s,
                IsFactoredTruncatedLocalRepresentative n widthFactor u
                  velocityLower velocityUpper e a) - A)| ≤
        ((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2) := by
    calc
      _ ≤ ∑ s ∈ halfGoodLocalSiteSets n m,
          |q * uniformProbability (fun e : SignVector (2 * n + 1) ↦
              ∀ a ∈ s,
                IsFactoredTruncatedLocalRepresentative n widthFactor u
                  velocityLower velocityUpper e a) - A| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ halfGoodLocalSiteSets n m, eps / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hhalf := (Finset.mem_filter.mp hs).1
        have hall : s ∈ Finset.univ.powersetCard m := by
          rw [Finset.mem_powersetCard] at hhalf ⊢
          exact ⟨Finset.subset_univ s, hhalf.2⟩
        have hgood := (Finset.mem_filter.mp hs).2
        simpa [q, A] using (hn s hall hgood).le
      _ = ((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2) := by simp
  rw [halfGoodFactoredTruncatedChooseContribution,
    sum_sub_normalized_card _ _ q A hqpos.ne']
  rw [abs_div, abs_of_pos hqpos]
  calc
    _ ≤ (((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2)) / q :=
      div_le_div_of_nonneg_right hsum hqpos.le
    _ = (((halfGoodLocalSiteSets n m).card : ℝ) / q) * (eps / 2) := by ring
    _ ≤ 1 * (eps / 2) := by
      gcongr
      exact (div_le_one hqpos).2 hcardR
    _ < eps := by linarith

theorem halfGoodFactoredTruncatedChooseContribution_tendsto
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfGoodFactoredTruncatedChooseContribution n m widthFactor u
        velocityLower velocityUpper) atTop
      (𝓝 (((widthFactor * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) ^ m) /
          (m.factorial : ℝ))) := by
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  let reference : ℕ → ℝ := fun n ↦
    A * ((halfGoodLocalSiteSets n m).card : ℝ) /
      (localMeshSize n : ℝ) ^ m
  have href : Tendsto reference atTop
      (𝓝 (A * (((1 / 2 : ℝ) ^ m) / (m.factorial : ℝ)))) := by
    dsimp [reference]
    convert tendsto_const_nhds.mul
      (halfGoodLocalSiteSets_ratio_tendsto_factorial m hm) using 1 <;> ring_nf
  have hdiff : Tendsto (fun n : ℕ ↦
      halfGoodFactoredTruncatedChooseContribution n m widthFactor u
          velocityLower velocityUpper - reference n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    have hclose := eventually_halfGoodFactoredTruncatedChooseContribution_close
      m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower
        hvelUpper heps
    apply eventually_atTop.1
    exact hclose.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, reference, A] using hn
  have hsum := hdiff.add href
  convert hsum using 1
  · funext n
    simp only [reference]
    ring
  · congr 1
    dsimp [A]
    rw [show widthFactor * (6 * u / Real.pi *
        blockVelocityMass velocityLower velocityUpper) =
      (widthFactor * (12 * u / Real.pi *
        blockVelocityMass velocityLower velocityUpper)) * (1 / 2 : ℝ) by ring,
      mul_pow]
    ring

/-- The position-space Fourier estimate used for nonspread tuples is uniform
in the center of the small ball. -/
lemma uniformProbability_positionBallAround_le_of_integral
    (n m : ℕ) (points : Fin m → ℝ) (sigma delta C : ℝ)
    (hsigma : 0 < sigma) (hdelta : 0 ≤ delta)
    (hintegral :
      (∫ u : PositionEuclidean m,
        Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
          ‖positionCharFun n points u‖) ≤ C)
    (y : PositionEuclidean m) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) ≤
      C / ((2 * Real.pi / sigma ^ 2) ^ m *
        Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by
  have hmass := uniformProbability_positionBall_mul_le_smoothedMassReal
    n points sigma delta hsigma hdelta y
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (2 * Real.pi / sigma ^ 2) ^ m by positivity)
  have hfour := positionGaussianSmoothedMassReal_fourier_le
    n m points sigma hsigma y
  have hupper : (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y ≤ C :=
    hfour.trans hintegral
  have hden : 0 < (2 * Real.pi / sigma ^ 2) ^ m *
      Real.exp (-(delta ^ 2 / (2 * sigma ^ 2))) := by positivity
  apply (le_div_iff₀ hden).2
  calc
    _ = (2 * Real.pi / sigma ^ 2) ^ m *
        (uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by ring
    _ ≤ (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y := hscaled
    _ ≤ C := hupper

theorem eventually_scaled_positionBallAround_probability_le_integralUpper
    {m : ℕ} (hm : 0 < m) (u velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (y : PositionEuclidean m),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      (localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ‖normalizedPositionEuclideanWalk n e points - y‖ ≤
              positionRepresentativeRadius m n u velocityUpper) ≤
        Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
          positionWeakIntegralUpper m n
            (rigidityPower n (-positionCovarianceFloorExponent m))
            (positionSmoothingScale n) := by
  filter_upwards [Nat.eventually_pos,
      eventually_hasPhaseCovarianceLower_weak hm,
      eventually_weakPhaseCovarianceGamma_lower hm,
      eventually_positionCharFun_integral_le_weakSpread hm]
    with n hn hcovWeak hgammaFloor hfourier
  intro points y hsmooth hspread
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : 0 < rigidityPower n
      (-positionCovarianceFloorExponent m) := rigidityPower_pos hn _
  have hsigma : 0 < positionSmoothingScale n := by
    unfold positionSmoothingScale
    positivity
  have hcov : HasPhaseCovarianceLower n points
      (rigidityPower n (-positionCovarianceFloorExponent m)) :=
    (hcovWeak points hsmooth hspread).mono hgammaFloor
  have hintegral := hfourier points
    (rigidityPower n (-positionCovarianceFloorExponent m))
    (positionSmoothingScale n) hgamma hsigma hcov hsmooth hspread
  have hdelta : 0 ≤ positionRepresentativeRadius m n u velocityUpper := by
    unfold positionRepresentativeRadius
    have hhalf : 0 ≤ localMeshHalfWidth n := by
      unfold localMeshHalfWidth
      positivity
    exact mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (mul_nonneg hhalf hvelocityUpper)
        (div_nonneg hu hnreal.le))
  have hprob := uniformProbability_positionBallAround_le_of_integral
    n m points (positionSmoothingScale n)
      (positionRepresentativeRadius m n u velocityUpper)
      (positionWeakIntegralUpper m n
        (rigidityPower n (-positionCovarianceFloorExponent m))
        (positionSmoothingScale n))
      hsigma hdelta hintegral y
  let probability : ℝ := uniformProbability (fun e : SignVector (2 * n) ↦
    ‖normalizedPositionEuclideanWalk n e points - y‖ ≤
      positionRepresentativeRadius m n u velocityUpper)
  let normalization : ℝ :=
    (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m
  let exponent : ℝ :=
    positionRepresentativeRadius m n u velocityUpper ^ 2 /
      (2 * positionSmoothingScale n ^ 2)
  let upper : ℝ := positionWeakIntegralUpper m n
    (rigidityPower n (-positionCovarianceFloorExponent m))
    (positionSmoothingScale n)
  let B : ℝ := positionRepresentativeExponentBound m u velocityUpper
  have hnormalization : (localMeshSize n : ℝ) ^ m ≤ normalization := by
    simpa [normalization] using positionSmoothing_normalization_lower m n hn
  have hexponent : exponent ≤ B := by
    simpa [exponent, B] using positionRepresentativeRadius_exponent_le
      m n hn u velocityUpper hu hvelocityUpper
  have hdenExp : Real.exp (-B) ≤ Real.exp (-exponent) :=
    Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hden : 0 < normalization * Real.exp (-exponent) := by
    dsimp [normalization]
    positivity
  have hprob' : probability ≤ upper /
      (normalization * Real.exp (-exponent)) := by
    simpa [probability, normalization, exponent, upper] using hprob
  have hproduct : probability *
      (normalization * Real.exp (-exponent)) ≤ upper :=
    (le_div_iff₀ hden).mp hprob'
  have hsmallDen : (localMeshSize n : ℝ) ^ m * Real.exp (-B) ≤
      normalization * Real.exp (-exponent) :=
    mul_le_mul hnormalization hdenExp
      (Real.exp_pos _).le (by dsimp [normalization]; positivity)
  have hscaledProduct :
      ((localMeshSize n : ℝ) ^ m * probability) * Real.exp (-B) ≤ upper := by
    calc
      ((localMeshSize n : ℝ) ^ m * probability) * Real.exp (-B) =
          probability * ((localMeshSize n : ℝ) ^ m * Real.exp (-B)) := by ring
      _ ≤ probability * (normalization * Real.exp (-exponent)) :=
        mul_le_mul_of_nonneg_left hsmallDen (uniformProbability_nonneg _)
      _ ≤ upper := hproduct
  have hdivide : (localMeshSize n : ℝ) ^ m * probability ≤
      upper / Real.exp (-B) :=
    (le_div_iff₀ (Real.exp_pos _)).2 hscaledProduct
  calc
    _ = (localMeshSize n : ℝ) ^ m * probability := rfl
    _ ≤ upper / Real.exp (-B) := hdivide
    _ = Real.exp B * upper := by
      rw [Real.exp_neg, div_inv_eq_mul]
      ring
    _ = _ := by rfl

theorem eventually_scaled_positionBallAround_probability_le_power
    {m : ℕ} (hm : 0 < m) (u velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (y : PositionEuclidean m),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      (localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ‖normalizedPositionEuclideanWalk n e points - y‖ ≤
              positionRepresentativeRadius m n u velocityUpper) ≤
        rigidityPower n (1 / 20) := by
  filter_upwards [
      eventually_scaled_positionBallAround_probability_le_integralUpper
        hm u velocityUpper hu hvelocityUpper,
      eventually_positionWeakIntegralUpper_le_power hm u velocityUpper]
    with n hprob hupper
  intro points y hsmooth hspread
  exact (hprob points y hsmooth hspread).trans hupper

noncomputable def normalizedPositionEuclideanWalk
    (n : ℕ) (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) :
    PositionEuclidean m :=
  positionToEuclidean (fun r c ↦
    normalizedPhaseWalk n e points r (Fin.castLE (by omega) c))

noncomputable def extraPositionEuclidean
    (n : ℕ) (b : Bool) (points : Fin m → ℝ) : PositionEuclidean m :=
  positionToEuclidean (fun r c ↦
    extraPhase n b points r (Fin.castLE (by omega) c))

lemma normalizedPositionEuclideanWalk_appendSign
    (n : ℕ) (e : SignVector (2 * n)) (b : Bool)
    (points : Fin m → ℝ) :
    normalizedPositionEuclideanWalk n (appendSign n e b) points =
      prefixScale n • Erdos525.normalizedPositionEuclideanWalk n e points +
        extraPositionEuclidean n b points := by
  ext rc
  rcases rc with ⟨r, c⟩
  fin_cases c <;>
    simp [normalizedPositionEuclideanWalk, extraPositionEuclidean,
      Erdos525.normalizedPositionEuclideanWalk, positionToEuclidean,
      normalizedPhaseWalk_eq]

lemma norm_normalizedPositionEuclideanWalk_sq
    (n : ℕ) (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) :
    ‖normalizedPositionEuclideanWalk n e points‖ ^ 2 =
      ∑ r : Fin m, ‖eval n e (points r)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold normalizedPositionEuclideanWalk positionToEuclidean
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Fin.sum_univ_two]
  simp only [WithLp.ofLp_toLp]
  change (normalizedPhaseWalk n e points r 0) ^ 2 +
      (normalizedPhaseWalk n e points r 1) ^ 2 = ‖eval n e (points r)‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq]
  simp [normalizedPhaseWalk, Complex.normSq_apply, pow_two]

lemma joint_factoredTruncatedLocalRepresentatives_positionBall
    (n : ℕ) (hn : 0 < n)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (e : SignVector (2 * n + 1))
    (s : Finset (Fin (localMeshSize n)))
    (hrep : ∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a) :
    ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
      positionRepresentativeRadius s.card n u
        (widthFactor * velocityUpper) := by
  let R : ℝ := widthFactor * localMeshHalfWidth n * velocityUpper + u / n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hfactor (by
        unfold localMeshHalfWidth
        positivity)) hvelocityUpper)
      (div_nonneg hu hnreal.le)
  have hregion := (joint_factoredTruncatedLocalRepresentatives_iff_region
    n hn widthFactor u velocityLower velocityUpper hvelocityLower e s).1 hrep
  have hcoord : ∀ r : Fin s.card,
      ‖eval n e (localSitesPoints s r)‖ ≤ R := by
    intro r
    have hr := hregion r (Set.mem_univ r)
    change phaseToBlocks
        (normalizedPhaseEuclideanWalk n e (localSitesPoints s)) r ∈
      truncatedBlockRegion n u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper at hr
    have hcompact := truncatedBlockRegion_subset_compactProduct n hn u
      (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper hu
      (mul_nonneg hfactor (by unfold localMeshHalfWidth; positivity))
      hvelocityLower hr
    have hfirst := hcompact.1
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk] at hfirst
    simpa [Metric.mem_closedBall, dist_zero_right, R, mul_assoc] using hfirst
  have hsquares : ∑ r : Fin s.card,
      ‖eval n e (localSitesPoints s r)‖ ^ 2 ≤ s.card * R ^ 2 := by
    calc
      _ ≤ ∑ _r : Fin s.card, R ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        exact (sq_le_sq₀ (norm_nonneg _) hR).2 (hcoord r)
      _ = s.card * R ^ 2 := by simp
  have hnormsq :
      ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ^ 2 ≤
        (Real.sqrt s.card * R) ^ 2 := by
    rw [norm_normalizedPositionEuclideanWalk_sq]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa [R] using hsquares
  have hnorm := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hR)).1 hnormsq
  simpa [positionRepresentativeRadius, R, mul_assoc, mul_left_comm,
    mul_comm] using hnorm

theorem eventually_scaled_halfWeakNonspread_factored_site_probability_le_power
    (k : ℕ) (hk : 0 < k)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        (localMeshSize n : ℝ) ^ k *
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            ∀ a ∈ s,
              IsFactoredTruncatedLocalRepresentative n widthFactor u
                velocityLower velocityUpper e a) ≤
        rigidityPower n (1 / 20) := by
  classical
  have hfactorUpper : 0 ≤ widthFactor * velocityUpper :=
    mul_nonneg hfactor hvelocityUpper
  filter_upwards [Nat.eventually_pos,
      prefixScale_inv_tendsto_one.eventually
        (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      eventually_scaled_positionBallAround_probability_le_power
        hk (2 * u) (2 * (widthFactor * velocityUpper))
          (mul_nonneg (by norm_num) hu) (mul_nonneg (by norm_num) hfactorUpper)]
    with n hn hinvTwo hball
  intro s hs
  have hweak := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hweak.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  have hcard : s.card = k := hpowerset.2
  have hsmooth : ∀ r : Fin s.card,
      IsSmooth n (rigiditySmoothScale n) (localSitesPoints s r) := by
    intro r
    exact (Finset.mem_filter.mp
      (hpowerset.1 (localSite_mem s r))).2
  subst k
  let P : SignVector (2 * n + 1) → Prop := fun e ↦
    ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a
  let R : ℝ := positionRepresentativeRadius s.card n u
    (widthFactor * velocityUpper)
  let R' : ℝ := positionRepresentativeRadius s.card n (2 * u)
    (2 * (widthFactor * velocityUpper))
  have hR0 : 0 ≤ R := by
    dsimp [R, positionRepresentativeRadius]
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg
      (mul_nonneg (by unfold localMeshHalfWidth; positivity) hfactorUpper)
      (div_nonneg hu (by positivity)))
  have hRscale : (prefixScale n)⁻¹ * R ≤ R' := by
    calc
      (prefixScale n)⁻¹ * R ≤ 2 * R :=
        mul_le_mul_of_nonneg_right hinvTwo.le hR0
      _ = R' := by
        dsimp [R, R', positionRepresentativeRadius]
        ring
  have hconditional : ∀ b : Bool,
      (localMeshSize n : ℝ) ^ s.card *
          uniformProbability (fun e : SignVector (2 * n) ↦ P (appendSign n e b)) ≤
        rigidityPower n (1 / 20) := by
    intro b
    let center : PositionEuclidean s.card :=
      -((prefixScale n)⁻¹ • extraPositionEuclidean n b (localSitesPoints s))
    have hmono : uniformProbability (fun e : SignVector (2 * n) ↦
          P (appendSign n e b)) ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖Erdos525.normalizedPositionEuclideanWalk n e (localSitesPoints s) -
              center‖ ≤ R') := by
      apply uniformProbability_mono
      intro e he
      have hOdd := joint_factoredTruncatedLocalRepresentatives_positionBall
        n hn widthFactor u velocityLower velocityUpper hfactor hu
          hvelocityLower hvelocityUpper (appendSign n e b) s he
      have hinvPos : 0 < (prefixScale n)⁻¹ := inv_pos.mpr (prefixScale_pos n)
      have heq :
          Erdos525.normalizedPositionEuclideanWalk n e (localSitesPoints s) -
              center =
            (prefixScale n)⁻¹ •
              normalizedPositionEuclideanWalk n (appendSign n e b)
                (localSitesPoints s) := by
        rw [normalizedPositionEuclideanWalk_appendSign]
        dsimp [center]
        have hscale0 : prefixScale n ≠ 0 := (prefixScale_pos n).ne'
        rw [smul_add, smul_smul, inv_mul_cancel₀ hscale0, one_smul]
        module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hinvPos]
      exact (mul_le_mul_of_nonneg_left hOdd hinvPos.le).trans hRscale
    have hscaled := mul_le_mul_of_nonneg_left hmono (by positivity :
      0 ≤ (localMeshSize n : ℝ) ^ s.card)
    exact hscaled.trans (hball (localSitesPoints s) center hsmooth hweak.2)
  have hsplit := uniformProbability_split n P
  have h0 := hconditional false
  have h1 := hconditional true
  rw [hsplit]
  nlinarith

noncomputable def halfWeakNonspreadFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfWeakNonspreadLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem halfWeakNonspreadFactoredChooseContribution_tendsto_zero
    (k : ℕ) (hk : 0 < k)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
    filter_upwards [
      eventually_scaled_halfWeakNonspread_factored_site_probability_le_power
        k hk widthFactor u velocityLower velocityUpper hfactor hu
          hvelocityLower hvelocityUpper] with n hsite
    let q : ℝ := (localMeshSize n : ℝ) ^ k
    have hq : 0 < q := by
      dsimp [q]
      exact pow_pos (by exact_mod_cast localMeshSize_pos n) k
    have hterm : ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) ≤
          rigidityPower n (1 / 20) / q := by
      intro s hs
      exact (le_div_iff₀ hq).2 (by simpa [q, mul_comm] using hsite s hs)
    calc
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        ∑ _s ∈ halfWeakNonspreadLocalSiteSets n k,
          rigidityPower n (1 / 20) / q := by
        unfold halfWeakNonspreadFactoredChooseContribution
        exact Finset.sum_le_sum fun s hs ↦ hterm s hs
      _ = ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by simp
      _ ≤ ((badLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by
        have hcard : ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) ≤
            (badLocalSiteSets n k).card := by
          exact_mod_cast Finset.card_le_card
            (halfWeakNonspread_subset_badLocalSiteSets n k)
        exact mul_le_mul_of_nonneg_right hcard
          (div_nonneg (rigidityPower_nonneg n _) hq.le)
      _ = rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
        dsimp only [q]
        ring
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      unfold halfWeakNonspreadFactoredChooseContribution
      exact Finset.sum_nonneg fun s _ ↦ uniformProbability_nonneg _)
    hupper
  exact weighted_badLocalSiteSets_ratio_tendsto_zero k hk

end Odd

end Erdos525
