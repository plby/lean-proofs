import ErdosProblems.Erdos239.External.Erdos67.CorrectionTransport
import ErdosProblems.Erdos239.External.Erdos67.Section4Probability

/-!
# Selecting the weighted Section 4 sample

This file formalizes the probability step which Tao uses immediately before
the deterministic Borwein--Choi--Coons calculation.  A bounded stochastic
prefix law controls the finite weighted average of every translated local
sum.  Markov's inequality can then be intersected with any previously chosen
two-scale pretentious event, so the factorization witnesses and the weighted
energy estimate belong to one and the same sample.

The residue-series grouping is kept in a separate finite/infinite transfer
module.  In particular, this file does not use the incorrect linear expression
`sum_a L_h(a) * |A(a)|^2`: Tao's equation (15) contains the squared norm of a
shifted convolution `sum_m u(a+m) * L_h(a+m)`.
-/

open scoped ENNReal
open MeasureTheory

namespace Erdos67

noncomputable section

/-! ## Deterministic removal of a slowly varying unit phase -/

/-- A translated finite sum, indexed exactly as in Tao's Section 4. -/
def shiftedFiniteSum (F : ℕ → ℂ) (n L : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L, F (n + m)

/-- The local increment defined as a difference of prefixes is the translated
sum over `1 ≤ m ≤ L`. -/
theorem circleLocalIncrement_eq_shiftedFiniteSum
    (z : PrimeAssignment) (n L : ℕ) :
    circleLocalIncrement z n L =
      shiftedFiniteSum (fun j ↦ (primeExtension z j : ℂ)) n L := by
  unfold circleLocalIncrement circlePartialSum shiftedFiniteSum
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (n + L) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hj'.1, hj'.2.trans (Nat.le_add_right n L)⟩
  rw [← Finset.sum_sdiff hsub]
  ring_nf
  let e : ℕ ↪ ℕ := ⟨fun m ↦ n + m, by
    intro a b hab
    exact Nat.add_left_cancel hab⟩
  have hsets :
      Finset.Icc 1 (n + L) \ Finset.Icc 1 n =
        (Finset.Icc 1 L).map e := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_map]
    constructor
    · rintro ⟨⟨hj1, hjtop⟩, hjn⟩
      refine ⟨j - n, ⟨by omega, by omega⟩, ?_⟩
      change n + (j - n) = j
      omega
    · rintro ⟨m, ⟨hm1, hmL⟩, rfl⟩
      change (1 ≤ n + m ∧ n + m ≤ n + L) ∧
        ¬ (1 ≤ n + m ∧ n + m ≤ n)
      omega
  rw [hsets, Finset.sum_map]
  rfl

/-- Removing a unit phase whose oscillation on one interval is at most
`eps` costs at most `L * eps` in norm.  The factorization hypothesis is kept
fully abstract, so this lemma applies verbatim to the modified character,
Archimedean phase, and correction assignment. -/
theorem norm_shiftedFiniteSum_remove_phase_le
    (base modified phase correction : ℕ → ℂ)
    (n L : ℕ) (eps : ℝ)
    (hfactor : ∀ j ∈ Finset.Icc 1 L,
      base (n + j) = modified (n + j) * phase (n + j) * correction (n + j))
    (hphase : ‖phase n‖ = 1)
    (hmodified : ∀ j ∈ Finset.Icc 1 L, ‖modified (n + j)‖ ≤ 1)
    (hcorrection : ∀ j ∈ Finset.Icc 1 L, ‖correction (n + j)‖ ≤ 1)
    (hslow : ∀ j ∈ Finset.Icc 1 L, ‖phase (n + j) - phase n‖ ≤ eps) :
    ‖shiftedFiniteSum (fun j ↦ modified j * correction j) n L‖ ≤
      ‖shiftedFiniteSum base n L‖ + (L : ℝ) * eps := by
  let U : ℂ := shiftedFiniteSum (fun j ↦ modified j * correction j) n L
  let V : ℂ := shiftedFiniteSum base n L
  have hdiff :
      V - phase n * U =
        ∑ j ∈ Finset.Icc 1 L,
          modified (n + j) * correction (n + j) *
            (phase (n + j) - phase n) := by
    dsimp only [U, V, shiftedFiniteSum]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfactor j hj]
    ring
  have herror : ‖V - phase n * U‖ ≤ (L : ℝ) * eps := by
    rw [hdiff]
    calc
      ‖∑ j ∈ Finset.Icc 1 L,
          modified (n + j) * correction (n + j) *
            (phase (n + j) - phase n)‖ ≤
          ∑ j ∈ Finset.Icc 1 L,
            ‖modified (n + j) * correction (n + j) *
              (phase (n + j) - phase n)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 L, eps := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul]
        have hmc : ‖modified (n + j)‖ * ‖correction (n + j)‖ ≤ 1 := by
          calc
            ‖modified (n + j)‖ * ‖correction (n + j)‖ ≤ 1 * 1 :=
              mul_le_mul (hmodified j hj) (hcorrection j hj)
                (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul 1
        calc
          ‖modified (n + j)‖ * ‖correction (n + j)‖ *
              ‖phase (n + j) - phase n‖ ≤
              1 * ‖phase (n + j) - phase n‖ :=
            mul_le_mul_of_nonneg_right hmc (norm_nonneg _)
          _ = ‖phase (n + j) - phase n‖ := one_mul _
          _ ≤ eps := hslow j hj
      _ = (L : ℝ) * eps := by
        have hcard : (Finset.Icc 1 L).card = L := by simp
        simp [hcard, nsmul_eq_mul]
  have hphaseU : ‖phase n * U‖ = ‖U‖ := by rw [norm_mul, hphase, one_mul]
  rw [← hphaseU]
  calc
    ‖phase n * U‖ ≤ ‖V‖ + ‖V - phase n * U‖ := by
      have h := norm_sub_le V (V - phase n * U)
      simpa only [sub_sub_cancel] using h
    _ ≤ ‖V‖ + (L : ℝ) * eps := by gcongr

/-- Squared-energy form of phase removal. -/
theorem normSq_shiftedFiniteSum_remove_phase_le
    (base modified phase correction : ℕ → ℂ)
    (n L : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hfactor : ∀ j ∈ Finset.Icc 1 L,
      base (n + j) = modified (n + j) * phase (n + j) * correction (n + j))
    (hphase : ‖phase n‖ = 1)
    (hmodified : ∀ j ∈ Finset.Icc 1 L, ‖modified (n + j)‖ ≤ 1)
    (hcorrection : ∀ j ∈ Finset.Icc 1 L, ‖correction (n + j)‖ ≤ 1)
    (hslow : ∀ j ∈ Finset.Icc 1 L, ‖phase (n + j) - phase n‖ ≤ eps) :
    Complex.normSq
        (shiftedFiniteSum (fun j ↦ modified j * correction j) n L) ≤
      2 * Complex.normSq (shiftedFiniteSum base n L) +
        2 * ((L : ℝ) * eps) ^ 2 := by
  have hnorm := norm_shiftedFiniteSum_remove_phase_le
    base modified phase correction n L eps hfactor hphase hmodified hcorrection hslow
  simp only [Complex.normSq_eq_norm_sq]
  have hU := norm_nonneg
    (shiftedFiniteSum (fun j ↦ modified j * correction j) n L)
  have hV := norm_nonneg (shiftedFiniteSum base n L)
  have hLeps : 0 ≤ (L : ℝ) * eps := mul_nonneg (Nat.cast_nonneg L) heps
  have hsq := (sq_le_sq₀ hU (add_nonneg hV hLeps)).2 hnorm
  nlinarith [sq_nonneg
    (‖shiftedFiniteSum base n L‖ - (L : ℝ) * eps)]

/-- Weighted shifted-sum energy for one interval length. -/
def weightedShiftedEnergy (F : ℕ → ℂ) (centers : Finset ℕ)
    (weight : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ n ∈ centers, weight n * Complex.normSq (shiftedFiniteSum F n L)

/-- Medium-length average of the preceding shifted-sum energy. -/
def mediumWeightedShiftedEnergy (F : ℕ → ℂ) (centers : Finset ℕ)
    (weight : ℕ → ℝ) (H : ℕ) : ℝ :=
  (H : ℝ)⁻¹ *
    ∑ L ∈ Finset.Ioc H (2 * H), weightedShiftedEnergy F centers weight L

/-- Uniform phase removal over all medium lengths.  The error is
`8 H² eps²` times the total center weight; consequently the main constant
stays independent of the conductor, its prime-power exponent, and the
eventual scale. -/
theorem mediumWeightedShiftedEnergy_remove_phase_le
    (base modified phase correction : ℕ → ℂ)
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ}
    (hH : 0 < H) (eps : ℝ) (heps : 0 ≤ eps)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hfactor : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L,
        base (n + j) = modified (n + j) * phase (n + j) * correction (n + j))
    (hphase : ∀ n ∈ centers, ‖phase n‖ = 1)
    (hmodified : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖modified (n + j)‖ ≤ 1)
    (hcorrection : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖correction (n + j)‖ ≤ 1)
    (hslow : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖phase (n + j) - phase n‖ ≤ eps) :
    mediumWeightedShiftedEnergy (fun j ↦ modified j * correction j)
        centers weight H ≤
      2 * mediumWeightedShiftedEnergy base centers weight H +
        8 * (H : ℝ) ^ 2 * eps ^ 2 * ∑ n ∈ centers, weight n := by
  have hL (L : ℕ) (hLIoc : L ∈ Finset.Ioc H (2 * H)) :
      weightedShiftedEnergy (fun j ↦ modified j * correction j)
          centers weight L ≤
        2 * weightedShiftedEnergy base centers weight L +
          8 * (H : ℝ) ^ 2 * eps ^ 2 * ∑ n ∈ centers, weight n := by
    unfold weightedShiftedEnergy
    calc
      (∑ n ∈ centers, weight n *
          Complex.normSq
            (shiftedFiniteSum (fun j ↦ modified j * correction j) n L)) ≤
          ∑ n ∈ centers, weight n *
            (2 * Complex.normSq (shiftedFiniteSum base n L) +
              2 * ((L : ℝ) * eps) ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (normSq_shiftedFiniteSum_remove_phase_le
            base modified phase correction n L eps heps
            (hfactor n hn L hLIoc) (hphase n hn)
            (hmodified n hn L hLIoc) (hcorrection n hn L hLIoc)
            (hslow n hn L hLIoc)) (hweight n hn)
      _ ≤ ∑ n ∈ centers, weight n *
            (2 * Complex.normSq (shiftedFiniteSum base n L) +
              8 * (H : ℝ) ^ 2 * eps ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left _ (hweight n hn)
        have hLR : (L : ℝ) ≤ 2 * H := by
          exact_mod_cast (Finset.mem_Ioc.mp hLIoc).2
        have hL0 : (0 : ℝ) ≤ L := by positivity
        have hH0 : (0 : ℝ) ≤ H := by positivity
        nlinarith [sq_le_sq₀ hL0 (by positivity : (0 : ℝ) ≤ 2 * H) |>.2 hLR]
      _ = 2 * (∑ n ∈ centers,
            weight n * Complex.normSq (shiftedFiniteSum base n L)) +
          8 * (H : ℝ) ^ 2 * eps ^ 2 * ∑ n ∈ centers, weight n := by
        calc
          (∑ n ∈ centers, weight n *
              (2 * Complex.normSq (shiftedFiniteSum base n L) +
                8 * (H : ℝ) ^ 2 * eps ^ 2)) =
              ∑ n ∈ centers,
                (2 * (weight n * Complex.normSq (shiftedFiniteSum base n L)) +
                  (8 * (H : ℝ) ^ 2 * eps ^ 2) * weight n) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  unfold mediumWeightedShiftedEnergy
  have hsum := Finset.sum_le_sum fun L hLIoc ↦ hL L hLIoc
  have hHinv : 0 ≤ (H : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg H)
  refine (mul_le_mul_of_nonneg_left hsum hHinv).trans_eq ?_
  have hcard : (Finset.Ioc H (2 * H)).card = H := by
    rw [Nat.card_Ioc]
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, hcard, nsmul_eq_mul]
  field_simp

/-! ## Pointwise medium weighted local energy -/

/-- The finite weighted energy of length-`L` translated sums for one prime
assignment. -/
def weightedLocalEnergy (centers : Finset ℕ) (weight : ℕ → ℝ)
    (L : ℕ) (z : PrimeAssignment) : ℝ :=
  ∑ n ∈ centers, weight n * circleLocalIncrementEnergy n L z

theorem continuous_weightedLocalEnergy
    (centers : Finset ℕ) (weight : ℕ → ℝ) (L : ℕ) :
    Continuous (weightedLocalEnergy centers weight L) := by
  unfold weightedLocalEnergy
  exact continuous_finsetSum centers fun n _ ↦
    continuous_const.mul (continuous_circleLocalIncrementEnergy n L)

theorem integrable_weightedLocalEnergy
    (mu : ProbabilityMeasure PrimeAssignment)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (L : ℕ) :
    Integrable (weightedLocalEnergy centers weight L)
      (mu : Measure PrimeAssignment) :=
  (continuous_weightedLocalEnergy centers weight L).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))

theorem weightedLocalEnergy_nonneg
    (centers : Finset ℕ) (weight : ℕ → ℝ) (L : ℕ)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n) (z : PrimeAssignment) :
    0 ≤ weightedLocalEnergy centers weight L z := by
  unfold weightedLocalEnergy
  exact Finset.sum_nonneg fun n hn ↦
    mul_nonneg (hweight n hn) (sq_nonneg _)

/-- Integration of the pointwise energy is exactly the weighted local
mean-square quantity. -/
theorem integral_weightedLocalEnergy
    (mu : ProbabilityMeasure PrimeAssignment)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (L : ℕ) :
    ∫ z, weightedLocalEnergy centers weight L z
        ∂(mu : Measure PrimeAssignment) =
      weightedLocalMeanSquare mu centers weight L := by
  unfold weightedLocalEnergy weightedLocalMeanSquare
  rw [integral_finsetSum centers fun n _ ↦
    (integrable_circleLocalIncrementEnergy mu n L).const_mul (weight n)]
  simp only [integral_const_mul, meanSquareLocalIncrement]

/-- Average the local energy over all medium lengths `H < L ≤ 2H`. -/
def mediumWeightedLocalEnergy (centers : Finset ℕ) (weight : ℕ → ℝ)
    (H : ℕ) (z : PrimeAssignment) : ℝ :=
  (H : ℝ)⁻¹ *
    ∑ L ∈ Finset.Ioc H (2 * H), weightedLocalEnergy centers weight L z

/-- The pointwise local energy is the shifted-sum energy of the prime
extension. -/
theorem weightedLocalEnergy_eq_weightedShiftedEnergy
    (z : PrimeAssignment) (centers : Finset ℕ) (weight : ℕ → ℝ) (L : ℕ) :
    weightedLocalEnergy centers weight L z =
      weightedShiftedEnergy (fun j ↦ (primeExtension z j : ℂ)) centers weight L := by
  unfold weightedLocalEnergy weightedShiftedEnergy circleLocalIncrementEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [circleLocalIncrement_eq_shiftedFiniteSum]
  simp only [Complex.normSq_eq_norm_sq]

theorem mediumWeightedLocalEnergy_eq_mediumWeightedShiftedEnergy
    (z : PrimeAssignment) (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    mediumWeightedLocalEnergy centers weight H z =
      mediumWeightedShiftedEnergy
        (fun j ↦ (primeExtension z j : ℂ)) centers weight H := by
  unfold mediumWeightedLocalEnergy mediumWeightedShiftedEnergy
  apply congrArg ((H : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro L hL
  exact weightedLocalEnergy_eq_weightedShiftedEnergy z centers weight L

theorem continuous_mediumWeightedLocalEnergy
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Continuous (mediumWeightedLocalEnergy centers weight H) := by
  unfold mediumWeightedLocalEnergy
  exact continuous_const.mul <|
    continuous_finsetSum (Finset.Ioc H (2 * H)) fun L _ ↦
      continuous_weightedLocalEnergy centers weight L

theorem integrable_mediumWeightedLocalEnergy
    (mu : ProbabilityMeasure PrimeAssignment)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Integrable (mediumWeightedLocalEnergy centers weight H)
      (mu : Measure PrimeAssignment) :=
  (continuous_mediumWeightedLocalEnergy centers weight H).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))

theorem mediumWeightedLocalEnergy_nonneg
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ}
    (hweight : ∀ n ∈ centers, 0 ≤ weight n) (z : PrimeAssignment) :
    0 ≤ mediumWeightedLocalEnergy centers weight H z := by
  unfold mediumWeightedLocalEnergy
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg H)) <|
    Finset.sum_nonneg fun L _ ↦ weightedLocalEnergy_nonneg centers weight L hweight z

/-- Pull the pointwise medium energy back to the compact character model in
which Section 3 selects its pretentious event. -/
def compactMediumWeightedLocalEnergy
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (g : CompactCircleCharacter) : ℝ :=
  mediumWeightedLocalEnergy centers weight H
    (primeAssignmentOfCompactCircleCharacter g)

theorem continuous_compactMediumWeightedLocalEnergy
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Continuous (compactMediumWeightedLocalEnergy centers weight H) := by
  exact (continuous_mediumWeightedLocalEnergy centers weight H).comp
    continuous_primeAssignmentOfCompactCircleCharacter

theorem integrable_compactMediumWeightedLocalEnergy
    (mu : ProbabilityMeasure CompactCircleCharacter)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Integrable (compactMediumWeightedLocalEnergy centers weight H)
      (mu : Measure CompactCircleCharacter) :=
  (continuous_compactMediumWeightedLocalEnergy centers weight H).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))

theorem compactMediumWeightedLocalEnergy_nonneg
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ}
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (g : CompactCircleCharacter) :
    0 ≤ compactMediumWeightedLocalEnergy centers weight H g :=
  mediumWeightedLocalEnergy_nonneg centers weight hweight _

/-- Pullback along the canonical prime-coordinate law preserves the medium
weighted energy integral. -/
theorem integral_compactMediumWeightedLocalEnergy_eq_map
    (mu : ProbabilityMeasure CompactCircleCharacter)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    ∫ g, compactMediumWeightedLocalEnergy centers weight H g
        ∂(mu : Measure CompactCircleCharacter) =
      ∫ z, mediumWeightedLocalEnergy centers weight H z
        ∂(primeAssignmentLaw mu : Measure PrimeAssignment) := by
  unfold compactMediumWeightedLocalEnergy primeAssignmentLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    continuous_primeAssignmentOfCompactCircleCharacter.measurable.aemeasurable
    (continuous_mediumWeightedLocalEnergy centers weight H).aestronglyMeasurable]

/-! ## Expected bound and Markov selection -/

/-- The stochastic prefix bound controls the whole medium-length average.
The constant is independent of `H`, the center set, and all later conductor
and residue parameters. -/
theorem integral_compactMediumWeightedLocalEnergy_le
    (mu : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C ^ 2)
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ}
    (hH : 0 < H) (hweight : ∀ n ∈ centers, 0 ≤ weight n) :
    ∫ g, compactMediumWeightedLocalEnergy centers weight H g
        ∂(mu : Measure CompactCircleCharacter) ≤
      4 * C ^ 2 * ∑ n ∈ centers, weight n := by
  rw [integral_compactMediumWeightedLocalEnergy_eq_map]
  unfold mediumWeightedLocalEnergy
  rw [integral_const_mul]
  rw [integral_finsetSum (Finset.Ioc H (2 * H)) fun L _ ↦
    integrable_weightedLocalEnergy (primeAssignmentLaw mu) centers weight L]
  simp only [integral_weightedLocalEnergy]
  have hterm (L : ℕ) :
      weightedLocalMeanSquare (primeAssignmentLaw mu) centers weight L ≤
        4 * C ^ 2 * ∑ n ∈ centers, weight n := by
    exact weightedLocalMeanSquare_primeAssignmentLaw_le
      mu centers weight L (C ^ 2) hweight hbound
  calc
    (H : ℝ)⁻¹ *
        ∑ L ∈ Finset.Ioc H (2 * H),
          weightedLocalMeanSquare (primeAssignmentLaw mu) centers weight L ≤
        (H : ℝ)⁻¹ *
          ∑ _L ∈ Finset.Ioc H (2 * H),
            (4 * C ^ 2 * ∑ n ∈ centers, weight n) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun L _ ↦ hterm L) (inv_nonneg.mpr (Nat.cast_nonneg H))
    _ = 4 * C ^ 2 * ∑ n ∈ centers, weight n := by
      have hcard : (Finset.Ioc H (2 * H)).card = H := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard, hH.ne', nsmul_eq_mul]

/-- Markov's inequality for the medium weighted local energy. -/
theorem measure_compactMediumWeightedLocalEnergy_ge_le
    (mu : ProbabilityMeasure CompactCircleCharacter) (C B W : ℝ)
    (hB : 0 < B) (hW : 0 < W)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C ^ 2)
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = W) :
    (mu : Measure CompactCircleCharacter)
        {g | B * W ≤ compactMediumWeightedLocalEnergy centers weight H g} ≤
      ENNReal.ofReal (4 * C ^ 2 / B) := by
  have hBW : 0 < B * W := mul_pos hB hW
  have hInt := integrable_compactMediumWeightedLocalEnergy mu centers weight H
  have hScaled := (hInt.div_const (B * W)).measure_le_integral
    (f_nonneg := ae_of_all _ fun g ↦ div_nonneg
      (compactMediumWeightedLocalEnergy_nonneg centers weight hweight g) hBW.le)
    (s := {g | B * W ≤ compactMediumWeightedLocalEnergy centers weight H g})
    (hs := fun g hg ↦ by
      rw [le_div_iff₀ hBW, one_mul]
      exact hg)
  refine hScaled.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  have hMean := integral_compactMediumWeightedLocalEnergy_le
    mu C hbound centers weight hH hweight
  rw [hweightSum] at hMean
  have hBWnonneg : 0 ≤ B * W := hBW.le
  calc
    (∫ g, compactMediumWeightedLocalEnergy centers weight H g
        ∂(mu : Measure CompactCircleCharacter)) / (B * W) ≤
        (4 * C ^ 2 * W) / (B * W) :=
      div_le_div_of_nonneg_right hMean hBWnonneg
    _ = 4 * C ^ 2 / B := by field_simp

/-- Intersect a previously selected event with the finite-energy Markov
event.  This is the precise common-sample step needed in Section 4. -/
theorem exists_mem_and_compactMediumWeightedLocalEnergy_lt
    (mu : ProbabilityMeasure CompactCircleCharacter) (C B W : ℝ)
    (hB : 0 < B) (hW : 0 < W)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C ^ 2)
    (centers : Finset ℕ) (weight : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = W)
    (G : Set CompactCircleCharacter) (δ : ℝ≥0∞)
    (hG : (mu : Measure CompactCircleCharacter) Gᶜ ≤ δ)
    (hsmall : δ + ENNReal.ofReal (4 * C ^ 2 / B) < 1) :
    ∃ g ∈ G, compactMediumWeightedLocalEnergy centers weight H g < B * W := by
  let E : Set CompactCircleCharacter :=
    {g | compactMediumWeightedLocalEnergy centers weight H g < B * W}
  have hE : (mu : Measure CompactCircleCharacter) Eᶜ ≤
      ENNReal.ofReal (4 * C ^ 2 / B) := by
    have hmarkov := measure_compactMediumWeightedLocalEnergy_ge_le
      mu C B W hB hW hbound centers weight hH hweight hweightSum
    simpa only [E, Set.compl_ofPred, not_lt] using hmarkov
  have hinter : (mu : Measure CompactCircleCharacter) (G ∩ E)ᶜ ≤
      δ + ENNReal.ofReal (4 * C ^ 2 / B) := by
    rw [Set.compl_inter]
    exact (measure_union_le _ _).trans (add_le_add hG hE)
  obtain ⟨g, hgG, hgE⟩ := set_nonempty_of_probability_compl_le mu hinter hsmall
  exact ⟨g, hgG, hgE⟩

end

end Erdos67
