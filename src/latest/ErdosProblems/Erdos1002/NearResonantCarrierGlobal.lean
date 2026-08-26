import ErdosProblems.Erdos1002.NearResonantActiveSparsity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global dyadic assembly for the shifted near-resonant carriers

This file combines the actual physical ingredients proved in the preceding
modules.  Denominator blocks are indexed by exponents `s ∈ [2,M+2)`, so the
block is `(2^(s-1),2^s]`.  The common carrier annuli have overlap at most
four.  Their complements are controlled by the literal growing Gevrey order,
while the unprojected block energy uses the reduced-rational packing bound.

No abstract carrier sequence or sparsity premise occurs below.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

private theorem fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt_global
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      unitFourierCoefficientInt f n := by
  rw [fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficientInt
  norm_num [fourier_coe_apply, paperExp]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  have hstar :
      (starRingEnd ℂ)
          (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) =
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha))) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_mul, map_ofNat, Complex.conj_I]
    ring
  change
    (starRingEnd ℂ)
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) *
      f alpha =
    f alpha *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha)))
  rw [hstar]
  ring

/-- Parseval in the exact coefficient-energy representation used by the
carrier projection lemmas. -/
theorem coefficientEnergy_unitFourierCoefficientInt_eq_integral
    (f : ℝ → ℂ) (hf : Continuous f) :
    coefficientEnergy (unitFourierCoefficientInt f) =
      ENNReal.ofReal (∫ alpha in (0 : ℝ)..1, ‖f alpha‖ ^ 2) := by
  have hmem : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hmeas : AEStronglyMeasurable f
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      hf.aestronglyMeasurable.restrict
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    exact hf.norm.pow 2 |>.integrableOn_Ioc
  have hsum := hasSum_sq_fourierCoeffOn
    (by norm_num : (0 : ℝ) < 1) hmem
  have hrealSummable : Summable fun n : ℤ ↦
      ‖unitFourierCoefficientInt f n‖ ^ 2 := by
    apply hsum.summable.congr
    intro n
    rw [fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt_global]
  unfold coefficientEnergy
  calc
    (∑' n : ℤ, ENNReal.ofReal (‖unitFourierCoefficientInt f n‖ ^ 2)) =
        ENNReal.ofReal
          (∑' n : ℤ, ‖unitFourierCoefficientInt f n‖ ^ 2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hrealSummable]
    _ = ENNReal.ofReal (∫ alpha in (0 : ℝ)..1, ‖f alpha‖ ^ 2) := by
      congr 1
      have hsumEq := hsum.tsum_eq
      norm_num at hsumEq
      simpa only [fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt_global]
        using! hsumEq

/-- Exponents of the dyadic blocks `(2^(s-1),2^s]`, starting at `s=2`.
The omitted denominators `1,2` are treated as a fixed finite remainder. -/
def nearCarrierDyadicExponents (M : ℕ) : Finset ℕ :=
  Finset.Ico 2 (M + 2)

@[simp] theorem card_nearCarrierDyadicExponents (M : ℕ) :
    (nearCarrierDyadicExponents M).card = M := by
  simp [nearCarrierDyadicExponents, Nat.card_Ico]

/-- The actual physical carrier block at exponent `s`. -/
def nearCarrierDyadicBlock
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (s : ℕ) : ℝ → ℂ :=
  smoothNearPrimitivePoleCarrierTail
    N ell a ε ((2 ^ s) / 2) (2 ^ s)

/-- Integer Fourier coefficients of one actual block. -/
def nearCarrierDyadicBlockCoefficients
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (s : ℕ) : ℤ → ℂ :=
  unitFourierCoefficientInt (nearCarrierDyadicBlock N ell a ε s)

theorem coefficientEnergy_nearCarrierDyadicBlockCoefficients_eq
    (N s : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    coefficientEnergy (nearCarrierDyadicBlockCoefficients N ell a ε s) =
      ENNReal.ofReal
        (∫ alpha in (0 : ℝ)..1,
          ‖nearCarrierDyadicBlock N ell a ε s alpha‖ ^ 2) := by
  exact coefficientEnergy_unitFourierCoefficientInt_eq_integral _
    (smoothNearPrimitivePoleCarrierTail_continuous
      N ((2 ^ s) / 2) (2 ^ s) ell a ε ha haε)

/-- The exact physical block energy with the active-denominator packing
bound inserted. -/
theorem coefficientEnergy_nearCarrierDyadicBlockCoefficients_le
    (N M s : ℕ) (ell : ℤ) (a ε : ℝ)
    (hs : s ∈ nearCarrierDyadicExponents M)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    coefficientEnergy (nearCarrierDyadicBlockCoefficients N ell a ε s) ≤
      ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
  have hsBounds := Finset.mem_Ico.mp hs
  have hP : 4 ≤ 2 ^ s := by
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hsBounds.1)
  rw [coefficientEnergy_nearCarrierDyadicBlockCoefficients_eq
    N s ell a ε ha haε]
  apply ENNReal.ofReal_le_ofReal
  exact integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le_scalar
    N (2 ^ s) ell a ε hP ha hε haε hεhalf

/-- Every selected shifted power-of-two annulus has overlap at most four. -/
theorem frequencyOverlapCount_nearCarrierDyadicExponents_le_four
    (N M : ℕ) (ell : ℤ) (hN : 0 < N) (hell : ell ≠ 0) (n : ℤ) :
    frequencyOverlapCount (nearCarrierDyadicExponents M)
      (fun s ↦ nearCarrierAnnulus N ell (2 ^ s)) n ≤ 4 := by
  classical
  unfold frequencyOverlapCount
  have hsubset :
      (nearCarrierDyadicExponents M).filter
          (fun s ↦ n ∈ nearCarrierAnnulus N ell (2 ^ s)) ⊆
        (Finset.range (M + 2)).filter
          (fun s ↦ n ∈ nearCarrierAnnulus N ell (2 ^ s)) := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by
      have := (Finset.mem_Ico.mp hs'.1).2
      simpa [nearCarrierDyadicExponents] using! this), hs'.2⟩
  exact (Finset.card_le_card hsubset).trans
    (frequencyOverlapCount_nearCarrierAnnulus_pow_two_le_four
      N ell (M + 2) hN hell n)

/-- Energy of the sum of all annular projections. -/
theorem coefficientEnergy_sum_projected_nearCarrierDyadicBlock_le
    (N M : ℕ) (ell : ℤ) (a ε : ℝ)
    (hN : 0 < N) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    coefficientEnergy (fun n ↦
        ∑ s ∈ nearCarrierDyadicExponents M,
          projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
            (nearCarrierDyadicBlockCoefficients N ell a ε s) n) ≤
      4 * M * ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
  let S := nearCarrierDyadicExponents M
  let B : ENNReal := ENNReal.ofReal
    (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)))
  have hoverlap : ∀ n : ℤ,
      frequencyOverlapCount S
        (fun s ↦ nearCarrierAnnulus N ell (2 ^ s)) n ≤ 4 := by
    intro n
    simpa only [S] using!
      frequencyOverlapCount_nearCarrierDyadicExponents_le_four
        N M ell hN hell n
  have hproj := coefficientEnergy_sum_projected_le_overlap
    S (fun s ↦ nearCarrierAnnulus N ell (2 ^ s))
      (fun s ↦ nearCarrierDyadicBlockCoefficients N ell a ε s) 4 hoverlap
  calc
    coefficientEnergy (fun n ↦
        ∑ s ∈ nearCarrierDyadicExponents M,
          projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
            (nearCarrierDyadicBlockCoefficients N ell a ε s) n) ≤
      4 * ∑ s ∈ S,
        coefficientEnergy
          (nearCarrierDyadicBlockCoefficients N ell a ε s) := by
        simpa only [S] using! hproj
    _ ≤ 4 * ∑ _s ∈ S, B := by
      gcongr with s hs
      exact coefficientEnergy_nearCarrierDyadicBlockCoefficients_le
        N M s ell a ε (by simpa only [S] using! hs)
          ha hε haε hεhalf
    _ = 4 * M * ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_nearCarrierDyadicExponents]
      dsimp [B]
      ring

/-- Complementary coefficients of one dyadic block. -/
def nearCarrierDyadicBlockLeakageCoefficients
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (s : ℕ) (n : ℤ) : ℂ :=
  nearCarrierDyadicBlockCoefficients N ell a ε s n -
    projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
      (nearCarrierDyadicBlockCoefficients N ell a ε s) n

/-- The blockwise definition above is exactly the already estimated sum of
the individual physical carrier leakages. -/
theorem nearCarrierDyadicBlockLeakageCoefficients_eq_physical
    (N s : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    nearCarrierDyadicBlockLeakageCoefficients N ell a ε s =
      physicalNearCarrierBlockLeakageCoefficients
        N ell a ε (2 ^ s) := by
  funext n
  have hcoeff : nearCarrierDyadicBlockCoefficients N ell a ε s n =
      ∑ p ∈ Finset.Ioc ((2 ^ s) / 2) (2 ^ s),
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n := by
    unfold nearCarrierDyadicBlockCoefficients nearCarrierDyadicBlock
    rw [unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTail
      N ((2 ^ s) / 2) (2 ^ s) ell n a ε ha haε]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTerm]
  unfold nearCarrierDyadicBlockLeakageCoefficients
    physicalNearCarrierBlockLeakageCoefficients
  rw [hcoeff]
  by_cases hn : n ∈ nearCarrierAnnulus N ell (2 ^ s)
  · simp [projectCoefficients, hn, hcoeff]
  · simp [projectCoefficients, hn]

/-- Global complementary leakage over the selected exponent family. -/
def nearCarrierDyadicLeakageCoefficients
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    nearCarrierDyadicBlockLeakageCoefficients N ell a ε s n

/-- The exponentially small one-block bound remains negligible after the
complete finite dyadic summation. -/
theorem eventually_coefficientEnergy_nearCarrierDyadicLeakage_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      coefficientEnergy
          (nearCarrierDyadicLeakageCoefficients
            N M ell (A / L) ε) ≤
        (M : ENNReal) ^ 2 *
          ENNReal.ofReal
            (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
              Real.exp (-(5 / 2 : ℝ) * L)) := by
  have hblockEventually :=
    eventually_coefficientEnergy_physicalNearCarrierBlock_le_coeff_mul_exp
      A ε hA hε hεhalf
  filter_upwards [hblockEventually,
      eventually_ge_atTop (max (1 : ℝ) (4 * A / ε))] with L hblock hL
  intro N M ell hN hell hNL hcut
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have ha : 0 < A / L := div_pos hA hLpos
  have hthreshold : 4 * A / ε ≤ L := (le_max_right _ _).trans hL
  have haε : A / L ≤ ε / 4 := by
    rw [div_le_iff₀ hLpos]
    have hfour : 4 * A ≤ ε * L := by
      have := mul_le_mul_of_nonneg_left hthreshold hε.le
      field_simp at this
      nlinarith
    nlinarith
  let S := nearCarrierDyadicExponents M
  let E : ENNReal := ENNReal.ofReal
    (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      Real.exp (-(5 / 2 : ℝ) * L))
  have hindividual : ∀ s ∈ S,
      coefficientEnergy
          (nearCarrierDyadicBlockLeakageCoefficients
            N ell (A / L) ε s) ≤ E := by
    intro s hs
    have hsBounds := Finset.mem_Ico.mp (show s ∈ nearCarrierDyadicExponents M by
      simpa only [S] using! hs)
    have hP : 4 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hsBounds.1
    rw [nearCarrierDyadicBlockLeakageCoefficients_eq_physical
      N s ell (A / L) ε ha haε]
    exact hblock N (2 ^ s) ell hN hP hell hNL
      (hcut s (by simpa only [S] using! hs))
  have hsum := coefficientEnergy_finset_sum_le_card_mul_sum
    S (fun s ↦ nearCarrierDyadicBlockLeakageCoefficients
      N ell (A / L) ε s)
  calc
    coefficientEnergy
        (nearCarrierDyadicLeakageCoefficients N M ell (A / L) ε) ≤
      S.card * ∑ s ∈ S,
        coefficientEnergy
          (nearCarrierDyadicBlockLeakageCoefficients
            N ell (A / L) ε s) := by
      simpa only [nearCarrierDyadicLeakageCoefficients, S] using! hsum
    _ ≤ S.card * ∑ _s ∈ S, E := by
      gcongr with s hs
      exact hindividual s hs
    _ = (M : ENNReal) ^ 2 *
        ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            Real.exp (-(5 / 2 : ℝ) * L)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_nearCarrierDyadicExponents]
      dsimp [E]
      ring

/-- Sum of the unprojected dyadic block coefficients. -/
def nearCarrierDyadicTotalCoefficients
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    nearCarrierDyadicBlockCoefficients N ell a ε s n

/-- Physical-space sum of the same dyadic blocks. -/
def nearCarrierDyadicTotal
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) (alpha : ℝ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    nearCarrierDyadicBlock N ell a ε s alpha

theorem nearCarrierDyadicTotal_continuous
    (N M : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    Continuous (nearCarrierDyadicTotal N M ell a ε) := by
  unfold nearCarrierDyadicTotal
  apply continuous_finset_sum
  intro s _hs
  exact smoothNearPrimitivePoleCarrierTail_continuous
    N ((2 ^ s) / 2) (2 ^ s) ell a ε ha haε

/-- The selected dyadic blocks partition exactly the denominator interval
`(2,2^(M+1)]`. -/
theorem nearCarrierDyadicTotal_eq_tail
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) :
    nearCarrierDyadicTotal N M ell a ε =
      smoothNearPrimitivePoleCarrierTail N ell a ε 2 (2 ^ (M + 1)) := by
  induction M with
  | zero =>
      funext alpha
      simp [nearCarrierDyadicTotal, nearCarrierDyadicExponents,
        smoothNearPrimitivePoleCarrierTail]
  | succ M ih =>
      have hexponents : nearCarrierDyadicExponents (M + 1) =
          insert (M + 2) (nearCarrierDyadicExponents M) := by
        ext s
        simp only [nearCarrierDyadicExponents, Finset.mem_Ico,
          Finset.mem_insert]
        omega
      have hnew : M + 2 ∉ nearCarrierDyadicExponents M := by
        simp [nearCarrierDyadicExponents]
      have hpowDiv : 2 ^ (M + 2) / 2 = 2 ^ (M + 1) := by
        rw [pow_succ]
        omega
      funext alpha
      unfold nearCarrierDyadicTotal
      rw [hexponents, Finset.sum_insert hnew]
      change nearCarrierDyadicBlock N ell a ε (M + 2) alpha +
          nearCarrierDyadicTotal N M ell a ε alpha = _
      rw [congrFun ih alpha]
      unfold nearCarrierDyadicBlock smoothNearPrimitivePoleCarrierTail
      rw [hpowDiv]
      have hdisjoint : Disjoint
          (Finset.Ioc 2 (2 ^ (M + 1)))
          (Finset.Ioc (2 ^ (M + 1)) (2 ^ (M + 2))) := by
        exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
      rw [add_comm, ← Finset.sum_union hdisjoint,
        Finset.Ioc_union_Ioc_eq_Ioc]
      · exact (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ M + 1))
      · exact (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : M + 1 ≤ M + 2))

/-- Coefficients of the physical dyadic sum agree with the explicitly
summed block coefficients. -/
theorem unitFourierCoefficientInt_nearCarrierDyadicTotal
    (N M : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    unitFourierCoefficientInt (nearCarrierDyadicTotal N M ell a ε) =
      nearCarrierDyadicTotalCoefficients N M ell a ε := by
  funext n
  unfold unitFourierCoefficientInt nearCarrierDyadicTotal
    nearCarrierDyadicTotalCoefficients nearCarrierDyadicBlockCoefficients
  rw [show (fun alpha ↦
      (∑ s ∈ nearCarrierDyadicExponents M,
          nearCarrierDyadicBlock N ell a ε s alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      (fun alpha ↦ ∑ s ∈ nearCarrierDyadicExponents M,
        nearCarrierDyadicBlock N ell a ε s alpha *
          paperExp (-(n : ℝ) * alpha)) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  · rfl
  · intro s _hs
    have hphase : Continuous
        (fun alpha : ℝ ↦ paperExp (-(n : ℝ) * alpha)) := by
      unfold paperExp
      fun_prop
    exact ((smoothNearPrimitivePoleCarrierTail_continuous
      N ((2 ^ s) / 2) (2 ^ s) ell a ε ha haε).mul hphase).intervalIntegrable 0 1

theorem coefficientEnergy_nearCarrierDyadicTotalCoefficients_eq_integral
    (N M : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    coefficientEnergy (nearCarrierDyadicTotalCoefficients N M ell a ε) =
      ENNReal.ofReal
        (∫ alpha in (0 : ℝ)..1,
          ‖nearCarrierDyadicTotal N M ell a ε alpha‖ ^ 2) := by
  rw [← unitFourierCoefficientInt_nearCarrierDyadicTotal
    N M ell a ε ha haε]
  exact coefficientEnergy_unitFourierCoefficientInt_eq_integral _
    (nearCarrierDyadicTotal_continuous N M ell a ε ha haε)

/-- Sum of the annularly projected dyadic block coefficients. -/
def nearCarrierDyadicProjectedCoefficients
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
      (nearCarrierDyadicBlockCoefficients N ell a ε s) n

theorem nearCarrierDyadicTotalCoefficients_eq_projected_add_leakage
    (N M : ℕ) (ell : ℤ) (a ε : ℝ) :
    nearCarrierDyadicTotalCoefficients N M ell a ε =
      fun n ↦ nearCarrierDyadicProjectedCoefficients N M ell a ε n +
        nearCarrierDyadicLeakageCoefficients N M ell a ε n := by
  funext n
  unfold nearCarrierDyadicTotalCoefficients
    nearCarrierDyadicProjectedCoefficients
    nearCarrierDyadicLeakageCoefficients
    nearCarrierDyadicBlockLeakageCoefficients
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Squared triangle inequality at the coefficient-energy level. -/
theorem coefficientEnergy_add_le_two
    (c d : ℤ → ℂ) :
    coefficientEnergy (fun n ↦ c n + d n) ≤
      2 * (coefficientEnergy c + coefficientEnergy d) := by
  let f : Fin 2 → ℤ → ℂ := fun i ↦ if i = 0 then c else d
  have h := coefficientEnergy_finset_sum_le_card_mul_sum
    (Finset.univ : Finset (Fin 2)) f
  simpa only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two,
    f, Fin.isValue, ↓reduceIte, OfNat.ofNat, Nat.cast_ofNat] using! h

/-- Weighted Cauchy--Schwarz followed by Tonelli for coefficient sequences.
Unlike `coefficientEnergy_finset_sum_le_card_mul_sum`, this estimate retains
the summable carrier weights and is therefore uniform in a growing carrier
cutoff. -/
theorem coefficientEnergy_finset_sum_le_weighted
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℤ → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
      ENNReal.ofReal (∑ i ∈ s, w i) *
        ∑ i ∈ s, (ENNReal.ofReal (w i))⁻¹ * coefficientEnergy (c i) := by
  have hswap (g : ι → ℤ → ENNReal) :
      (∑' n : ℤ, ∑ i ∈ s, g i n) =
        ∑ i ∈ s, ∑' n : ℤ, g i n := by
    clear hw w c
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, ENNReal.tsum_add, ih]
  unfold coefficientEnergy
  calc
    (∑' n : ℤ, ENNReal.ofReal (‖∑ i ∈ s, c i n‖ ^ 2)) ≤
        ∑' n : ℤ,
          ENNReal.ofReal (∑ i ∈ s, w i) *
            ∑ i ∈ s,
              ENNReal.ofReal (‖c i n‖ ^ 2 / w i) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hnorm : ‖∑ i ∈ s, c i n‖ ≤ ∑ i ∈ s, ‖c i n‖ :=
        norm_sum_le _ _
      have hcauchy : (∑ i ∈ s, ‖c i n‖) ^ 2 ≤
          (∑ i ∈ s, w i) *
            ∑ i ∈ s, ‖c i n‖ ^ 2 / w i := by
        apply sum_sq_le_sum_mul_sum_of_sq_eq_mul s
        · intro i hi
          exact (hw i hi).le
        · intro i hi
          exact div_nonneg (sq_nonneg _) (hw i hi).le
        · intro i hi
          field_simp [(hw i hi).ne']
      have hreal : ‖∑ i ∈ s, c i n‖ ^ 2 ≤
          (∑ i ∈ s, w i) *
            ∑ i ∈ s, ‖c i n‖ ^ 2 / w i :=
        (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy
      calc
        ENNReal.ofReal (‖∑ i ∈ s, c i n‖ ^ 2) ≤
            ENNReal.ofReal
              ((∑ i ∈ s, w i) *
                ∑ i ∈ s, ‖c i n‖ ^ 2 / w i) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (∑ i ∈ s, w i) *
            ∑ i ∈ s,
              ENNReal.ofReal (‖c i n‖ ^ 2 / w i) := by
          rw [ENNReal.ofReal_mul
            (Finset.sum_nonneg fun i hi ↦ (hw i hi).le)]
          congr 1
          apply ENNReal.ofReal_sum_of_nonneg
          intro i hi
          exact div_nonneg (sq_nonneg _) (hw i hi).le
    _ = ENNReal.ofReal (∑ i ∈ s, w i) *
        ∑ i ∈ s, (ENNReal.ofReal (w i))⁻¹ *
          (∑' n : ℤ, ENNReal.ofReal (‖c i n‖ ^ 2)) := by
      rw [ENNReal.tsum_mul_left, hswap]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_div_of_pos (hw i hi)]
      simp only [div_eq_mul_inv, mul_comm]

/-- Uniform weighted aggregation when each summand has energy at most its
weight squared times one common bound. -/
theorem coefficientEnergy_finset_sum_le_weighted_common
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℤ → ℂ) (w : ι → ℝ)
    (B : ENNReal) (hw : ∀ i ∈ s, 0 < w i)
    (hc : ∀ i ∈ s,
      coefficientEnergy (c i) ≤ ENNReal.ofReal ((w i) ^ 2) * B) :
    coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
      ENNReal.ofReal ((∑ i ∈ s, w i) ^ 2) * B := by
  have hweighted := coefficientEnergy_finset_sum_le_weighted s c w hw
  have hterm (i : ι) (hi : i ∈ s) :
      (ENNReal.ofReal (w i))⁻¹ * coefficientEnergy (c i) ≤
        ENNReal.ofReal (w i) * B := by
    calc
      (ENNReal.ofReal (w i))⁻¹ * coefficientEnergy (c i) ≤
          (ENNReal.ofReal (w i))⁻¹ *
            (ENNReal.ofReal ((w i) ^ 2) * B) := by
        exact mul_le_mul_right (hc i hi) _
      _ = ENNReal.ofReal (w i) * B := by
        rw [ENNReal.ofReal_pow (hw i hi).le]
        have hne : ENNReal.ofReal (w i) ≠ 0 := by
          intro hzero
          have := ENNReal.ofReal_eq_zero.mp hzero
          linarith [hw i hi]
        rw [pow_two, mul_assoc,
          ENNReal.inv_mul_cancel_left hne ENNReal.ofReal_ne_top]
  have hsum :
      (∑ i ∈ s, (ENNReal.ofReal (w i))⁻¹ * coefficientEnergy (c i)) ≤
        ∑ i ∈ s, ENNReal.ofReal (w i) * B := by
    exact Finset.sum_le_sum fun i hi ↦ hterm i hi
  calc
    coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
        ENNReal.ofReal (∑ i ∈ s, w i) *
          ∑ i ∈ s, (ENNReal.ofReal (w i))⁻¹ *
            coefficientEnergy (c i) := hweighted
    _ ≤ ENNReal.ofReal (∑ i ∈ s, w i) *
          ∑ i ∈ s, ENNReal.ofReal (w i) * B := by
      exact mul_le_mul_right hsum _
    _ = ENNReal.ofReal ((∑ i ∈ s, w i) ^ 2) * B := by
      have hsumNonneg : 0 ≤ ∑ i ∈ s, w i :=
        Finset.sum_nonneg fun i hi ↦ (hw i hi).le
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i hi ↦ (hw i hi).le), ENNReal.ofReal_pow hsumNonneg]
      ring

/-- Complete shifted-carrier coefficient energy over all low dyadic blocks.
The first term is the bounded-overlap main part; the second is the fully
summed Gevrey leakage. -/
theorem eventually_coefficientEnergy_nearCarrierDyadicTotal_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      coefficientEnergy
          (nearCarrierDyadicTotalCoefficients
            N M ell (A / L) ε) ≤
        2 *
          (4 * M * ENNReal.ofReal
              (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                ((2 * nearGevreyProfileConstant) ^ 2 *
                  (32 / (A / L)))) +
            (M : ENNReal) ^ 2 *
              ENNReal.ofReal
                (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                  Real.exp (-(5 / 2 : ℝ) * L))) := by
  have hleakEventually :=
    eventually_coefficientEnergy_nearCarrierDyadicLeakage_le
      A ε hA hε hεhalf
  filter_upwards [hleakEventually,
      eventually_ge_atTop (max (1 : ℝ) (4 * A / ε))] with L hleak hL
  intro N M ell hN hell hNL hcut
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have ha : 0 < A / L := div_pos hA hLpos
  have hthreshold : 4 * A / ε ≤ L := (le_max_right _ _).trans hL
  have haε : A / L ≤ ε / 4 := by
    rw [div_le_iff₀ hLpos]
    have hfour : 4 * A ≤ ε * L := by
      have := mul_le_mul_of_nonneg_left hthreshold hε.le
      field_simp at this
      nlinarith
    nlinarith
  rw [nearCarrierDyadicTotalCoefficients_eq_projected_add_leakage]
  refine (coefficientEnergy_add_le_two _ _).trans ?_
  gcongr
  · exact coefficientEnergy_sum_projected_nearCarrierDyadicBlock_le
      N M ell (A / L) ε hN hell ha hε haε hεhalf
  · exact hleak N M ell hN hell hNL hcut

/-- Common energy factor after removing the square of one Bernoulli carrier
coefficient. -/
def nearCarrierLowCommonEnergyBound (A L : ℝ) (M : ℕ) : ENNReal :=
  2 *
    (4 * M * ENNReal.ofReal
        (8 * ((2 * nearGevreyProfileConstant) ^ 2 *
          (32 / (A / L)))) +
      (M : ENNReal) ^ 2 *
        ENNReal.ofReal (Real.exp (-(5 / 2 : ℝ) * L)))

/-- Coefficient-sensitive form of the low shifted-carrier estimate.  This
factorization is what permits the infinite Bernoulli carrier family to be
summed without a cardinality loss. -/
theorem eventually_coefficientEnergy_nearCarrierDyadicTotal_le_coeff_sq_mul
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      coefficientEnergy
          (nearCarrierDyadicTotalCoefficients N M ell (A / L) ε) ≤
        ENNReal.ofReal (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
          nearCarrierLowCommonEnergyBound A L M := by
  filter_upwards [eventually_coefficientEnergy_nearCarrierDyadicTotal_le
      A ε hA hε hεhalf] with L hL
  intro N M ell hN hell hNL hcut
  refine (hL N M ell hN hell hNL hcut).trans_eq ?_
  unfold nearCarrierLowCommonEnergyBound
  have hcoeff : 0 ≤ ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 := sq_nonneg _
  have hexp : 0 ≤ Real.exp (-(5 / 2 : ℝ) * L) := (Real.exp_pos _).le
  rw [show
      8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / (A / L))) =
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (8 * ((2 * nearGevreyProfileConstant) ^ 2 *
            (32 / (A / L)))) by ring,
    ENNReal.ofReal_mul hcoeff,
    ENNReal.ofReal_mul hcoeff]
  ring

/-- Physical-space form of the complete low-denominator shifted-carrier
estimate.  This is not merely a bound for a formal Fourier sequence: the
left side is the literal integral of the finite smooth carrier sum over the
unit interval. -/
theorem eventually_integral_nearCarrierDyadicTotal_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      ENNReal.ofReal
          (∫ alpha in (0 : ℝ)..1,
            ‖nearCarrierDyadicTotal N M ell (A / L) ε alpha‖ ^ 2) ≤
        2 *
          (4 * M * ENNReal.ofReal
              (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                ((2 * nearGevreyProfileConstant) ^ 2 *
                  (32 / (A / L)))) +
            (M : ENNReal) ^ 2 *
              ENNReal.ofReal
                (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                  Real.exp (-(5 / 2 : ℝ) * L))) := by
  have henergyEventually :=
    eventually_coefficientEnergy_nearCarrierDyadicTotal_le
      A ε hA hε hεhalf
  filter_upwards [henergyEventually,
      eventually_ge_atTop (max (1 : ℝ) (4 * A / ε))] with
      L henergy hL
  intro N M ell hN hell hNL hcut
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have ha : 0 < A / L := div_pos hA hLpos
  have hthreshold : 4 * A / ε ≤ L := (le_max_right _ _).trans hL
  have haε : A / L ≤ ε / 4 := by
    rw [div_le_iff₀ hLpos]
    have hfour : 4 * A ≤ ε * L := by
      have := mul_le_mul_of_nonneg_left hthreshold hε.le
      field_simp at this
      nlinarith
    nlinarith
  rw [← coefficientEnergy_nearCarrierDyadicTotalCoefficients_eq_integral
    N M ell (A / L) ε ha haε]
  exact henergy N M ell hN hell hNL hcut

/-- The same physical estimate written for the single exact denominator
interval `(2,2^(M+1)]` rather than for its dyadic presentation. -/
theorem eventually_integral_smoothNearPrimitivePoleCarrierTail_low_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      ENNReal.ofReal
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleCarrierTail
              N ell (A / L) ε 2 (2 ^ (M + 1)) alpha‖ ^ 2) ≤
        2 *
          (4 * M * ENNReal.ofReal
              (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                ((2 * nearGevreyProfileConstant) ^ 2 *
                  (32 / (A / L)))) +
            (M : ENNReal) ^ 2 *
              ENNReal.ofReal
                (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                  Real.exp (-(5 / 2 : ℝ) * L))) := by
  filter_upwards [eventually_integral_nearCarrierDyadicTotal_le
      A ε hA hε hεhalf] with L hL
  intro N M ell hN hell hNL hcut
  rw [← nearCarrierDyadicTotal_eq_tail]
  exact hL N M ell hN hell hNL hcut

/-! ## Crude assembly of a short high-denominator dyadic range -/

/-- A consecutive range of dyadic exponents.  It is used above the carrier
separation cutoff, where the number of blocks is only `O(L^(1/3))` and a
direct Cauchy--Schwarz summation is stronger than needed. -/
def nearCarrierDyadicRangeExponents (S H : ℕ) : Finset ℕ :=
  Finset.Ico S (S + H)

@[simp] theorem card_nearCarrierDyadicRangeExponents (S H : ℕ) :
    (nearCarrierDyadicRangeExponents S H).card = H := by
  simp [nearCarrierDyadicRangeExponents, Nat.card_Ico]

def nearCarrierDyadicRangeTotalCoefficients
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicRangeExponents S H,
    nearCarrierDyadicBlockCoefficients N ell a ε s n

def nearCarrierDyadicRangeTotal
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ) (alpha : ℝ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicRangeExponents S H,
    nearCarrierDyadicBlock N ell a ε s alpha

theorem nearCarrierDyadicRangeTotal_continuous
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    Continuous (nearCarrierDyadicRangeTotal N S H ell a ε) := by
  unfold nearCarrierDyadicRangeTotal
  apply continuous_finset_sum
  intro s _hs
  exact smoothNearPrimitivePoleCarrierTail_continuous
    N ((2 ^ s) / 2) (2 ^ s) ell a ε ha haε

/-- Consecutive dyadic blocks are an exact partition, including all endpoint
conventions.  This is the high-range counterpart of
`nearCarrierDyadicTotal_eq_tail`. -/
theorem nearCarrierDyadicRangeTotal_eq_tail
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ) :
    nearCarrierDyadicRangeTotal N S H ell a ε =
      smoothNearPrimitivePoleCarrierTail N ell a ε
        ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) := by
  induction H with
  | zero =>
      funext alpha
      simp [nearCarrierDyadicRangeTotal, nearCarrierDyadicRangeExponents,
        smoothNearPrimitivePoleCarrierTail]
  | succ H ih =>
      have hexponents : nearCarrierDyadicRangeExponents S (H + 1) =
          insert (S + H) (nearCarrierDyadicRangeExponents S H) := by
        ext s
        simp only [nearCarrierDyadicRangeExponents, Finset.mem_Ico,
          Finset.mem_insert]
        omega
      have hnew : S + H ∉ nearCarrierDyadicRangeExponents S H := by
        simp [nearCarrierDyadicRangeExponents]
      have hnext : 2 ^ (S + (H + 1)) / 2 = 2 ^ (S + H) := by
        rw [show S + (H + 1) = S + H + 1 by omega, pow_succ]
        omega
      funext alpha
      unfold nearCarrierDyadicRangeTotal
      rw [hexponents, Finset.sum_insert hnew]
      change nearCarrierDyadicBlock N ell a ε (S + H) alpha +
          nearCarrierDyadicRangeTotal N S H ell a ε alpha = _
      rw [congrFun ih alpha]
      unfold nearCarrierDyadicBlock smoothNearPrimitivePoleCarrierTail
      rw [hnext, add_comm]
      have horder : (2 ^ S) / 2 ≤ (2 ^ (S + H)) / 2 := by
        exact Nat.div_le_div_right
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
      have hdisjoint : Disjoint
          (Finset.Ioc ((2 ^ S) / 2) ((2 ^ (S + H)) / 2))
          (Finset.Ioc ((2 ^ (S + H)) / 2) (2 ^ (S + H))) := by
        exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
      rw [← Finset.sum_union hdisjoint,
        Finset.Ioc_union_Ioc_eq_Ioc horder]
      exact Nat.div_le_self _ _

theorem unitFourierCoefficientInt_nearCarrierDyadicRangeTotal
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    unitFourierCoefficientInt
        (nearCarrierDyadicRangeTotal N S H ell a ε) =
      nearCarrierDyadicRangeTotalCoefficients N S H ell a ε := by
  funext n
  unfold unitFourierCoefficientInt nearCarrierDyadicRangeTotal
    nearCarrierDyadicRangeTotalCoefficients nearCarrierDyadicBlockCoefficients
  rw [show (fun alpha ↦
      (∑ s ∈ nearCarrierDyadicRangeExponents S H,
          nearCarrierDyadicBlock N ell a ε s alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      (fun alpha ↦ ∑ s ∈ nearCarrierDyadicRangeExponents S H,
        nearCarrierDyadicBlock N ell a ε s alpha *
          paperExp (-(n : ℝ) * alpha)) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  · rfl
  · intro s _hs
    have hphase : Continuous
        (fun alpha : ℝ ↦ paperExp (-(n : ℝ) * alpha)) := by
      unfold paperExp
      fun_prop
    exact ((smoothNearPrimitivePoleCarrierTail_continuous
      N ((2 ^ s) / 2) (2 ^ s) ell a ε ha haε).mul hphase).intervalIntegrable 0 1

theorem coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_eq_integral
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    coefficientEnergy
        (nearCarrierDyadicRangeTotalCoefficients N S H ell a ε) =
      ENNReal.ofReal
        (∫ alpha in (0 : ℝ)..1,
          ‖nearCarrierDyadicRangeTotal N S H ell a ε alpha‖ ^ 2) := by
  rw [← unitFourierCoefficientInt_nearCarrierDyadicRangeTotal
    N S H ell a ε ha haε]
  exact coefficientEnergy_unitFourierCoefficientInt_eq_integral _
    (nearCarrierDyadicRangeTotal_continuous N S H ell a ε ha haε)

/-- A short high range costs only the square of its number of dyadic blocks.
In the application `H = O(L^(1/3))`, so after `a=A/L` this is
`O(|v_ell|^2 L^(5/3)/A)=o(L^2)`. -/
theorem coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    coefficientEnergy
        (nearCarrierDyadicRangeTotalCoefficients N S H ell a ε) ≤
      (H : ENNReal) ^ 2 * ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
  let T := nearCarrierDyadicRangeExponents S H
  let B : ENNReal := ENNReal.ofReal
    (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)))
  have hsum := coefficientEnergy_finset_sum_le_card_mul_sum
    T (fun s ↦ nearCarrierDyadicBlockCoefficients N ell a ε s)
  calc
    coefficientEnergy
        (nearCarrierDyadicRangeTotalCoefficients N S H ell a ε) ≤
      T.card * ∑ s ∈ T,
        coefficientEnergy
          (nearCarrierDyadicBlockCoefficients N ell a ε s) := by
      simpa only [nearCarrierDyadicRangeTotalCoefficients, T] using! hsum
    _ ≤ T.card * ∑ _s ∈ T, B := by
      gcongr with s hs
      apply coefficientEnergy_nearCarrierDyadicBlockCoefficients_le
        N (S + H) s ell a ε
      · unfold nearCarrierDyadicExponents
        have hsBounds := Finset.mem_Ico.mp (show s ∈ T by exact hs)
        rw [Finset.mem_Ico]
        omega
      · exact ha
      · exact hε
      · exact haε
      · exact hεhalf
    _ = (H : ENNReal) ^ 2 * ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_nearCarrierDyadicRangeExponents]
      dsimp [B, T]
      ring

def nearCarrierHighCommonEnergyBound (a : ℝ) (H : ℕ) : ENNReal :=
  (H : ENNReal) ^ 2 * ENNReal.ofReal
    (8 * ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)))

theorem coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le_coeff_sq_mul
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    coefficientEnergy
        (nearCarrierDyadicRangeTotalCoefficients N S H ell a ε) ≤
      ENNReal.ofReal (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
        nearCarrierHighCommonEnergyBound a H := by
  refine (coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le
    N S H ell a ε hS ha hε haε hεhalf).trans_eq ?_
  unfold nearCarrierHighCommonEnergyBound
  have hcoeff : 0 ≤ ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 := sq_nonneg _
  rw [show
      8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) =
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (8 * ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) by ring,
    ENNReal.ofReal_mul hcoeff]
  ring

theorem integral_nearCarrierDyadicRangeTotal_le
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    ENNReal.ofReal
        (∫ alpha in (0 : ℝ)..1,
          ‖nearCarrierDyadicRangeTotal N S H ell a ε alpha‖ ^ 2) ≤
      (H : ENNReal) ^ 2 * ENNReal.ofReal
        (8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
  rw [← coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_eq_integral
    N S H ell a ε ha haε]
  exact coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le
    N S H ell a ε hS ha hε haε hεhalf

end

end Erdos1002
