import ErdosProblems.Erdos67.MRFiniteHalaszDyadicEndpoint

/-!
# Sharp dyadic composition of the finite three-band Halasz endpoint

This module combines the exact tilted three-band estimate with the finite
boundary-ramp extraction.  Its right side retains the two complementary
band masses and the explicit missing-prime-block core bound.
-/

open scoped BigOperators
open Complex Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.MRFiniteHalaszSmoothing

/-- The concrete right side of the sharp typical-dyadic endpoint. -/
def finiteHalaszTypicalDyadicCoreTailBound
    (C : ℝ) (Iblock : ℕ × ℕ) (f : ℕ → ℂ)
    (A0 X Y : ℕ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (R t0 delta : ℝ) (hdelta : 0 < delta) : ℝ :=
  fixedFiniteHalaszEulerBound C A0 X Y *
      tiltedFiniteHalaszKernelUniformBound
        (Erdos67.EulerResidue.taoExponent Y - 1)
        delta (Real.log X) (Real.log (2 * X)) hdelta *
      finiteHalaszMissingBlockCoreBound Iblock (2 * X) t0 R +
    finiteHalaszLSeriesAbsoluteMass
        (primeBandCoefficient f P₁)
        (Erdos67.EulerResidue.taoExponent Y) *
      finiteHalaszPositiveBandMass f
        (fun p ↦ ¬ P₁ p ∧ P₂ p) (2 * X)
        (Erdos67.EulerResidue.taoExponent Y) *
      finiteHalaszPositiveBandMass f
        (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) (2 * X)
        (Erdos67.EulerResidue.taoExponent Y) *
      tiltedFiniteHalaszKernelTailMass
        (Erdos67.EulerResidue.taoExponent Y - 1)
        delta (Real.log X) (Real.log (2 * X)) hdelta R +
    (X : ℝ)⁻¹ +
      2 * finiteHalaszDyadicBoundaryMass
        (finiteHalaszTypicalCoefficient f P₁ P₂) X delta

/-- The sharp dyadic polynomial of the actual finite typical coefficient is
bounded by the three-band Halasz core, exact Schwartz tail, one endpoint,
and two explicit boundary ramps. -/
theorem exists_uniform_norm_finiteHalaszTypicalDyadic_le_missingBlock :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Iblock : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock Iblock, P₁ p) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta : ℝ) (hdelta : 0 < delta),
        ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X))
            (finiteHalaszTypicalCoefficient f P₁ P₂) X t0‖ ≤
          finiteHalaszTypicalDyadicCoreTailBound C Iblock f A0 X Y P₁ P₂
            R t0 delta hdelta := by
  obtain ⟨C, hC, hwindow⟩ :=
    exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_missingBlock
  refine ⟨C, hC, ?_⟩
  intro Iblock f A0 X Y P₁ P₂ _ _ hmul hbound hY hYX hP hblock
    hnonpret R t0 hR hfreq delta hdelta
  have hX : 0 < X := by omega
  have hN : 0 < 2 * X := by omega
  let g : ℕ → ℂ := finiteHalaszTypicalCoefficient f P₁ P₂
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    unfold g finiteHalaszTypicalCoefficient
    split_ifs
    · exact hbound n hn
    · simp
  have hlogB : Real.log (2 * (X : ℝ)) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    norm_num
  have hsmooth := hwindow Iblock P₁ P₂ hmul hbound hY hYX hN hP
    hblock hnonpret hR hfreq delta (Real.log X) (Real.log (2 * X))
      hdelta hlogB
  have hsumEq :
      (∑ n ∈ Finset.Ioc 0 (2 * X),
          (g n / (n : ℂ)) * logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n)) =
        ∑ n ∈ Finset.Ioc 1 (2 * X),
          (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
            logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n) := by
    have hdisj : Disjoint (Finset.Ioc 0 1) (Finset.Ioc 1 (2 * X)) := by
      rw [Finset.disjoint_left]
      intro n hn0 hn1
      have hn0' := Finset.mem_Ioc.mp hn0
      have hn1' := Finset.mem_Ioc.mp hn1
      omega
    have hunion : Finset.Ioc 0 1 ∪ Finset.Ioc 1 (2 * X) =
        Finset.Ioc 0 (2 * X) :=
      Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)
    rw [← hunion, Finset.sum_union hdisj]
    have hg1 : g 1 = 0 := by
      simp [g, finiteHalaszTypicalCoefficient, HasPrimeFactor]
    simp [hg1, g]
  have hsmooth0 :
      ‖∑ n ∈ Finset.Ioc 0 (2 * X),
          (g n / (n : ℂ)) * logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n)‖ ≤
        finiteHalaszTypicalDyadicCoreTailBound C Iblock f A0 X Y P₁ P₂
            R t0 delta hdelta - (X : ℝ)⁻¹ -
              2 * finiteHalaszDyadicBoundaryMass g X delta := by
    rw [hsumEq]
    refine hsmooth.trans_eq ?_
    unfold finiteHalaszTypicalDyadicCoreTailBound
    dsimp only [g]
    ring
  have hsharp :=
    norm_dyadicVerticalDirichletPolynomial_le_harmonicWindow_add_boundary
      (f := g) hX hgbound delta hdelta t0
  dsimp only [g] at hsharp ⊢
  exact hsharp.trans (by linarith)

/-- Concrete sharp-dyadic right side with two separate missing blocks. -/
def finiteHalaszTypicalDyadicTwoBlockCoreTailBound
    (C : ℝ) (I₂ I₃ : ℕ × ℕ) (f : ℕ → ℂ)
    (A0 X Y : ℕ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (R t0 delta : ℝ) (hdelta : 0 < delta) : ℝ :=
  fixedFiniteHalaszEulerBound C A0 X Y *
      tiltedFiniteHalaszKernelUniformBound
        (Erdos67.EulerResidue.taoExponent Y - 1)
        delta (Real.log X) (Real.log (2 * X)) hdelta *
      (finiteHalaszMissingBlockCoreBound I₂ (2 * X) t0 R) ^ ((1 : ℝ) / 2) *
      (finiteHalaszMissingBlockCoreBound I₃ (2 * X) t0 R) ^ ((1 : ℝ) / 2) +
    finiteHalaszLSeriesAbsoluteMass
        (primeBandCoefficient f P₁)
        (Erdos67.EulerResidue.taoExponent Y) *
      finiteHalaszPositiveBandMass f
        (fun p ↦ ¬ P₁ p ∧ P₂ p) (2 * X)
        (Erdos67.EulerResidue.taoExponent Y) *
      finiteHalaszPositiveBandMass f
        (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) (2 * X)
        (Erdos67.EulerResidue.taoExponent Y) *
      tiltedFiniteHalaszKernelTailMass
        (Erdos67.EulerResidue.taoExponent Y - 1)
        delta (Real.log X) (Real.log (2 * X)) hdelta R +
    (X : ℝ)⁻¹ +
      2 * finiteHalaszDyadicBoundaryMass
        (finiteHalaszTypicalCoefficient f P₁ P₂) X delta

/-- Sharp dyadic three-band endpoint with the two missing-block
cardinalities kept separate. -/
theorem exists_uniform_norm_finiteHalaszTypicalDyadic_le_twoMissingBlocks :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I₂ I₃ : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock I₂, ¬ (¬ P₁ p ∧ P₂ p)) →
        (∀ p ∈ primesInBlock I₃, ¬ (¬ P₁ p ∧ ¬ P₂ p)) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta : ℝ) (hdelta : 0 < delta),
        ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X))
            (finiteHalaszTypicalCoefficient f P₁ P₂) X t0‖ ≤
          finiteHalaszTypicalDyadicTwoBlockCoreTailBound C I₂ I₃ f
            A0 X Y P₁ P₂ R t0 delta hdelta := by
  obtain ⟨C, hC, hwindow⟩ :=
    exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_twoMissingBlocks
  refine ⟨C, hC, ?_⟩
  intro I₂ I₃ f A0 X Y P₁ P₂ _ _ hmul hbound hY hYX hP hdisj₂ hdisj₃
    hnonpret R t0 hR hfreq delta hdelta
  have hX : 0 < X := by omega
  have hN : 0 < 2 * X := by omega
  let g : ℕ → ℂ := finiteHalaszTypicalCoefficient f P₁ P₂
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    unfold g finiteHalaszTypicalCoefficient
    split_ifs
    · exact hbound n hn
    · simp
  have hlogB : Real.log (2 * (X : ℝ)) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    norm_num
  have hsmooth := hwindow I₂ I₃ P₁ P₂ hmul hbound hY hYX hN hP
    hdisj₂ hdisj₃ hnonpret hR hfreq delta (Real.log X) (Real.log (2 * X))
      hdelta hlogB
  have hsumEq :
      (∑ n ∈ Finset.Ioc 0 (2 * X),
          (g n / (n : ℂ)) * logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n)) =
        ∑ n ∈ Finset.Ioc 1 (2 * X),
          (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
            logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n) := by
    have hdisj : Disjoint (Finset.Ioc 0 1) (Finset.Ioc 1 (2 * X)) := by
      rw [Finset.disjoint_left]
      intro n hn0 hn1
      have hn0' := Finset.mem_Ioc.mp hn0
      have hn1' := Finset.mem_Ioc.mp hn1
      omega
    have hunion : Finset.Ioc 0 1 ∪ Finset.Ioc 1 (2 * X) =
        Finset.Ioc 0 (2 * X) :=
      Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)
    rw [← hunion, Finset.sum_union hdisj]
    have hg1 : g 1 = 0 := by
      simp [g, finiteHalaszTypicalCoefficient, HasPrimeFactor]
    simp [hg1, g]
  have hsmooth0 :
      ‖∑ n ∈ Finset.Ioc 0 (2 * X),
          (g n / (n : ℂ)) * logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n)‖ ≤
        finiteHalaszTypicalDyadicTwoBlockCoreTailBound C I₂ I₃ f
            A0 X Y P₁ P₂ R t0 delta hdelta - (X : ℝ)⁻¹ -
              2 * finiteHalaszDyadicBoundaryMass g X delta := by
    rw [hsumEq]
    refine hsmooth.trans_eq ?_
    unfold finiteHalaszTypicalDyadicTwoBlockCoreTailBound
    dsimp only [g]
    ring
  have hsharp :=
    norm_dyadicVerticalDirichletPolynomial_le_harmonicWindow_add_boundary
      (f := g) hX hgbound delta hdelta t0
  dsimp only [g] at hsharp ⊢
  exact hsharp.trans (by linarith)

/-! ## `L²` transfer back to the unrestricted dyadic polynomial -/

/-- The finite dyadic set on which both complementary prime bands occur. -/
def finiteHalaszTypicalDyadicSet
    (X : ℕ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun n ↦
    HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
      HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n

/-- Restriction of `f` to the typical dyadic set is exactly the unrestricted
dyadic polynomial of `finiteHalaszTypicalCoefficient`. -/
theorem dyadicVerticalDirichletPolynomial_typicalSet_eq_coefficient
    (f : ℕ → ℂ) (X : ℕ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (t : ℝ) :
    dyadicVerticalDirichletPolynomial
        (finiteHalaszTypicalDyadicSet X P₁ P₂) f X t =
      dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X))
        (finiteHalaszTypicalCoefficient f P₁ P₂) X t := by
  classical
  unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
    dyadicRestrictedSupport finiteHalaszTypicalDyadicSet
  rw [Finset.inter_self]
  have hsupp :
      Finset.Ioc X (2 * X) ∩
          (Finset.Ioc X (2 * X)).filter (fun n ↦
            HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
              HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n) =
        (Finset.Ioc X (2 * X)).filter (fun n ↦
          HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
            HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n) := by
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  rw [hsupp]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases htyp :
      HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
        HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n
  · simp [htyp, finiteHalaszTypicalCoefficient]
  · simp [htyp, finiteHalaszTypicalCoefficient]

/-- A pointwise bound for a restricted dyadic polynomial transfers to the
unrestricted polynomial in square mean.  The loss is exactly the finite
mean-square cardinality of the removed coefficients. -/
theorem intervalIntegral_normSq_full_dyadic_le_of_restricted_bound
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hrestricted : ∀ t, |t| ≤ T →
      ‖dyadicVerticalDirichletPolynomial S f X t‖ ≤ B) :
    (∫ t in -T..T, Complex.normSq
        (dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t)) ≤
      4 * T * B ^ 2 +
        2 * ((2 * T + 4 * Real.pi * X) *
          (((Finset.Ioc X (2 * X) \ S).card : ℝ) / (X : ℝ) ^ 2)) := by
  let FS : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f X
  let FA : ℝ → ℂ :=
    dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X
  let D : ℝ → ℂ := fun t ↦ FA t - FS t
  have hFS : Continuous FS := continuous_dyadicVerticalDirichletPolynomial S f X
  have hFA : Continuous FA :=
    continuous_dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X
  have hD : Continuous D := hFA.sub hFS
  have hFAint : IntervalIntegrable (fun t ↦ Complex.normSq (FA t))
      volume (-T) T := (Complex.continuous_normSq.comp hFA).intervalIntegrable _ _
  have hmajorInt : IntervalIntegrable
      (fun t ↦ 2 * (Complex.normSq (FS t) + Complex.normSq (D t)))
      volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      Complex.normSq (FA t) ≤
        2 * (Complex.normSq (FS t) + Complex.normSq (D t)) := by
    intro t ht
    have h := normSq_sub_le_two_mul_add (FS t) (-D t)
    simp only [sub_neg_eq_add, Complex.normSq_neg] at h
    have hid : FS t + D t = FA t := by
      dsimp [D]
      ring
    rwa [hid] at h
  have hmono :
      (∫ t in -T..T, Complex.normSq (FA t)) ≤
        ∫ t in -T..T,
          2 * (Complex.normSq (FS t) + Complex.normSq (D t)) :=
    intervalIntegral.integral_mono_on (by linarith) hFAint hmajorInt hpoint
  have hFSenergy :
      (∫ t in -T..T, Complex.normSq (FS t)) ≤ 2 * T * B ^ 2 := by
    have hconst : IntervalIntegrable (fun _t : ℝ ↦ B ^ 2) volume (-T) T :=
      intervalIntegrable_const
    have hm :
        (∫ t in -T..T, Complex.normSq (FS t)) ≤
          ∫ _t in -T..T, B ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((Complex.continuous_normSq.comp hFS).intervalIntegrable _ _) hconst
      intro t ht
      change Complex.normSq (FS t) ≤ B ^ 2
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hB).2
        (hrestricted t (abs_le.mpr ⟨ht.1, ht.2⟩))
    calc
      (∫ t in -T..T, Complex.normSq (FS t)) ≤
          ∫ _t in -T..T, B ^ 2 := hm
      _ = 2 * T * B ^ 2 := by
        rw [intervalIntegral.integral_const]
        ring
  have hdiff0 :=
    intervalIntegral_normSq_dyadicVerticalDirichletPolynomial_sub_full_le
      S hbound hX hT
  have hdiff :
      (∫ t in -T..T, Complex.normSq (D t)) ≤
        (2 * T + 4 * Real.pi * (X : ℝ)) *
          (((Finset.Ioc X (2 * X) \ S).card : ℝ) / (X : ℝ) ^ 2) := by
    have heq : (∫ t in -T..T, Complex.normSq (D t)) =
        ∫ t in -T..T, Complex.normSq
          (dyadicVerticalDirichletPolynomial S f X t -
            dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [D, FS, FA]
      rw [← Complex.normSq_neg]
      congr 2
      ring
    rw [heq]
    exact hdiff0
  have hsplit :
      (∫ t in -T..T,
          2 * (Complex.normSq (FS t) + Complex.normSq (D t))) =
        2 * (∫ t in -T..T, Complex.normSq (FS t)) +
          2 * (∫ t in -T..T, Complex.normSq (D t)) := by
    rw [intervalIntegral.integral_const_mul]
    have hadd := intervalIntegral.integral_add
      ((Complex.continuous_normSq.comp hFS).intervalIntegrable
        (μ := MeasureTheory.volume) (-T) T)
      ((Complex.continuous_normSq.comp hD).intervalIntegrable
        (μ := MeasureTheory.volume) (-T) T)
    have hadd' :
        (∫ x in -T..T, Complex.normSq (FS x) + Complex.normSq (D x)) =
          (∫ x in -T..T, Complex.normSq (FS x)) +
            ∫ x in -T..T, Complex.normSq (D x) := by
      simpa only [Function.comp_apply] using hadd
    change 2 * (∫ x in -T..T,
      Complex.normSq (FS x) + Complex.normSq (D x)) = _
    rw [hadd']
    ring
  rw [hsplit] at hmono
  dsimp only [FA] at hmono ⊢
  exact hmono.trans (by nlinarith [hFSenergy, hdiff])

/-- Direct integrated/squared consumer of the sharp typical-dyadic Halasz
bound.  All analytic terms are concrete; `hEnvelope` merely chooses one
uniform scalar majorant for their displayed formula on `[-T,T]`. -/
theorem exists_uniform_intervalIntegral_normSq_full_dyadic_le_threeBand :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Iblock : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock Iblock, P₁ p) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R T B : ℝ}, 0 ≤ R → 0 ≤ T → 0 ≤ B →
        T + 2 * Real.pi * R ≤ X →
        ∀ (delta : ℝ) (hdelta : 0 < delta),
        (∀ t, |t| ≤ T →
          finiteHalaszTypicalDyadicCoreTailBound C Iblock f A0 X Y P₁ P₂
            R t delta hdelta ≤ B) →
        (∫ t in -T..T, Complex.normSq
            (dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t)) ≤
          4 * T * B ^ 2 +
            2 * ((2 * T + 4 * Real.pi * X) *
              (((Finset.Ioc X (2 * X) \
                finiteHalaszTypicalDyadicSet X P₁ P₂).card : ℝ) /
                  (X : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_uniform_norm_finiteHalaszTypicalDyadic_le_missingBlock
  refine ⟨C, hC, ?_⟩
  intro Iblock f A0 X Y P₁ P₂ _ _ hmul hbound hY hYX hP hblock
    hnonpret R T B hR hT hB hfreq delta hdelta hEnvelope
  have hX : 0 < X := by omega
  apply intervalIntegral_normSq_full_dyadic_le_of_restricted_bound
    (finiteHalaszTypicalDyadicSet X P₁ P₂) hbound hX hT hB
  intro t ht
  rw [dyadicVerticalDirichletPolynomial_typicalSet_eq_coefficient]
  exact (hpoint Iblock P₁ P₂ hmul hbound hY hYX hP hblock hnonpret
      hR (by linarith [abs_nonneg t]) delta hdelta).trans (hEnvelope t ht)

/-- Integrated/squared three-band endpoint with two separate missing-prime
blocks.  The conclusion is for the original unrestricted dyadic polynomial. -/
theorem exists_uniform_intervalIntegral_normSq_full_dyadic_le_twoBlocks :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I₂ I₃ : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock I₂, ¬ (¬ P₁ p ∧ P₂ p)) →
        (∀ p ∈ primesInBlock I₃, ¬ (¬ P₁ p ∧ ¬ P₂ p)) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R T B : ℝ}, 0 ≤ R → 0 ≤ T → 0 ≤ B →
        T + 2 * Real.pi * R ≤ X →
        ∀ (delta : ℝ) (hdelta : 0 < delta),
        (∀ t, |t| ≤ T →
          finiteHalaszTypicalDyadicTwoBlockCoreTailBound C I₂ I₃ f
            A0 X Y P₁ P₂ R t delta hdelta ≤ B) →
        (∫ t in -T..T, Complex.normSq
            (dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t)) ≤
          4 * T * B ^ 2 +
            2 * ((2 * T + 4 * Real.pi * X) *
              (((Finset.Ioc X (2 * X) \
                finiteHalaszTypicalDyadicSet X P₁ P₂).card : ℝ) /
                  (X : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_uniform_norm_finiteHalaszTypicalDyadic_le_twoMissingBlocks
  refine ⟨C, hC, ?_⟩
  intro I₂ I₃ f A0 X Y P₁ P₂ _ _ hmul hbound hY hYX hP hdisj₂ hdisj₃
    hnonpret R T B hR hT hB hfreq delta hdelta hEnvelope
  have hX : 0 < X := by omega
  apply intervalIntegral_normSq_full_dyadic_le_of_restricted_bound
    (finiteHalaszTypicalDyadicSet X P₁ P₂) hbound hX hT hB
  intro t ht
  rw [dyadicVerticalDirichletPolynomial_typicalSet_eq_coefficient]
  exact (hpoint I₂ I₃ P₁ P₂ hmul hbound hY hYX hP hdisj₂ hdisj₃
      hnonpret hR (by linarith [abs_nonneg t]) delta hdelta).trans
        (hEnvelope t ht)

end

end Erdos67.MRHalaszBands
