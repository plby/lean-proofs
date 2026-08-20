/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RankDropTerminalContradiction
import ErdosProblems.Erdos407.RankDropHeightBridge

/-!
# Final codimension-one rank-drop contradiction

This module absorbs every fixed coefficient and coordinate-change factor
into the common logarithmic scale and proves the unconditional finiteness
of the codimension-one approximation spaces.
-/

namespace Erdos407.RankDrop

open scoped BigOperators

attribute [local instance] Matrix.seminormedAddCommGroup

noncomputable section

/-- The degree-independent base which absorbs the residual monomial count,
the transformed coefficient bound, the finite grid, and the denominators of
the three local coordinate changes. -/
noncomputable def terminalEvaluationBase {coords : ℕ}
    (L : LocalForms coords) (G : ℝ) : ℝ :=
  ∏ v : PadicSubspace.Place23,
    ((2 : ℝ) ^ coords *
      AuxiliaryHeightEstimates.transformedCoefficientHeightBase
        (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) *
      max 1 (G * HeightBoxes.realPlaceNorm v
        ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹)))

theorem one_le_terminalEvaluationBase {coords : ℕ}
    (L : LocalForms coords) (G : ℝ) :
    1 ≤ terminalEvaluationBase L G := by
  unfold terminalEvaluationBase
  apply Finset.one_le_prod
  intro v _
  have htwo : 1 ≤ (2 : ℝ) ^ coords := one_le_pow₀ (by norm_num)
  have htrans := AuxiliaryHeightEstimates.one_le_transformedCoefficientHeightBase
    (fun w ↦ PadicSubspace.integralInverseFormMatrix L w)
  have hlocal : 1 ≤ max 1 (G * HeightBoxes.realPlaceNorm v
      ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹)) := le_max_left _ _
  nlinarith [mul_le_mul htwo htrans (by positivity) (by positivity),
    mul_le_mul (mul_le_mul htwo htrans (by positivity) (by positivity))
      hlocal (by positivity) (by positivity)]

/-- All non-radius factors in the three local estimates have at most fixed
exponential growth in the total multidegree. -/
theorem prod_localPrefactor_le_terminalEvaluationBase_pow
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (L : LocalForms coords) (G : ℝ)
    (hdegree : ∀ h, 0 < degree h)
    (P : ℝ)
    (hP : P ≤
      AuxiliaryHeightEstimates.transformedCoefficientHeightBase
        (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) ^
          AuxiliaryHeightEstimates.totalDegree degree)
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree) :
    (∏ v : PadicSubspace.Place23,
      (Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) : ℝ) *
        max 1 P *
        (max 1 (G * HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
            AuxiliaryHeightEstimates.totalDegree degree) ≤
      terminalEvaluationBase L G ^
        AuxiliaryHeightEstimates.totalDegree degree := by
  let T : PadicSubspace.Place23 → Matrix (Fin coords) (Fin coords) ℤ :=
    fun w ↦ PadicSubspace.integralInverseFormMatrix L w
  have hcardRes : (Fintype.card
      (GLRAuxiliary.ResidualMonomialIndex I) : ℝ) ≤
      ((2 : ℝ) ^ coords) ^ AuxiliaryHeightEstimates.totalDegree degree := by
    exact_mod_cast (card_residualMonomialIndex_le I).trans
      (AuxiliaryHeightEstimates.card_monomialIndex_le_two_pow hdegree)
  have hTN : 1 ≤ AuxiliaryHeightEstimates.transformedCoefficientHeightBase T ^
      AuxiliaryHeightEstimates.totalDegree degree :=
    one_le_pow₀ (AuxiliaryHeightEstimates.one_le_transformedCoefficientHeightBase T)
  have hmaxN : max 1 P ≤
      AuxiliaryHeightEstimates.transformedCoefficientHeightBase T ^
        AuxiliaryHeightEstimates.totalDegree degree := max_le hTN (by simpa [T] using hP)
  have hone (v : PadicSubspace.Place23) :
      (Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) : ℝ) * max 1 P *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree ≤
        (((2 : ℝ) ^ coords *
            AuxiliaryHeightEstimates.transformedCoefficientHeightBase T *
            max 1 (G * HeightBoxes.realPlaceNorm v
              ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
          AuxiliaryHeightEstimates.totalDegree degree) := by
    calc
      (Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) : ℝ) * max 1 P *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree ≤
        (((2 : ℝ) ^ coords) ^ AuxiliaryHeightEstimates.totalDegree degree) *
          (AuxiliaryHeightEstimates.transformedCoefficientHeightBase T ^
            AuxiliaryHeightEstimates.totalDegree degree) *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree := by
        gcongr
      _ = _ := by rw [mul_pow, mul_pow]
  calc
    (∏ v : PadicSubspace.Place23,
      (Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) : ℝ) *
        max 1 P *
        (max 1 (G * HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
            AuxiliaryHeightEstimates.totalDegree degree) ≤
        ∏ v : PadicSubspace.Place23,
          (((2 : ℝ) ^ coords *
              AuxiliaryHeightEstimates.transformedCoefficientHeightBase T *
              max 1 (G * HeightBoxes.realPlaceNorm v
                ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
            AuxiliaryHeightEstimates.totalDegree degree) :=
      Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun v _ ↦ hone v)
    _ = terminalEvaluationBase L G ^
        AuxiliaryHeightEstimates.totalDegree degree := by
      unfold terminalEvaluationBase
      rw [← Finset.prod_pow]

/-- If the fixed-base logarithmic cost is at most a quarter of the central
saving, the radius product wins strictly. -/
theorem terminalProduct_lt_one
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) (hQ : ∀ h, 2 ≤ Q h)
    (Base D saving : ℝ) (hBase : 1 ≤ Base) (hD : 0 < D)
    (hsaving : 0 < saving)
    (hcost : Real.log Base *
        (AuxiliaryHeightEstimates.totalDegree degree : ℝ) ≤ saving * D / 4)
    (hscale : TerminalEstimates.scaleWeightedExponent c J
        (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ)) ≤
      -(saving * D / 2)) :
    Base ^ AuxiliaryHeightEstimates.totalDegree degree *
        (∏ v, TerminalEstimates.residualMonomialRadius c (J v) Q v) < 1 := by
  rw [TerminalEstimates.prod_residualMonomialRadius_eq_exp_scaleWeightedExponent
    hdegree c J Q hQ]
  have hBpos : 0 < Base := zero_lt_one.trans_le hBase
  rw [show Base ^ AuxiliaryHeightEstimates.totalDegree degree =
      Real.exp (Real.log Base *
        (AuxiliaryHeightEstimates.totalDegree degree : ℝ)) by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hBpos]]
  rw [← Real.exp_add, Real.exp_lt_one_iff]
  calc
    Real.log Base * (AuxiliaryHeightEstimates.totalDegree degree : ℝ) +
        TerminalEstimates.scaleWeightedExponent c J
          (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ)) ≤
      saving * D / 4 + -(saving * D / 2) := add_le_add hcost hscale
    _ < 0 := by
      nlinarith

/-! ## Unconditional codimension-one finiteness -/

/-- The terminal GLR rank-drop theorem in ambient dimension `m+1`. -/
theorem sCodimOneApproximationSpaces_finite_succ
    {m : ℕ} (hm : 0 < m)
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    (sCodimOneApproximationSpaces L c).Finite := by
  classical
  by_contra hfinite
  have hinfinite : (sCodimOneApproximationSpaces L c).Infinite :=
    hfinite
  have hcoords : 0 < m + 1 := Nat.succ_pos _
  obtain ⟨eta, heta, hetaQuarter, blocks, hblocks, hmany, hband⟩ :=
    TerminalEstimates.exists_auxiliary_parameters hcoords c hdelta
  have hetaOne : eta ≤ 1 := hetaQuarter.trans (by norm_num)
  obtain ⟨B, hB, hgrid⟩ := TerminalEstimates.exists_gridBound heta m
  let G : ℝ := (m : ℝ) * max 1 (B : ℝ)
  let T : PadicSubspace.Place23 → Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
    fun v ↦ PadicSubspace.integralInverseFormMatrix L v
  let sigma : ℝ := rankDropSigmaAt blocks eta
  let kappa : ℝ := delta / (12 * (m + 1 : ℝ))
  let saving : ℝ :=
    (((blocks : ℚ) / ((m + 1 : ℕ) : ℚ) : ℚ) : ℝ) * delta
  let Aheight : ℝ :=
    Real.log (2 * AuxiliaryHeightEstimates.coefficientHeightBase T)
  let Base : ℝ := terminalEvaluationBase L G
  have hsigma : 0 < sigma := rankDropSigmaAt_pos heta
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hsaving : 0 < saving := by
    dsimp [saving]
    have hbq : (0 : ℚ) < blocks := by exact_mod_cast hblocks
    have hmq : (0 : ℚ) < m + 1 := by positivity
    positivity
  have hAheight : 0 ≤ Aheight := by
    dsimp [Aheight]
    apply Real.log_nonneg
    nlinarith [AuxiliaryHeightEstimates.one_le_coefficientHeightBase T]
  have hBase : 1 ≤ Base := one_le_terminalEvaluationBase L G
  let Croth : ℝ := (m : ℝ) * sigma⁻¹ *
    ((Aheight + 4) * (blocks : ℝ))
  let Cprod : ℝ := Real.log Base * (blocks : ℝ)
  have hCroth : 0 ≤ Croth := by
    dsimp [Croth]
    positivity
  have hCprod : 0 ≤ Cprod := by
    dsimp [Cprod]
    exact mul_nonneg (Real.log_nonneg hBase) (by positivity)
  obtain ⟨Qroth, hQroth, hcutRoth⟩ :=
    TerminalEstimates.exists_log_cutoff_div_le
      (C := Croth) (target := kappa / 2) (by positivity)
  obtain ⟨Qprod, hQprod, hcutProd⟩ :=
    TerminalEstimates.exists_log_cutoff_div_le
      (C := Cprod) (target := saving / 4) (by positivity)
  let Q₀ : ℕ := max Qroth Qprod
  have hQ₀ : 2 ≤ Q₀ := hQroth.trans (le_max_left _ _)
  have hlogRoth : Real.log (Qroth : ℝ) ≤ Real.log (Q₀ : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast le_max_left Qroth Qprod)
  have hlogProd : Real.log (Qprod : ℝ) ≤ Real.log (Q₀ : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast le_max_right Qroth Qprod)
  have hlogRothPos : 0 < Real.log (Qroth : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Qroth by omega))
  have hlogProdPos : 0 < Real.log (Qprod : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Qprod by omega))
  have hcutRoth₀ : Croth / Real.log (Q₀ : ℝ) ≤ kappa / 2 :=
    (div_le_div_of_nonneg_left hCroth hlogRothPos hlogRoth).trans hcutRoth
  have hcutProd₀ : Cprod / Real.log (Q₀ : ℝ) ≤ saving / 4 :=
    (div_le_div_of_nonneg_left hCprod hlogProdPos hlogProd).trans hcutProd
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / sigma)
  have hKsigma : (2 : ℝ) ≤ sigma * (K : ℝ) := by
    have := (div_lt_iff₀ hsigma).mp hK
    linarith
  obtain ⟨W, znormal, hWexceptional, hWlarge, hWgap, hWinj, hnormal⟩ :=
    exists_logSeparated_primitiveNormals L hL c hdelta hc hinfinite Q₀ K blocks
  let Q : Fin blocks → ℕ := fun h ↦ sCodimOneScale (W h)
  let M : GeneralizedRoth.FormFamily blocks m :=
    fun h ↦ primitiveNormalForm (znormal h)
  have hQlarge : ∀ h, Q₀ ≤ Q h := fun h ↦ (hWlarge h).le
  have hQtwo : ∀ h, 2 ≤ Q h := fun h ↦ hQ₀.trans (hQlarge h)
  have hM : ∀ h, M h ≠ 0 := fun h ↦
    primitiveNormalForm_ne_zero (hnormal h).1
  have hMheight : ∀ h, kappa * Real.log (Q h : ℝ) ≤
      GeneralizedRoth.formHeight (M h) := by
    intro h
    simpa [kappa, Q, M] using (hnormal h).2.2.2
  have hbasis : ∀ h, ∃ x : Fin m → RatVector (m + 1),
      (∀ i, x i ∈ realSIntegralApproximationDomain L (Q h) c) ∧
      LinearIndependent ℚ x ∧
      (W h).1 = SubspaceHeights.rowSpace (rationalRowMatrix x) ∧
      SubspaceHeights.cofactorVector (rationalRowMatrix x) ≠ 0 ∧
      (∀ y ∈ (W h).1,
        y ⬝ᵥ SubspaceHeights.cofactorVector (rationalRowMatrix x) = 0) := by
    intro h
    simpa [Q] using exists_sIntegral_basis_cofactor_normal (W h)
  choose x hxbox hxlin hxrow hxcof hxnormal using hbasis
  have hxS : ∀ h i, AdelicMinkowski.InZOneSix (x h i) :=
    fun h i ↦ (hxbox h i).1
  have hxapprox : ∀ h i, HeightBoxes.InApproximationBox
      L (Q h : ℝ) c (x h i) := fun h i ↦ (hxbox h i).2
  have hxmem : ∀ h i, x h i ∈ (W h).1 := by
    intro h i
    rw [sCodimOne_eq_span_scale]
    exact mem_realSApproximationSpan (hxbox h i)
  have hxker : ∀ h i, BasisNonvanishing.formValue (M h) (x h i) = 0 := by
    intro h i
    have hz := (hnormal h).2.2.1 (x h i) (hxmem h i)
    simpa [M, primitiveNormalForm, BasisNonvanishing.formValue,
      dotProduct, mul_comm] using hz
  let E : ℝ := ∑ h, Real.log (Q h : ℝ)
  have hlogQpos : ∀ h, 0 < Real.log (Q h : ℝ) := fun h ↦
    Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) (hQtwo h)))
  have hEpos : 0 < E := by
    let h₀ : Fin blocks := ⟨0, hblocks⟩
    calc
      0 < Real.log (Q h₀ : ℝ) := hlogQpos h₀
      _ ≤ E := by
        unfold E
        exact Finset.single_le_sum (fun j _ ↦ (hlogQpos j).le)
          (Finset.mem_univ h₀)
  let upper : ℝ :=
    ((((blocks : ℚ) / ((m + 1 : ℕ) : ℚ) +
      2 * blocks * eta : ℚ) : ℚ) : ℝ) *
        (∑ v, ∑ i, |c v i|)
  have hupper : 0 ≤ upper := by
    dsimp [upper]
    have hbq : (0 : ℚ) ≤ blocks := by positivity
    have hmq : (0 : ℚ) < m + 1 := by positivity
    have : (0 : ℚ) ≤
        (blocks : ℚ) / (m + 1 : ℚ) + 2 * blocks * eta := by positivity
    positivity
  let D : ℝ := max (2 * E) (4 * E * upper / saving + 1)
  have hD : 0 < D := by
    exact lt_of_lt_of_le (by positivity : 0 < 2 * E) (le_max_left _ _)
  have hlogQleE : ∀ h, Real.log (Q h : ℝ) ≤ E := by
    intro h
    unfold E
    exact Finset.single_le_sum (fun j _ ↦ (hlogQpos j).le) (Finset.mem_univ h)
  have hDlarge : ∀ h, 2 * Real.log (Q h : ℝ) ≤ D := by
    intro h
    exact (mul_le_mul_of_nonneg_left (hlogQleE h) (by norm_num)).trans
      (le_max_left _ _)
  have hfloorBudget : E * upper ≤ saving * D / 4 := by
    have hspos : 0 < saving := hsaving
    have hlargeD : 4 * E * upper / saving + 1 ≤ D := le_max_right _ _
    have hraw : 4 * E * upper / saving < D := by linarith
    have := (div_lt_iff₀ hspos).mp hraw
    nlinarith
  let degree : Fin blocks → ℕ := fun h ↦ logarithmicDegree D (Q h)
  have hdegree : ∀ h, 0 < degree h := fun h ↦
    TerminalEstimates.logarithmicDegree_pos_of_two_log_le (hQtwo h) (hDlarge h)
  have hratio : ∀ j : Fin (blocks - 1),
      (degree ⟨j.val + 1, by omega⟩ : ℝ) /
          (degree ⟨j.val, by omega⟩ : ℝ) ≤ sigma := by
    intro j
    exact TerminalEstimates.logarithmicDegree_ratio_of_log_separation
      (hQtwo ⟨j.val, by omega⟩) (hQtwo ⟨j.val + 1, by omega⟩)
      hsigma hKsigma (by simpa [Q] using hWgap j) (hDlarge ⟨j.val, by omega⟩)
  have hmany3 : (3 : ℚ) * ((m + 1 : ℕ) : ℚ) < blocks * eta ^ 2 := by
    have hpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    exact (mul_lt_mul_of_pos_right (by norm_num : (3 : ℚ) < 6) hpos).trans hmany
  obtain ⟨coeff, hcoeffne, hpolyne, hhom, hsupport, hvanish,
      hcoeffnorm, htransnorm⟩ :=
    exists_rankDropAuxiliaryAt L hL eta hblocks hcoords hdegree heta hmany3
  have hheightP : PolynomialHeights.projectiveCoeffHeight
      (rationalAuxiliaryPolynomial coeff) ≤
      Aheight * ∑ h, (degree h : ℝ) := by
    simpa [Aheight, T] using
      (projectiveCoeffHeight_rationalAuxiliaryPolynomial_le_sum_degree
        (n := m) eta T hblocks hdegree heta hmany coeff hcoeffnorm)
  have hRothSlope : (m : ℝ) * sigma⁻¹ *
      ((Aheight + 4) * (blocks : ℝ) / Real.log (Q₀ : ℝ)) ≤
      kappa / 2 := by
    have : Croth / Real.log (Q₀ : ℝ) =
        (m : ℝ) * sigma⁻¹ *
          ((Aheight + 4) * (blocks : ℝ) / Real.log (Q₀ : ℝ)) := by
      dsimp [Croth]
      ring
    rw [← this]
    exact hcutRoth₀
  have hheight := TerminalEstimates.roth_height_hypothesis_of_linear_degreeHeight
    (Q₀ := Q₀) hblocks hsigma hkappa hAheight hD hQ₀ Q hQlarge hDlarge M hMheight
    hheightP hRothSlope
  obtain ⟨I, hIweight, zgrid, hzgrid, hyS, hEval⟩ :=
    exists_integralDerivativeIndex_of_rothHeight hblocks hm heta hetaOne
      hdegree coeff hpolyne hhom M hM x hxlin hxker hxS B hgrid hratio hheight
  let y : Fin blocks → RatVector (m + 1) :=
    BasisNonvanishing.basisCombination x zgrid
  have hyS' : ∀ h, AdelicMinkowski.InZOneSix (y h) := by
    simpa [y] using hyS
  have hyapprox : ∀ h v i,
      HeightBoxes.realPlaceNorm v (L v i (y h)) ≤
        G * HeightBoxes.exponentRadius (Q h : ℝ) c v i := by
    intro h v i
    simpa [y, G] using
      (BasisNonvanishing.realPlaceNorm_basisCombination_le
        L Q c x hxapprox zgrid B hzgrid h v i)
  let P : ℝ :=
    (Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks (m + 1) degree) : ℝ) *
      ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
      GLRAuxiliary.coefficientHeightBound (degree := degree) eta T
  have hPpow : P ≤
      AuxiliaryHeightEstimates.transformedCoefficientHeightBase T ^
        AuxiliaryHeightEstimates.totalDegree degree := by
    dsimp [P]
    exact AuxiliaryHeightEstimates.transformedCoefficientPrefactor_le_pow
      eta T hblocks hcoords hdegree heta hmany
  have htransnorm' : ∀ v J,
      ‖GLRAuxiliary.transformedCoefficient T v I J coeff‖ ≤ P := by
    simpa [P, T] using fun v J ↦ htransnorm v I J
  have hvanish' : ∀ v J, GLRAuxiliary.OutsideCentralBand eta J →
      GLRAuxiliary.transformedCoefficient T v I J coeff = 0 := by
    intro v J hJ
    exact hvanish v I J hIweight hJ
  have hsumDegree : (AuxiliaryHeightEstimates.totalDegree degree : ℝ) ≤
      (blocks : ℝ) * (D / Real.log (Q₀ : ℝ)) := by
    rw [AuxiliaryHeightEstimates.totalDegree_cast_eq_sum]
    exact TerminalEstimates.sum_logarithmicDegree_le_cutoff hD.le hQ₀ hQlarge
  have hcost : Real.log Base *
      (AuxiliaryHeightEstimates.totalDegree degree : ℝ) ≤ saving * D / 4 := by
    calc
      Real.log Base * (AuxiliaryHeightEstimates.totalDegree degree : ℝ) ≤
          Real.log Base * ((blocks : ℝ) *
            (D / Real.log (Q₀ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsumDegree (Real.log_nonneg hBase)
      _ = (Cprod / Real.log (Q₀ : ℝ)) * D := by
        dsimp [Cprod]
        ring
      _ ≤ (saving / 4) * D :=
        mul_le_mul_of_nonneg_right hcutProd₀ hD.le
      _ = saving * D / 4 := by ring
  have hsApprox : ∀ h,
      |(degree h : ℝ) * Real.log (Q h : ℝ) - D| ≤ E := by
    intro h
    have hb := logarithmicDegree_mul_log_bounds hD.le (hQtwo h)
    rw [abs_le]
    constructor
    · linarith [hlogQleE h]
    · linarith
  have hsmall : ∀ J : PadicSubspace.Place23 →
      GLRAuxiliary.ResidualMonomialIndex I,
      (∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v)) →
      (∏ v,
        Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) * max 1 P *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree *
          TerminalEstimates.residualMonomialRadius c (J v) Q v) < 1 := by
    intro J hJ
    have hscale := TerminalEstimates.scaleWeightedExponent_le_neg_half
      hcoords hdegree heta.le J hJ c hc hband
      (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ)) D E
      hD.le hEpos.le hsApprox
      (by simpa [upper, saving, mul_assoc] using hfloorBudget)
    have hpref := prod_localPrefactor_le_terminalEvaluationBase_pow
      L G hdegree P (by simpa [Base, T] using hPpow) I
    rw [Finset.prod_mul_distrib]
    refine (mul_le_mul hpref (le_refl _)
      (Finset.prod_nonneg fun v _ ↦ by
        unfold TerminalEstimates.residualMonomialRadius
        exact Finset.prod_nonneg fun h _ ↦ Finset.prod_nonneg fun i _ ↦
          pow_nonneg (Real.rpow_nonneg (by positivity) _) _)
      (pow_nonneg (zero_le_one.trans hBase) _)).trans_lt ?_
    exact terminalProduct_lt_one hdegree c J Q hQtwo Base D saving hBase hD
      hsaving hcost (by simpa [saving] using hscale)
  have hzero := dividedDerivative_eval_eq_zero_of_centralProduct_lt_one
    L hL eta coeff I hIweight y hyS' Q c G hyapprox P
    (by simpa [T] using htransnorm') (by simpa [T] using hvanish') hsmall
  exact hEval (by simpa [y] using hzero)

/-- **Generalized Roth rank-drop theorem (GLR, Theorem 4.14).**  In every
ambient dimension at least two, a negative total system of local exponents
admits only finitely many codimension-one `ℤ[1/6]` approximation spans. -/
theorem sCodimOneApproximationSpaces_finite
    {n : ℕ} (hn : 2 ≤ n)
    (L : LocalForms n)
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n)
    {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    (sCodimOneApproximationSpaces L c).Finite := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply sCodimOneApproximationSpaces_finite_succ (m := m) (by omega)
    L hL c hdelta hc

end

end Erdos407.RankDrop

#print axioms Erdos407.RankDrop.sCodimOneApproximationSpaces_finite
