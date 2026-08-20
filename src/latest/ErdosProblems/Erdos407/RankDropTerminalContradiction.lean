/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RankDropTerminal
import ErdosProblems.Erdos407.RankDropTerminalEstimates
import ErdosProblems.Erdos407.BasisNonvanishing
import ErdosProblems.Erdos407.AuxiliaryHeightEstimates

/-!
# Terminal contradiction for the rational rank-drop theorem

This module assembles the generalized Roth estimate, finite-grid
nonvanishing, integral coordinate changes, and the restricted product
formula.  Its imports are all strictly below the final exterior-power
endpoint, so the dimension-generic codimension-one finiteness theorem can be
used by that endpoint without an import cycle.
-/

namespace Erdos407.RankDrop

open scoped BigOperators

noncomputable section

/-- Generalized Roth plus the finite-grid restriction argument produces an
integral derivative inside the full GLR central-band budget. -/
theorem exists_integralDerivativeIndex_of_rothHeight
    {blocks n : ℕ} (hblocks : 0 < blocks) (hn : 0 < n)
    {eta : ℚ} (heta : 0 < eta) (hetaOne : eta ≤ 1)
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    (coeff : AuxiliaryPolynomial.MonomialIndex
      blocks (n + 1) degree → ℤ)
    (hcoeff : AuxiliaryPolynomial.ofCoefficients coeff ≠ 0)
    (hhom : GLRAuxiliary.IsMultihomogeneous degree
      (AuxiliaryPolynomial.ofCoefficients coeff))
    (M : GeneralizedRoth.FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (x : Fin blocks → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, BasisNonvanishing.formValue (M h) (x h i) = 0)
    (hxS : ∀ h i, AdelicMinkowski.InZOneSix (x h i))
    (B : ℕ)
    (hgrid : (n : ℚ) / (B + 1 : ℚ) ≤ eta / 2)
    (hratio : ∀ j : Fin (blocks - 1),
      (degree ⟨j.val + 1, by omega⟩ : ℝ) /
        (degree ⟨j.val, by omega⟩ : ℝ) ≤
          rankDropSigmaAt blocks eta)
    (hheight : ∀ j,
      (n : ℝ) * (rankDropSigmaAt blocks eta)⁻¹ *
          (PolynomialHeights.projectiveCoeffHeight
              (rationalAuxiliaryPolynomial coeff) +
            4 * (blocks : ℝ) *
              (degree ⟨0, hblocks⟩ : ℝ)) ≤
        (degree j : ℝ) * GeneralizedRoth.formHeight (M j)) :
    ∃ I : GLRAuxiliary.DerivativeIndex blocks (n + 1) degree,
      GLRAuxiliary.derivativeWeight I ≤ (blocks : ℚ) * eta ∧
      ∃ z : Fin blocks × Fin n → ℤ,
        (∀ u, |z u| ≤ (B : ℤ)) ∧
        (∀ h, AdelicMinkowski.InZOneSix
          (BasisNonvanishing.basisCombination x z h)) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          (fun u ↦ BasisNonvanishing.basisCombination x z u.1 u.2)
          (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff) ≠ 0 := by
  have hindexR := GeneralizedRoth.generalizedRothLemma
    hblocks hn (rationalAuxiliaryPolynomial_ne_zero hcoeff)
    degree hdegree
    (rationalAuxiliaryPolynomial_isMultiHomogeneous coeff hhom)
    M hM (rankDropSigmaAt_pos heta)
    (rankDropSigmaAt_le_half heta hetaOne) hratio hheight
  rw [twice_blocks_mul_rothRoot_rankDropSigmaAt heta] at hindexR
  have hindex : GeneralizedRoth.formIndex M hM
      (AuxiliaryPolynomial.ofCoefficients (fun A ↦ (coeff A : ℚ))) degree ≤
        (blocks : ℚ) * eta / 2 := by
    have hindexQ : GeneralizedRoth.formIndex M hM
        (rationalAuxiliaryPolynomial coeff) degree ≤
          (blocks : ℚ) * eta / 2 := by
      exact_mod_cast hindexR
    simpa [rationalAuxiliaryPolynomial, GLRAuxiliary.map_ofCoefficients]
      using hindexQ
  have hbudget : (blocks : ℚ) * eta / 2 +
        (blocks : ℚ) * (n : ℚ) / (B + 1 : ℚ) ≤
      (blocks : ℚ) * eta := by
    have hextra := TerminalEstimates.grid_extra_weight_le_half
      (blocks := blocks) hgrid
    linarith
  exact BasisNonvanishing.exists_integralDerivativeIndex_weight_le_blocks_mul
    M hM x hxlin hxker hxS hdegree coeff hcoeff hindex B hbudget

/-! ## Local evaluation of the transformed derivative -/

/-- Adding the derivative order embeds residual monomials into the original
monomial family. -/
theorem addDerivativeResidual_injective
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree) :
    Function.Injective (GLRAuxiliary.addDerivativeResidual I) := by
  intro J K hJK
  funext h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he := congrArg
    (fun A ↦ AuxiliaryPolynomial.exponent A (h, i)) hJK
  simp only [GLRAuxiliary.exponent_addDerivativeResidual] at he
  exact Nat.add_left_cancel he

/-- There are no more residual monomials after differentiation than there
were monomials before differentiation. -/
theorem card_residualMonomialIndex_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree) :
    Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) ≤
      Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
  exact Fintype.card_le_of_injective
    (GLRAuxiliary.addDerivativeResidual I)
    (addDerivativeResidual_injective I)

/-- The total degree left after differentiation is at most the original
total multidegree. -/
theorem totalDegree_residual_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree) :
    AuxiliaryHeightEstimates.totalDegree (GLRAuxiliary.residualDegree I) ≤
      AuxiliaryHeightEstimates.totalDegree degree := by
  unfold AuxiliaryHeightEstimates.totalDegree GLRAuxiliary.residualDegree
  exact Finset.sum_le_sum fun h _ ↦ Nat.sub_le _ _

/-- The exponents of one residual monomial sum to its total residual
multidegree. -/
theorem sum_exponent_residual
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (J : GLRAuxiliary.ResidualMonomialIndex I) :
    (∑ q : AuxiliaryPolynomial.BlockVar blocks coords,
        AuxiliaryPolynomial.exponent J q) =
      AuxiliaryHeightEstimates.totalDegree (GLRAuxiliary.residualDegree I) := by
  rw [Fintype.sum_prod_type]
  unfold AuxiliaryHeightEstimates.totalDegree
  apply Finset.sum_congr rfl
  intro h _
  exact AuxiliaryPolynomial.sum_exponent_block J h

/-- A fixed coordinate factor which is at least one may be pulled out of a
residual monomial using the original total degree. -/
theorem prod_coordinateBound_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (J : GLRAuxiliary.ResidualMonomialIndex I)
    (r : AuxiliaryPolynomial.BlockVar blocks coords → ℝ)
    (A : ℝ) (hA : 1 ≤ A) (hr : ∀ q, 0 ≤ r q) :
    (∏ q, (A * r q) ^ AuxiliaryPolynomial.exponent J q) ≤
      A ^ AuxiliaryHeightEstimates.totalDegree degree *
        ∏ q, r q ^ AuxiliaryPolynomial.exponent J q := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum Finset.univ
      (fun q ↦ AuxiliaryPolynomial.exponent J q) A]
  have hpow :
      A ^ AuxiliaryHeightEstimates.totalDegree
          (GLRAuxiliary.residualDegree I) ≤
        A ^ AuxiliaryHeightEstimates.totalDegree degree := by
    exact pow_le_pow_right₀ hA (totalDegree_residual_le I)
  rw [sum_exponent_residual J]
  exact mul_le_mul_of_nonneg_right hpow (Finset.prod_nonneg fun q _ ↦
    pow_nonneg (hr q) _)

/-- The normalized local-form coordinate of a basis combination is bounded
by the fixed denominator factor times its approximation-box radius. -/
theorem realPlaceNorm_normalizedLocalFormCoordinates_le
    {blocks coords : ℕ} (L : LocalForms coords)
    (y : Fin blocks → RatVector coords) (Q : Fin blocks → ℕ)
    (c : HeightBoxes.LocalConstants coords) (G : ℝ)
    (hy : ∀ h v i, HeightBoxes.realPlaceNorm v (L v i (y h)) ≤
      G * HeightBoxes.exponentRadius (Q h : ℝ) c v i)
    (v : PadicSubspace.Place23) (q : AuxiliaryPolynomial.BlockVar blocks coords) :
    HeightBoxes.realPlaceNorm v
        (TerminalEstimates.normalizedLocalFormCoordinates L v y q) ≤
      max 1 (G * HeightBoxes.realPlaceNorm v
        ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹)) *
        HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2 := by
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (PadicSubspace.placeNorm v)
  have hdiv : HeightBoxes.realPlaceNorm v
      (L v q.2 (y q.1) / PadicSubspace.inverseFormDenominator L v) =
      HeightBoxes.realPlaceNorm v (L v q.2 (y q.1)) *
        HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹) := by
    simp only [div_eq_mul_inv, RankDrop.realPlaceNorm_mul]
  have hform : Matrix.mulVec (PadicSubspace.formMatrix L v) (y q.1) q.2 =
      L v q.2 (y q.1) := by
    change (∑ j, L v q.2 (Pi.single j 1) * y q.1 j) = _
    rw [PadicSubspace.linearForm_eq_sum_coeff]
  rw [TerminalEstimates.normalizedLocalFormCoordinates, hform, hdiv]
  calc
    HeightBoxes.realPlaceNorm v (L v q.2 (y q.1)) *
        HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹) ≤
        (G * HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2) *
          HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹) :=
      mul_le_mul_of_nonneg_right (hy q.1 v q.2)
        (HeightBoxes.realPlaceNorm_nonneg _ _)
    _ ≤ max 1 (G * HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹)) *
        HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2 := by
      calc
        G * HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2 *
            HeightBoxes.realPlaceNorm v
              ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹) =
            (G * HeightBoxes.realPlaceNorm v
                ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹)) *
              HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2 := by ring
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg (by positivity) _)

/-- Triangle inequality for a polynomial when the monomial estimate is
needed only on its nonzero coefficients. -/
theorem realPlaceNorm_eval₂_ofCoefficients_le_of_nonzero
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (v : PadicSubspace.Place23)
    (a : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (x : AuxiliaryPolynomial.BlockVar blocks coords → ℚ)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (ha : ∀ J, HeightBoxes.realPlaceNorm v (a J : ℚ) ≤ C)
    (hmon : ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
      a J ≠ 0 → HeightBoxes.realPlaceNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1)) ≤ R) :
    HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
          (AuxiliaryPolynomial.ofCoefficients a)) ≤
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) * C * R := by
  classical
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (PadicSubspace.placeNorm v)
  have hsumQ :
      PadicSubspace.placeNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (AuxiliaryPolynomial.ofCoefficients a)) ≤
        ∑ J, PadicSubspace.placeNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J))) := by
    unfold AuxiliaryPolynomial.ofCoefficients
    change PadicSubspace.placeNorm v
        ((MvPolynomial.eval₂Hom (Int.castRingHom ℚ) x)
          (∑ m, MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp m) (a m))) ≤ _
    rw [map_sum]
    exact abv.sum_le Finset.univ
      (fun J ↦ MvPolynomial.eval₂ (Int.castRingHom ℚ) x
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J)))
  have hsumR :
      HeightBoxes.realPlaceNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (AuxiliaryPolynomial.ofCoefficients a)) ≤
        ∑ J, HeightBoxes.realPlaceNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J))) := by
    unfold HeightBoxes.realPlaceNorm
    change ((PadicSubspace.placeNorm v
      (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
        (AuxiliaryPolynomial.ofCoefficients a)) : ℚ) : ℝ) ≤ _
    rw [← Rat.cast_sum]
    exact_mod_cast hsumQ
  calc
    HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
          (AuxiliaryPolynomial.ofCoefficients a)) ≤
        ∑ J, HeightBoxes.realPlaceNorm v
          (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J))) := hsumR
    _ ≤ ∑ _J : AuxiliaryPolynomial.MonomialIndex blocks coords degree, C * R := by
      apply Finset.sum_le_sum
      intro J _
      by_cases haJ : a J = 0
      · rw [haJ]
        simp only [map_zero, MvPolynomial.monomial_zero,
          MvPolynomial.eval₂_zero]
        have hz : HeightBoxes.realPlaceNorm v 0 = 0 := by
          fin_cases v <;>
            simp [HeightBoxes.realPlaceNorm, PadicSubspace.placeNorm]
        rw [hz]
        exact mul_nonneg hC hR
      · rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J) =
            MvPolynomial.C (a J) *
              MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1 by
          rw [MvPolynomial.C_mul_monomial, mul_one]]
        change HeightBoxes.realPlaceNorm v
          ((MvPolynomial.eval₂Hom (Int.castRingHom ℚ) x)
            (MvPolynomial.C (a J) *
              MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1)) ≤ _
        rw [map_mul, MvPolynomial.eval₂Hom_C, HeightBoxes.realPlaceNorm]
        rw [PadicSubspace.placeNorm_mul, Rat.cast_mul]
        exact mul_le_mul (ha J) (hmon J haJ)
          (HeightBoxes.realPlaceNorm_nonneg _ _) hC
    _ = Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) * C * R := by
      simp [mul_assoc]

/-- Local upper bound for a transformed divided derivative, with the
surviving central-band monomial supplied explicitly. -/
theorem transformedDerivative_local_bound
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (L : LocalForms coords) (hL : PadicSubspace.IsNonsingularFamily L)
    (eta : ℚ)
    (coeff : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (hweight : GLRAuxiliary.derivativeWeight I ≤ blocks * eta)
    (y : Fin blocks → RatVector coords) (Q : Fin blocks → ℕ)
    (c : HeightBoxes.LocalConstants coords) (G : ℝ)
    (hy : ∀ h v i, HeightBoxes.realPlaceNorm v (L v i (y h)) ≤
      G * HeightBoxes.exponentRadius (Q h : ℝ) c v i)
    (P : ℝ)
    (hcoeff : ∀ v J, ‖GLRAuxiliary.transformedCoefficient
      (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I J coeff‖ ≤ P)
    (hvanish : ∀ v J, GLRAuxiliary.OutsideCentralBand eta J →
      GLRAuxiliary.transformedCoefficient
        (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I J coeff = 0)
    (v : PadicSubspace.Place23)
    (Jmax : GLRAuxiliary.ResidualMonomialIndex I)
    (hJmax : ¬ GLRAuxiliary.OutsideCentralBand eta Jmax)
    (hmax : ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
      ¬ GLRAuxiliary.OutsideCentralBand eta J →
      TerminalEstimates.residualMonomialRadius c J Q v ≤
        TerminalEstimates.residualMonomialRadius c Jmax Q v) :
    HeightBoxes.realPlaceNorm v
      (MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun q ↦ y q.1 q.2)
        (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff)) ≤
      Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) * max 1 P *
        (max 1 (G * HeightBoxes.realPlaceNorm v
          ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
            AuxiliaryHeightEstimates.totalDegree degree *
        TerminalEstimates.residualMonomialRadius c Jmax Q v := by
  let A : ℝ := max 1 (G * HeightBoxes.realPlaceNorm v
    ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  rw [← TerminalEstimates.eval₂_integralInverse_changeCoordinates_normalized
    L hL v (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff) y,
    ← ofCoefficients_transformedCoefficient
      (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I coeff]
  have hlocal := realPlaceNorm_eval₂_ofCoefficients_le_of_nonzero
      (degree := GLRAuxiliary.residualDegree I)
      v (fun J : GLRAuxiliary.ResidualMonomialIndex I ↦
        GLRAuxiliary.transformedCoefficient
          (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I J coeff)
      (TerminalEstimates.normalizedLocalFormCoordinates L v y)
      (C := max 1 P)
      (R := A ^ AuxiliaryHeightEstimates.totalDegree degree *
        TerminalEstimates.residualMonomialRadius c Jmax Q v)
      (zero_le_one.trans (le_max_left _ _))
      (mul_nonneg (pow_nonneg hA0 _) (Finset.prod_nonneg fun h _ ↦
        Finset.prod_nonneg fun i _ ↦ pow_nonneg (Real.rpow_nonneg (by positivity) _) _)) (by
        intro J
        exact (TerminalEstimates.realPlaceNorm_intCast_le_max_one_norm v _).trans
          (max_le_max_left 1 (hcoeff v J))) (by
        intro J
        intro haJ
        have hJ : ¬ GLRAuxiliary.OutsideCentralBand eta J := by
          intro hout
          exact haJ (hvanish v J hout)
        refine (TerminalEstimates.realPlaceNorm_eval₂_monomial_one_le
              v _ (fun q ↦ A * HeightBoxes.exponentRadius
                (Q q.1 : ℝ) c v q.2) ?_ J).trans ?_
        · intro q
          exact realPlaceNorm_normalizedLocalFormCoordinates_le
            L y Q c G hy v q
        · refine (prod_coordinateBound_le J
            (fun q ↦ HeightBoxes.exponentRadius (Q q.1 : ℝ) c v q.2)
            A hA (fun q ↦ Real.rpow_nonneg (by positivity) _)).trans ?_
          have hradius : (∏ q, HeightBoxes.exponentRadius
              (Q q.1 : ℝ) c v q.2 ^ AuxiliaryPolynomial.exponent J q) ≤
              TerminalEstimates.residualMonomialRadius c Jmax Q v := by
            simpa [TerminalEstimates.residualMonomialRadius,
              Fintype.prod_prod_type] using hmax J hJ
          exact mul_le_mul_of_nonneg_left hradius (pow_nonneg hA0 _))
  simpa only [A, mul_assoc] using hlocal

/-- Product-formula endpoint for the transformed derivative.  The only
numerical input is the strict product bound for any independently chosen
surviving central monomial at the three places. -/
theorem dividedDerivative_eval_eq_zero_of_centralProduct_lt_one
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (L : LocalForms coords) (hL : PadicSubspace.IsNonsingularFamily L)
    (eta : ℚ)
    (coeff : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (hweight : GLRAuxiliary.derivativeWeight I ≤ blocks * eta)
    (y : Fin blocks → RatVector coords)
    (hyS : ∀ h, AdelicMinkowski.InZOneSix (y h))
    (Q : Fin blocks → ℕ) (c : HeightBoxes.LocalConstants coords) (G : ℝ)
    (hy : ∀ h v i, HeightBoxes.realPlaceNorm v (L v i (y h)) ≤
      G * HeightBoxes.exponentRadius (Q h : ℝ) c v i)
    (P : ℝ)
    (hcoeff : ∀ v J, ‖GLRAuxiliary.transformedCoefficient
      (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I J coeff‖ ≤ P)
    (hvanish : ∀ v J, GLRAuxiliary.OutsideCentralBand eta J →
      GLRAuxiliary.transformedCoefficient
        (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I J coeff = 0)
    (hsmall : ∀ J : PadicSubspace.Place23 →
        GLRAuxiliary.ResidualMonomialIndex I,
      (∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v)) →
      (∏ v,
        Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) * max 1 P *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree *
          TerminalEstimates.residualMonomialRadius c (J v) Q v) < 1) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun q ↦ y q.1 q.2)
      (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff) = 0 := by
  classical
  by_cases hall : ∀ v : PadicSubspace.Place23,
      ∃ J : GLRAuxiliary.ResidualMonomialIndex I,
        ¬ GLRAuxiliary.OutsideCentralBand eta J
  · have hmax : ∀ v : PadicSubspace.Place23,
        ∃ Jmax : GLRAuxiliary.ResidualMonomialIndex I,
          ¬ GLRAuxiliary.OutsideCentralBand eta Jmax ∧
          ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
            ¬ GLRAuxiliary.OutsideCentralBand eta J →
            TerminalEstimates.residualMonomialRadius c J Q v ≤
              TerminalEstimates.residualMonomialRadius c Jmax Q v := by
      intro v
      let s : Finset (GLRAuxiliary.ResidualMonomialIndex I) :=
        Finset.univ.filter fun J ↦
          ¬ GLRAuxiliary.OutsideCentralBand eta J
      have hs : s.Nonempty := by
        obtain ⟨J, hJ⟩ := hall v
        exact ⟨J, by simp [s, hJ]⟩
      obtain ⟨Jmax, hJmem, hJmax⟩ := Finset.exists_max_image s
        (fun J ↦ TerminalEstimates.residualMonomialRadius c J Q v) hs
      refine ⟨Jmax, (Finset.mem_filter.mp hJmem).2, ?_⟩
      intro J hJ
      exact hJmax J (by simp [s, hJ])
    choose Jmax hJmax using hmax
    apply TerminalEstimates.eval₂_int_eq_zero_of_localBounds
      (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff)
      (fun q ↦ y q.1 q.2)
      (fun q ↦ SIntegerSix.of_inZOneSix_coordinate (hyS q.1) q.2)
      (fun v ↦
        Fintype.card (GLRAuxiliary.ResidualMonomialIndex I) * max 1 P *
          (max 1 (G * HeightBoxes.realPlaceNorm v
            ((PadicSubspace.inverseFormDenominator L v : ℚ)⁻¹))) ^
              AuxiliaryHeightEstimates.totalDegree degree *
          TerminalEstimates.residualMonomialRadius c (Jmax v) Q v)
    · intro v
      exact transformedDerivative_local_bound L hL eta coeff I hweight
        y Q c G hy P hcoeff hvanish v (Jmax v) (hJmax v).1 (hJmax v).2
    · exact hsmall Jmax (fun v ↦ (hJmax v).1)
  · push_neg at hall
    obtain ⟨v, hv⟩ := hall
    have hzero : (fun J : GLRAuxiliary.ResidualMonomialIndex I ↦
        GLRAuxiliary.transformedCoefficient
          (fun w ↦ PadicSubspace.integralInverseFormMatrix L w)
          v I J coeff) = 0 := by
      funext J
      exact hvanish v J (hv J)
    rw [← TerminalEstimates.eval₂_integralInverse_changeCoordinates_normalized
      L hL v (GLRAuxiliary.dividedDerivativeOfCoefficients I coeff) y,
      ← ofCoefficients_transformedCoefficient
        (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v I coeff,
      hzero]
    simp [AuxiliaryPolynomial.ofCoefficients]

end

end Erdos407.RankDrop

#print axioms Erdos407.RankDrop.exists_integralDerivativeIndex_of_rothHeight
