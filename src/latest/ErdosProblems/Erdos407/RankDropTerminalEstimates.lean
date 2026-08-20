/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RankDrop
import ErdosProblems.Erdos407.SIntegerPolynomialEvaluation

/-!
# Numerical estimates for the terminal rank-drop contradiction

The GLR support theorem confines every surviving residual monomial to a
small band around the uniform coordinate load.  The local constants in the
dimension-generic rank-drop theorem are arbitrary real numbers, so the
resulting error is naturally measured by their `L¹` norm.  These lemmas keep
that dependence explicit; in particular they do not assume an unstated
uniform bound on the local constants.
-/

namespace Erdos407.RankDrop.TerminalEstimates

open scoped BigOperators

noncomputable section

/-- A weighted sum changes by at most the `L¹` norm of the weights times a
uniform displacement from the center. -/
theorem weighted_sum_le_center_add_l1_error
    {ι : Type*} [Fintype ι] (c w : ι → ℝ) (center radius : ℝ)
    (hw : ∀ i, |w i - center| ≤ radius) :
    (∑ i, c i * w i) ≤
      center * (∑ i, c i) + radius * (∑ i, |c i|) := by
  calc
    (∑ i, c i * w i) =
        ∑ i, (center * c i + c i * (w i - center)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, (center * c i + |c i| * radius) := by
      apply Finset.sum_le_sum
      intro i _
      exact add_le_add (le_refl _) (by
        calc
        c i * (w i - center) ≤ |c i * (w i - center)| := le_abs_self _
        _ = |c i| * |w i - center| := abs_mul _ _
        _ ≤ |c i| * radius :=
          mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _))
    _ = center * (∑ i, c i) + radius * (∑ i, |c i|) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_comm]

/-- A point which is not outside a symmetric band is within the band in
every coordinate. -/
theorem abs_sub_center_le_of_not_outsideCentralBand
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (eta : ℚ) (J : GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ¬ GLRAuxiliary.OutsideCentralBand eta J) (i : Fin coords) :
    |(GLRAuxiliary.coordinateWeight J i : ℝ) -
        ((blocks : ℚ) / (coords : ℚ) : ℝ)| ≤
      (2 * (blocks : ℚ) * eta : ℚ) := by
  have hi := hJ
  simp only [GLRAuxiliary.OutsideCentralBand, not_exists, not_or,
    not_le] at hi
  have hlo := (hi i).1
  have hhi := (hi i).2
  have habs :
      |GLRAuxiliary.coordinateWeight J i -
          (blocks : ℚ) / (coords : ℚ)| ≤ 2 * (blocks : ℚ) * eta := by
    rw [abs_le]
    constructor <;> linarith
  exact_mod_cast habs

/-- The exact one-place exponent estimate for a monomial surviving the GLR
central-band vanishing. -/
theorem weighted_coordinateWeight_le_of_not_outsideCentralBand
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ¬ GLRAuxiliary.OutsideCentralBand eta J)
    (c : Fin coords → ℝ) :
    (∑ i, c i * (GLRAuxiliary.coordinateWeight J i : ℝ)) ≤
      (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * (∑ i, c i) +
        ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) * (∑ i, |c i|) := by
  apply weighted_sum_le_center_add_l1_error
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    abs_sub_center_le_of_not_outsideCentralBand eta J hJ

/-- Sum the preceding estimate over the three places.  The residual
monomial is allowed to be chosen independently at each place, as happens
when bounding the largest local monomial. -/
theorem weighted_coordinateWeight_sum_places_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) :
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
      (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) *
          (∑ v, ∑ i, c v i) +
        ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) := by
  calc
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
        ∑ v, (
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) *
              (∑ i, c v i) +
            ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
              (∑ i, |c v i|)) := by
      apply Finset.sum_le_sum
      intro v _
      exact weighted_coordinateWeight_le_of_not_outsideCentralBand
        heta (J v) (hJ v) (c v)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- If the band error consumes at most half of the main negative saving,
every surviving choice of local monomials has a uniformly negative weighted
exponent. -/
theorem weighted_coordinateWeight_sum_places_le_neg_half
    {blocks coords : ℕ} (hcoords : 0 < coords)
    {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) {delta : ℝ}
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (herror :
      ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 2) :
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
      -((((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 2) := by
  have hcenter :
      (0 : ℝ) ≤ (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast (div_nonneg (by positivity : (0 : ℚ) ≤ blocks)
      (by positivity : (0 : ℚ) ≤ coords))
  calc
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) *
            (∑ v, ∑ i, c v i) +
          ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
            (∑ v, ∑ i, |c v i|) :=
      weighted_coordinateWeight_sum_places_le heta J hJ c
    _ ≤ (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * (-delta) +
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hc hcenter) herror
    _ = -((((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 2) := by
      ring

/-- Quarter-sized band error leaves three quarters of the main saving for
the later logarithmic-degree and coefficient losses. -/
theorem weighted_coordinateWeight_sum_places_le_neg_three_quarters
    {blocks coords : ℕ} (hcoords : 0 < coords)
    {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) {delta : ℝ}
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (herror :
      ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4) :
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
      -(3 * (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4) := by
  have hcenter :
      (0 : ℝ) ≤ (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast (div_nonneg (by positivity : (0 : ℚ) ≤ blocks)
      (by positivity : (0 : ℚ) ≤ coords))
  calc
    (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) *
            (∑ v, ∑ i, c v i) +
          ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
            (∑ v, ∑ i, |c v i|) :=
      weighted_coordinateWeight_sum_places_le heta J hJ c
    _ ≤ (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * (-delta) +
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4 :=
      add_le_add (mul_le_mul_of_nonneg_left hc hcenter) herror
    _ = -(3 * (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4) := by
      ring

/-! ## Choosing the band width and the number of blocks -/

/-- For arbitrary real local constants, choose a positive rational band
width and then enough blocks for the GLR dimension count.  The band error is
at most half of the main saving.  This is the quantitative choice needed by
the exact dimension-generic theorem; a fixed width would not suffice when
the entries of `c` are unbounded. -/
theorem exists_auxiliary_parameters {coords : ℕ} (hcoords : 0 < coords)
    (c : HeightBoxes.LocalConstants coords) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℚ, 0 < eta ∧ eta ≤ 1 / 4 ∧
      ∃ blocks : ℕ, 0 < blocks ∧
        (6 : ℚ) * coords < blocks * eta ^ 2 ∧
        ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
            (∑ v, ∑ i, |c v i|) ≤
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4 := by
  let C : ℝ := ∑ v, ∑ i, |c v i|
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hnR : (0 : ℝ) < coords := by exact_mod_cast hcoords
  have hden : 0 < 16 * (coords : ℝ) * (C + 1) := by positivity
  have htarget : 0 < delta / (16 * (coords : ℝ) * (C + 1)) :=
    div_pos hdelta hden
  have hquarter : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
  obtain ⟨eta, heta, hetaSmall⟩ :=
    exists_pos_rat_lt (lt_min hquarter htarget)
  have hetaQuarter : eta ≤ (1 / 4 : ℚ) := by
    apply (Rat.cast_le (K := ℝ)).mp
    have h : (eta : ℝ) < (1 / 4 : ℝ) :=
      hetaSmall.trans_le (min_le_left _ _)
    norm_num at h ⊢
    exact h.le
  obtain ⟨blocks, hblocksLarge⟩ :=
    exists_nat_gt ((6 : ℚ) * coords / eta ^ 2)
  have hetaSq : (0 : ℚ) < eta ^ 2 := sq_pos_of_pos heta
  have hmany : (6 : ℚ) * coords < blocks * eta ^ 2 := by
    exact (div_lt_iff₀ hetaSq).mp hblocksLarge
  have hblocks : 0 < blocks := by
    by_contra hb
    have hb0 : blocks = 0 := Nat.eq_zero_of_not_pos hb
    rw [hb0] at hmany
    have : (0 : ℚ) < 6 * coords := by positivity
    simpa using (this.trans hmany)
  refine ⟨eta, heta, hetaQuarter, blocks, hblocks, hmany, ?_⟩
  have hetaR : (0 : ℝ) < eta := by exact_mod_cast heta
  have hetaTarget : (eta : ℝ) <
      delta / (16 * (coords : ℝ) * (C + 1)) :=
    hetaSmall.trans_le (min_le_right _ _)
  have hraw :
      (eta : ℝ) * (16 * (coords : ℝ) * (C + 1)) < delta :=
    (lt_div_iff₀ hden).mp hetaTarget
  have hcompare :
      8 * (coords : ℝ) * (eta : ℝ) * C ≤
        (eta : ℝ) * (16 * (coords : ℝ) * (C + 1)) := by
    have hnonneg :
        0 ≤ 8 * (coords : ℝ) * (eta : ℝ) * (C + 2) := by positivity
    nlinarith
  have hsmall :
      8 * (coords : ℝ) * (eta : ℝ) * C ≤ delta :=
    hcompare.trans hraw.le
  dsimp [C] at hsmall ⊢
  have hmR : (0 : ℝ) < blocks := by exact_mod_cast hblocks
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  calc
    2 * (blocks : ℝ) * (eta : ℝ) * (∑ v, ∑ i, |c v i|) =
        ((blocks : ℝ) / (coords : ℝ)) *
          (8 * (coords : ℝ) * (eta : ℝ) *
            (∑ v, ∑ i, |c v i|)) / 4 := by
      field_simp
      <;> ring
    _ ≤ ((blocks : ℝ) / (coords : ℝ)) * delta / 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmall (by positivity)) (by norm_num)

/-- Choose the finite-grid bound so the additional tangential derivative
cost is at most half of the GLR derivative budget. -/
theorem exists_gridBound {eta : ℚ} (heta : 0 < eta) (n : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧
      (n : ℚ) / (B + 1 : ℚ) ≤ eta / 2 := by
  obtain ⟨B, hB⟩ := exists_nat_gt (((2 : ℚ) * n) / eta)
  have hquotNonneg : (0 : ℚ) ≤ ((2 : ℚ) * n) / eta := by positivity
  have hBposQ : (0 : ℚ) < B := hquotNonneg.trans_lt hB
  have hBpos : 0 < B := by exact_mod_cast hBposQ
  have hmul : (2 : ℚ) * n < eta * B := by
    simpa [mul_comm] using (div_lt_iff₀ heta).mp hB
  refine ⟨B, hBpos, ?_⟩
  have hden : (0 : ℚ) < B + 1 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

theorem grid_extra_weight_le_half {blocks n : ℕ} {eta : ℚ} {B : ℕ}
    (hB : (n : ℚ) / (B + 1 : ℚ) ≤ eta / 2) :
    (blocks : ℚ) * (n : ℚ) / (B + 1 : ℚ) ≤
      (blocks : ℚ) * eta / 2 := by
  calc
    (blocks : ℚ) * (n : ℚ) / (B + 1 : ℚ) =
        (blocks : ℚ) * ((n : ℚ) / (B + 1 : ℚ)) := by ring
    _ ≤ (blocks : ℚ) * (eta / 2) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (blocks : ℚ) * eta / 2 := by ring

/-- The logarithm of a natural cutoff eventually dominates any fixed
constant, in the quotient form used by both terminal slope estimates. -/
theorem exists_log_cutoff_div_le {C target : ℝ} (htarget : 0 < target) :
    ∃ Q₀ : ℕ, 2 ≤ Q₀ ∧ C / Real.log (Q₀ : ℝ) ≤ target := by
  have htendsto : Filter.Tendsto
      (fun Q : ℕ ↦ Real.log (Q : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heventually : ∀ᶠ Q : ℕ in Filter.atTop,
      C / target < Real.log (Q : ℝ) :=
    htendsto.eventually_gt_atTop (C / target)
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨N, hN⟩ := heventually
  let Q₀ := max 2 N
  have hQ₀ : 2 ≤ Q₀ := le_max_left _ _
  have hlarge : C / target < Real.log (Q₀ : ℝ) :=
    hN Q₀ (le_max_right _ _)
  have hlog : 0 < Real.log (Q₀ : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Q₀ by omega)
  refine ⟨Q₀, hQ₀, ?_⟩
  apply (div_le_iff₀ hlog).2
  simpa [mul_comm] using ((div_lt_iff₀ htarget).1 hlarge).le

/-! ## Local evaluation of a full coefficient vector -/

/-- Evaluating an integral GLR coordinate change is the same as evaluating
the original polynomial after multiplying each block by the coordinate
matrix. -/
theorem eval₂_changeCoordinates
    {blocks coords : ℕ}
    (T : PadicSubspace.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : PadicSubspace.Place23)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ)
    (x : AuxiliaryPolynomial.BlockVar blocks coords → ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x
        (GLRAuxiliary.changeCoordinates T v P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun q ↦ ∑ j, (T v q.2 j : ℚ) * x (q.1, j)) P := by
  unfold GLRAuxiliary.changeCoordinates
  change MvPolynomial.eval₂ (Int.castRingHom ℚ) x
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun q => ∑ j, MvPolynomial.C (T v q.2 j) *
          MvPolynomial.X (q.1, j)) P) = _
  rw [← MvPolynomial.eval₂_assoc]
  congr 1
  funext q
  change (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) x)
      (∑ j, MvPolynomial.C (T v q.2 j) *
        MvPolynomial.X (q.1, j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X']
  rfl

/-- A point whose blockwise matrix image is `y` evaluates the changed
polynomial exactly as `y` evaluates the original one. -/
theorem eval₂_changeCoordinates_eq_of_mulVec_eq
    {blocks coords : ℕ}
    (T : PadicSubspace.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : PadicSubspace.Place23)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ)
    (x y : AuxiliaryPolynomial.BlockVar blocks coords → ℚ)
    (hxy : ∀ q, ∑ j, (T v q.2 j : ℚ) * x (q.1, j) = y q) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x
        (GLRAuxiliary.changeCoordinates T v P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) y P := by
  rw [eval₂_changeCoordinates]
  congr 1
  funext q
  exact hxy q

/-- Local-form coordinates divided by the common denominator used to clear
the inverse form matrix. -/
noncomputable def normalizedLocalFormCoordinates
    {blocks coords : ℕ} (L : LocalForms coords)
    (v : PadicSubspace.Place23)
    (y : Fin blocks → RatVector coords) :
    AuxiliaryPolynomial.BlockVar blocks coords → ℚ :=
  fun q ↦ Matrix.mulVec (PadicSubspace.formMatrix L v) (y q.1) q.2 /
    PadicSubspace.inverseFormDenominator L v

/-- The denominator-cleared inverse form matrix sends normalized local-form
coordinates back to the original point. -/
theorem integralInverse_mul_normalizedLocalFormCoordinates
    {blocks coords : ℕ} (L : LocalForms coords)
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23)
    (y : Fin blocks → RatVector coords)
    (q : AuxiliaryPolynomial.BlockVar blocks coords) :
    (∑ j, (PadicSubspace.integralInverseFormMatrix L v q.2 j : ℚ) *
        normalizedLocalFormCoordinates L v y (q.1, j)) = y q.1 q.2 := by
  let A := PadicSubspace.formMatrix L v
  let den : ℚ := PadicSubspace.inverseFormDenominator L v
  have hden : den ≠ 0 := by
    dsimp [den]
    exact_mod_cast PadicSubspace.inverseFormDenominator_ne_zero L v
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (PadicSubspace.formMatrix_det_ne_zero hL v)
  have hT := PadicSubspace.integralInverseFormMatrix_map_eq_smul L v
  change Matrix.mulVec
      ((PadicSubspace.integralInverseFormMatrix L v).map
        (Int.castRingHom ℚ))
      (fun j ↦ Matrix.mulVec A (y q.1) j / den) q.2 = _
  have hx : (fun j ↦ Matrix.mulVec A (y q.1) j / den) =
      den⁻¹ • Matrix.mulVec A (y q.1) := by
    funext j
    simp [div_eq_mul_inv, mul_comm]
  rw [hx, hT]
  change Matrix.mulVec (den • A⁻¹)
      (den⁻¹ • Matrix.mulVec A (y q.1)) q.2 = _
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  simp only [mul_inv_cancel₀ hden, one_smul]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit,
    Matrix.one_mulVec]

/-- Exact evaluation identity for the canonical integral inverse local
coordinate change. -/
theorem eval₂_integralInverse_changeCoordinates_normalized
    {blocks coords : ℕ} (L : LocalForms coords)
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ)
    (y : Fin blocks → RatVector coords) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (normalizedLocalFormCoordinates L v y)
        (GLRAuxiliary.changeCoordinates
          (fun w ↦ PadicSubspace.integralInverseFormMatrix L w) v P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun q ↦ y q.1 q.2) P := by
  apply eval₂_changeCoordinates_eq_of_mulVec_eq
  exact integralInverse_mul_normalizedLocalFormCoordinates L hL v y

/-- Terminal restricted-product contradiction: an integral polynomial at an
`S`-integral rational point must vanish if the product of its three retained
local norms is strictly less than one. -/
theorem eval₂_int_eq_zero_of_prod_realPlaceNorm_lt_one
    {ι : Type*} (P : MvPolynomial ι ℤ) (x : ι → ℚ)
    (hx : ∀ i, SIntegerSix.IsSInteger (x i))
    (hsmall : (∏ v, HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x P)) < 1) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x P = 0 := by
  by_contra hne
  exact (not_lt_of_ge
    (SIntegerSix.one_le_prod_realPlaceNorm_mvPolynomial_eval₂_int
      P x hx hne)) hsmall

/-- Coordinatewise local upper bounds whose product is below one force an
integral polynomial to vanish at an `S`-integral point. -/
theorem eval₂_int_eq_zero_of_localBounds
    {ι : Type*} (P : MvPolynomial ι ℤ) (x : ι → ℚ)
    (hx : ∀ i, SIntegerSix.IsSInteger (x i))
    (R : PadicSubspace.Place23 → ℝ)
    (hlocal : ∀ v, HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x P) ≤ R v)
    (hsmall : (∏ v, R v) < 1) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x P = 0 := by
  apply eval₂_int_eq_zero_of_prod_realPlaceNorm_lt_one P x hx
  exact (Finset.prod_le_prod
    (fun v _ ↦ HeightBoxes.realPlaceNorm_nonneg v _) fun v _ ↦ hlocal v).trans_lt
      hsmall

/-- A local triangle-inequality bound for an integral multihomogeneous
polynomial.  Coefficients and monomials are bounded separately so this lemma
can be applied directly to the transformed GLR derivative. -/
theorem realPlaceNorm_eval₂_ofCoefficients_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (v : PadicSubspace.Place23)
    (a : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (x : AuxiliaryPolynomial.BlockVar blocks coords → ℚ)
    {C R : ℝ} (hC : 0 ≤ C)
    (ha : ∀ J, HeightBoxes.realPlaceNorm v (a J : ℚ) ≤ C)
    (hmon : ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
      HeightBoxes.realPlaceNorm v
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
      rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) (a J) =
          MvPolynomial.C (a J) *
            MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1 by
        rw [MvPolynomial.C_mul_monomial, mul_one]]
      change HeightBoxes.realPlaceNorm v
        ((MvPolynomial.eval₂Hom (Int.castRingHom ℚ) x)
          (MvPolynomial.C (a J) *
            MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1)) ≤ _
      rw [map_mul, MvPolynomial.eval₂Hom_C, HeightBoxes.realPlaceNorm]
      rw [PadicSubspace.placeNorm_mul, Rat.cast_mul]
      exact mul_le_mul (ha J) (hmon J)
        (HeightBoxes.realPlaceNorm_nonneg _ _) hC
    _ = Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) * C * R := by
      simp [mul_assoc]

/-- Multiplicativity of the real-valued local norm for natural powers. -/
theorem realPlaceNorm_pow (v : PadicSubspace.Place23) (q : ℚ) (e : ℕ) :
    HeightBoxes.realPlaceNorm v (q ^ e) =
      HeightBoxes.realPlaceNorm v q ^ e := by
  induction e with
  | zero => simp [HeightBoxes.realPlaceNorm]
  | succ e ih =>
      rw [pow_succ, pow_succ, RankDrop.realPlaceNorm_mul, ih]

/-- The local norm of a monomial evaluation is the product of the local
coordinate norms to the indicated exponents. -/
theorem realPlaceNorm_eval₂_monomial_one
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (v : PadicSubspace.Place23)
    (x : AuxiliaryPolynomial.BlockVar blocks coords → ℚ)
    (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1)) =
      ∏ q, HeightBoxes.realPlaceNorm v (x q) ^
        AuxiliaryPolynomial.exponent J q := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · change HeightBoxes.realPlaceNorm v
        (∏ q, x q ^ AuxiliaryPolynomial.exponent J q) = _
    induction (Finset.univ : Finset
        (AuxiliaryPolynomial.BlockVar blocks coords)) using Finset.induction_on with
    | empty => simp [HeightBoxes.realPlaceNorm]
    | @insert q s hq ih =>
        rw [Finset.prod_insert hq, Finset.prod_insert hq,
          RankDrop.realPlaceNorm_mul, realPlaceNorm_pow, ih]
  · intro q
    simp

/-- Coordinatewise local bounds imply the corresponding monomial bound. -/
theorem realPlaceNorm_eval₂_monomial_one_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (v : PadicSubspace.Place23)
    (x : AuxiliaryPolynomial.BlockVar blocks coords → ℚ)
    (r : AuxiliaryPolynomial.BlockVar blocks coords → ℝ)
    (hx : ∀ q, HeightBoxes.realPlaceNorm v (x q) ≤ r q)
    (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    HeightBoxes.realPlaceNorm v
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp J) 1)) ≤
      ∏ q, r q ^ AuxiliaryPolynomial.exponent J q := by
  rw [realPlaceNorm_eval₂_monomial_one]
  apply Finset.prod_le_prod
  · intro q _
    exact pow_nonneg (HeightBoxes.realPlaceNorm_nonneg _ _) _
  · intro q _
    exact pow_le_pow_left₀ (HeightBoxes.realPlaceNorm_nonneg _ _)
      (hx q) _

/-- At every retained place an integral coefficient is bounded by the
maximum of one and its ordinary norm. -/
theorem realPlaceNorm_intCast_le_max_one_norm
    (v : PadicSubspace.Place23) (z : ℤ) :
    HeightBoxes.realPlaceNorm v (z : ℚ) ≤ max 1 ‖z‖ := by
  fin_cases v
  · unfold HeightBoxes.realPlaceNorm PadicSubspace.placeNorm
    have hz : ((|(z : ℚ)| : ℚ) : ℝ) = ‖z‖ := by
      norm_num [Int.norm_eq_abs]
    rw [hz]
    exact le_max_right _ _
  · unfold HeightBoxes.realPlaceNorm PadicSubspace.placeNorm
    have hz := padicNorm.of_int (p := 2) z
    have hzR : ((padicNorm 2 (z : ℚ) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast hz
    change ((padicNorm 2 (z : ℚ) : ℚ) : ℝ) ≤ max 1 ‖z‖
    exact hzR.trans (le_max_left _ _)
  · unfold HeightBoxes.realPlaceNorm PadicSubspace.placeNorm
    have hz := padicNorm.of_int (p := 3) z
    have hzR : ((padicNorm 3 (z : ℚ) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast hz
    change ((padicNorm 3 (z : ℚ) : ℚ) : ℝ) ≤ max 1 ‖z‖
    exact hzR.trans (le_max_left _ _)

/-! ## Products of the scale radii of a residual monomial -/

/-- The contribution of the box radii to one residual monomial at one
place. -/
noncomputable def residualMonomialRadius
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) (v : PadicSubspace.Place23) : ℝ :=
  ∏ h, ∏ i, HeightBoxes.exponentRadius (Q h : ℝ) c v i ^
    AuxiliaryPolynomial.exponent J (h, i)

/-- The product of all local monomial radii is the exponential of the
ordinary logarithmic exponent. -/
theorem prod_residualMonomialRadius_eq_exp
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) (hQ : ∀ h, 2 ≤ Q h) :
    (∏ v, residualMonomialRadius c (J v) Q v) =
      Real.exp (∑ v, ∑ i, ∑ h,
        (AuxiliaryPolynomial.exponent (J v) (h, i) : ℝ) *
          c v i * Real.log (Q h : ℝ)) := by
  have hfactor (v : PadicSubspace.Place23) (h : Fin blocks)
      (i : Fin coords) :
      HeightBoxes.exponentRadius (Q h : ℝ) c v i ^
          AuxiliaryPolynomial.exponent (J v) (h, i) =
        Real.exp ((AuxiliaryPolynomial.exponent (J v) (h, i) : ℝ) *
          c v i * Real.log (Q h : ℝ)) := by
    have hQpos : (0 : ℝ) < Q h := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hQ h))
    rw [HeightBoxes.exponentRadius,
      Real.rpow_def_of_pos hQpos, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [residualMonomialRadius, hfactor]
  let f := fun (v : PadicSubspace.Place23) (h : Fin blocks)
      (i : Fin coords) ↦
    (AuxiliaryPolynomial.exponent (J v) (h, i) : ℝ) *
      c v i * Real.log (Q h : ℝ)
  calc
    (∏ v, ∏ h, ∏ i, Real.exp (f v h i)) =
        ∏ v, ∏ h, Real.exp (∑ i, f v h i) := by
      apply Finset.prod_congr rfl
      intro v hv
      apply Finset.prod_congr rfl
      intro h hh
      symm
      simpa using Real.exp_sum (s := (Finset.univ : Finset (Fin coords)))
        (f := fun i ↦ f v h i)
    _ = ∏ v, Real.exp (∑ h, ∑ i, f v h i) := by
      apply Finset.prod_congr rfl
      intro v hv
      symm
      simpa using Real.exp_sum (s := (Finset.univ : Finset (Fin blocks)))
        (f := fun h ↦ ∑ i, f v h i)
    _ = Real.exp (∑ v, ∑ h, ∑ i, f v h i) := by
      symm
      simpa using Real.exp_sum
        (s := (Finset.univ : Finset PadicSubspace.Place23))
        (f := fun v ↦ ∑ h, ∑ i, f v h i)
    _ = Real.exp (∑ v, ∑ i, ∑ h,
        (AuxiliaryPolynomial.exponent (J v) (h, i) : ℝ) *
          c v i * Real.log (Q h : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm

/-! ## The logarithmic-degree perturbation -/

/-- If the common scale parameter is at least twice the logarithm of the
block scale, the corresponding floor degree is positive. -/
theorem logarithmicDegree_pos_of_two_log_le {D : ℝ} {Q : ℕ}
    (hQ : 2 ≤ Q) (hD : 2 * Real.log (Q : ℝ) ≤ D) :
    0 < logarithmicDegree D Q := by
  apply Nat.floor_pos.mpr
  have hlog : 0 < Real.log (Q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Q by omega)
  apply (le_div_iff₀ hlog).2
  linarith

/-- Power separation of two natural scales gives the floor-degree ratio
needed by the generalized Roth lemma.  The factor `2` is precisely the
one-unit loss incurred by taking the floor. -/
theorem logarithmicDegree_ratio_of_log_separation
    {D sigma : ℝ} {Q R K : ℕ}
    (hQ : 2 ≤ Q) (hR : 2 ≤ R) (hsigma : 0 < sigma)
    (hK : (2 : ℝ) ≤ sigma * (K : ℝ))
    (hsep : (K : ℝ) * Real.log (Q : ℝ) < Real.log (R : ℝ))
    (hD : 2 * Real.log (Q : ℝ) ≤ D) :
    (logarithmicDegree D R : ℝ) /
        (logarithmicDegree D Q : ℝ) ≤ sigma := by
  have hlogQ : 0 < Real.log (Q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Q by omega)
  have hlogR : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R by omega)
  have hD0 : 0 ≤ D := by linarith
  have hquot : 2 ≤ D / Real.log (Q : ℝ) := by
    exact (le_div_iff₀ hlogQ).2 hD
  have hnonneg : 0 ≤ D / Real.log (Q : ℝ) - 1 := by linarith
  have hmain : D ≤ sigma *
      (D / Real.log (Q : ℝ) - 1) * Real.log (R : ℝ) := by
    have hfirst : D ≤ sigma *
        (D / Real.log (Q : ℝ) - 1) *
          ((K : ℝ) * Real.log (Q : ℝ)) := by
      have heq : sigma * (D / Real.log (Q : ℝ) - 1) *
          ((K : ℝ) * Real.log (Q : ℝ)) =
          (sigma * (K : ℝ)) *
            (D - Real.log (Q : ℝ)) := by
        field_simp
      rw [heq]
      have hsub : 0 ≤ D - Real.log (Q : ℝ) := by linarith
      calc
        D ≤ 2 * (D - Real.log (Q : ℝ)) := by linarith
        _ ≤ (sigma * (K : ℝ)) *
            (D - Real.log (Q : ℝ)) :=
          mul_le_mul_of_nonneg_right hK hsub
    exact hfirst.trans (mul_le_mul_of_nonneg_left hsep.le
      (mul_nonneg hsigma.le hnonneg))
  have hslack : D / Real.log (R : ℝ) ≤
      sigma * (D / Real.log (Q : ℝ) - 1) :=
    (div_le_iff₀ hlogR).2 hmain
  have hdegrees := logarithmicDegree_ratio_of_slack
    hD0 hQ hR hsigma.le hslack
  have hdQ : (0 : ℝ) < logarithmicDegree D Q := by
    exact_mod_cast logarithmicDegree_pos_of_two_log_le hQ hD
  exact (div_le_iff₀ hdQ).2 hdegrees

/-- A common lower cutoff for all block scales gives a uniform upper bound
for the total logarithmic degree. -/
theorem sum_logarithmicDegree_le_cutoff
    {blocks : ℕ} {D : ℝ} {Q : Fin blocks → ℕ} {Q₀ : ℕ}
    (hD : 0 ≤ D) (hQ₀ : 2 ≤ Q₀) (hQ : ∀ h, Q₀ ≤ Q h) :
    (∑ h, (logarithmicDegree D (Q h) : ℝ)) ≤
      (blocks : ℝ) * (D / Real.log (Q₀ : ℝ)) := by
  have hlog₀ : 0 < Real.log (Q₀ : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Q₀ by omega)
  calc
    (∑ h, (logarithmicDegree D (Q h) : ℝ)) ≤
        ∑ _h : Fin blocks, D / Real.log (Q₀ : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      have hQh : 2 ≤ Q h := hQ₀.trans (hQ h)
      refine (logarithmicDegree_cast_le hD hQh).trans ?_
      have hlog : Real.log (Q₀ : ℝ) ≤ Real.log (Q h : ℝ) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; positivity)
          (by simp only [Set.mem_Ioi]; positivity)
          (by exact_mod_cast hQ h)
      exact div_le_div_of_nonneg_left hD hlog₀ hlog
    _ = (blocks : ℝ) * (D / Real.log (Q₀ : ℝ)) := by simp

/-- A coefficient height linear in total degree satisfies the pointwise
height hypothesis of the generalized Roth lemma once all scales lie beyond
a cutoff making that linear slope sufficiently small. -/
theorem roth_height_hypothesis_of_linear_degreeHeight
    {blocks n : ℕ} (hblocks : 0 < blocks)
    {sigma kappa A H D : ℝ} (hsigma : 0 < sigma)
    (hkappa : 0 < kappa) (hA : 0 ≤ A) (hD : 0 < D)
    {Q₀ : ℕ} (hQ₀ : 2 ≤ Q₀)
    (Q : Fin blocks → ℕ) (hQ : ∀ h, Q₀ ≤ Q h)
    (hDlarge : ∀ h, 2 * Real.log (Q h : ℝ) ≤ D)
    (M : GeneralizedRoth.FormFamily blocks n)
    (hMheight : ∀ h, kappa * Real.log (Q h : ℝ) ≤
      GeneralizedRoth.formHeight (M h))
    (hH : H ≤ A *
      (∑ h, (logarithmicDegree D (Q h) : ℝ)))
    (hslope : (n : ℝ) * sigma⁻¹ *
      ((A + 4) * (blocks : ℝ) / Real.log (Q₀ : ℝ)) ≤ kappa / 2) :
    ∀ j,
      (n : ℝ) * sigma⁻¹ *
          (H + 4 * (blocks : ℝ) *
            (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ)) ≤
        (logarithmicDegree D (Q j) : ℝ) *
          GeneralizedRoth.formHeight (M j) := by
  have hD0 : 0 ≤ D := hD.le
  have hlogQ₀ : 0 < Real.log (Q₀ : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Q₀ by omega)
  have hsum := sum_logarithmicDegree_le_cutoff hD0 hQ₀ hQ
  have hq0 : 2 ≤ Q ⟨0, hblocks⟩ := hQ₀.trans (hQ _)
  have hd0raw := logarithmicDegree_cast_le hD0 hq0
  have hlog0 : Real.log (Q₀ : ℝ) ≤
      Real.log (Q ⟨0, hblocks⟩ : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hQ ⟨0, hblocks⟩)
  have hd0 : (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ) ≤
      D / Real.log (Q₀ : ℝ) :=
    hd0raw.trans (div_le_div_of_nonneg_left hD0 hlogQ₀ hlog0)
  have hinside : H + 4 * (blocks : ℝ) *
        (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ) ≤
      ((A + 4) * (blocks : ℝ) / Real.log (Q₀ : ℝ)) * D := by
    calc
      H + 4 * (blocks : ℝ) *
          (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ) ≤
          A * (∑ h, (logarithmicDegree D (Q h) : ℝ)) +
            4 * (blocks : ℝ) *
              (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ) :=
        add_le_add hH (le_refl _)
      _ ≤ A * ((blocks : ℝ) * (D / Real.log (Q₀ : ℝ))) +
            4 * (blocks : ℝ) * (D / Real.log (Q₀ : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hA)
          (mul_le_mul_of_nonneg_left hd0 (by positivity))
      _ = ((A + 4) * (blocks : ℝ) /
          Real.log (Q₀ : ℝ)) * D := by field_simp
  intro j
  have hleft : (n : ℝ) * sigma⁻¹ *
        (H + 4 * (blocks : ℝ) *
          (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ)) ≤
      kappa * D / 2 := by
    calc
      (n : ℝ) * sigma⁻¹ *
          (H + 4 * (blocks : ℝ) *
            (logarithmicDegree D (Q ⟨0, hblocks⟩) : ℝ)) ≤
          (n : ℝ) * sigma⁻¹ *
            (((A + 4) * (blocks : ℝ) /
              Real.log (Q₀ : ℝ)) * D) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = ((n : ℝ) * sigma⁻¹ *
          ((A + 4) * (blocks : ℝ) / Real.log (Q₀ : ℝ))) * D := by ring
      _ ≤ (kappa / 2) * D :=
        mul_le_mul_of_nonneg_right hslope hD0
      _ = kappa * D / 2 := by ring
  have hQj : 2 ≤ Q j := hQ₀.trans (hQ j)
  have hfloor := logarithmicDegree_mul_log_bounds hD0 hQj
  have hhalf : D / 2 ≤ D - Real.log (Q j : ℝ) := by
    linarith [hDlarge j]
  have hright : kappa * D / 2 ≤
      (logarithmicDegree D (Q j) : ℝ) *
        GeneralizedRoth.formHeight (M j) := by
    calc
      kappa * D / 2 ≤ kappa *
          ((logarithmicDegree D (Q j) : ℝ) *
            Real.log (Q j : ℝ)) := by
        rw [show kappa * D / 2 = kappa * (D / 2) by ring]
        exact mul_le_mul_of_nonneg_left
          (hhalf.trans hfloor.1.le) hkappa.le
      _ = (logarithmicDegree D (Q j) : ℝ) *
          (kappa * Real.log (Q j : ℝ)) := by ring
      _ ≤ (logarithmicDegree D (Q j) : ℝ) *
          GeneralizedRoth.formHeight (M j) :=
        mul_le_mul_of_nonneg_left (hMheight j) (by positivity)
  exact hleft.trans hright

/-- The logarithm of the scale contribution of a residual monomial, written
using its normalized block exponents and the actual block scales
`s h = d_h log Q_h`. -/
noncomputable def scaleWeightedExponent
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (s : Fin blocks → ℝ) : ℝ :=
  ∑ v, ∑ i, ∑ h,
    c v i *
      (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
        (degree h : ℚ) : ℚ) : ℝ) * s h

theorem sum_real_exponent_div_eq_coordinateWeight
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (J : GLRAuxiliary.ResidualMonomialIndex I) (i : Fin coords) :
    (∑ h,
      (((AuxiliaryPolynomial.exponent J (h, i) : ℚ) /
        (degree h : ℚ) : ℚ) : ℝ)) =
      (GLRAuxiliary.coordinateWeight J i : ℝ) := by
  unfold GLRAuxiliary.coordinateWeight
  rw [Rat.cast_sum]

/-- With `s_h = d_h log Q_h`, the normalized expression is the ordinary
logarithmic monomial exponent. -/
theorem scaleWeightedExponent_degree_mul_log
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) :
    scaleWeightedExponent c J
        (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ)) =
      ∑ v, ∑ i, ∑ h,
        (AuxiliaryPolynomial.exponent (J v) (h, i) : ℝ) *
          c v i * Real.log (Q h : ℝ) := by
  unfold scaleWeightedExponent
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  have hd : (degree h : ℝ) ≠ 0 := by exact_mod_cast (hdegree h).ne'
  push_cast
  field_simp

/-- The radius-product identity in the normalized scale notation used by
the central-band estimates. -/
theorem prod_residualMonomialRadius_eq_exp_scaleWeightedExponent
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) (hQ : ∀ h, 2 ≤ Q h) :
    (∏ v, residualMonomialRadius c (J v) Q v) =
      Real.exp (scaleWeightedExponent c J
        (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ))) := by
  rw [prod_residualMonomialRadius_eq_exp c J Q hQ,
    scaleWeightedExponent_degree_mul_log hdegree]

/-- A negative normalized logarithmic exponent makes the product of the
three local monomial radii strictly smaller than one. -/
theorem prod_residualMonomialRadius_lt_one
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (Q : Fin blocks → ℕ) (hQ : ∀ h, 2 ≤ Q h)
    (hneg : scaleWeightedExponent c J
      (fun h ↦ (degree h : ℝ) * Real.log (Q h : ℝ)) < 0) :
    (∏ v, residualMonomialRadius c (J v) Q v) < 1 := by
  rw [prod_residualMonomialRadius_eq_exp_scaleWeightedExponent
    hdegree c J Q hQ, Real.exp_lt_one_iff]
  exact hneg

/-- Replacing each `d_h log Q_h` by a common value `D` costs at most the
uniform displacement times the corresponding absolute weighted load. -/
theorem scaleWeightedExponent_le_common_add_error
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    (c : HeightBoxes.LocalConstants coords)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (s : Fin blocks → ℝ) (D E : ℝ)
    (hs : ∀ h, |s h - D| ≤ E) :
    scaleWeightedExponent c J s ≤
      D * (∑ v, ∑ i, c v i *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
      E * (∑ v, ∑ i, |c v i| *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) := by
  have hone (v : PadicSubspace.Place23) (i : Fin coords) :
      (∑ h, c v i *
          (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
            (degree h : ℚ) : ℚ) : ℝ) * s h) ≤
        D * (c v i * (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
          E * (|c v i| *
            (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) := by
    have h := weighted_sum_le_center_add_l1_error
      (fun h : Fin blocks ↦ c v i *
        (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
          (degree h : ℚ) : ℚ) : ℝ)) s D E hs
    calc
      (∑ h, c v i *
          (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
            (degree h : ℚ) : ℚ) : ℝ) * s h) =
          ∑ h, (c v i *
            (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
              (degree h : ℚ) : ℚ) : ℝ)) * s h := by
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ ≤ D * (∑ h, c v i *
            (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
              (degree h : ℚ) : ℚ) : ℝ)) +
          E * (∑ h, |c v i *
            (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
              (degree h : ℚ) : ℚ) : ℝ)|) := h
      _ = D * (c v i *
            (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
          E * (|c v i| *
            (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) := by
        have hnonneg (h : Fin blocks) :
            0 ≤ (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
              (degree h : ℚ) : ℚ) : ℝ) := by
          exact_mod_cast (div_nonneg (by positivity :
            (0 : ℚ) ≤ AuxiliaryPolynomial.exponent (J v) (h, i))
            (by positivity : (0 : ℚ) ≤ degree h))
        simp_rw [abs_mul, abs_of_nonneg (hnonneg _)]
        rw [← Finset.mul_sum, ← Finset.mul_sum,
          sum_real_exponent_div_eq_coordinateWeight]
  unfold scaleWeightedExponent
  calc
    (∑ v, ∑ i, ∑ h,
        c v i *
          (((AuxiliaryPolynomial.exponent (J v) (h, i) : ℚ) /
            (degree h : ℚ) : ℚ) : ℝ) * s h) ≤
        ∑ v, ∑ i,
          (D * (c v i *
              (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
            E * (|c v i| *
              (GLRAuxiliary.coordinateWeight (J v) i : ℝ))) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro i _
      exact hone v i
    _ = D * (∑ v, ∑ i, c v i *
          (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
        E * (∑ v, ∑ i, |c v i| *
          (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- In the central band, the absolute local constants weighted by the
residual coordinate loads are bounded by the upper edge of that band. -/
theorem abs_weighted_coordinateWeight_sum_places_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ}
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) :
    (∑ v, ∑ i, |c v i| *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
      ((((blocks : ℚ) / (coords : ℚ) + 2 * blocks * eta : ℚ) : ℚ) : ℝ) *
        (∑ v, ∑ i, |c v i|) := by
  have hupper (v : PadicSubspace.Place23) (i : Fin coords) :
      (GLRAuxiliary.coordinateWeight (J v) i : ℝ) ≤
        (((blocks : ℚ) / (coords : ℚ) + 2 * blocks * eta : ℚ) : ℝ) := by
    have hv := hJ v
    simp only [GLRAuxiliary.OutsideCentralBand, not_exists, not_or,
      not_le] at hv
    exact_mod_cast (hv i).2.le
  calc
    (∑ v, ∑ i, |c v i| *
        (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) ≤
        ∑ v, ∑ i, |c v i| *
          (((blocks : ℚ) / (coords : ℚ) + 2 * blocks * eta : ℚ) : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hupper v i) (abs_nonneg _)
    _ = _ := by
      simp only [← Finset.sum_mul]
      ring

/-- Combining the central-band saving with the floor-degree perturbation
leaves one half of the main negative exponent. -/
theorem scaleWeightedExponent_le_neg_half
    {blocks coords : ℕ} (hcoords : 0 < coords)
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) {delta : ℝ}
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (hband :
      ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4)
    (s : Fin blocks → ℝ) (D E : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hs : ∀ h, |s h - D| ≤ E)
    (hfloor : E *
        ((((blocks : ℚ) / (coords : ℚ) +
            2 * blocks * eta : ℚ) : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta * D / 4) :
    scaleWeightedExponent c J s ≤
      -((((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta * D / 2) := by
  have hmain := weighted_coordinateWeight_sum_places_le_neg_three_quarters
    hcoords heta J hJ c hc hband
  have herr := abs_weighted_coordinateWeight_sum_places_le J hJ c
  have hcombine := scaleWeightedExponent_le_common_add_error
    hdegree c J s D E hs
  calc
    scaleWeightedExponent c J s ≤
        D * (∑ v, ∑ i, c v i *
          (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) +
        E * (∑ v, ∑ i, |c v i| *
          (GLRAuxiliary.coordinateWeight (J v) i : ℝ)) := hcombine
    _ ≤ D * (-(3 *
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4)) +
        E * (((((blocks : ℚ) / (coords : ℚ) +
            2 * blocks * eta : ℚ) : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hD)
        (mul_le_mul_of_nonneg_left herr hE)
    _ ≤ D * (-(3 *
          (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4)) +
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta * D / 4 :=
      by nlinarith [hfloor]
    _ = -((((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) *
        delta * D / 2) := by ring

/-- Under positive block count, saving, and common scale, the preceding
bound is strictly negative. -/
theorem scaleWeightedExponent_neg
    {blocks coords : ℕ} (hblocks : 0 < blocks) (hcoords : 0 < coords)
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    {I : GLRAuxiliary.DerivativeIndex blocks coords degree}
    {eta : ℚ} (heta : 0 ≤ eta)
    (J : PadicSubspace.Place23 → GLRAuxiliary.ResidualMonomialIndex I)
    (hJ : ∀ v, ¬ GLRAuxiliary.OutsideCentralBand eta (J v))
    (c : HeightBoxes.LocalConstants coords) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (hband :
      ((2 * (blocks : ℚ) * eta : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta / 4)
    (s : Fin blocks → ℝ) (D E : ℝ)
    (hD : 0 < D) (hE : 0 ≤ E)
    (hs : ∀ h, |s h - D| ≤ E)
    (hfloor : E *
        ((((blocks : ℚ) / (coords : ℚ) +
            2 * blocks * eta : ℚ) : ℚ) : ℝ) *
          (∑ v, ∑ i, |c v i|) ≤
        (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta * D / 4) :
    scaleWeightedExponent c J s < 0 := by
  have hle := scaleWeightedExponent_le_neg_half hcoords hdegree heta J hJ
    c hc hband s D E hD.le hE hs hfloor
  have hcenter : (0 : ℝ) <
      (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast (div_pos (by exact_mod_cast hblocks : (0 : ℚ) < blocks)
      (by exact_mod_cast hcoords : (0 : ℚ) < coords))
  have hpos : 0 <
      (((blocks : ℚ) / (coords : ℚ) : ℚ) : ℝ) * delta * D / 2 := by
    positivity
  exact hle.trans_lt (neg_neg_of_pos hpos)

end

end Erdos407.RankDrop.TerminalEstimates

#print axioms Erdos407.RankDrop.TerminalEstimates.weighted_coordinateWeight_sum_places_le_neg_half
