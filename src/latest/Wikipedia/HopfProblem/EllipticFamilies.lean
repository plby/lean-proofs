import Wikipedia.HopfProblem.EllipticFlatTorus
import Wikipedia.HopfProblem.EllipticLinearMonodromy
import Wikipedia.HopfProblem.SpecialPeriodsRotations

/-!
# The logarithmic affine action on the actual local torus families

The explicit order-three and order-four period maps carry the prescribed
affine cyclic action.  Although their underlying real torus families are
products, holomorphicity is proved in the varying-period complex atlas by
an explicit complex lift and the period-matrix covariance identity.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

/-- The two explicitly constructed holomorphic local period maps. -/
def familyPeriods (j : Kind) : HolomorphicPeriodMap ℂ Disc :=
  match j with
  | .three => threePeriodMap
  | .four => fourPeriodMap

/-- The actual holomorphic base rotations. -/
def familyRotation (j : Kind) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) Disc Disc ω :=
  match j with
  | .three => threeRotation
  | .four => fourRotation

theorem familyRotation_iterate_order (j : Kind) :
    (familyRotation j)^[j.order] = id := by
  cases j
  · exact discRotateThree_iterate_order
  · exact discRotateFour_iterate_order

/-- The total space is the actual torus family of the explicit periods. -/
abbrev Family (j : Kind) := (familyPeriods j).TotalSpace

abbrev FamilyModel := ℂ × ComplexPlane₂

local instance familyCoveringChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance familyCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ ℂ)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) Disc ComplexPlane₂

theorem familyPeriodEquiv_matrix (j : Kind) (z : Disc) (x : RealCoordinates) :
    (familyPeriods j).periodEquiv z x =
      ((familyPeriods j).point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem familyPeriods_matrix_covariance (j : Kind) (z : Disc) :
    ((familyPeriods j).point (familyRotation j z)).val.matrix *
        j.matrix.map (Int.castRingHom ℂ) =
      linearMatrix j ((familyPeriods j).point z) * ((familyPeriods j).point z).val.matrix := by
  cases j
  · exact threePeriodMap_matrix_covariance z
  · exact fourPeriodMap_matrix_covariance z

/-- The varying complex periods intertwine the constant integral action. -/
theorem familyPeriodEquiv_flatLinear (j : Kind) (z : Disc) (x : RealCoordinates) :
    (familyPeriods j).periodEquiv (familyRotation j z) (flatLinear j x) =
      linearMatrix j ((familyPeriods j).point z) *ᵥ (familyPeriods j).periodEquiv z x := by
  rw [familyPeriodEquiv_matrix, flatLinear_complexCast, Matrix.mulVec_mulVec,
    familyPeriodEquiv_matrix, Matrix.mulVec_mulVec, familyPeriods_matrix_covariance]

theorem familyPeriodEquiv_symm_linearMatrix (j : Kind) (z : Disc) (w : ComplexPlane₂) :
    ((familyPeriods j).periodEquiv (familyRotation j z)).symm
        (linearMatrix j ((familyPeriods j).point z) *ᵥ w) =
      flatLinear j (((familyPeriods j).periodEquiv z).symm w) := by
  apply ((familyPeriods j).periodEquiv (familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, familyPeriodEquiv_flatLinear,
    LinearEquiv.apply_symm_apply]

/-- The affine transformation on the underlying actual real-torus family. -/
def familyPermutation (j : Kind) (v : Lattice) : Equiv.Perm (Family j) :=
  (familyRotation j).toEquiv.prodCongr (flatTorusAffine j v).toEquiv

@[simp] theorem familyPermutation_apply (j : Kind) (v : Lattice) (x : Family j) :
    familyPermutation j v x = (familyRotation j x.1, flatTorusAffine j v x.2) := rfl

/-- Its explicit complex lift over the rotated base. -/
def familyLift (j : Kind) (v : Lattice) (x : Disc × ComplexPlane₂) : Disc × ComplexPlane₂ :=
  (familyRotation j x.1,
    linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
      (familyPeriods j).periodEquiv (familyRotation j x.1)
        ((1 / (j.order : ℝ)) • realCast v))

theorem familyLift_quotientMap (j : Kind) (v : Lattice) (x : Disc × ComplexPlane₂) :
    (familyPeriods j).quotientMap (familyLift j v x) =
      familyPermutation j v ((familyPeriods j).quotientMap x) := by
  change (familyRotation j x.1,
    standardLattice.mkQ (((familyPeriods j).periodEquiv (familyRotation j x.1)).symm
      (linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
        (familyPeriods j).periodEquiv (familyRotation j x.1)
          ((1 / (j.order : ℝ)) • realCast v)))) =
    (familyRotation j x.1,
      flatTorusAffine j v (standardLattice.mkQ (((familyPeriods j).periodEquiv x.1).symm x.2)))
  rw [flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    familyPeriodEquiv_symm_linearMatrix]
  rfl

theorem familyLinearLift_holomorphic (j : Kind) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun x : Disc × ComplexPlane₂ => linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : Disc × ComplexPlane₂ → Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs : ContMDiff (modelWithCornersSelf ℂ FamilyModel)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (Prod.snd : Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := (familyPeriods j).holomorphic_tau.comp hf
  have hμ := (familyPeriods j).holomorphic_mu.comp hf
  have hτ0 : ∀ x : Disc × ComplexPlane₂, ((familyPeriods j).point x.1).val.τ ≠ 0 :=
    fun x => ((familyPeriods j).point x.1).val.τ_ne_zero ((familyPeriods j).point x.1).property.1
  have h₀ := (contMDiff_pi_space.mp hs) 0
  have h₁ := (contMDiff_pi_space.mp hs) 1
  cases j
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (-1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((((contMDiff_const (c := (1 : ℂ))).sub hμ).div₀ hτ hτ0).mul h₀).add h₁)
        using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((hμ.neg.div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]

theorem familyLift_holomorphic (j : Kind) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyLift j v) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : Disc × ComplexPlane₂ => familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw := (familyLinearLift_holomorphic j).add
    (((familyPeriods j).holomorphic_periodEquiv_const
      ((1 / (j.order : ℝ)) • realCast v)).comp hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

/-- Holomorphicity holds for the actual varying-period complex atlas. -/
theorem familyPermutation_holomorphic (j : Kind) (v : Lattice) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyPermutation j v) := by
  let := (familyPeriods j).coveringAction
  let := (familyPeriods j).totalChartedSpace
  apply CoveringQuotient.contMDiff_of_comp (E := FamilyModel)
    (familyPeriods j).quotientCoveringMap (modelWithCornersSelf ℂ FamilyModel) ω
  have h := ((familyPeriods j).quotientMap_holomorphic).comp (familyLift_holomorphic j v)
  convert h using 1
  funext x
  exact (familyLift_quotientMap j v x).symm

end Wikipedia.HopfProblem.Elliptic
