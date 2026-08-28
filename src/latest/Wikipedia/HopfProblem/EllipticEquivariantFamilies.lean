import Wikipedia.HopfProblem.EllipticEquivariantMonodromy

/-!
# Holomorphic logarithmic actions for arbitrary equivariant periods

The actual affine cyclic action on the real torus family is holomorphic
in the complex atlas of any admissible holomorphic period map with the
prescribed covariance.  The proof uses the explicit complex lift, not an
identification with the special concrete local period triples.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

local instance equivariantCoveringChartedSpace :
    ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance equivariantCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ ℂ)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) Disc ComplexPlane₂

/-- The actual complex affine lift over the rotated base. -/
def complexLift (v : Lattice) (x : Disc × ComplexPlane₂) : Disc × ComplexPlane₂ :=
  (familyRotation j x.1,
    linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
      D.periods.periodEquiv (familyRotation j x.1) ((1 / (j.order : ℝ)) • realCast v))

theorem complexLift_quotientMap (v : Lattice) (x : Disc × ComplexPlane₂) :
    D.periods.quotientMap (D.complexLift v x) =
      D.permutation v (D.periods.quotientMap x) := by
  change (familyRotation j x.1,
    standardLattice.mkQ ((D.periods.periodEquiv (familyRotation j x.1)).symm
      (linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
        D.periods.periodEquiv (familyRotation j x.1)
          ((1 / (j.order : ℝ)) • realCast v)))) =
    (familyRotation j x.1,
      flatTorusAffine j v (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    D.periodEquiv_symm_linearMatrix]
  rfl

/-- The complex linear part varies holomorphically with the arbitrary period map. -/
theorem linearLift_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun x : Disc × ComplexPlane₂ => linearMatrix j (D.periods.point x.1) *ᵥ x.2) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : Disc × ComplexPlane₂ → Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs : ContMDiff (modelWithCornersSelf ℂ FamilyModel)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (Prod.snd : Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := D.periods.holomorphic_tau.comp hf
  have hμ := D.periods.holomorphic_mu.comp hf
  have hτ0 : ∀ x : Disc × ComplexPlane₂, (D.periods.point x.1).val.τ ≠ 0 :=
    fun x => (D.periods.point x.1).val.τ_ne_zero (D.periods.point x.1).property.1
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

theorem complexLift_holomorphic (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (D.complexLift v) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : Disc × ComplexPlane₂ => familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw := D.linearLift_holomorphic.add
    ((D.periods.holomorphic_periodEquiv_const ((1 / (j.order : ℝ)) • realCast v)).comp hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

/-- The affine permutation is holomorphic for this input period map's
actual varying-period atlas. -/
theorem permutation_holomorphic (v : Lattice) :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (D.permutation v) := by
  let := D.periods.coveringAction
  let := D.periods.totalChartedSpace
  apply CoveringQuotient.contMDiff_of_comp (E := FamilyModel)
    D.periods.quotientCoveringMap (modelWithCornersSelf ℂ FamilyModel) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic v)
  convert h using 1
  funext x
  exact (D.complexLift_quotientMap v x).symm

/-- Every element of the proved finite cyclic action is holomorphic. -/
theorem action_holomorphic (v : Lattice) (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := D.action v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  exact CyclicAction.smul_contMDiff (D.permutation v)
    (D.permutation_pow_order v hv) (D.permutation_holomorphic v) g

/-- The action maps are actual biholomorphisms, including their proved
holomorphic inverses, for every covariant period map. -/
def actionBiholomorph (v : Lattice) (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    Diffeomorph (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel)
      D.TotalSpace D.TotalSpace ω := by
  letI := D.periods.totalChartedSpace
  let := D.action v hv
  exact {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := fun x => inv_smul_smul g x
    right_inv := fun x => smul_inv_smul g x
    contMDiff_toFun := D.action_holomorphic v hv g
    contMDiff_invFun := D.action_holomorphic v hv g⁻¹ }

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
