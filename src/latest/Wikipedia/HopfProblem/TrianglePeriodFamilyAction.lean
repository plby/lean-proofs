import Wikipedia.HopfProblem.TrianglePeriodFamilyData
import Wikipedia.HopfProblem.TrianglePeriodFamilyLattice

/-!
# The actual holomorphic action on a covariant triangle period family

The integral representation acts on the real coordinate torus, and hence
on the actual varying-period family.  The all-word period covariance
identifies this action with an explicit holomorphic complex-linear lift.
The complex structure is the atlas determined by the supplied periods.
-/

noncomputable section

open Set Matrix
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

abbrev TotalSpace := D.periods.TotalSpace

/-- The diagonal action on the actual topological period-torus family. -/
@[instance_reducible] def totalAction : MulAction TriangleGroup D.TotalSpace := by
  let := triangleTorusAction
  exact inferInstanceAs (MulAction TriangleGroup (B × RealTorus₄))

theorem totalAction_apply (g : TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    g • x = (g • x.1, triangleTorusHomeomorph g x.2) := rfl

theorem totalAction_continuous :
    letI := D.totalAction
    ContinuousConstSMul TriangleGroup D.TotalSpace := by
  let := D.totalAction
  constructor
  intro g
  exact ((D.base_holomorphic g).continuous.comp continuous_fst).prodMk
    ((triangleTorusHomeomorph g).continuous.comp continuous_snd)

theorem totalAction_zeroSection (g : TriangleGroup) (b : B) :
    letI := D.totalAction
    g • D.periods.zeroSection b = D.periods.zeroSection (g • b) := by
  let := D.totalAction
  change (g • b, triangleTorusHomeomorph g 0) = (g • b, 0)
  rw [triangleTorusHomeomorph_zero]

/-- The real period isomorphism has exactly the specified complex columns. -/
theorem periodEquiv_matrix (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv b x =
      (D.periods.point b).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem realEquiv_complexCast (g : TriangleGroup) (x : RealPlane₄) :
    (fun i => ((triangleRealEquiv g x) i : ℂ)) =
      dualComplexMatrix g *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [triangleRealEquiv_apply, dualComplexMatrix, Matrix.mulVec, dotProduct]

/-- The actual real action and the constructed complex matrices intertwine. -/
theorem periodEquiv_monodromy (g : TriangleGroup) (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv (g • b) (triangleRealEquiv g x) =
      D.rightBlock g b *ᵥ D.periods.periodEquiv b x := by
  rw [D.periodEquiv_matrix, realEquiv_complexCast, Matrix.mulVec_mulVec,
    D.periodEquiv_matrix, Matrix.mulVec_mulVec, D.matrix_covariance]

theorem periodEquiv_symm_monodromy (g : TriangleGroup) (b : B) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (g • b)).symm (D.rightBlock g b *ᵥ w) =
      triangleRealEquiv g ((D.periods.periodEquiv b).symm w) := by
  apply (D.periods.periodEquiv (g • b)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy,
    LinearEquiv.apply_symm_apply]

/-- The actual linear lift on the covering complex vector family. -/
def complexLift (g : TriangleGroup) (x : B × ComplexPlane₂) : B × ComplexPlane₂ :=
  (g • x.1, D.rightBlock g x.1 *ᵥ x.2)

@[simp] theorem complexLift_one (x : B × ComplexPlane₂) : D.complexLift 1 x = x := by
  simp [complexLift]

theorem complexLift_mul (g h : TriangleGroup) (x : B × ComplexPlane₂) :
    D.complexLift (g * h) x = D.complexLift g (D.complexLift h x) := by
  simp only [complexLift, mul_smul, D.rightBlock_mul, Matrix.mulVec_mulVec]

/-- The cocycle defines a genuine action on the covering vector spaces. -/
@[instance_reducible] def vectorAction : MulAction TriangleGroup (B × ComplexPlane₂) where
  smul := D.complexLift
  one_smul := D.complexLift_one
  mul_smul := D.complexLift_mul

theorem complexLift_quotientMap (g : TriangleGroup) (x : B × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift g x) = g • D.periods.quotientMap x := by
  let := D.totalAction
  change (g • x.1, standardLattice.mkQ
    ((D.periods.periodEquiv (g • x.1)).symm (D.rightBlock g x.1 *ᵥ x.2))) =
    (g • x.1, triangleTorusHomeomorph g
      (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, triangleTorusHomeomorph_mkQ]

local instance coveringChartedSpace :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

local instance coveringManifold [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ V)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

theorem periodMatrix_entry_holomorphic (i : Fin 2) (k : Fin 4) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => (D.periods.point b).val.matrix i k) := by
  fin_cases i
  · fin_cases k
    · exact contMDiff_const.mul D.periods.holomorphic_mu
    · exact D.periods.holomorphic_tau
    · exact contMDiff_const
    · exact contMDiff_const
  · fin_cases k
    · exact D.periods.holomorphic_beta
    · exact D.periods.holomorphic_mu
    · exact contMDiff_const
    · exact contMDiff_const

/-- Every constructed matrix entry is holomorphic, directly from its
period-matrix formula and the actual holomorphic base action. -/
theorem rightBlock_entry_holomorphic (g : TriangleGroup) (i k : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => D.rightBlock g b i k) := by
  have h₀ := ((D.periodMatrix_entry_holomorphic i 0).comp (D.base_holomorphic g)).mul
    (contMDiff_const (c := dualComplexMatrix g 0 (![2, 3] k)))
  have h₁ := ((D.periodMatrix_entry_holomorphic i 1).comp (D.base_holomorphic g)).mul
    (contMDiff_const (c := dualComplexMatrix g 1 (![2, 3] k)))
  have h₂ := ((D.periodMatrix_entry_holomorphic i 2).comp (D.base_holomorphic g)).mul
    (contMDiff_const (c := dualComplexMatrix g 2 (![2, 3] k)))
  have h₃ := ((D.periodMatrix_entry_holomorphic i 3).comp (D.base_holomorphic g)).mul
    (contMDiff_const (c := dualComplexMatrix g 3 (![2, 3] k)))
  convert ((h₀.add h₁).add h₂).add h₃ using 1
  funext b
  simp [rightBlock, Matrix.mul_apply, Fin.sum_univ_four, add_assoc, Function.comp_def]

theorem linearLift_holomorphic (g : TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun x : B × ComplexPlane₂ => D.rightBlock g x.1 *ᵥ x.2) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ V) ω (Prod.fst : B × ComplexPlane₂ → B) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs : ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (Prod.snd : B × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  apply contMDiff_pi_space.mpr
  intro i
  have h₀ := ((D.rightBlock_entry_holomorphic g i 0).comp hf).mul
    ((contMDiff_pi_space.mp hs) 0)
  have h₁ := ((D.rightBlock_entry_holomorphic g i 1).comp hf).mul
    ((contMDiff_pi_space.mp hs) 1)
  convert h₀.add h₁ using 1
  funext x
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_def]

theorem complexLift_holomorphic (g : TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.complexLift g) := by
  have hf : ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ V) ω (fun x : B × ComplexPlane₂ => g • x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (D.base_holomorphic g).comp contMDiff_fst
  have hs := D.linearLift_holomorphic g
  rw [modelWithCornersSelf_prod] at hf hs ⊢
  exact hf.prodMk hs

/-- The actual total action is holomorphic for the supplied varying
period atlas, not a fixed real-product atlas. -/
theorem totalAction_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B]
    (g : TriangleGroup) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply CoveringQuotient.contMDiff_of_comp (E := V × ComplexPlane₂)
    D.periods.quotientCoveringMap (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic g)
  convert h using 1
  funext x
  exact (D.complexLift_quotientMap g x).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
