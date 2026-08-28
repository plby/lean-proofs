import Wikipedia.HopfProblem.CoveringManifold
import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Topology.Instances.Matrix
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Submersion

/-!
# Varying period tori

The family construction in Theorem 3.4(iv), from holomorphic period data.
The input consists of actual functions taking values in the checked period
domain. No existence of the special equivariant functions of §3.1–3.3 is
assumed as an axiom; their construction remains a separate task.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem

abbrev RealPlane₄ := Fin 4 → ℝ

/-- The fixed integer lattice in real coordinates, used to trivialize the
underlying topological family. -/
def standardLattice : Submodule ℤ RealPlane₄ :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))

instance standardLattice_discrete : DiscreteTopology standardLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_isZLattice : IsZLattice ℝ standardLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_closed : IsClosed (standardLattice : Set RealPlane₄) := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact AddSubgroup.isClosed_of_discrete (H := standardLattice.toAddSubgroup)

abbrev RealTorus₄ := RealPlane₄ ⧸ standardLattice

instance realTorus_t3 : T3Space RealTorus₄ := inferInstance

instance realTorus_secondCountable : SecondCountableTopology RealTorus₄ :=
  standardLattice.isQuotientMap_mkQ.secondCountableTopology standardLattice.isOpenMap_mkQ

instance realTorus_pathConnected : PathConnectedSpace RealTorus₄ :=
  standardLattice.mkQ_surjective.pathConnectedSpace standardLattice.continuous_mkQ

instance realTorus_compact : CompactSpace RealTorus₄ := by
  have hper : ∀ z w, w ∈ standardLattice → standardLattice.mkQ (z + w) = standardLattice.mkQ z := by
    intro z w hw
    have hw' : standardLattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero standardLattice).mpr hw
    rw [map_add, hw', add_zero]
  have h := IsZLattice.isCompact_range_of_periodic standardLattice standardLattice.mkQ
    standardLattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr standardLattice.mkQ_surjective] using h⟩

/-- A holomorphic triple satisfying the pointwise nondegeneracy conditions.
This is the input to the torus-family part of Theorem 3.4. -/
structure HolomorphicPeriodMap (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] where
  point : B → PeriodDomain
  holomorphic_tau : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
    (fun b => (point b).val.τ)
  holomorphic_mu : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
    (fun b => (point b).val.μ)
  holomorphic_beta : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
    (fun b => (point b).val.β)

namespace HolomorphicPeriodMap

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- The real isomorphism from fixed coordinates to the varying period vectors. -/
def periodEquiv (b : B) : RealPlane₄ ≃ₗ[ℝ] ComplexPlane₂ :=
  (P.point b).realEquiv.trans complexCoordinates

theorem periodEquiv_apply (b : B) (v : RealPlane₄) :
    P.periodEquiv b v = complexCoordinates ((P.point b).val.realMatrix *ᵥ v) := by
  simp only [periodEquiv, LinearEquiv.trans_apply, PeriodDomain.realEquiv_apply]

theorem periodEquiv_symm_apply (b : B) (z : ComplexPlane₂) :
    (P.periodEquiv b).symm z = (P.point b).val.realMatrix⁻¹ *ᵥ complexCoordinates.symm z := by
  simp [periodEquiv, PeriodDomain.realEquiv, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]

theorem continuous_realMatrix : Continuous (fun b => (P.point b).val.realMatrix) := by
  have ht := P.holomorphic_tau.continuous
  have hm := P.holomorphic_mu.continuous
  have hb := P.holomorphic_beta.continuous
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [PeriodPoint.realMatrix] <;> fun_prop

theorem continuous_realMatrix_inv : Continuous (fun b => (P.point b).val.realMatrix⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hd : (P.point b).val.realMatrix.det ≠ 0 :=
    ne_of_lt ((P.point b).val.det_realMatrix_neg (P.point b).property)
  have hinv : ContinuousAt (fun A : Matrix (Fin 4) (Fin 4) ℝ => A⁻¹)
      (P.point b).val.realMatrix := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd
  exact hinv.comp (f := fun b : B => (P.point b).val.realMatrix)
    (P.continuous_realMatrix.continuousAt (x := b))

theorem continuous_periodEquiv : Continuous (fun x : B × RealPlane₄ => P.periodEquiv x.1 x.2) := by
  simp_rw [periodEquiv_apply]
  exact complexCoordinates.toContinuousLinearEquiv.continuous.comp
    ((P.continuous_realMatrix.comp continuous_fst).matrix_mulVec continuous_snd)

theorem continuous_periodEquiv_symm :
    Continuous (fun x : B × ComplexPlane₂ => (P.periodEquiv x.1).symm x.2) := by
  simp_rw [periodEquiv_symm_apply]
  exact (P.continuous_realMatrix_inv.comp continuous_fst).matrix_mulVec
    (complexCoordinates.symm.toContinuousLinearEquiv.continuous.comp continuous_snd)

/-- A topological trivialization of the covering vector spaces; it is only
real-linear in the fibres and is not asserted to be holomorphic. -/
def realTrivialization : (B × ComplexPlane₂) ≃ₜ (B × RealPlane₄) where
  toFun x := (x.1, (P.periodEquiv x.1).symm x.2)
  invFun x := (x.1, P.periodEquiv x.1 x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk P.continuous_periodEquiv_symm
  continuous_invFun := continuous_fst.prodMk P.continuous_periodEquiv

/-- The total space with its quotient topology, expressed in real coordinates.
The complex atlas will come from the covering projection, not the real product. -/
abbrev TotalSpace (_P : HolomorphicPeriodMap V B) := B × RealTorus₄

def quotientMap : (B × ComplexPlane₂) → P.TotalSpace :=
  fun x => (x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2))

theorem quotientMap_localHomeomorph : IsLocalHomeomorph P.quotientMap := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  have h := (AddSubgroup.isAddQuotientCoveringMap_of_comm standardLattice.toAddSubgroup
    DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph
  exact (localHomeomorph_prod_id (B := B) h).comp P.realTrivialization.isLocalHomeomorph

theorem quotientMap_surjective : Function.Surjective P.quotientMap := by
  rintro ⟨b, z⟩
  obtain ⟨v, hv⟩ := standardLattice.mkQ_surjective z
  refine ⟨(b, P.periodEquiv b v), ?_⟩
  simpa [quotientMap] using congrArg (Prod.mk b) hv

theorem periodEquiv_coordinates (b : B) (v : RealPlane₄) :
    P.periodEquiv b v =
      ![6 * (P.point b).val.μ * (v 0) + (P.point b).val.τ * (v 1) + (v 2),
        (P.point b).val.β * (v 0) + (P.point b).val.μ * (v 1) + (v 3)] := by
  rw [periodEquiv_apply]
  ext i : 1
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, dotProduct,
      Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]

/-- Each fixed integral translation vector varies holomorphically in the base.
The same statement holds for arbitrary fixed real coefficients. -/
theorem holomorphic_periodEquiv_const (v : RealPlane₄) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun b => P.periodEquiv b v) := by
  simp_rw [periodEquiv_coordinates]
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact (((contMDiff_const.mul P.holomorphic_mu).mul contMDiff_const).add
      (P.holomorphic_tau.mul contMDiff_const)).add contMDiff_const
  · exact ((P.holomorphic_beta.mul contMDiff_const).add
      (P.holomorphic_mu.mul contMDiff_const)).add contMDiff_const

theorem periodEquiv_map_lattice (b : B) :
    standardLattice.map ((P.periodEquiv b).restrictScalars ℤ).toLinearMap =
      (P.point b).lattice := by
  rw [standardLattice, Submodule.map_span, PeriodDomain.lattice_eq_span_basis]
  congr 1
  rw [← Set.range_comp]
  congr 1

/-- Translation by the varying periods. The acting lattice is written in
fixed real coordinates and is the integer column lattice under `periodEquiv`. -/
@[instance_reducible] def coveringAction :
    MulAction (Multiplicative standardLattice) (B × ComplexPlane₂) where
  smul g x := (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))
  one_smul x := by
    change (x.1, x.2 + P.periodEquiv x.1
      ((1 : Multiplicative standardLattice).toAdd : RealPlane₄)) = x
    simp
  mul_smul g h x := by
    change (x.1, x.2 + P.periodEquiv x.1 ((g * h).toAdd : RealPlane₄)) =
      (x.1, (x.2 + P.periodEquiv x.1 (h.toAdd : RealPlane₄)) +
        P.periodEquiv x.1 (g.toAdd : RealPlane₄))
    simp [map_add, add_left_comm, add_comm]

theorem realTrivialization_smul (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.realTrivialization (g • x) =
      (x.1, (P.periodEquiv x.1).symm x.2 + (g.toAdd : RealPlane₄)) := by
  let := P.coveringAction
  change (x.1, (P.periodEquiv x.1).symm
    (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))) = _
  simp only [map_add, LinearEquiv.symm_apply_apply]

theorem coveringAction_continuous :
    letI := P.coveringAction
    ContinuousConstSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g
  change Continuous (fun x : B × ComplexPlane₂ =>
    (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact continuous_fst.prodMk (continuous_snd.add
    ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).continuous.comp continuous_fst))

theorem coveringAction_free :
    letI := P.coveringAction
    IsCancelSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g h x he
  have he' := congrArg (fun y => (P.realTrivialization y).2) he
  rw [P.realTrivialization_smul, P.realTrivialization_smul] at he'
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact add_left_cancel he'

theorem quotientMap_smul (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.quotientMap (g • x) = P.quotientMap x := by
  let := P.coveringAction
  have hg : standardLattice.mkQ (g.toAdd : RealPlane₄) = 0 :=
    (Submodule.Quotient.mk_eq_zero standardLattice).mpr g.toAdd.property
  change (x.1, standardLattice.mkQ
    ((P.periodEquiv x.1).symm (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))) = _
  simp only [map_add, LinearEquiv.symm_apply_apply, hg, add_zero]
  rfl

theorem quotientMap_orbit :
    letI := P.coveringAction
    ∀ x y : B × ComplexPlane₂,
      P.quotientMap x = P.quotientMap y ↔
        x ∈ MulAction.orbit (Multiplicative standardLattice) y := by
  let := P.coveringAction
  rintro ⟨b, z⟩ ⟨b', w⟩
  constructor
  · intro h
    have hb : b = b' := congrArg Prod.fst h
    subst b'
    have hv : (P.periodEquiv b).symm z - (P.periodEquiv b).symm w ∈ standardLattice :=
      (Submodule.Quotient.eq standardLattice).mp (congrArg Prod.snd h)
    refine ⟨Multiplicative.ofAdd ⟨_, hv⟩, ?_⟩
    change (b, w + P.periodEquiv b
      ((P.periodEquiv b).symm z - (P.periodEquiv b).symm w)) = (b, z)
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    congr 1
    abel
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact P.quotientMap_smul g (b', w)

/-- This is the actual quotient covering by the varying period lattice. -/
theorem quotientCoveringMap :
    letI := P.coveringAction
    IsQuotientCoveringMap P.quotientMap (Multiplicative standardLattice) := by
  let := P.coveringAction
  have := P.coveringAction_continuous
  have := P.coveringAction_free
  exact quotientCoveringMap_of_localHomeomorph P.quotientMap_localHomeomorph
    P.quotientMap_surjective P.quotientMap_orbit

local instance coveringChartedSpace : ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

local instance coveringManifold [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ V)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

theorem coveringAction_holomorphic (g : Multiplicative standardLattice) :
    letI := P.coveringAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : B × ComplexPlane₂ => g • x) := by
  let := P.coveringAction
  rw [modelWithCornersSelf_prod]
  change ContMDiff _ _ ω (fun x : B × ComplexPlane₂ =>
    (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact contMDiff_fst.prodMk (contMDiff_snd.add
    ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).comp contMDiff_fst))

/-- The complex charts on the total space are lifted holomorphic charts, not
the real-coordinate product charts. -/
@[instance_reducible] def totalChartedSpace : ChartedSpace (V × ComplexPlane₂) P.TotalSpace := by
  let := P.coveringAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) P.quotientCoveringMap

theorem totalSpace_isManifold [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.TotalSpace := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact CoveringQuotient.isManifold (E := V × ComplexPlane₂)
    P.quotientCoveringMap ω P.coveringAction_holomorphic

theorem quotientMap_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact CoveringQuotient.contMDiff_project (E := V × ComplexPlane₂)
    P.quotientCoveringMap ω P.coveringAction_holomorphic

def projection : P.TotalSpace → B := Prod.fst

theorem projection_surjective : Function.Surjective P.projection :=
  fun b => ⟨(b, 0), rfl⟩

theorem projection_proper : IsProperMap P.projection := isProperMap_fst_of_compactSpace

theorem projection_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      P.projection := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  apply CoveringQuotient.contMDiff_of_comp (E := V × ComplexPlane₂)
    P.quotientCoveringMap (modelWithCornersSelf ℂ V) ω
  change ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
    (Prod.fst : B × ComplexPlane₂ → B)
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

/-- The real-coordinate fibre is canonically homeomorphic to its actual
complex period torus. The real linear map is not claimed to be complex linear. -/
def torusHomeomorph (b : B) : RealTorus₄ ≃ₜ (P.point b).Torus where
  toEquiv := (Submodule.Quotient.equiv standardLattice (P.point b).lattice
    ((P.periodEquiv b).restrictScalars ℤ) (P.periodEquiv_map_lattice b)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact (P.point b).lattice.continuous_mkQ.comp
      (P.periodEquiv b).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply (P.point b).lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp
      (P.periodEquiv b).symm.toContinuousLinearEquiv.continuous

/-- The inclusion of the genuine complex torus over `b` into the total space. -/
def fibreInclusion (b : B) : (P.point b).Torus → P.TotalSpace :=
  fun z => (b, (P.torusHomeomorph b).symm z)

theorem fibreInclusion_injective (b : B) : Function.Injective (P.fibreInclusion b) := by
  intro x y h
  exact (P.torusHomeomorph b).symm.injective (congrArg Prod.snd h)

@[simp] theorem fibreInclusion_mkQ (b : B) (z : ComplexPlane₂) :
    P.fibreInclusion b ((P.point b).lattice.mkQ z) = P.quotientMap (b, z) := rfl

theorem range_fibreInclusion (b : B) :
    Set.range (P.fibreInclusion b) = P.projection ⁻¹' {b} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hz
    have hb : z.1 = b := hz
    refine ⟨P.torusHomeomorph b z.2, ?_⟩
    simp only [fibreInclusion, Homeomorph.symm_apply_apply, ← hb, Prod.mk.eta]

theorem fibreInclusion_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B] (b : B) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (P.fibreInclusion b) := by
  let := P.totalChartedSpace
  apply DiscreteQuotient.contMDiff_of_comp_mkQ (P.point b).lattice
  have h : ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun z : ComplexPlane₂ => (b, z)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_const.prodMk contMDiff_id
  exact P.quotientMap_holomorphic.comp h

def zeroSection : B → P.TotalSpace := fun b => (b, 0)

@[simp] theorem projection_zeroSection (b : B) : P.projection (P.zeroSection b) = b := rfl

theorem zeroSection_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      P.zeroSection := by
  let := P.totalChartedSpace
  have h : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun b : B => (b, (0 : ComplexPlane₂))) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_id.prodMk contMDiff_const
  change ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
    (fun b : B => (b, (0 : RealTorus₄)))
  simpa only [Function.comp_def, quotientMap, map_zero] using
    P.quotientMap_holomorphic.comp h

/-- In the lifted complex charts the family projection is precisely the
projection onto the base coordinates, hence it is a holomorphic submersion. -/
theorem projection_submersion [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    Manifold.IsSubmersionOfComplement ComplexPlane₂ (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ V) ω P.projection := by
  let := P.totalChartedSpace
  have := P.totalSpace_isManifold
  let := P.coveringAction
  intro x
  let r := CoveringQuotient.representative P.quotientCoveringMap x
  have hr : P.quotientMap r = x :=
    CoveringQuotient.project_representative P.quotientCoveringMap x
  have hb : r.1 = P.projection x := congrArg Prod.fst hr
  have hbase : P.projection x ∈ (chartAt V r.1).source := by
    rw [← hb]
    exact mem_chart_source V r.1
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    P.projection_proper.continuous.continuousAt
    (ContinuousLinearEquiv.refl ℂ (V × ComplexPlane₂))
    (chartAt (V × ComplexPlane₂) x) (chartAt V r.1)
    (mem_chart_source (V × ComplexPlane₂) x) hbase
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas r.1) ?_
  intro v hv
  have hv' : v ∈ (chartAt (V × ComplexPlane₂) x).target := by
    simpa [OpenPartialHomeomorph.extend] using hv
  change v ∈ (CoveringQuotient.chart (E := V × ComplexPlane₂) P.quotientCoveringMap x).target at hv'
  have hvbase : v.1 ∈ (chartAt V r.1).target := hv'.1.1
  have hs : ((chartAt (V × ComplexPlane₂) x).symm : V × ComplexPlane₂ → P.TotalSpace) =
      fun w => P.quotientMap ((chartAt V r.1).symm w.1, w.2) := by
    change ((CoveringQuotient.chart (E := V × ComplexPlane₂) P.quotientCoveringMap x).symm :
      V × ComplexPlane₂ → P.TotalSpace) = _
    rw [CoveringQuotient.chart_symm]
    rfl
  change (chartAt V r.1) (P.projection ((chartAt (V × ComplexPlane₂) x).symm v)) = v.1
  rw [hs]
  exact (chartAt V r.1).right_inv hvbase

theorem projection_isSubmersion [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    Manifold.IsSubmersion (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ V) ω P.projection := by
  let := P.totalChartedSpace
  exact P.projection_submersion.isSubmersion

end HolomorphicPeriodMap

end Wikipedia.HopfProblem
