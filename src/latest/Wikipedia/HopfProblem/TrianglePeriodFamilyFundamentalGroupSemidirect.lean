import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupData
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupExactness
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupConjugation
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupLattice
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSplit
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMonodromy

/-!
# The actual period-family fundamental group is a split lattice extension

The inclusion of the actual fibre is injective on fundamental groups,
its image is exactly the kernel of the actual projection, and the actual
zero section splits the projection. The homotopy-square calculation
identifies conjugation with genuine path transport. These proved facts
construct the semidirect-product equivalence.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods FirstHurewicz

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

include hq

/-- The actual fibre inclusion injects on fundamental groups. -/
theorem flatFibreFundamentalGroupHom_injective (b : B) :
    Function.Injective (D.flatFibreFundamentalGroupHom b) :=
  DiagonalQuotient.fibreFundamentalGroupHom_injective hq b (0 : RealTorus₄)

theorem latticeFundamentalGroupHom_injective (b : B) :
    Function.Injective (D.latticeFundamentalGroupHom b) :=
  (D.flatFibreFundamentalGroupHom_injective hq b).comp
    FlatTorus.fundamentalGroupEquiv.symm.injective

/-- Exactness is obtained from actual lifted loops, not from an assumed
homotopy exact sequence. -/
theorem latticeFundamentalGroupHom_range_eq_ker (b : B) :
    (D.latticeFundamentalGroupHom b).range = (D.projectionFundamentalGroupHom b).ker := by
  have hflat : (D.flatFibreFundamentalGroupHom b).range =
      (D.projectionFundamentalGroupHom b).ker :=
    DiagonalQuotient.fibreFundamentalGroupHom_range_eq_ker hq b (0 : RealTorus₄)
  rw [← hflat]
  ext γ
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨FlatTorus.fundamentalGroupEquiv.symm v, rfl⟩
  · rintro ⟨δ, rfl⟩
    refine ⟨FlatTorus.fundamentalGroupEquiv δ, ?_⟩
    change D.flatFibreFundamentalGroupHom b
      (FlatTorus.fundamentalGroupEquiv.symm (FlatTorus.fundamentalGroupEquiv δ)) = _
    rw [MulEquiv.symm_apply_apply]

/-- The action is defined by the proved integral representation of actual
covering transport, with no meridian or matrix assignment assumed. -/
def fundamentalGroupAction (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →* MulAut (Multiplicative Lattice) :=
  triangleLatticeMulAutHom.comp (D.deckTransportHom hq b)

@[simp] theorem fundamentalGroupAction_toAdd (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (v : Multiplicative Lattice) :
    (D.fundamentalGroupAction hq b β v).toAdd =
      (D.latticeTransportHom hq b β : LatticeMatrix) *ᵥ v.toAdd := rfl

/-- Conjugation by the actual section is the proved transport action on
the actual marked fibre fundamental group. -/
theorem latticeFundamentalGroupHom_conjugation (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (v : Multiplicative Lattice) :
    D.latticeFundamentalGroupHom b (D.fundamentalGroupAction hq b β v) =
      D.sectionFundamentalGroupHom b β * D.latticeFundamentalGroupHom b v *
        (D.sectionFundamentalGroupHom b β)⁻¹ := by
  have hmark : FlatTorus.fundamentalGroupEquiv.symm
      (triangleLatticeMulAutHom (D.deckTransportHom hq b β) v) =
      DiagonalQuotient.fibreActionFundamentalGroupHom (0 : RealTorus₄)
        triangleTorusAction_zero (D.deckTransportHom hq b β)
        (FlatTorus.fundamentalGroupEquiv.symm v) := by
    apply FlatTorus.fundamentalGroupEquiv.injective
    simp only [FlatTorus.fundamentalGroupEquiv_fibreAction, MulEquiv.apply_symm_apply]
  change D.flatFibreFundamentalGroupHom b
      (FlatTorus.fundamentalGroupEquiv.symm
        (triangleLatticeMulAutHom (D.deckTransportHom hq b β) v)) = _
  rw [hmark]
  exact (DiagonalQuotient.sectionFundamentalGroupHom_conjugate_fibre hq
    (0 : RealTorus₄) triangleTorusAction_zero b β
      (FlatTorus.fundamentalGroupEquiv.symm v)).symm

/-- The constructed semidirect product maps isomorphically to the actual
fundamental group of the actual period family. -/
def semidirectFundamentalGroupEquiv (b : B) :
    (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
      (FundamentalGroup D.BaseSpace (D.baseQuotient b)) ≃*
        FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  SplitGroupExtension.mulEquiv (D.latticeFundamentalGroupHom b)
    (D.projectionFundamentalGroupHom b) (D.sectionFundamentalGroupHom b)
    (D.fundamentalGroupAction hq b) (D.latticeFundamentalGroupHom_injective hq b)
    (D.projectionFundamentalGroupHom_comp_section b)
    (D.latticeFundamentalGroupHom_range_eq_ker hq b)
    (D.latticeFundamentalGroupHom_conjugation hq b)

/-- The actual period-family fundamental group, in lattice/base-loop coordinates. -/
def fundamentalGroupSemidirectEquiv (b : B) :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) ≃*
      (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
        (FundamentalGroup D.BaseSpace (D.baseQuotient b)) :=
  (D.semidirectFundamentalGroupEquiv hq b).symm

@[simp] theorem semidirectFundamentalGroupEquiv_apply (b : B)
    (x : (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
      (FundamentalGroup D.BaseSpace (D.baseQuotient b))) :
    D.semidirectFundamentalGroupEquiv hq b x =
      D.latticeFundamentalGroupHom b x.left * D.sectionFundamentalGroupHom b x.right := rfl

@[simp] theorem fundamentalGroupSemidirectEquiv_lattice (b : B) (v : Multiplicative Lattice) :
    D.fundamentalGroupSemidirectEquiv hq b (D.latticeFundamentalGroupHom b v) =
      SemidirectProduct.inl v :=
  SplitGroupExtension.mulEquiv_symm_inclusion _ _ _ _ _ _ _ _ v

@[simp] theorem fundamentalGroupSemidirectEquiv_section (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.fundamentalGroupSemidirectEquiv hq b (D.sectionFundamentalGroupHom b β) =
      SemidirectProduct.inr β :=
  SplitGroupExtension.mulEquiv_symm_section _ _ _ _ _ _ _ _ β

@[simp] theorem fundamentalGroupSemidirectEquiv_projection (b : B)
    (γ : FundamentalGroup D.Space (D.fundamentalGroupBasepoint b)) :
    (D.fundamentalGroupSemidirectEquiv hq b γ).right = D.projectionFundamentalGroupHom b γ :=
  SplitGroupExtension.mulEquiv_symm_right _ _ _ _ _ _ _ _ γ

/-- The extension is exact and split for the actual spaces and actual maps. -/
theorem fundamentalGroup_split_exact (b : B) :
    Function.Injective (D.latticeFundamentalGroupHom b) ∧
      (D.latticeFundamentalGroupHom b).range = (D.projectionFundamentalGroupHom b).ker ∧
      Function.Surjective (D.projectionFundamentalGroupHom b) ∧
      (D.projectionFundamentalGroupHom b).comp (D.sectionFundamentalGroupHom b) =
        MonoidHom.id (FundamentalGroup D.BaseSpace (D.baseQuotient b)) :=
  ⟨D.latticeFundamentalGroupHom_injective hq b,
    D.latticeFundamentalGroupHom_range_eq_ker hq b,
    D.projectionFundamentalGroupHom_surjective b,
    D.projectionFundamentalGroupHom_comp_section b⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods FirstHurewicz

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- In the same source-column marking, this is the map induced by actual
path transport on the literal fibre's integral singular homology. -/
theorem fundamentalGroupAction_actual_transport (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) :
    (D.fundamentalGroupAction hq b β
      (Multiplicative.ofAdd (D.fibreSingularH1Equiv hq b a))).toAdd =
        D.fibreSingularH1Equiv hq b
          (inducedHomology (D.transport hq β :
            C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) a) := by
  rw [D.fundamentalGroupAction_toAdd]
  exact (D.transport_singularH1 hq b β a).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
