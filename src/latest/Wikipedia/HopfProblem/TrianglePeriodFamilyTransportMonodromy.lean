import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMarking

/-!
# Actual singular-homology monodromy of the transported family fibres

The intrinsic path-transport homeomorphism is computed in the actual flat
fibre marking. Naturality of the genuine singular homology functor then
identifies its induced map with the integral special-linear representation
constructed from the actual lifted endpoint. The marking has already
been proved to agree with the original complex period columns.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open FirstHurewicz SpecialPeriods

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- In the actual fibre parametrization, genuine flat transport is the
triangle action prescribed by the inverse lifted endpoint. -/
theorem transport_flatFibreHomeomorph (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (f : RealTorus₄) :
    D.transport hq γ (D.flatFibreHomeomorph hq b f) =
      D.flatFibreHomeomorph hq b (triangleTorusHomeomorph (D.deckTransportHom hq b γ) f) := by
  have hin : D.flatFibreHomeomorph hq b f = ⟨D.quotient (b, f), rfl⟩ :=
    Subtype.ext (D.flatFibreHomeomorph_coe hq b f)
  apply Subtype.ext
  rw [hin, D.flatFibreHomeomorph_coe, D.transport_loop_apply_quotient]

/-- This is equality of actual homeomorphisms after changing to the
source's real period coordinates, not just equality of their matrices. -/
theorem transport_loop_conjugate (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    ((D.flatFibreHomeomorph hq b).trans (D.transport hq γ)).trans
      (D.flatFibreHomeomorph hq b).symm =
        triangleTorusHomeomorph (D.deckTransportHom hq b γ) := by
  apply Homeomorph.ext
  intro f
  change (D.flatFibreHomeomorph hq b).symm
    (D.transport hq γ (D.flatFibreHomeomorph hq b f)) = _
  rw [D.transport_flatFibreHomeomorph, Homeomorph.symm_apply_apply]

/-- The actual continuous maps form the fibre-marking commutative square. -/
theorem transport_flat_commutes (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
      D.projection ⁻¹' {D.baseQuotient b})).comp
        (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) =
      (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})).comp
        (triangleTorusHomeomorph (D.deckTransportHom hq b γ) : C(RealTorus₄, RealTorus₄)) := by
  apply ContinuousMap.ext
  intro f
  exact D.transport_flatFibreHomeomorph hq b γ f

/-- Naturality transfers the genuine transport map to the genuine torus
action on actual singular homology. -/
theorem transport_inducedHomology_flat (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (a : SingularH1 RealTorus₄) :
    inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
      D.projection ⁻¹' {D.baseQuotient b}))
        (inducedHomology (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) a) =
      inducedHomology (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b}))
          (inducedHomology (triangleTorusHomeomorph (D.deckTransportHom hq b γ) :
            C(RealTorus₄, RealTorus₄)) a) := by
  have he := congrArg inducedHomology (D.transport_flat_commutes hq b γ)
  rw [inducedHomology_comp, inducedHomology_comp] at he
  exact congrArg (fun L => L a) he

/-- The actual singular first homology map of flat transport is exactly
the integral dual representation of the inverse lifted endpoint. -/
theorem transport_singularH1 (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) :
    D.fibreSingularH1Equiv hq b
      (inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
        D.projection ⁻¹' {D.baseQuotient b})) a) =
      (D.latticeTransportHom hq b γ : LatticeMatrix) *ᵥ D.fibreSingularH1Equiv hq b a := by
  obtain ⟨a, rfl⟩ := (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b)).surjective a
  change D.fibreSingularH1Equiv hq b
    (inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
      D.projection ⁻¹' {D.baseQuotient b}))
      (inducedHomology (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) a)) =
    (D.latticeTransportHom hq b γ : LatticeMatrix) *ᵥ D.fibreSingularH1Equiv hq b
      (inducedHomology (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) a)
  rw [D.transport_inducedHomology_flat, D.fibreSingularH1Equiv_inducedHomology_flat,
    FlatTorus.singularH1Equiv_inducedHomology_triangle,
    D.fibreSingularH1Equiv_inducedHomology_flat, D.latticeTransportHom_apply]

/-- The actual singular-homology map conjugated by the proved period
marking is precisely the integral matrix linear map. -/
theorem transport_singularH1_conjugate (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.fibreSingularH1Equiv hq b).toLinearMap.comp
      ((inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
        D.projection ⁻¹' {D.baseQuotient b}))).comp
          (D.fibreSingularH1Equiv hq b).symm.toLinearMap) =
      Matrix.toLin' (D.latticeTransportHom hq b γ : LatticeMatrix) := by
  apply LinearMap.ext
  intro c
  change D.fibreSingularH1Equiv hq b
    (inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
      D.projection ⁻¹' {D.baseQuotient b})) ((D.fibreSingularH1Equiv hq b).symm c)) = _
  rw [D.transport_singularH1, LinearEquiv.apply_symm_apply]
  rfl

/-- For a specified inverse-generator lifted endpoint, the computed
action is the corresponding actual dual matrix. -/
theorem transport_singularH1_of_inverse_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b)
    (a : SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) :
    D.fibreSingularH1Equiv hq b
      (inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {D.baseQuotient b},
        D.projection ⁻¹' {D.baseQuotient b})) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ D.fibreSingularH1Equiv hq b a := by
  rw [D.transport_singularH1, D.latticeTransportHom_eq_of_inverse_endpoint hq b γ g hγ]

/-- Projecting the specified actual lifted path proves its endpoint and
computes its actual singular-homology transport without extra endpoint data. -/
theorem projectedLoop_transport_singularH1 (b : B) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) (a : SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) :
    D.fibreSingularH1Equiv hq b
      (inducedHomology (D.pathTransport hq (D.projectedLoop hq b g δ) :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ D.fibreSingularH1Equiv hq b a := by
  change D.fibreSingularH1Equiv hq b
    (inducedHomology (D.transport hq
      (Path.Homotopic.Quotient.mk (D.projectedLoop hq b g δ)) :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) a) = _
  rw [D.transport_singularH1, D.latticeTransportHom_projectedLoop]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
