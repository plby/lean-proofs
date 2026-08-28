import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticParametrization
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibreTopology

/-!
# The genuine global elliptic normal tangent quotient

The original full filling maps into the constructed threefold by its actual
analytic partial diffeomorphism. Its differential carries the tangent image
of the special central inclusion onto the tangent image of the global central
inclusion. This gives a continuous complex-linear equivalence of their literal
normal tangent quotients, with their natural quotient topologies.

Both derivatives use the previously constructed native complex atlases. No
ambient atlas or differential is replaced by a transported model.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Elliptic.FamilyModel

attribute [local instance] specialFullFillingChartedSpace Threefold.chartedSpace

private theorem normal_inclusion_square (j : Elliptic.Kind) :
    fullParametrization j ∘ specialCentralInclusion j = centralSurfaceInclusion j := by
  funext x
  exact fullParametrization_apply j (pieceCentralInclusion j x)

/-- The genuine differential of the original filling's parametrization,
at the actual central surface point. -/
def fullParametrizationDerivative (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    Elliptic.FamilyModel ≃L[ℂ] Elliptic.FamilyModel :=
  (fullParametrization_isLocalDiffeomorphAt j
    (specialCentralInclusion_mem_fullParametrization_source j x)).mfderivToContinuousLinearEquiv
      (by simp)

@[simp] theorem fullParametrizationDerivative_toContinuousLinearMap
    (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    (fullParametrizationDerivative j x).toContinuousLinearMap =
      mfderiv IF IF (fullParametrization j) (specialCentralInclusion j x) := rfl

@[simp] theorem fullParametrizationDerivative_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) (w : Elliptic.FamilyModel) :
    fullParametrizationDerivative j x w =
      mfderiv IF IF (fullParametrization j) (specialCentralInclusion j x) w := rfl

/-- The chain rule for the actual commuting square of central inclusions.
The domain is the same native central surface on both sides. -/
theorem centralNormalDerivative_square (j : Elliptic.Kind) (x : SpecialCentralSurface j)
    (w : ComplexPlane₂) :
    fullParametrizationDerivative j x
        (mfderiv I₂ IF (specialCentralInclusion j) x w) =
      mfderiv I₂ IF (centralSurfaceInclusion j) x w := by
  have he : (fullParametrization j ∘ specialCentralInclusion j) =ᶠ[𝓝 x]
      centralSurfaceInclusion j :=
    Filter.Eventually.of_forall (congrFun (normal_inclusion_square j))
  have hd := he.mfderiv_eq (I := I₂) (I' := IF)
  have hlocalHol : ContMDiff I₂ IF ω (specialCentralInclusion j) :=
    (specialLocalData j).centralFibreInclusion_holomorphic
      j.twist (Elliptic.mainTwist_admissible j)
  have hlocal : MDifferentiableAt I₂ IF (specialCentralInclusion j) x :=
    hlocalHol.mdifferentiableAt (by simp)
  have hglobal := (fullParametrization_isLocalDiffeomorphAt j
    (specialCentralInclusion_mem_fullParametrization_source j x)).mdifferentiableAt (by simp)
  rw [mfderiv_comp x hglobal hlocal] at hd
  exact congrArg (fun L : ComplexPlane₂ →L[ℂ] Elliptic.FamilyModel => L w) hd

/-- The actual parametrization differential takes the local central
tangent image onto the global central tangent image. -/
theorem fullParametrizationDerivative_map_tangentRange (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    (mfderiv I₂ IF (specialCentralInclusion j) x).range.map
      (fullParametrizationDerivative j x).toLinearEquiv.toLinearMap =
        (mfderiv I₂ IF (centralSurfaceInclusion j) x).range := by
  apply le_antisymm
  · rintro w ⟨z, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (centralNormalDerivative_square j x u).symm⟩
  · rintro w ⟨u, rfl⟩
    exact ⟨mfderiv I₂ IF (specialCentralInclusion j) x u,
      ⟨u, rfl⟩, centralNormalDerivative_square j x u⟩

/-- The literal normal quotient of the genuine central surface in the
already constructed global threefold atlas. -/
abbrev GlobalCentralNormalFibre (j : Elliptic.Kind) (x : SpecialCentralSurface j) :=
  letI := Threefold.chartedSpace
  Elliptic.FamilyModel ⧸ (mfderiv I₂ IF (centralSurfaceInclusion j) x).range

/-- The actual open-embedding derivative induces the equivalence of
the two geometric normal quotient spaces. -/
def normalTransportLinearEquiv (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    SpecialCentralNormalFibre j x ≃ₗ[ℂ] GlobalCentralNormalFibre j x :=
  Submodule.Quotient.equiv _ _ (fullParametrizationDerivative j x).toLinearEquiv
    (fullParametrizationDerivative_map_tangentRange j x)

@[simp] theorem normalTransportLinearEquiv_mk (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) (w : Elliptic.FamilyModel) :
    normalTransportLinearEquiv j x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fullParametrizationDerivative j x w) := rfl

@[simp] theorem normalTransportLinearEquiv_symm_mk (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) (w : Elliptic.FamilyModel) :
    (normalTransportLinearEquiv j x).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((fullParametrizationDerivative j x).symm w) := rfl

theorem globalCentralTangentRange_isClosed (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    let S : Submodule ℂ Elliptic.FamilyModel :=
      (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
    IsClosed (S : Set Elliptic.FamilyModel) := by
  let S : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
  exact S.closed_of_finiteDimensional

/-- Hausdorffness is for the natural quotient topology of the actual
global tangent range, without a transported topology. -/
instance globalCentralNormalFibre_t2Space (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    T2Space (GlobalCentralNormalFibre j x) := by
  let S : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
  let : IsClosed (S : Set Elliptic.FamilyModel) := globalCentralTangentRange_isClosed j x
  exact inferInstanceAs (T2Space (Elliptic.FamilyModel ⧸ S))

instance globalCentralNormalFibre_finiteDimensional (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) : FiniteDimensional ℂ (GlobalCentralNormalFibre j x) := by
  let S : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
  exact inferInstanceAs (FiniteDimensional ℂ (Elliptic.FamilyModel ⧸ S))

/-- The same actual quotient-derivative map is continuous in both directions. -/
def normalTransport (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    SpecialCentralNormalFibre j x ≃L[ℂ] GlobalCentralNormalFibre j x := by
  let S : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (specialCentralInclusion j) x).range
  let T : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
  exact
    { normalTransportLinearEquiv j x with
      continuous_toFun := S.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        (continuous_quot_mk.comp (fullParametrizationDerivative j x).continuous)
      continuous_invFun := T.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        (continuous_quot_mk.comp (fullParametrizationDerivative j x).symm.continuous) }

@[simp] theorem normalTransport_toLinearEquiv (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    (normalTransport j x).toLinearEquiv = normalTransportLinearEquiv j x := rfl

@[simp] theorem normalTransport_mk (j : Elliptic.Kind) (x : SpecialCentralSurface j)
    (w : Elliptic.FamilyModel) :
    normalTransport j x (Submodule.Quotient.mk w) = Submodule.Quotient.mk
      (mfderiv IF IF (fullParametrization j) (specialCentralInclusion j x) w) := rfl

@[simp] theorem normalTransport_symm_mk (j : Elliptic.Kind) (x : SpecialCentralSurface j)
    (w : Elliptic.FamilyModel) :
    (normalTransport j x).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((fullParametrizationDerivative j x).symm w) := rfl

/-- The known analytic special normal bundle is identified with the
actual global normal quotient through the genuine parametrization differential. -/
def specialNormalFibreToGlobal (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    (specialCentralNormalBundle j).Fiber x ≃L[ℂ] GlobalCentralNormalFibre j x :=
  (specialCentralNormalFibreIdentification j x).trans (normalTransport j x)

@[simp] theorem specialNormalFibreToGlobal_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) (z : (specialCentralNormalBundle j).Fiber x) :
    specialNormalFibreToGlobal j x z =
      normalTransport j x (specialCentralNormalFibreIdentification j x z) := rfl

theorem globalCentralNormalFibre_rank_one (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) : Module.finrank ℂ (GlobalCentralNormalFibre j x) = 1 :=
  (specialNormalFibreToGlobal j x).toLinearEquiv.symm.finrank_eq.trans
    (Elliptic.Equivariant.Data.NormalBundle.fibre_rank_one
      (specialLocalData j) j.twist (Elliptic.mainTwist_admissible j) x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
