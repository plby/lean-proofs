import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelShear
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelActualFibre

/-!
# The marked product-torus form of the actual positive-level collapse

The source's phase shear and inverse quarter-turn base coordinate identify
the actual free deck quotient with a product of two tori. Composing the
proved fibre homeomorphism gives this product presentation for the literal
positive-real fibre. The collapse map on the marked product is independent
of the chosen positive level, and its exact representative formula retains
the frozen phase shear.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspHoneycomb CuspPositive
open PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual central collapse in marked compact-phase and base-torus coordinates. -/
def productCollapse : C(CompactFibreTorus × ProductTorus 2, QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0)))

theorem productCollapse_sourceCoordinates (p : PhasePlane) :
    productCollapse C ε hε (sourceProductCoordinates (C 0) p) =
      honeycombCollapseMap C ε hε p := by
  change sourceCollapse C ε hε
    ((sourceProductHomeomorph (C 0)).symm (sourceProductCoordinates (C 0) p)) = _
  have hp : sourceProductHomeomorph (C 0) (sourceProjection (C 0) p) =
      sourceProductCoordinates (C 0) p := rfl
  rw [← hp, Homeomorph.symm_apply_apply, sourceCollapse_projection]

/-- In the marked base coordinate the actual positive point is at `B₀ y`,
and the frozen phase shear is retained explicitly. -/
theorem productCollapse_coordinateProjection (u : CompactFibreTorus) (y : Plane) :
    productCollapse C ε hε (u, coordinateProjection 2 y) =
      honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (realCuspVector y), realCuspVector y) := by
  change sourceCollapse C ε hε
    ((sourceProductHomeomorph (C 0)).symm (u, coordinateProjection 2 y)) = _
  rw [sourceProductHomeomorph_symm_coordinateProjection, sourceCollapse_projection]

theorem productCollapse_surjective : Function.Surjective (productCollapse C ε hε) :=
  (sourceCollapse_surjective C ε hε).comp (sourceProductHomeomorph (C 0)).symm.surjective

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- The actual frozen positive-real fibre, in the source's marked product coordinates. -/
def frozenProductFibreHomeomorph :
    (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre (fun _ => C₀) ε (ρ : ℂ) :=
  (sourceProductHomeomorph C₀).symm.trans
    (frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR)

theorem frozenProductFibreHomeomorph_sourceCoordinates (p : PhasePlane) :
    frozenProductFibreHomeomorph ε C₀ ρ hρ hε1 hρε hR (sourceProductCoordinates C₀ p) =
      frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p := by
  change frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR
    ((sourceProductHomeomorph C₀).symm (sourceProductCoordinates C₀ p)) = _
  have hp : sourceProductHomeomorph C₀ (sourceProjection C₀ p) =
      sourceProductCoordinates C₀ p := rfl
  rw [← hp, Homeomorph.symm_apply_apply, frozenSourceHomeomorph_projection]

theorem frozenProductFibreHomeomorph_coordinateProjection
    (u : CompactFibreTorus) (y : Plane) :
    frozenProductFibreHomeomorph ε C₀ ρ hρ hε1 hρε hR (u, coordinateProjection 2 y) =
      frozenFibreMap C₀ ρ hρ ε hε1 hρε hR
        (u * sourcePhaseCharacter C₀ (realCuspVector y), realCuspVector y) := by
  change frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR
    ((sourceProductHomeomorph C₀).symm (u, coordinateProjection 2 y)) = _
  rw [sourceProductHomeomorph_symm_coordinateProjection, frozenSourceHomeomorph_projection]

/-- Exact factorization of the independently prescribed fibre map through
the marked torus homeomorphism, without choosing a retraction. -/
theorem prescribedActualFibreCollapse_frozenProductFibreHomeomorph
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CompactFibreTorus × ProductTorus 2) :
    prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
        (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
        (frozenProductFibreHomeomorph ε C₀ ρ hρ hε1 hρε hR p) =
      productCollapse (fun _ => C₀) ε hε p :=
  prescribedActualFibreCollapse_frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR
    hε η hρη hηε ((sourceProductHomeomorph C₀).symm p)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
