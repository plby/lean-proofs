import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupFree
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase

/-!
# The unconditional fundamental group of the chosen regular family

The actual special periods instantiate the proved lattice-by-free-group
extension. Its basepoint is the existing zero-section point over the
normalized sphere coordinate two. An actual covering lift represents
this point, and equality of basepoints is the only transport used for
the total fundamental group.

The free-group action is the actual loop-transport action in the proved
free marking of the regular base. No matrix values are assigned to an
arbitrary change of meridian marking.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle TrianglePeriodFamily

attribute [local instance] triangleRegularQuotientChartedSpace
  triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "hqsp" =>
  regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- An actual covering lift of the selected regular point of coordinate two. -/
def specialRegularFamilyLift : TriangleRegularPoint :=
  Classical.choose (triangleRegularProject_surjective (regularBiholomorph.symm regularPatchPoint))

@[simp] theorem specialRegularFamilyLift_project :
    triangleRegularProject specialRegularFamilyLift =
      regularBiholomorph.symm regularPatchPoint :=
  Classical.choose_spec
    (triangleRegularProject_surjective (regularBiholomorph.symm regularPatchPoint))

/-- The lifted zero is literally the already chosen regular-family point. -/
theorem specialRegularFamilyLift_basepoint :
    (Dsp).fundamentalGroupBasepoint specialRegularFamilyLift = specialRegularFamilyPoint := by
  rw [← (Dsp).zeroSection_fundamentalGroupBasepoint]
  change (Dsp).zeroSection (triangleRegularProject specialRegularFamilyLift) =
    (Dsp).zeroSection (regularBiholomorph.symm regularPatchPoint)
  rw [specialRegularFamilyLift_project]

/-- Basepoint transport is the equality cast of the preceding geometric equality. -/
def specialRegularFamilyBasepointEquiv :
    FundamentalGroup SpecialRegularFamily
        ((Dsp).fundamentalGroupBasepoint specialRegularFamilyLift) ≃*
      FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint :=
  MulEquiv.cast (M := fun x : SpecialRegularFamily => FundamentalGroup SpecialRegularFamily x)
    specialRegularFamilyLift_basepoint

/-- The already proved free-group marking at the actual base orbit of the lift. -/
def specialRegularBaseFundamentalGroupEquiv :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject specialRegularFamilyLift) ≃*
      FreeGroup Bool :=
  triangleRegularFundamentalGroupFreeEquivAt (triangleRegularProject specialRegularFamilyLift)

/-- Actual path transport, expressed in the chosen free coordinates on the base. -/
def specialRegularFamilyFundamentalGroupAction :
    FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  regularFundamentalGroupFreeAction specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialRegularFamilyLift

/-- The fundamental group of the actual special regular family, at its
existing chosen point, is a lattice semidirect the free group on two letters. -/
def specialRegularFamilyFundamentalGroupEquiv :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint ≃*
      (Multiplicative Lattice) ⋊[specialRegularFamilyFundamentalGroupAction] (FreeGroup Bool) :=
  specialRegularFamilyBasepointEquiv.symm.trans
    (regularFundamentalGroupFreeEquiv specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialRegularFamilyLift)

/-- The genuine fibre-lattice injection, followed only by equality of basepoints. -/
def specialRegularFamilyLatticeHom :
    Multiplicative Lattice →* FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint :=
  specialRegularFamilyBasepointEquiv.toMonoidHom.comp
    ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift)

/-- The actual projection on fundamental groups, in the proved free base coordinates. -/
def specialRegularFamilyFreeProjectionHom :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint →* FreeGroup Bool :=
  specialRegularBaseFundamentalGroupEquiv.toMonoidHom.comp
    (((Dsp).projectionFundamentalGroupHom specialRegularFamilyLift).comp
      specialRegularFamilyBasepointEquiv.symm.toMonoidHom)

/-- The actual zero section on fundamental groups, in the same free base coordinates. -/
def specialRegularFamilyFreeSectionHom :
    FreeGroup Bool →* FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint :=
  specialRegularFamilyBasepointEquiv.toMonoidHom.comp
    (((Dsp).sectionFundamentalGroupHom specialRegularFamilyLift).comp
      specialRegularBaseFundamentalGroupEquiv.symm.toMonoidHom)

/-- The named lattice subgroup consists of actual straight period loops
included into the family, with the actual basepoint equality applied. -/
theorem specialRegularFamilyLatticeHom_periodLoop (v : Lattice) :
    specialRegularFamilyLatticeHom (Multiplicative.ofAdd v) =
      specialRegularFamilyBasepointEquiv
        ((Dsp).flatFibreFundamentalGroupHom specialRegularFamilyLift
          (Path.Homotopic.Quotient.mk (FlatTorus.periodLoop v))) := by
  change specialRegularFamilyBasepointEquiv
    ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift (Multiplicative.ofAdd v)) = _
  rw [(Dsp).latticeFundamentalGroupHom_periodLoop]

@[simp] theorem specialRegularFamilyFundamentalGroupEquiv_lattice
    (v : Multiplicative Lattice) :
    specialRegularFamilyFundamentalGroupEquiv (specialRegularFamilyLatticeHom v) =
      SemidirectProduct.inl v := by
  change regularFundamentalGroupFreeEquiv specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialRegularFamilyLift
      (specialRegularFamilyBasepointEquiv.symm
        (specialRegularFamilyBasepointEquiv
          ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift v))) = _
  rw [MulEquiv.symm_apply_apply, regularFundamentalGroupFreeEquiv_lattice]
  rfl

@[simp] theorem specialRegularFamilyFundamentalGroupEquiv_section (w : FreeGroup Bool) :
    specialRegularFamilyFundamentalGroupEquiv (specialRegularFamilyFreeSectionHom w) =
      SemidirectProduct.inr w := by
  change (Dsp).fundamentalGroupFreeSemidirectEquiv hqsp specialRegularFamilyLift
    specialRegularBaseFundamentalGroupEquiv
      (specialRegularFamilyBasepointEquiv.symm
        (specialRegularFamilyBasepointEquiv
          ((Dsp).sectionFundamentalGroupHom specialRegularFamilyLift
            (specialRegularBaseFundamentalGroupEquiv.symm w)))) = _
  rw [MulEquiv.symm_apply_apply]
  calc
    _ = SemidirectProduct.inr (specialRegularBaseFundamentalGroupEquiv
        (specialRegularBaseFundamentalGroupEquiv.symm w)) :=
      (Dsp).fundamentalGroupFreeSemidirectEquiv_section hqsp specialRegularFamilyLift
        specialRegularBaseFundamentalGroupEquiv (specialRegularBaseFundamentalGroupEquiv.symm w)
    _ = _ := congrArg SemidirectProduct.inr
      (specialRegularBaseFundamentalGroupEquiv.apply_symm_apply w)

@[simp] theorem specialRegularFamilyFundamentalGroupEquiv_projection
    (γ : FundamentalGroup SpecialRegularFamily specialRegularFamilyPoint) :
    (specialRegularFamilyFundamentalGroupEquiv γ).right =
      specialRegularFamilyFreeProjectionHom γ :=
  regularFundamentalGroupFreeEquiv_projection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialRegularFamilyLift
      (specialRegularFamilyBasepointEquiv.symm γ)

/-- The action is precisely the proved integral representation of actual
path transport, evaluated on the inverse image of the free word. -/
theorem specialRegularFamilyFundamentalGroupAction_toAdd
    (w : FreeGroup Bool) (v : Multiplicative Lattice) :
    (specialRegularFamilyFundamentalGroupAction w v).toAdd =
      ((Dsp).latticeTransportHom hqsp specialRegularFamilyLift
        (specialRegularBaseFundamentalGroupEquiv.symm w) : LatticeMatrix) *ᵥ v.toAdd := rfl

theorem specialRegularFamilyLatticeHom_injective :
    Function.Injective specialRegularFamilyLatticeHom :=
  specialRegularFamilyBasepointEquiv.injective.comp
    ((Dsp).latticeFundamentalGroupHom_injective hqsp specialRegularFamilyLift)

/-- The actual zero section splits the actual projection in free coordinates. -/
theorem specialRegularFamilyFreeProjectionHom_comp_section :
    specialRegularFamilyFreeProjectionHom.comp specialRegularFamilyFreeSectionHom =
      MonoidHom.id (FreeGroup Bool) := by
  apply MonoidHom.ext
  intro w
  change specialRegularBaseFundamentalGroupEquiv
    ((Dsp).projectionFundamentalGroupHom specialRegularFamilyLift
      (specialRegularFamilyBasepointEquiv.symm
        (specialRegularFamilyBasepointEquiv
          ((Dsp).sectionFundamentalGroupHom specialRegularFamilyLift
            (specialRegularBaseFundamentalGroupEquiv.symm w))))) = w
  rw [MulEquiv.symm_apply_apply]
  have h := DFunLike.congr_fun
    ((Dsp).projectionFundamentalGroupHom_comp_section specialRegularFamilyLift)
    (specialRegularBaseFundamentalGroupEquiv.symm w)
  change (Dsp).projectionFundamentalGroupHom specialRegularFamilyLift
    ((Dsp).sectionFundamentalGroupHom specialRegularFamilyLift
      (specialRegularBaseFundamentalGroupEquiv.symm w)) =
      specialRegularBaseFundamentalGroupEquiv.symm w at h
  rw [h, MulEquiv.apply_symm_apply]

theorem specialRegularFamilyFreeProjectionHom_surjective :
    Function.Surjective specialRegularFamilyFreeProjectionHom := by
  intro w
  exact ⟨specialRegularFamilyFreeSectionHom w,
    DFunLike.congr_fun specialRegularFamilyFreeProjectionHom_comp_section w⟩

theorem specialRegularFamilyFreeSectionHom_injective :
    Function.Injective specialRegularFamilyFreeSectionHom := by
  apply Function.LeftInverse.injective (g := specialRegularFamilyFreeProjectionHom)
  intro w
  exact DFunLike.congr_fun specialRegularFamilyFreeProjectionHom_comp_section w

/-- A loop projects trivially exactly when it comes from the actual fibre lattice. -/
theorem specialRegularFamilyLatticeHom_range_eq_ker :
    specialRegularFamilyLatticeHom.range = specialRegularFamilyFreeProjectionHom.ker := by
  ext γ
  constructor
  · rintro ⟨v, rfl⟩
    change specialRegularBaseFundamentalGroupEquiv
      ((Dsp).projectionFundamentalGroupHom specialRegularFamilyLift
        (specialRegularFamilyBasepointEquiv.symm
          (specialRegularFamilyBasepointEquiv
            ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift v)))) = 1
    rw [MulEquiv.symm_apply_apply, (Dsp).projectionFundamentalGroupHom_lattice]
    exact specialRegularBaseFundamentalGroupEquiv.map_one
  · intro hγ
    have hp : (Dsp).projectionFundamentalGroupHom specialRegularFamilyLift
        (specialRegularFamilyBasepointEquiv.symm γ) = 1 := by
      apply specialRegularBaseFundamentalGroupEquiv.injective
      change specialRegularBaseFundamentalGroupEquiv
        ((Dsp).projectionFundamentalGroupHom specialRegularFamilyLift
          (specialRegularFamilyBasepointEquiv.symm γ)) = 1 at hγ
      exact hγ.trans specialRegularBaseFundamentalGroupEquiv.map_one.symm
    have hm : specialRegularFamilyBasepointEquiv.symm γ ∈
        ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift).range := by
      rw [(Dsp).latticeFundamentalGroupHom_range_eq_ker hqsp specialRegularFamilyLift]
      exact hp
    obtain ⟨v, hv⟩ := hm
    refine ⟨v, ?_⟩
    change specialRegularFamilyBasepointEquiv
      ((Dsp).latticeFundamentalGroupHom specialRegularFamilyLift v) = γ
    rw [hv, MulEquiv.apply_symm_apply]

/-- Conjugation by the actual zero section agrees with actual transport. -/
theorem specialRegularFamilyLatticeHom_conjugation
    (w : FreeGroup Bool) (v : Multiplicative Lattice) :
    specialRegularFamilyLatticeHom (specialRegularFamilyFundamentalGroupAction w v) =
      specialRegularFamilyFreeSectionHom w * specialRegularFamilyLatticeHom v *
        (specialRegularFamilyFreeSectionHom w)⁻¹ := by
  have h := congrArg specialRegularFamilyBasepointEquiv
    ((Dsp).latticeFundamentalGroupHom_conjugation hqsp specialRegularFamilyLift
      (specialRegularBaseFundamentalGroupEquiv.symm w) v)
  simp only [map_mul, map_inv] at h
  exact h

/-- The actual special regular family has an unconditional split exact
lattice-by-free-group fundamental-group extension at its existing chosen point. -/
theorem specialRegularFamilyFundamentalGroup_split_exact :
    Function.Injective specialRegularFamilyLatticeHom ∧
      specialRegularFamilyLatticeHom.range = specialRegularFamilyFreeProjectionHom.ker ∧
      Function.Surjective specialRegularFamilyFreeProjectionHom ∧
      specialRegularFamilyFreeProjectionHom.comp specialRegularFamilyFreeSectionHom =
        MonoidHom.id (FreeGroup Bool) :=
  ⟨specialRegularFamilyLatticeHom_injective,
    specialRegularFamilyLatticeHom_range_eq_ker,
    specialRegularFamilyFreeProjectionHom_surjective,
    specialRegularFamilyFreeProjectionHom_comp_section⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
