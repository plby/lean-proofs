import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMarked
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase

/-!
# The source-marked fundamental group of the actual special family

The actual special periods specialize the proved joint geometric
meridian marking. The basepoint is the zero of the fibre above normalized
coordinate one half, and the two section loops are the actual meridians
whose lifts have the proved inverse-generator endpoints.

The resulting semidirect product has the fixed source action `A₁`, `A₂`.
This does not transport that matrix marking to the separate previously
chosen regular-family point of coordinate two.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle TrianglePeriodFamily Meridians

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "hqsp" =>
  regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "bsp" => normalizedRegularMeridianBasepoint

/-- The actual fibre zero above the canonical jointly based meridians. -/
def specialRegularFamilyMarkedPoint : SpecialRegularFamily :=
  (Dsp).fundamentalGroupBasepoint bsp

@[simp] theorem specialRegularFamilyMarkedPoint_zeroSection :
    (Dsp).zeroSection (triangleRegularProject bsp) = specialRegularFamilyMarkedPoint := rfl

/-- Its normalized regular-base coordinate is literally one half. -/
theorem specialRegularFamilyMarkedPoint_coordinate :
    (triangleRegularPlaneHomeomorph ((Dsp).projection specialRegularFamilyMarkedPoint) : ℂ) =
      1 / 2 := by
  change (triangleRegularPlaneHomeomorph (triangleRegularProject bsp) : ℂ) = 1 / 2
  rw [normalizedRegularMeridianBasepoint_coordinate]
  rfl

/-- The literal marked fibre-lattice inclusion into the actual special family. -/
def specialRegularFamilyMarkedLatticeHom :
    Multiplicative Lattice →*
      FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  (Dsp).latticeFundamentalGroupHom bsp

/-- The homomorphism induced by the actual projection at the marked point. -/
def specialRegularFamilyMarkedProjectionHom :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint →*
      FundamentalGroup TriangleRegularQuotient (triangleRegularProject bsp) :=
  (Dsp).projectionFundamentalGroupHom bsp

/-- The homomorphism induced by the actual zero section at the marked point. -/
def specialRegularFamilyMarkedSectionHom :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject bsp) →*
      FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  (Dsp).sectionFundamentalGroupHom bsp

/-- The actual geometric meridian, followed through the actual zero section. -/
def specialRegularFamilyMarkedMeridianPath (b : Bool) :
    Path specialRegularFamilyMarkedPoint specialRegularFamilyMarkedPoint :=
  (compatibleRegularMeridian b).map (Dsp).zeroSection_continuous

/-- The class of that literal section loop in the actual fundamental group. -/
def specialRegularFamilyMarkedMeridianClass (b : Bool) :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (specialRegularFamilyMarkedMeridianPath b))

@[simp] theorem specialRegularFamilyMarkedMeridianClass_eq_section (b : Bool) :
    specialRegularFamilyMarkedMeridianClass b =
      specialRegularFamilyMarkedSectionHom (compatibleRegularMeridianClass b) := rfl

/-- The actual projection, in the jointly proved geometric free coordinates. -/
def specialRegularFamilyMarkedFreeProjectionHom :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint →* FreeGroup Bool :=
  compatibleRegularFundamentalGroupEquiv.toMonoidHom.comp
    specialRegularFamilyMarkedProjectionHom

/-- The actual section, in the same jointly proved geometric free coordinates. -/
def specialRegularFamilyMarkedFreeSectionHom :
    FreeGroup Bool →* FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint :=
  specialRegularFamilyMarkedSectionHom.comp
    compatibleRegularFundamentalGroupEquiv.symm.toMonoidHom

@[simp] theorem specialRegularFamilyMarkedFreeSectionHom_of (b : Bool) :
    specialRegularFamilyMarkedFreeSectionHom (FreeGroup.of b) =
      specialRegularFamilyMarkedMeridianClass b := by
  change specialRegularFamilyMarkedSectionHom
    (compatibleRegularFundamentalGroupEquiv.symm (FreeGroup.of b)) = _
  rw [compatibleRegularFundamentalGroupEquiv_symm_of]
  rfl

/-- The actual fundamental group of the unconditional special family,
with the source-column lattice and the actual joint geometric meridian marking. -/
def specialRegularFamilyMarkedFundamentalGroupEquiv :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint ≃*
      (Multiplicative Lattice) ⋊[sourceFreeLatticeAction] (FreeGroup Bool) :=
  markedRegularFundamentalGroupEquiv specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

/-- The lattice generators are actual straight period loops in the included fibre. -/
theorem specialRegularFamilyMarkedLatticeHom_periodLoop (v : Lattice) :
    specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd v) =
      (Dsp).flatFibreFundamentalGroupHom bsp
        (Path.Homotopic.Quotient.mk (FlatTorus.periodLoop v)) :=
  (Dsp).latticeFundamentalGroupHom_periodLoop bsp v

@[simp] theorem specialRegularFamilyMarkedFundamentalGroupEquiv_lattice
    (v : Multiplicative Lattice) :
    specialRegularFamilyMarkedFundamentalGroupEquiv
      (specialRegularFamilyMarkedLatticeHom v) = SemidirectProduct.inl v :=
  markedRegularFundamentalGroupEquiv_lattice specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ v

@[simp] theorem specialRegularFamilyMarkedFundamentalGroupEquiv_meridian (b : Bool) :
    specialRegularFamilyMarkedFundamentalGroupEquiv
      (specialRegularFamilyMarkedMeridianClass b) = SemidirectProduct.inr (FreeGroup.of b) :=
  markedRegularFundamentalGroupEquiv_meridian specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ b

@[simp] theorem specialRegularFamilyMarkedFundamentalGroupEquiv_projection
    (γ : FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint) :
    (specialRegularFamilyMarkedFundamentalGroupEquiv γ).right =
      specialRegularFamilyMarkedFreeProjectionHom γ :=
  markedRegularFundamentalGroupEquiv_projection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ γ

/-- The actual zero section becomes the second semidirect-product inclusion. -/
theorem specialRegularFamilyMarkedFundamentalGroupEquiv_comp_section :
    specialRegularFamilyMarkedFundamentalGroupEquiv.toMonoidHom.comp
      specialRegularFamilyMarkedFreeSectionHom = SemidirectProduct.inr := by
  apply FreeGroup.ext_hom
  intro b
  change specialRegularFamilyMarkedFundamentalGroupEquiv
    (specialRegularFamilyMarkedFreeSectionHom (FreeGroup.of b)) = _
  rw [specialRegularFamilyMarkedFreeSectionHom_of,
    specialRegularFamilyMarkedFundamentalGroupEquiv_meridian]

@[simp] theorem specialRegularFamilyMarkedFundamentalGroupEquiv_section (w : FreeGroup Bool) :
    specialRegularFamilyMarkedFundamentalGroupEquiv
      (specialRegularFamilyMarkedFreeSectionHom w) = SemidirectProduct.inr w :=
  DFunLike.congr_fun specialRegularFamilyMarkedFundamentalGroupEquiv_comp_section w

theorem specialRegularFamilyMarkedLatticeHom_injective :
    Function.Injective specialRegularFamilyMarkedLatticeHom :=
  (Dsp).latticeFundamentalGroupHom_injective hqsp bsp

/-- The original projection and original zero section form a split exact
extension at the actual marked point, without any supplied geometric hypotheses. -/
theorem specialRegularFamilyMarkedFundamentalGroup_split_exact :
    Function.Injective specialRegularFamilyMarkedLatticeHom ∧
      specialRegularFamilyMarkedLatticeHom.range = specialRegularFamilyMarkedProjectionHom.ker ∧
      Function.Surjective specialRegularFamilyMarkedProjectionHom ∧
      specialRegularFamilyMarkedProjectionHom.comp specialRegularFamilyMarkedSectionHom =
        MonoidHom.id (FundamentalGroup TriangleRegularQuotient (triangleRegularProject bsp)) :=
  (Dsp).fundamentalGroup_split_exact hqsp bsp

/-- Conjugation by either literal section meridian is the fixed source action. -/
theorem specialRegularFamilyMarkedMeridian_conjugation
    (b : Bool) (v : Multiplicative Lattice) :
    specialRegularFamilyMarkedMeridianClass b * specialRegularFamilyMarkedLatticeHom v *
        (specialRegularFamilyMarkedMeridianClass b)⁻¹ =
      specialRegularFamilyMarkedLatticeHom (sourceFreeLatticeAction (FreeGroup.of b) v) := by
  apply specialRegularFamilyMarkedFundamentalGroupEquiv.injective
  rw [map_mul, map_mul, map_inv, specialRegularFamilyMarkedFundamentalGroupEquiv_meridian,
    specialRegularFamilyMarkedFundamentalGroupEquiv_lattice,
    specialRegularFamilyMarkedFundamentalGroupEquiv_lattice]
  simpa only [map_inv] using
    (SemidirectProduct.inl_aut (φ := sourceFreeLatticeAction) (FreeGroup.of b) v).symm

/-- The first actual section meridian conjugates the marked lattice by `A₁`. -/
theorem specialRegularFamilyMarkedMeridian_first_conjugation (v : Lattice) :
    specialRegularFamilyMarkedMeridianClass false *
        specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd v) *
        (specialRegularFamilyMarkedMeridianClass false)⁻¹ =
      specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd (A₁ *ᵥ v)) := by
  rw [specialRegularFamilyMarkedMeridian_conjugation]
  exact congrArg specialRegularFamilyMarkedLatticeHom
    (Multiplicative.toAdd.injective (sourceFreeLatticeAction_first (Multiplicative.ofAdd v)))

/-- The second actual section meridian conjugates the marked lattice by `A₂`. -/
theorem specialRegularFamilyMarkedMeridian_second_conjugation (v : Lattice) :
    specialRegularFamilyMarkedMeridianClass true *
        specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd v) *
        (specialRegularFamilyMarkedMeridianClass true)⁻¹ =
      specialRegularFamilyMarkedLatticeHom (Multiplicative.ofAdd (A₂ *ᵥ v)) := by
  rw [specialRegularFamilyMarkedMeridian_conjugation]
  exact congrArg specialRegularFamilyMarkedLatticeHom
    (Multiplicative.toAdd.injective (sourceFreeLatticeAction_second (Multiplicative.ofAdd v)))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
