import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyZero

/-!
# Native open-set maps for the degree-zero period-family direct image

The total-space atlas is always the original varying-period quotient
atlas. The projection, zero section, and inclusions of the original
complex period tori restrict to their literal maps on every base open.
Compactness of each native torus makes actual holomorphic functions
constant along its full fibre.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The original continuous family projection, as an actual morphism of spaces. -/
def projectionMap (P : HolomorphicPeriodMap V B) : TopCat.of P.TotalSpace ⟶ TopCat.of B :=
  TopCat.ofHom ⟨P.projection, P.projection_proper.continuous⟩

/-- The literal full inverse image of a base open set. -/
def basePreimage (P : HolomorphicPeriodMap V B) (U : Opens B) : Opens P.TotalSpace :=
  ⟨P.projection ⁻¹' (U : Set B), U.isOpen.preimage P.projection_proper.continuous⟩

@[simp] theorem mem_basePreimage (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : P.TotalSpace) : x ∈ basePreimage P U ↔ P.projection x ∈ U := Iff.rfl

theorem basePreimage_mono (P : HolomorphicPeriodMap V B) {U W : Opens B} (h : U ≤ W) :
    basePreimage P U ≤ basePreimage P W := fun _ hx => h hx

/-- The actual projection on the full inverse image of an open set. -/
def baseProjection (P : HolomorphicPeriodMap V B) (U : Opens B) : basePreimage P U → U :=
  fun x => ⟨P.projection x, x.property⟩

@[simp] theorem baseProjection_val (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : basePreimage P U) : (baseProjection P U x : B) = P.projection x := rfl

/-- The literal zero section restricted over the given base open. -/
def zeroSectionOn (P : HolomorphicPeriodMap V B) (U : Opens B) : U → basePreimage P U :=
  fun b => ⟨P.zeroSection b, b.property⟩

@[simp] theorem zeroSectionOn_val (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    (zeroSectionOn P U b : P.TotalSpace) = P.zeroSection b := rfl

@[simp] theorem baseProjection_zeroSectionOn (P : HolomorphicPeriodMap V B)
    (U : Opens B) (b : U) : baseProjection P U (zeroSectionOn P U b) = b := rfl

/-- The actual complex period-torus inclusion over a point of the base open. -/
def fibreOn (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    (P.point b).Torus → basePreimage P U :=
  fun z => ⟨P.fibreInclusion b z, b.property⟩

@[simp] theorem fibreOn_val (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U)
    (z : (P.point b).Torus) : (fibreOn P U b z : P.TotalSpace) = P.fibreInclusion b z := rfl

/-- The native fibre parametrization retains every original real-coordinate point. -/
@[simp] theorem fibreOn_torusHomeomorph (P : HolomorphicPeriodMap V B) (U : Opens B)
    (b : U) (t : RealTorus₄) :
    fibreOn P U b (P.torusHomeomorph b t) =
      (⟨((b : B), t), b.property⟩ : basePreimage P U) := by
  apply Subtype.ext
  exact congrArg (Prod.mk (b : B)) ((P.torusHomeomorph b).symm_apply_apply t)

/-- Actual holomorphic functions on the original base open. -/
abbrev BaseSection (_P : HolomorphicPeriodMap V B) (U : Opens B) :=
  HolomorphicFunctionSheaf.Section IB B U

/-- Actual holomorphic functions on its full preimage, using precisely
the original varying-period complex atlas. -/
abbrev PreimageSection (P : HolomorphicPeriodMap V B) (U : Opens B) : Type :=
  letI := P.totalChartedSpace
  HolomorphicFunctionSheaf.Section IT P.TotalSpace (basePreimage P U)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The restricted projection is holomorphic in the original total-space atlas. -/
theorem baseProjection_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := P.totalChartedSpace
    ContMDiff IT IB ω (baseProjection P U) := by
  let := P.totalChartedSpace
  intro x
  have h : ContMDiffAt IT IB ω
      (fun y : basePreimage P U => (baseProjection P U y : B)) x ↔
      ContMDiffAt IT IB ω (baseProjection P U) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp ((P.projection_holomorphic.comp contMDiff_subtype_val) x)

/-- The actual restricted zero section is holomorphic for that same native atlas. -/
theorem zeroSectionOn_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := P.totalChartedSpace
    ContMDiff IB IT ω (zeroSectionOn P U) := by
  let := P.totalChartedSpace
  intro b
  have h : ContMDiffAt IB IT ω
      (fun x : U => (zeroSectionOn P U x : P.TotalSpace)) b ↔
      ContMDiffAt IB IT ω (zeroSectionOn P U) b :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp ((P.zeroSection_holomorphic.comp contMDiff_subtype_val) b)

/-- The original compact complex torus maps holomorphically into the full preimage. -/
theorem fibreOn_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    letI := P.totalChartedSpace
    ContMDiff I₂ IT ω (fibreOn P U b) := by
  let := P.totalChartedSpace
  intro z
  have h : ContMDiffAt I₂ IT ω
      (fun t : (P.point b).Torus => (fibreOn P U b t : P.TotalSpace)) z ↔
      ContMDiffAt I₂ IT ω (fibreOn P U b) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (P.fibreInclusion_holomorphic b z)

/-- Restrict a native holomorphic section to the actual compact complex torus. -/
def sectionOnFibre (P : HolomorphicPeriodMap V B) (U : Opens B) (s : PreimageSection P U)
    (b : U) : PeriodTorusHolomorphicCohomology.HolomorphicFunction (P.point b) := by
  letI := P.totalChartedSpace
  exact ⟨s ∘ fibreOn P U b, s.contMDiff.comp (fibreOn_holomorphic P U b)⟩

@[simp] theorem sectionOnFibre_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (s : PreimageSection P U) (b : U) (z : (P.point b).Torus) :
    sectionOnFibre P U s b z = s (fibreOn P U b z) := rfl

/-- Every genuine holomorphic section has its zero-section value on
each full fibre, by constancy on the original compact complex period torus. -/
theorem section_apply_eq_zeroSection (P : HolomorphicPeriodMap V B) (U : Opens B)
    (s : PreimageSection P U) (x : basePreimage P U) :
    s x = s (zeroSectionOn P U (baseProjection P U x)) := by
  rcases x with ⟨⟨b, t⟩, hb⟩
  let b' : U := ⟨b, hb⟩
  have h := PeriodTorusHolomorphicCohomology.holomorphic_apply_eq (P.point b)
    (sectionOnFibre P U s b') (P.torusHomeomorph b t) (P.torusHomeomorph b 0)
  exact (congrArg s (fibreOn_torusHomeomorph P U b' t)).symm.trans
    (h.trans (congrArg s (fibreOn_torusHomeomorph P U b' 0)))

/-- Constancy is on literal fibres of the original projection on every base open. -/
theorem section_fibre_apply_eq (P : HolomorphicPeriodMap V B) (U : Opens B)
    (s : PreimageSection P U) (x y : basePreimage P U)
    (hxy : P.projection x = P.projection y) : s x = s y := by
  have h : baseProjection P U x = baseProjection P U y := Subtype.ext hxy
  exact (section_apply_eq_zeroSection P U s x).trans
    ((congrArg (fun b => s (zeroSectionOn P U b)) h).trans
      (section_apply_eq_zeroSection P U s y).symm)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero
