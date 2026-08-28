import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticTransverse
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic

/-!
# Actual transverse coefficients of arbitrary native canonical sections

An arbitrary section of the original canonical bundle is read in the
genuine holomorphic frame supplied by the proved canonical-bundle
isomorphism.  Its restriction to the original transverse inverse-chart
curve is analytic.  Dividing by the proved nonzero period unit gives
the holomorphic numerator used in the ramified removability argument.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

open TrianglePeriodFamily.Canonical GlobalComparison

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  specialEllipticPieceChartedSpace

/-- The coefficient of a literal canonical vector after the actual
holomorphic fibre-linear isomorphism and the original target chart. -/
def fiberCoefficient (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) : ℂ :=
  (GlobalPrescribedDivisor.bundle.localTriv i
    (canonicalBundleBiholomorph ⟨x, v⟩)).2

theorem fiberCoefficient_smul (i : GlobalPrescribedDivisor.Index) {x : Threefold.Space}
    (hx : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i)
    (c : ℂ) (v : Threefold.Canonical.bundle.Fiber x) :
    fiberCoefficient i x (c • v) = c * fiberCoefficient i x v := by
  simp only [fiberCoefficient, canonicalBundleBiholomorph_mk, map_smul]
  exact ((GlobalPrescribedDivisor.bundle.localTriv i).linear ℂ hx).2 c
    (canonicalFiberEquiv x v)

theorem fiberCoefficient_rawSection (i : GlobalPrescribedDivisor.Index)
    (x : Threefold.Space) :
    fiberCoefficient i x (GlobalMeromorphicSection.rawSection x) =
      GlobalMeromorphicSection.coefficient i x := rfl

def sectionCoefficient (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (i : GlobalPrescribedDivisor.Index) (x : V) : ℂ :=
  fiberCoefficient i x.val (s x)

theorem sectionCoefficient_holomorphicAt (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (i : GlobalPrescribedDivisor.Index) (x : V)
    (hx : x.val ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i) :
    ContMDiffAt IF 𝓘(ℂ) ω (sectionCoefficient V s i) x := by
  have hs : ContMDiff IF Iκ ω (fun x : V =>
      (⟨x.val, canonicalFiberEquiv x.val (s x)⟩ : GlobalPrescribedDivisor.bundle.TotalSpace)) :=
    canonicalBundleBiholomorph.contMDiff.comp s.contMDiff_toFun
  exact (NativeBundleSections.Section.holomorphicAt_iff
    GlobalPrescribedDivisor.bundle IF (fun x : V => canonicalFiberEquiv x.val (s x)) x i hx).mp
      (hs x)

/-- The actual transverse curve, codrestricted to an arbitrary section
domain near its centre.  Only its irrelevant values outside that domain
are filled in by the centre itself. -/
def transverseInto (V : Opens Threefold.Space) (y : GlobalEllipticDivisor.patch)
    (hyV : y.val ∈ V) (z : ℂ) : V := by
  classical
  exact if hz : (transversePoint y z).val ∈ V then ⟨(transversePoint y z).val, hz⟩
    else ⟨y.val, hyV⟩

theorem transverseInto_val_of_mem (V : Opens Threefold.Space)
    (y : GlobalEllipticDivisor.patch) (hyV : y.val ∈ V) {z : ℂ}
    (hz : (transversePoint y z).val ∈ V) :
    (transverseInto V y hyV z).val = (transversePoint y z).val := by
  simp only [transverseInto, dif_pos hz]

theorem transverseInto_zero (V : Opens Threefold.Space) (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) (hyV : y.val ∈ V) :
    transverseInto V y hyV 0 = ⟨y.val, hyV⟩ := by
  apply Subtype.ext
  have hm : (transversePoint y 0).val ∈ V := by
    rw [transversePoint_zero y hy]
    exact hyV
  rw [transverseInto_val_of_mem V y hyV hm, transversePoint_zero y hy]

theorem transversePoint_mem_eventually (V : Opens Threefold.Space)
    (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
    (hyV : y.val ∈ V) : ∀ᶠ z in 𝓝 (0 : ℂ), (transversePoint y z).val ∈ V := by
  have hh := transversePoint_val_continuousAt y hy
  have hz : (transversePoint y 0).val ∈ V := by
    rw [transversePoint_zero y hy]
    exact hyV
  exact hh (V.isOpen.mem_nhds hz)

theorem transverseInto_val_eventuallyEq (V : Opens Threefold.Space)
    (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
    (hyV : y.val ∈ V) :
    (fun z => (transverseInto V y hyV z).val) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (transversePoint y z).val) :=
  (transversePoint_mem_eventually V y hy hyV).mono
    (fun _ hz => transverseInto_val_of_mem V y hyV hz)

theorem transverseInto_holomorphicAt (V : Opens Threefold.Space)
    (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
    (hyV : y.val ∈ V) : ContMDiffAt 𝓘(ℂ) IF ω (transverseInto V y hyV) 0 := by
  have hh : ContMDiffAt 𝓘(ℂ) IF ω (fun z => (transversePoint y z).val) 0 :=
    (contMDiff_subtype_val _).comp 0 (transversePoint_holomorphicAt y hy)
  have he : ContMDiffAt 𝓘(ℂ) IF ω (Subtype.val ∘ transverseInto V y hyV) 0 ↔
      ContMDiffAt 𝓘(ℂ) IF ω (transverseInto V y hyV) 0 :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hh.congr_of_eventuallyEq (transverseInto_val_eventuallyEq V y hy hyV))

def transverseSectionCoefficient (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (y : GlobalEllipticDivisor.patch) (hyV : y.val ∈ V) : ℂ → ℂ :=
  sectionCoefficient V s (GlobalMeromorphicSection.transverseFrameIndex y) ∘
    transverseInto V y hyV

/-- The actual coefficient of any holomorphic native section is an
analytic function along this original transverse chart curve. -/
theorem transverseSectionCoefficient_analyticAt (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
    (hyV : y.val ∈ V) : AnalyticAt ℂ (transverseSectionCoefficient V s y hyV) 0 := by
  have hi : y.val ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet
      (GlobalMeromorphicSection.transverseFrameIndex y) := by
    have h := mem_of_mem_nhds (GlobalMeromorphicSection.transverseFrame_valid_eventually y hy)
    change (transversePoint y 0).val ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet
      (GlobalMeromorphicSection.transverseFrameIndex y) at h
    simpa only [transversePoint_zero y hy] using h
  have hh := sectionCoefficient_holomorphicAt V s
    (GlobalMeromorphicSection.transverseFrameIndex y) ⟨y.val, hyV⟩ hi
  have hc := transverseInto_holomorphicAt V y hy hyV
  have hh' : ContMDiffAt IF 𝓘(ℂ) ω
      (sectionCoefficient V s (GlobalMeromorphicSection.transverseFrameIndex y))
      (transverseInto V y hyV 0) := by
    rw [transverseInto_zero V y hy hyV]
    exact hh
  exact (hh'.comp 0 hc).contDiffAt.analyticAt

def periodUnitExtension : ℂ → ℂ := SectionsUnit.discExtension (SectionsUnit.specialUnit .four)

theorem periodUnitExtension_analyticAt : AnalyticAt ℂ periodUnitExtension 0 :=
  SectionsUnit.discExtension_analyticAt (SectionsUnit.specialUnit_holomorphic .four)

theorem periodUnitExtension_zero_ne_zero : periodUnitExtension 0 ≠ 0 := by
  rw [periodUnitExtension, SectionsUnit.discExtension_zero]
  exact SectionsUnit.specialUnit_ne_zero .four _

def normalizedTransverseCoefficient (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (y : GlobalEllipticDivisor.patch) (hyV : y.val ∈ V) : ℂ → ℂ :=
  fun z => transverseSectionCoefficient V s y hyV z / periodUnitExtension z

theorem normalizedTransverseCoefficient_analyticAt (V : Opens Threefold.Space)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
    (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
    (hyV : y.val ∈ V) : AnalyticAt ℂ (normalizedTransverseCoefficient V s y hyV) 0 :=
  (transverseSectionCoefficient_analyticAt V s y hy hyV).div
    periodUnitExtension_analyticAt periodUnitExtension_zero_ne_zero

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
