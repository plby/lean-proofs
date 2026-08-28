import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFormula

/-!
# The actual meromorphic canonical form and its holomorphic local frames

The bundle formula carries the independently constructed Cartier section
to the original normalized three-form.  Its native canonical section is
holomorphic off the cusp fibre, including the second elliptic fibre.
The local frames below are genuine holomorphic nonvanishing sections of
the original alternating-cotangent canonical bundle.  In those frames
the coefficients are the proved Cartier fractions, rather than formal
divisor labels.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalMeromorphicSection

open TrianglePeriodFamily.Canonical GlobalComparison
open CanonicalGlobalLineBundle.OpenMaps

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- The actual canonical fibre vector determined by the Cartier section.
Its values on the pole fibre are not asserted to be a holomorphic extension. -/
def rawSection (x : Threefold.Space) : Threefold.Canonical.bundle.Fiber x :=
  (canonicalFiberEquiv x).symm (GlobalPrescribedDivisor.cartier.rawSection x)

def rawSectionMap (x : Threefold.Space) : Threefold.Canonical.bundle.TotalSpace :=
  canonicalBundleBiholomorph.symm (GlobalPrescribedDivisor.cartier.rawSectionMap x)

@[simp] theorem rawSectionMap_mk (x : Threefold.Space) :
    rawSectionMap x = ⟨x, rawSection x⟩ := rfl

@[simp] theorem rawSectionMap_proj (x : Threefold.Space) :
    (rawSectionMap x).proj = x := rfl

@[simp] theorem canonicalFiberEquiv_rawSection (x : Threefold.Space) :
    canonicalFiberEquiv x (rawSection x) = GlobalPrescribedDivisor.cartier.rawSection x :=
  (canonicalFiberEquiv x).apply_symm_apply _

@[simp] theorem canonicalBundleBiholomorph_rawSectionMap (x : Threefold.Space) :
    canonicalBundleBiholomorph (rawSectionMap x) =
      GlobalPrescribedDivisor.cartier.rawSectionMap x :=
  canonicalBundleBiholomorph.apply_symm_apply _

/-- This is holomorphic on the whole complement of the cusp, not just
on the regular family or the complement of both special fibres. -/
theorem rawSectionMap_holomorphicOn_outside_cusp :
    ContMDiffOn IF Iκ ω rawSectionMap GlobalCusp.outside :=
  canonicalBundleBiholomorph.symm.contMDiff.comp_contMDiffOn
    GlobalPrescribedDivisor.rawSectionMap_holomorphicOn_outside_cusp

theorem rawSection_ne_zero {x : Threefold.Space}
    (hx : x ∈ GlobalPrescribedDivisor.cartier.genericSet) : rawSection x ≠ 0 := by
  intro hz
  have he := congrArg (canonicalFiberEquiv x) hz
  rw [canonicalFiberEquiv_rawSection, map_zero] at he
  exact GlobalPrescribedDivisor.cartier.rawSection_ne_zero hx he

/-- On the entire dense generic open this is the already constructed
normalized form, including its extension across the first elliptic fibre. -/
theorem rawSectionMap_eq_generic {x : Threefold.Space}
    (hx : x ∈ GlobalFiniteRegularSection.domain) :
    rawSectionMap x = GlobalFiniteRegularSection.genericSectionMap ⟨x, hx⟩ :=
  canonicalBundleBiholomorph_symm_rawSection hx

theorem rawSection_eq_generic {x : Threefold.Space}
    (hx : x ∈ GlobalFiniteRegularSection.domain) :
    rawSection x = GlobalFiniteRegularSection.genericSection ⟨x, hx⟩ :=
  congrArg (fun p : Threefold.Canonical.bundle.TotalSpace => id (α := ℂ) p.2)
    (rawSectionMap_eq_generic hx)

theorem rawSection_eq_regular {x : Threefold.Space} (hx : x ∈ regularLocus) :
    rawSection x = GlobalRegular.globalSection ⟨x, hx⟩ :=
  (rawSection_eq_generic (regular_le_generic hx)).trans
    (GlobalFiniteRegularSection.genericSection_eq_regular
      ⟨x, regular_le_generic hx⟩ hx)

/-- The equality with the actual elliptic extension holds on the full
original filling patch, including its central zero surface. -/
theorem rawSectionMap_eq_four (x : GlobalEllipticDivisor.patch) :
    rawSectionMap x.val = GlobalEllipticComparison.extendedSectionMap .four x := by
  have he := (globalGauge_diffeomorph_eq .elliptic
    (GlobalPrescribedDivisor.cartier.rawSectionMap x.val) x.property).trans
      (GlobalComparisonElliptic.totalMap_rawSection x)
  exact (congrArg NativePresentation.bundleBiholomorph.symm he).trans
    (NativePresentation.bundleBiholomorph.symm_apply_apply _)

/-- Genuine local frames of the original canonical bundle, obtained
from its actual holomorphic isomorphism with the independent Cartier line. -/
def frame (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space) :
    Threefold.Canonical.bundle.Fiber x :=
  (canonicalFiberEquiv x).symm
    (CanonicalGlobalLineBundle.OpenMaps.localFrame GlobalPrescribedDivisor.cartier.transitions i x)

def frameMap (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space) :
    Threefold.Canonical.bundle.TotalSpace :=
  canonicalBundleBiholomorph.symm
    (CanonicalGlobalLineBundle.OpenMaps.localFrameMap
      GlobalPrescribedDivisor.cartier.transitions i x)

@[simp] theorem frameMap_mk (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space) :
    frameMap i x = ⟨x, frame i x⟩ := rfl

theorem frameMap_holomorphicOn (i : GlobalPrescribedDivisor.Index) :
    ContMDiffOn IF Iκ ω (frameMap i)
      (GlobalPrescribedDivisor.cartier.transitions.baseSet i) :=
  canonicalBundleBiholomorph.symm.contMDiff.comp_contMDiffOn
    (CanonicalGlobalLineBundle.OpenMaps.localFrameMap_holomorphicOn
      GlobalPrescribedDivisor.cartier.transitions IF i)

theorem frame_ne_zero (i : GlobalPrescribedDivisor.Index) {x : Threefold.Space}
    (hx : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i) : frame i x ≠ 0 := by
  intro hz
  have he := congrArg (canonicalFiberEquiv x) hz
  change canonicalFiberEquiv x ((canonicalFiberEquiv x).symm
    (CanonicalGlobalLineBundle.OpenMaps.localFrame
      GlobalPrescribedDivisor.cartier.transitions i x)) =
      canonicalFiberEquiv x 0 at he
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at he
  exact CanonicalGlobalLineBundle.OpenMaps.localFrame_ne_zero
    GlobalPrescribedDivisor.cartier.transitions i hx he

/-- Coefficients are read in the actual local trivialization after
the proved holomorphic, fibre-linear canonical-bundle isomorphism. -/
def coefficient (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space) : ℂ :=
  (GlobalPrescribedDivisor.bundle.localTriv i
    (canonicalBundleBiholomorph (rawSectionMap x))).2

theorem coefficient_eq (i : GlobalPrescribedDivisor.Index) (x : Threefold.Space) :
    coefficient i x = GlobalPrescribedDivisor.cartier.transitions.localCoefficient
      GlobalPrescribedDivisor.cartier.rawSection i x := by
  rw [coefficient, canonicalBundleBiholomorph_rawSectionMap]
  rfl

/-- The native canonical coefficient is the literal holomorphic
numerator divided by the literal holomorphic denominator. -/
theorem coefficient_eq_fraction (i : GlobalPrescribedDivisor.Index) {x : Threefold.Space}
    (hi : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i)
    (hx : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    coefficient i x = GlobalPrescribedDivisor.cartier.localFraction i x :=
  (coefficient_eq i x).trans
    (GlobalPrescribedDivisor.cartier.rawSection_localCoefficient i hi hx)

/-- The canonical form is the stated coefficient times its genuine
holomorphic nonzero frame, as an equality in its original fibre. -/
theorem rawSection_eq_smul_frame (i : GlobalPrescribedDivisor.Index) {x : Threefold.Space}
    (hi : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i) :
    rawSection x = coefficient i x • frame i x := by
  apply (canonicalFiberEquiv x).injective
  rw [map_smul, canonicalFiberEquiv_rawSection]
  change GlobalPrescribedDivisor.cartier.rawSection x =
    coefficient i x • canonicalFiberEquiv x ((canonicalFiberEquiv x).symm
      (CanonicalGlobalLineBundle.OpenMaps.localFrame
        GlobalPrescribedDivisor.cartier.transitions i x))
  rw [ContinuousLinearEquiv.apply_symm_apply, coefficient_eq]
  let A := GlobalPrescribedDivisor.cartier.transitions
  have hc := A.transition_comp (A.indexAt x) i (A.indexAt x) x
    ⟨⟨A.mem_baseSet_at x, hi⟩, A.mem_baseSet_at x⟩
  have hc' := congrArg (fun z : ℂˣ => (z : ℂ))
    (hc.trans (A.transition_self _ _ (A.mem_baseSet_at x)))
  change id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x) =
    ((A.transition (A.indexAt x) i x : ℂ) *
      id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x)) *
        id (α := ℂ) (CanonicalGlobalLineBundle.OpenMaps.localFrame A i x)
  rw [CanonicalGlobalLineBundle.OpenMaps.localFrame_preferred A i hi]
  change (A.transition i (A.indexAt x) x : ℂ) *
    (A.transition (A.indexAt x) i x : ℂ) = 1 at hc'
  rw [mul_right_comm, mul_comm (A.transition (A.indexAt x) i x : ℂ), hc', one_mul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalMeromorphicSection
