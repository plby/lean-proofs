import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionRatioBasic

/-!
# The full global cusp patch and its actual regular overlap

The original full cusp-patch biholomorphism identifies its punctured part
with the actual regular locus. The fixed reciprocal sphere coordinate is
holomorphic on this entire patch and vanishes exactly on its central fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance patchNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance patchGlobalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The entire actual global cusp neighborhood, including the central fibre. -/
abbrev FullCuspPatch := Threefold.liftedPatch (some none)

/-- Its point in the original native quotient, using the genuine patch biholomorphism. -/
def nativePoint (y : FullCuspPatch) : LocalSpace := nativePatchBiholomorph.symm y

@[simp] theorem inclusion_nativePoint (y : FullCuspPatch) :
    CuspGeometry.inclusion (nativePoint y) = y.val :=
  congrArg Subtype.val (nativePatchBiholomorph.apply_symm_apply y)

/-- The actual cusp parameter on the full patch. -/
def patchParameter (y : FullCuspPatch) : ℂ := parameter (nativePoint y)

theorem patchParameter_eq_cuspCoordinate (y : FullCuspPatch) :
    patchParameter y = cuspCoordinate y.val := by
  rw [← inclusion_nativePoint y, cuspCoordinate_inclusion]
  rfl

theorem patchParameter_holomorphic : ContMDiff IF I₁ ω patchParameter :=
  parameter_holomorphic.comp nativePatchBiholomorph.symm.contMDiff

/-- Removing the central fibre is exactly the actual regular overlap, not a new open set. -/
theorem patch_mem_regular_iff (y : FullCuspPatch) :
    y.val ∈ regularLocus ↔ patchParameter y ≠ 0 := by
  constructor
  · intro hy hz
    have hn := ((mem_sphereRegularPatch _).mp ((mem_regularLocus_iff_sphere _).mp hy)).1
    apply hn
    rw [← inclusion_nativePoint y]
    exact (projectionSphere_inclusion_eq_infty_iff (nativePoint y)).mpr hz
  · intro hy
    have hm := inclusion_mem_regular (⟨nativePoint y, hy⟩ : puncturedNative)
    simpa only [inclusion_nativePoint y] using hm

/-- The corresponding original native punctured point on any actual global regular overlap. -/
def regularPatchPoint (y : FullCuspPatch) (hy : y.val ∈ regularLocus) : puncturedNative :=
  ⟨nativePoint y, (patch_mem_regular_iff y).mp hy⟩

theorem puncturedRegularPoint_regularPatchPoint (y : FullCuspPatch)
    (hy : y.val ∈ regularLocus) :
    puncturedRegularPoint (regularPatchPoint y hy) = ⟨y.val, hy⟩ :=
  Subtype.ext (inclusion_nativePoint y)

/-- The full native cusp patch misses the omitted point of the reciprocal sphere chart. -/
theorem native_projection_ne_zero (x : LocalSpace) :
    Threefold.projectionSphere (CuspGeometry.inclusion x) ≠ ((0 : ℂ) : RiemannSphere) := by
  by_cases hx : parameter x = 0
  · rw [(projectionSphere_inclusion_eq_infty_iff x).mpr hx]
    exact OnePoint.infty_ne_coe 0
  · exact (punctured_projection_ne (⟨x, hx⟩ : puncturedNative)).2.1

/-- The fixed reciprocal coordinate composed with the actual full native cusp inclusion. -/
def nativeReciprocal (x : LocalSpace) : ℂ :=
  GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (CuspGeometry.inclusion x))

theorem nativeReciprocal_holomorphic : ContMDiff I₃ I₁ ω nativeReciprocal := by
  intro x
  apply (MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
    (native_projection_ne_zero x)).comp x
  exact (Threefold.projectionSphere_holomorphic.comp CuspGeometry.inclusion_holomorphic) x

@[simp] theorem nativeReciprocal_punctured (x : puncturedNative) :
    nativeReciprocal x.val = reciprocalParameter x := rfl

theorem nativeReciprocal_eq_zero_iff (x : LocalSpace) :
    nativeReciprocal x = 0 ↔ parameter x = 0 := by
  constructor
  · intro hx
    by_contra hn
    exact reciprocalParameter_ne_zero (⟨x, hn⟩ : puncturedNative) hx
  · intro hx
    change GlobalCusp.reciprocalCoordinate
      (Threefold.projectionSphere (CuspGeometry.inclusion x)) = 0
    rw [(projectionSphere_inclusion_eq_infty_iff x).mpr hx,
      GlobalCusp.reciprocalCoordinate_infty]

/-- The fixed reciprocal coordinate restricted to the actual full global cusp patch. -/
def patchReciprocal (y : FullCuspPatch) : ℂ :=
  GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere y.val)

theorem patchReciprocal_eq_native (y : FullCuspPatch) :
    patchReciprocal y = nativeReciprocal (nativePoint y) := by
  change _ = GlobalCusp.reciprocalCoordinate
    (Threefold.projectionSphere (CuspGeometry.inclusion (nativePoint y)))
  rw [inclusion_nativePoint]
  rfl

theorem patchReciprocal_holomorphic : ContMDiff IF I₁ ω patchReciprocal := by
  have he : patchReciprocal = nativeReciprocal ∘ nativePatchBiholomorph.symm :=
    funext patchReciprocal_eq_native
  rw [he]
  exact nativeReciprocal_holomorphic.comp nativePatchBiholomorph.symm.contMDiff

theorem patchReciprocal_eq_zero_iff (y : FullCuspPatch) :
    patchReciprocal y = 0 ↔ patchParameter y = 0 := by
  rw [patchReciprocal_eq_native, nativeReciprocal_eq_zero_iff]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
