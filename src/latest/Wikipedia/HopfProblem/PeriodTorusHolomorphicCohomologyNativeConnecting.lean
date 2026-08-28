import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyOne
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyTwo
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyNativeConnectingForget
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionRepresentatives

/-!
# Native Dolbeault representatives are the genuine Ext connecting classes

The previously constructed representative maps agree with the actual
connecting maps of the two short exact sequences in the native Dolbeault
resolution. Their coordinates are the literal marked Haar means, with
the unchanged positive connecting-map convention in degrees one and two.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyScalarResolution

/-- Literal global sections of the actual intermediate kernel sheaf. -/
abbrev GlobalKernelSections (p : PeriodDomain) :=
  (globalSectionsFunctor (TopCat.of p.Torus)).obj (Dolbeault.resolution p).K

/-- The actual kernel inclusion sends a global kernel section to its two
native smooth coefficients. -/
def nativeKernelSection (p : PeriodDomain) (k : GlobalKernelSections p) :
    Dolbeault.PairSection p ⊤ :=
  (globalSectionsFunctor (TopCat.of p.Torus)).map
    (kernel.ι (Dolbeault.resolution p).complex.g) k

/-- The original kernel inclusion makes the literal native coefficient pair closed. -/
theorem nativeKernelSection_closed (p : PeriodDomain) (k : GlobalKernelSections p) :
    Dolbeault.topSection p ⊤ (nativeKernelSection p k) = 0 :=
  ConcreteCategory.congr_hom
    (((Dolbeault.resolution p).second.map
      (globalSectionsFunctor (TopCat.of p.Torus))).zero) k

/-- Its actual global cycle has exactly the original included coefficients. -/
theorem globalCycleMap_nativeKernelSection (p : PeriodDomain) (k : GlobalKernelSections p) :
    (Dolbeault.resolution p).globalComplex.iCycles
      ((Dolbeault.resolution p).globalCycleMap k) = nativeKernelSection p k :=
  ConcreteCategory.congr_hom (Dolbeault.resolution p).globalCycleMap_i k

namespace NativeConnecting

/-- Apply the genuine global-complex and forgetful cycle comparisons to
the original global kernel section. -/
def comparedKernelCycle (p : PeriodDomain) (k : GlobalKernelSections p) :
    (FourierLinear.complex p).cycles :=
  ((FourierLinear.complex p).mapCyclesIso linearForget).hom
    (ShortComplex.cyclesMap (GlobalFourier.complexIso p).hom
      ((Dolbeault.resolution p).globalCycleMap k))

/-- The compared cycle retains the actual native coefficient functions. -/
theorem comparedKernelCycle_iCycles (p : PeriodDomain) (k : GlobalKernelSections p) :
    (FourierLinear.complex p).iCycles (comparedKernelCycle p k) =
      GlobalFourier.pairSectionEquiv p (nativeKernelSection p k) := by
  let y := ShortComplex.cyclesMap (GlobalFourier.complexIso p).hom
    ((Dolbeault.resolution p).globalCycleMap k)
  have hf := ConcreteCategory.congr_hom
    ((FourierLinear.complex p).mapCyclesIso_hom_iCycles linearForget) y
  have he := ConcreteCategory.congr_hom
    (ShortComplex.cyclesMap_i (GlobalFourier.complexIso p).hom)
    ((Dolbeault.resolution p).globalCycleMap k)
  exact hf.trans (he.trans
    (congrArg (GlobalFourier.pairSectionEquiv p) (globalCycleMap_nativeKernelSection p k)))

/-- The original degree-one connecting class gives its corresponding
canonical cycle class in the actual Fourier complex. -/
theorem h1FourierEquiv_globalConnectingOne (p : PeriodDomain) (k : GlobalKernelSections p) :
    h1FourierEquiv p ((Dolbeault.resolution p).globalConnectingOne k) =
      (FourierLinear.complex p).homologyπ (comparedKernelCycle p k) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  have hd := ConcreteCategory.congr_hom (Dolbeault.resolution p).h1Iso_connecting k
  have hp := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_naturality (GlobalFourier.complexIso p).hom)
    ((Dolbeault.resolution p).globalCycleMap k)
  change homologyForgetAddEquiv (FourierLinear.complex p)
    (ShortComplex.homologyMap (GlobalFourier.complexIso p).hom
      ((Dolbeault.resolution p).h1Iso.hom
        ((Dolbeault.resolution p).globalConnectingOne k))) = _
  exact (congrArg (homologyForgetAddEquiv (FourierLinear.complex p))
    ((congrArg (ShortComplex.homologyMap (GlobalFourier.complexIso p).hom) hd).trans hp)).trans
      (homologyForget_projection_apply (FourierLinear.complex p) _)

end NativeConnecting

/-- The coordinates of the original Ext connecting class are precisely
the Haar means of its original two native smooth coefficients. -/
theorem h1Equiv_globalConnectingOne (p : PeriodDomain) (k : GlobalKernelSections p) :
    h1Equiv p ((Dolbeault.resolution p).globalConnectingOne k) =
      GlobalFourier.pairMean p (nativeKernelSection p k) := by
  change (FourierLinear.homologyIso p).hom
    (h1FourierEquiv p ((Dolbeault.resolution p).globalConnectingOne k)) = _
  rw [NativeConnecting.h1FourierEquiv_globalConnectingOne]
  have h := ConcreteCategory.congr_hom (FourierLinear.homologyIso_π p)
    (NativeConnecting.comparedKernelCycle p k)
  exact h.trans (congrArg FourierLinear.pairMean
    (NativeConnecting.comparedKernelCycle_iCycles p k))

/-- The native degree-one representative map agrees with the genuine
connecting map on every actual global section of the kernel sheaf. -/
theorem nativeH1Class_eq_globalConnectingOne (p : PeriodDomain) (k : GlobalKernelSections p) :
    nativeH1Class p (nativeKernelSection p k) (nativeKernelSection_closed p k) =
      (Dolbeault.resolution p).globalConnectingOne k := by
  apply (h1Equiv p).injective
  exact (h1Equiv_nativeClass p _ _).trans (h1Equiv_globalConnectingOne p k).symm

/-- The actual double connecting map gives the canonical top coefficient
class in the actual Fourier cokernel. -/
theorem h2FourierEquiv_globalConnectingTwo (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) :
    h2FourierEquiv p ((Dolbeault.resolution p).globalConnectingTwo s) =
      cokernel.π (FourierLinear.complex p).g (GlobalFourier.sectionEquiv p s) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 2) :=
    Dolbeault.smooth_higher_subsingleton p 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₂ 1) :=
    Dolbeault.pair_higher_subsingleton p 0
  have hd := ConcreteCategory.congr_hom (Dolbeault.resolution p).h2Iso_connecting s
  have hp := ConcreteCategory.congr_hom
    (ResolutionLinear.cokernelComplexIso_π (GlobalFourier.complexIso p)) s
  change cokernelForgetAddEquiv (FourierLinear.complex p)
    ((ResolutionLinear.cokernelComplexIso (GlobalFourier.complexIso p)).hom
      ((Dolbeault.resolution p).h2Iso.hom
        ((Dolbeault.resolution p).globalConnectingTwo s))) = _
  exact (congrArg (cokernelForgetAddEquiv (FourierLinear.complex p))
    ((congrArg (ResolutionLinear.cokernelComplexIso (GlobalFourier.complexIso p)).hom hd).trans
      hp)).trans (cokernelForgetAddEquiv_π (FourierLinear.complex p) _)

/-- The native degree-two representative map is the original double
Ext connecting map, with no change of sign or constant normalization. -/
theorem nativeH2Class_eq_globalConnectingTwo (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) :
    nativeH2Class p s = (Dolbeault.resolution p).globalConnectingTwo s := by
  apply (h2FourierEquiv p).injective
  change h2FourierEquiv p ((h2FourierEquiv p).symm
    (cokernel.π (FourierLinear.complex p).g (GlobalFourier.sectionEquiv p s))) = _
  rw [LinearEquiv.apply_symm_apply, h2FourierEquiv_globalConnectingTwo]

/-- The coordinate of an actual double connecting class is precisely
the probability Haar mean of its original native coefficient. -/
theorem h2Equiv_globalConnectingTwo (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) :
    h2Equiv p ((Dolbeault.resolution p).globalConnectingTwo s) =
      GlobalFourier.mean p s := by
  rw [← nativeH2Class_eq_globalConnectingTwo]
  exact h2Equiv_nativeClass p s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
