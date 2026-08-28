import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionNative
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearHomology

/-!
# Genuine degree-one holomorphic cohomology and the two Haar means

The original Ext group is compared with the actual global Dolbeault
complex through the proved acyclic resolution. Fourier primitives then
identify a closed form's class with the literal means of its two marked
coefficients. Constants give the inverse, for every period domain point.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

/-- Actual degree-one sheaf cohomology, with its original scalars, is the marked pair space. -/
def h1Equiv (p : PeriodDomain) : H p 1 ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (h1FourierEquiv p).trans (FourierLinear.homologyIso p).toLinearEquiv

/-- The actual Ext class represented by a closed Fourier coefficient pair. -/
def h1Class (p : PeriodDomain) : FourierLinear.closedPairs p →ₗ[ℂ] H p 1 :=
  (h1FourierEquiv p).symm.toLinearMap.comp (FourierLinear.homologyClass p).hom

/-- The two cohomology coordinates are exactly the coefficient Haar means. -/
@[simp] theorem h1Equiv_class (p : PeriodDomain) (a : FourierLinear.closedPairs p) :
    h1Equiv p (h1Class p a) = FourierLinear.pairMean a.val := by
  change (FourierLinear.homologyIso p).hom
    (h1FourierEquiv p ((h1FourierEquiv p).symm (FourierLinear.homologyClass p a))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact FourierLinear.homologyIso_class_apply p a

/-- Literal constant coefficient pairs give actual cohomology classes. -/
def h1Constant (p : PeriodDomain) : (Fin 2 → ℂ) →ₗ[ℂ] H p 1 :=
  (h1Class p).comp (FourierLinear.closedConstantPair p)

@[simp] theorem h1Equiv_constant (p : PeriodDomain) (c : Fin 2 → ℂ) :
    h1Equiv p (h1Constant p c) = c := by
  change h1Equiv p (h1Class p (FourierLinear.closedConstantPair p c)) = c
  rw [h1Equiv_class, FourierLinear.closedConstantPair_val,
    FourierLinear.pairMean_constantPair]

/-- The inverse consists of the actual constant Dolbeault classes. -/
@[simp] theorem h1Equiv_symm_apply (p : PeriodDomain) (c : Fin 2 → ℂ) :
    (h1Equiv p).symm c = h1Constant p c := by
  apply (h1Equiv p).injective
  rw [LinearEquiv.apply_symm_apply, h1Equiv_constant]

/-- A genuinely closed pair represents zero precisely when both original Haar means vanish. -/
theorem h1Class_eq_zero_iff (p : PeriodDomain) (a : FourierLinear.closedPairs p) :
    h1Class p a = 0 ↔ FourierLinear.pairMean a.val = 0 := by
  rw [← (h1Equiv p).map_eq_zero_iff, h1Equiv_class]

/-- Every closed form has the actual class of its constant Haar-mean pair. -/
theorem h1Class_eq_constant (p : PeriodDomain) (a : FourierLinear.closedPairs p) :
    h1Class p a = h1Constant p (FourierLinear.pairMean a.val) := by
  apply (h1Equiv p).injective
  rw [h1Equiv_class, h1Equiv_constant]

/-- The Fourier representative of a literal closed pair of global sections on the native torus. -/
def nativeClosedPair (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) : FourierLinear.closedPairs p :=
  ⟨GlobalFourier.pairSectionEquiv p s, by
    change FourierLinear.top p (GlobalFourier.pairSectionEquiv p s) = 0
    rw [← GlobalFourier.sectionEquiv_top, hs, map_zero]⟩

/-- The actual Ext class of the two original smooth coefficients on the original torus. -/
def nativeH1Class (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) : H p 1 :=
  h1Class p (nativeClosedPair p s hs)

@[simp] theorem h1Equiv_nativeClass (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    h1Equiv p (nativeH1Class p s hs) = GlobalFourier.pairMean p s :=
  h1Equiv_class p (nativeClosedPair p s hs)

/-- The dimension is a consequence of the actual scalar-compatible class computation. -/
theorem h1_finrank (p : PeriodDomain) : Module.finrank ℂ (H p 1) = 2 :=
  (h1Equiv p).finrank_eq.trans (Module.finrank_fin_fun ℂ)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
