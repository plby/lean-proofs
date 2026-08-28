import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarLocalGenerators
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarGluing

/-!
# A native polar line bundle for every genuine surface meromorphic function

Starting with an arbitrary section of the original meromorphic sheaf, the
proved analytic preparation theorem constructs local reduced numerator and
denominator functions. Their actual principal denominator ideals determine
holomorphic transition units. The resulting `VectorBundleCore` carries its
native topology and analytic atlas, and its two genuine `ContMDiffSection`s
recover the original meromorphic section in every native bundle frame.

No line bundle, quotient presentation, coherence statement, or local
denominator-principality premise is supplied to this construction.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarRepresentation

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]
  (e : (ℂ × ℂ) ≃L[ℂ] E) (s : Section I M ⊤)

/-- The actual local domain chosen around each original point. -/
abbrev domain (i : M) : Opens M := (PolarLocal.presentationAt I M e s i).domain

theorem mem_domain (x : M) : x ∈ domain I M e s x :=
  PolarLocal.mem_presentationAt I M e s x

theorem domains_cover : ∀ x : M, ∃ i : M, x ∈ domain I M e s i :=
  PolarLocal.presentationAt_cover I M e s

/-- Actual polar transition functions, derived from the original function. -/
def cocycle : PolarBundle.ScalarCocycle I M M :=
  PolarGluing.cocycle I M (PolarLocal.presentationAt I M e s)
    (PolarLocal.presentationAt_cover I M e s)

/-- The genuine polar bundle, with the native bundle-core topology and atlas. -/
abbrev bundleCore : VectorBundleCore ℂ M ℂ M := (cocycle I M e s).core

theorem bundle_isHolomorphic :
    ContMDiffVectorBundle ω ℂ (bundleCore I M e s).Fiber I := inferInstance

theorem bundle_fibre_finrank (x : M) :
    Module.finrank ℂ ((bundleCore I M e s).Fiber x) = 1 :=
  (cocycle I M e s).core_finrank x

theorem bundle_totalSpace_isManifold :
    IsManifold (I.prod 𝓘(ℂ)) ω (bundleCore I M e s).TotalSpace := inferInstance

/-- The original function's genuine global holomorphic numerator section. -/
def nativeNumerator : ContMDiffSection I ℂ ω (bundleCore I M e s).Fiber :=
  PolarGluing.numeratorSection I M (PolarLocal.presentationAt I M e s)
    (PolarLocal.presentationAt_cover I M e s)

/-- The original function's genuine global holomorphic denominator section. -/
def nativeDenominator : ContMDiffSection I ℂ ω (bundleCore I M e s).Fiber :=
  PolarGluing.denominatorSection I M (PolarLocal.presentationAt I M e s)
    (PolarLocal.presentationAt_cover I M e s)

theorem nativeNumerator_localTriv (i : M) {x : M} (hx : x ∈ domain I M e s i) :
    (bundleCore I M e s).localTriv i ⟨x, nativeNumerator I M e s x⟩ =
      (x, (PolarLocal.presentationAt I M e s i).numerator ⟨x, hx⟩) :=
  PolarGluing.numeratorSection_localTriv I M _ _ i hx

theorem nativeDenominator_localTriv (i : M) {x : M} (hx : x ∈ domain I M e s i) :
    (bundleCore I M e s).localTriv i ⟨x, nativeDenominator I M e s x⟩ =
      (x, (PolarLocal.presentationAt I M e s i).denominator ⟨x, hx⟩) :=
  PolarGluing.denominatorSection_localTriv I M _ _ i hx

/-- The literal native frame coordinates of the constructed numerator. -/
def numeratorInChart (i : M) : HolomorphicFunctionSheaf.Section I M (domain I M e s i) :=
  PolarGluing.numeratorInChart I M _ (PolarLocal.presentationAt_cover I M e s) i

/-- The literal native frame coordinates of the constructed denominator. -/
def denominatorInChart (i : M) : HolomorphicFunctionSheaf.Section I M (domain I M e s i) :=
  PolarGluing.denominatorInChart I M _ (PolarLocal.presentationAt_cover I M e s) i

@[simp] theorem numeratorInChart_apply (i : M) (x : domain I M e s i) :
    numeratorInChart I M e s i x =
      ((bundleCore I M e s).localTriv i ⟨x.val, nativeNumerator I M e s x.val⟩).2 := rfl

@[simp] theorem denominatorInChart_apply (i : M) (x : domain I M e s i) :
    denominatorInChart I M e s i x =
      ((bundleCore I M e s).localTriv i ⟨x.val, nativeDenominator I M e s x.val⟩).2 := rfl

theorem denominatorInChart_germ_ne_zero (i : M) (x : domain I M e s i) :
    holomorphicGerm I M (domain I M e s i) x (denominatorInChart I M e s i) ≠ 0 :=
  PolarGluing.denominatorInChart_germ_ne_zero I M _ _ i x

/-- The ratio of the actual native sections is the original meromorphic
germ at every point, including zeros of the denominator section. -/
theorem ratio_germ (i : M) (x : domain I M e s i) :
    s ⟨x.val, Set.mem_univ x.val⟩ =
      fraction I M (domain I M e s i) (numeratorInChart I M e s i)
        (denominatorInChart I M e s i) x :=
  PolarGluing.quotient_germ I M _ _ i x

/-- Equality with the original meromorphic section on a genuine open cover. -/
theorem ratio_in_chart (i : M) :
    restrict I M le_top s =
      ofFraction I M (domain I M e s i) (numeratorInChart I M e s i)
        (denominatorInChart I M e s i) (denominatorInChart_germ_ne_zero I M e s i) :=
  PolarGluing.quotient_in_chart I M _ _ i

/-- On a nonempty surface the constructed denominator section is genuinely
nonzero, not merely a formal denominator label. -/
theorem nativeDenominator_ne_zero [Nonempty M] :
    ∃ x : M, nativeDenominator I M e s x ≠ 0 := by
  classical
  by_contra h
  apply PolarGluing.denominatorSection_ne_zero I M
    (PolarLocal.presentationAt I M e s) (PolarLocal.presentationAt_cover I M e s)
  apply ContMDiffSection.ext
  intro x
  exact not_not.mp (fun hx => h ⟨x, hx⟩)

/-- Proportionality of these actual native sections forces the original
full meromorphic function to equal a genuine complex constant. -/
theorem eq_constant_of_native_proportionality (c : ℂ)
    (h : ∀ x : M, nativeNumerator I M e s x = c • nativeDenominator I M e s x) :
    s = algebraMap ℂ (Section I M ⊤) c := by
  apply PolarGluing.proportionality_constancy I M
    (PolarLocal.presentationAt I M e s) (PolarLocal.presentationAt_cover I M e s) c
  apply ContMDiffSection.ext
  exact h

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarRepresentation
