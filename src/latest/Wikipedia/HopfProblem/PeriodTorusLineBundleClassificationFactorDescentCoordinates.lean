import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentFiber

/-!
# Native coordinate formulas for the descended frame isomorphism

The forward map multiplies the factor-bundle coordinate in any quotient
lift by the frame coefficient in any original native chart. Solving that
nonzero scalar equation gives the local expression for the inverse.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

variable (s : CoverSection p V) (hne : ∀ z, s z ≠ 0) (F : FactorOfAutomorphy p)
    (hrel : ∀ (l : p.lattice) (z : ComplexPlane₂) (c : ℂ),
      coverScalarMap s (z + l, (F.factor l z : ℂ) * c) = coverScalarMap s (z, c))

include hrel

theorem frameCoreToNative_localTriv (i j : p.Torus)
    (u : (Core.data F).core.TotalSpace)
    (hi : u.proj ∈ Core.baseSet p i) (hj : u.proj ∈ (nativeTriv V j).baseSet) :
    (nativeTriv V j (frameCoreToNative s hne F u)).2 =
      ((Core.data F).core.localTriv i u).2 * coefficient s j (Core.lift p i u.proj) := by
  have hmap : frameCoreToNative s hne F u =
      coverScalarMap s (Core.lift p i u.proj, ((Core.data F).core.localTriv i u).2) := by
    rw [frameCoreToNative_eq_quotient s hne F hrel]
    change frameQuotientMap F s hrel (Core.toAssociated F u) = _
    rw [Core.toAssociated_localTriv F i u hi, frameQuotientMap_associatedMap]
  rw [hmap]
  exact congrArg Prod.snd (coverScalarMap_localTriv s j _ (by
    rw [Core.lift_project p i hi]
    exact hj))

theorem frameNativeToCore_localTriv (i j : p.Torus) (v : TotalSpace ℂ V)
    (hi : v.proj ∈ Core.baseSet p i) (hj : v.proj ∈ (nativeTriv V j).baseSet) :
    ((Core.data F).core.localTriv i (frameNativeToCore s hne F v)).2 =
      (nativeTriv V j v).2 / coefficient s j (Core.lift p i v.proj) := by
  have hc : coefficient s j (Core.lift p i v.proj) ≠ 0 :=
    coefficient_ne_zero s hne j _ (by rw [Core.lift_project p i hi]; exact hj)
  apply (eq_div_iff hc).mpr
  have h := frameCoreToNative_localTriv s hne F hrel i j
    (frameNativeToCore s hne F v) hi hj
  simpa only [frameCoreToNative_frameNativeToCore, frameNativeToCore_proj] using h.symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
