import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassOperations

/-!
# Independence of the native first Chern class from a factor presentation

The class on a factor bundle was defined by the winding of the actual
native boundary section in a nonzero frame on each singular triangle.
Here two genuine analytic presentations of the same original native
bundle give the same class.  This is a well-definedness statement; no
existence of a factor presentation is assumed or asserted in this file.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open SingularCohomologyFree

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} {V W : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W]

/-- Actual presentations of the same native bundle have identical winding classes. -/
theorem firstChernClass_eq_of_presentations {F G : FactorOfAutomorphy p}
    (e : AnalyticBundleIso IC (Core.data F).core.Fiber V)
    (f : AnalyticBundleIso IC (Core.data G).core.Fiber V) :
    Chern.firstChernClass F = Chern.firstChernClass G :=
  Chern.firstChernClass_bundleIso (e.trans f.symm)

/-- A winding class is attached to the original bundle through an actual
analytic fibre-linear presentation, not through an assigned period form. -/
def IsFirstChernClass (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] (a : SingularCohomology p.Torus 2) : Prop :=
  ∃ F : FactorOfAutomorphy p,
    Nonempty (AnalyticBundleIso IC (Core.data F).core.Fiber V) ∧
      Chern.firstChernClass F = a

/-- This condition determines at most one genuine singular cohomology class. -/
theorem IsFirstChernClass.unique {a b : SingularCohomology p.Torus 2}
    (ha : IsFirstChernClass V a) (hb : IsFirstChernClass V b) : a = b := by
  obtain ⟨F, ⟨e⟩, rfl⟩ := ha
  obtain ⟨G, ⟨f⟩, rfl⟩ := hb
  exact firstChernClass_eq_of_presentations e f

/-- Genuine native analytic isomorphisms transport the same winding-defined class. -/
theorem IsFirstChernClass.map {a : SingularCohomology p.Torus 2}
    (ha : IsFirstChernClass V a) (e : AnalyticBundleIso IC V W) :
    IsFirstChernClass W a := by
  obtain ⟨F, ⟨f⟩, hF⟩ := ha
  exact ⟨F, ⟨f.trans e⟩, hF⟩

theorem isFirstChernClass_iff_of_bundleIso (e : AnalyticBundleIso IC V W)
    (a : SingularCohomology p.Torus 2) :
    IsFirstChernClass V a ↔ IsFirstChernClass W a :=
  ⟨fun h => h.map e, fun h => h.map e.symm⟩

/-- The original native factor bundle has its already constructed actual class. -/
theorem isFirstChernClass_factor (F : FactorOfAutomorphy p) :
    IsFirstChernClass (Core.data F).core.Fiber (Chern.firstChernClass F) :=
  ⟨F, ⟨AnalyticBundleIso.refl _⟩, rfl⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
