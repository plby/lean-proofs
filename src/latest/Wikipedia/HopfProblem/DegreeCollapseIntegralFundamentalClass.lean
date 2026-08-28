import Wikipedia.HopfProblem.DegreeCollapseIntegralNormalizedClass
import Wikipedia.HopfProblem.DegreeCollapseIntegralTopClassLift

/-!
# A constructed integral fundamental class for compact simply connected smooth manifolds

The actual top-class lift has nonzero localizations. Marking-independent
normalization and the proved compact assembly theorem turn it into an
original integral class whose localization generates every original top
local homology group. No orientation, fundamental class, or integral
duality hypothesis is supplied. The original support projections retain
this class on every compact support.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

/-- A fundamental class is an original integral top class with primitive original localizations. -/
def IsFundamental (d : ℕ) (a : SingularHomology M d) : Prop :=
  ∀ (x : M) (c : Homology (ModuleCat.of ℤ ℤ) {x} d),
    ∃ k : ℤ, k • fromAbsolute (ModuleCat.of ℤ ℤ) {x} d a = c

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

include E in
/-- The actual integral fundamental class exists without an orientation or duality premise. -/
theorem exists_fundamentalClass : ∃ b : SingularHomology M (n + 3), IsFundamental (n + 3) b := by
  obtain ⟨a, _, ha⟩ := IntegralTopClassLift.exists_integral_class_nonzero_localizations (E := E) n M
  refine ⟨IntegralLocalNormalization.absoluteClass (E := E) (n + 1) a, ?_⟩
  exact IntegralLocalNormalization.absoluteClass_localize_generates (E := E) (n + 1) a ha

def fundamentalClass : SingularHomology M (n + 3) :=
  Classical.choose (exists_fundamentalClass (E := E) n M)

theorem fundamentalClass_isFundamental : IsFundamental (n + 3) (fundamentalClass (E := E) n M) :=
  Classical.choose_spec (exists_fundamentalClass (E := E) n M)

/-- Restrict the constructed original absolute class to the specified actual support. -/
def supportedClass (K : Set M) : Homology (ModuleCat.of ℤ ℤ) K (n + 3) :=
  fromAbsolute (ModuleCat.of ℤ ℤ) K (n + 3) (fundamentalClass (E := E) n M)

theorem supportedClass_evaluate (K : Set M) (x : M) (hx : x ∈ K) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 3) (supportedClass (E := E) n M K) =
      fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 3) (fundamentalClass (E := E) n M) :=
  IntegralLocalNormalization.evaluate_fromAbsolute K x hx (n + 3) (fundamentalClass (E := E) n M)

theorem supportedClass_restrict {K L : Set M} (hKL : K ⊆ L) :
    restrict (ModuleCat.of ℤ ℤ) hKL (n + 3) (supportedClass (E := E) n M L) =
      supportedClass (E := E) n M K :=
  LinearMap.congr_fun (restrict_fromAbsolute (ModuleCat.of ℤ ℤ) hKL (n + 3))
    (fundamentalClass (E := E) n M)

/-- Every supported localization is the same actual primitive generator. -/
theorem supportedClass_evaluate_generates (K : Set M) (x : M) (hx : x ∈ K)
    (c : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3)) :
    ∃ k : ℤ, k • evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 3)
      (supportedClass (E := E) n M K) = c := by
  obtain ⟨k, hk⟩ := fundamentalClass_isFundamental (E := E) n M x c
  exact ⟨k, (congrArg (fun z => k • z) (supportedClass_evaluate (E := E) n M K x hx)).trans hk⟩

/-- An actual original integral singular cycle represents the constructed class. -/
theorem exists_fundamental_cycle :
    ∃ c : ModuleHomology.Cycle (singularComplex M) (n + 3),
      ModuleHomology.cycleClass (singularComplex M) (n + 3) c = fundamentalClass (E := E) n M :=
  ModuleHomology.cycleClass_surjective (singularComplex M) (n + 3) (fundamentalClass (E := E) n M)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass
