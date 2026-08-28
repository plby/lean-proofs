import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralFundamentalClass

/-!
# The constructed integral compact-support cap map

An actual compatible family of supported integral homology classes gives
a cap map on the original compact-support direct limit. For compact
simply connected smooth manifolds, the proved primitive fundamental class
constructs this family without an orientation or duality premise.
Neither bijectivity nor a Poincare--Lefschetz theorem is asserted here.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap

open FirstHurewicz NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X]

/-- Cap with the specified actual class, on its original support. -/
def componentMap (K : Set X) {p q d : ℕ} (h : p + q = d)
    (c : Homology (ModuleCat.of ℤ ℤ) K d) :
    IntegralSupportedCohomology.Cohomology K p →ₗ[ℤ] (singularComplex X).homology q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun a => RelativeIntegralCap.capProductInDegree Kᶜ h a c
      map_zero' := congrArg (fun f => f c) (RelativeIntegralCap.capProductInDegree Kᶜ h).map_zero
      map_add' a b := congrArg (fun f => f c)
        ((RelativeIntegralCap.capProductInDegree Kᶜ h).map_add a b) }

theorem componentMap_extend {K L : Set X} (hKL : K ⊆ L) {p q d : ℕ} (h : p + q = d)
    (c : Homology (ModuleCat.of ℤ ℤ) L d) (a : IntegralSupportedCohomology.Cohomology K p) :
    componentMap L h c (IntegralSupportedCohomology.extend hKL p a) =
      componentMap K h (restrict (ModuleCat.of ℤ ℤ) hKL d c) a :=
  IntegralSupportedCohomology.cap_extend hKL h a c

/-- Compatible original classes define a map on the actual compact-support quotient. -/
def withClasses {p q d : ℕ} (h : p + q = d)
    (c : ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) d)
    (hc : ∀ (K L : Compacts X) (hKL : K ≤ L), restrict (ModuleCat.of ℤ ℤ) hKL d (c L) = c K) :
    Cohomology X p →ₗ[ℤ] (singularComplex X).homology q :=
  lift X p (fun K => componentMap (K : Set X) h (c K)) (by
    intro K L hKL a
    exact (componentMap_extend hKL h (c L) a).trans
      (congrArg (fun z => componentMap (K : Set X) h z a) (hc K L hKL)))

theorem withClasses_of {p q d : ℕ} (h : p + q = d)
    (c : ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) d)
    (hc : ∀ (K L : Compacts X) (hKL : K ≤ L), restrict (ModuleCat.of ℤ ℤ) hKL d (c L) = c K)
    (K : Compacts X) (a : Component X p K) :
    withClasses h c hc (of X p K a) = componentMap (K : Set X) h (c K) a := rfl

/-- On compact spaces the actual whole-space component computes the cap map. -/
theorem withClasses_eq_top [CompactSpace X] {p q d : ℕ} (h : p + q = d)
    (c : ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) d)
    (hc : ∀ (K L : Compacts X) (hKL : K ≤ L), restrict (ModuleCat.of ℤ ℤ) hKL d (c L) = c K)
    (a : Cohomology X p) :
    withClasses h c hc a = componentMap Set.univ h (c ⊤) (topEquiv X p a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  rw [withClasses_of]
  change componentMap (K : Set X) h (c K) b =
    componentMap Set.univ h (c ⊤) (IntegralSupportedCohomology.extend (le_top : K ≤ ⊤) p b)
  exact ((componentMap_extend (le_top : K ≤ ⊤) h (c ⊤) b).trans
    (congrArg (fun z => componentMap (K : Set X) h z b) (hc K ⊤ le_top))).symm

section Manifold

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- Cap with the constructed primitive integral class; no orientation or duality input. -/
def dualityMap (p q : ℕ) (h : p + q = n + 3) :
    Cohomology M p →ₗ[ℤ] (singularComplex M).homology q :=
  withClasses h (fun K => IntegralManifoldFundamentalClass.supportedClass (E := E) n M K)
    (fun _K _L hKL => IntegralManifoldFundamentalClass.supportedClass_restrict (E := E) n M hKL)

/-- The actual capped relative representative is the value on its direct-limit class. -/
theorem dualityMap_of (p q : ℕ) (h : p + q = n + 3) (K : Compacts M) (a : Component M p K) :
    dualityMap (E := E) n M p q h (of M p K a) =
      RelativeIntegralCap.capProductInDegree ((K : Set M)ᶜ) h a
        (IntegralManifoldFundamentalClass.supportedClass (E := E) n M K) := rfl

/-- On compact manifolds, use the original equivalence to absolute integral cohomology. -/
def absoluteDualityMap (p q : ℕ) (h : p + q = n + 3) :
    SingularCohomologyFree.SingularCohomology M p →ₗ[ℤ] (singularComplex M).homology q :=
  (dualityMap (E := E) n M p q h).comp (absoluteEquiv M p).symm.toLinearMap

theorem absoluteDualityMap_forget (p q : ℕ) (h : p + q = n + 3)
    (K : Compacts M) (a : Component M p K) :
    absoluteDualityMap (E := E) n M p q h (IntegralSupportedCohomology.toAbsolute (K : Set M) p a) =
      RelativeIntegralCap.capProductInDegree ((K : Set M)ᶜ) h a
        (IntegralManifoldFundamentalClass.supportedClass (E := E) n M K) := by
  rw [← absoluteEquiv_of M p K a]
  change dualityMap (E := E) n M p q h
    ((absoluteEquiv M p).symm (absoluteEquiv M p (of M p K a))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact dualityMap_of (E := E) n M p q h K a

end Manifold

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap
