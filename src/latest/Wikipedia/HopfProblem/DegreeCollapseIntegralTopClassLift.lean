import Wikipedia.HopfProblem.DegreeCollapseCompactHomologyFinite
import Wikipedia.NoExoticSixSphere.CompactManifoldCapDuality
import Wikipedia.NoExoticSixSphere.SingularModTwoEvaluation
import Wikipedia.NoExoticSixSphere.CoefficientHomologyZero
import Wikipedia.HopfProblem.FirstHurewiczEquivalence
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# An actual integral lift of the mod-two top class

For a compact simply connected smooth manifold of dimension at least
three, mod-two duality kills homology one degree below the top. On that
finitely generated integral group, the coefficient sequence makes
multiplication by two surjective, hence injective by the Noetherian
endomorphism theorem. The actual top Bockstein is therefore zero and
the constructed mod-two fundamental class lifts to original integral
homology. Integral duality and a primitive integral orientation class
are not assumed or concluded.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTopClassLift

open SingularMayerVietoris SphereHomologyCoefficients NoExoticSixSphere

theorem reduction_surjective_next_of_mod_vanishing (p : ℕ) (hp : p ≠ 0)
    (X : Type) [TopologicalSpace X] (n : ℕ)
    [Module.Finite ℤ (SingularHomology X n)] [Subsingleton (ModHomology p X n)] :
    Function.Surjective (reductionHomologyMap p X (n + 1)) := by
  let f : SingularHomology X n →ₗ[ℤ] SingularHomology X n := (p : ℤ) • LinearMap.id
  have hsur : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    change scalarImage p (SingularHomology X n) = ⊤
    rw [scalarImage_eq_reduction_ker p hp X n]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  have hinj := IsNoetherian.injective_of_surjective_endomorphism f hsur
  apply LinearMap.range_eq_top.mp
  rw [reductionHomologyMap_range_succ p hp X n,
    bockstein_eq_zero_of_injective p hp X n hinj, LinearMap.ker_zero]

theorem first_homology_subsingleton (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X] :
    Subsingleton (SingularHomology X 1) := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hs : Subsingleton (Multiplicative (FirstHurewicz.SingularH1 X)) :=
    (FirstHurewicz.hurewiczPi1_surjective x).subsingleton
  exact ⟨fun a b => congrArg Multiplicative.toAdd
    (hs.elim (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))⟩

theorem first_cohomology_subsingleton (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    [Subsingleton (SingularHomology X 1)] : Subsingleton (ModTwoCapProduct.Cohomology X 1) := by
  let : Module.Free ℤ (SingularHomology X 0) :=
    Module.Free.of_equiv (CoefficientChains.connectedZeroEquiv (ModuleCat.of ℤ ℤ) X).symm
  let : Module.Projective ℤ (SingularHomology X 0) := inferInstance
  exact (SingularModTwoEvaluation.evaluation_succ_injective X 0).subsingleton

theorem local_reduction_commute (p : ℕ) (X : Type) [TopologicalSpace X] (x : X) (k : ℕ)
    (a : SingularHomology X k) :
    RelativeCoefficients.reductionMap p ({x}ᶜ : Set X) k
        (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) {x} k a) =
      SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ (ZMod p)) {x} k
        (reductionHomologyMap p X k a) := by
  have he := (homologyLinearMap_comp
    (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) ({x}ᶜ : Set X))
    (RelativeCoefficients.change (reductionCoefficient p) ({x}ᶜ : Set X)) k).symm.trans
      ((congrArg (fun f => homologyLinearMap f k)
        (RelativeCoefficients.projection_change (reductionCoefficient p) ({x}ᶜ : Set X))).trans
          (homologyLinearMap_comp (coefficientComplexMap (reductionCoefficient p) X)
            (RelativeCoefficients.projection (ModuleCat.of ℤ (ZMod p)) ({x}ᶜ : Set X)) k))
  exact LinearMap.congr_fun he a

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
include E in
theorem modTwo_codimensionOne_subsingleton : Subsingleton (ModHomology 2 M (n + 2)) := by
  let := first_homology_subsingleton M
  let := first_cohomology_subsingleton M
  exact (ManifoldCapMap.dualityEquiv (E := E) n M 1 (n + 2) (by omega)).symm.injective.subsingleton

include E in
theorem top_reduction_surjective : Function.Surjective (reductionHomologyMap 2 M (n + 3)) := by
  let := modTwo_codimensionOne_subsingleton (E := E) n M
  let := MorseFiniteness.compactManifold_higherHomology_finite E M (n + 1) (Nat.succ_ne_zero n)
  exact reduction_surjective_next_of_mod_vanishing 2 (by decide) M (n + 2)

include E in
/-- A nonzero original integral class is constructed, with its actual mod-two reduction fixed. -/
theorem exists_integral_lift_fundamentalClass :
    ∃ a : SingularHomology M (n + 3),
      reductionHomologyMap 2 M (n + 3) a = ManifoldFundamentalClass.fundamentalClass (E := E) n M ∧
        a ≠ 0 := by
  obtain ⟨a, ha⟩ := top_reduction_surjective (E := E) n M
    (ManifoldFundamentalClass.fundamentalClass (E := E) n M)
  refine ⟨a, ha, ?_⟩
  intro hz
  rw [hz, map_zero] at ha
  exact ManifoldFundamentalClass.fundamentalClass_ne_zero (E := E) n M ha.symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M] in
include E in
theorem localization_ne_zero_of_lift (a : SingularHomology M (n + 3))
    (ha : reductionHomologyMap 2 M (n + 3) a =
      ManifoldFundamentalClass.fundamentalClass (E := E) n M) (x : M) :
    SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 3) a ≠ 0 := by
  intro hz
  have he := local_reduction_commute 2 M x (n + 3) a
  let r : SupportedRelativeHomology.Homology (ModuleCat.of ℤ ℤ) {x} (n + 3) →ₗ[ℤ]
      RelativeCoefficients.ModHomology 2 ({x}ᶜ : Set M) (n + 3) :=
    RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set M) (n + 3)
  have hr := (congrArg r hz).trans r.map_zero
  have hf := (congrArg
    (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ (ZMod 2)) {x} (n + 3)) ha).symm.trans
      (he.symm.trans hr)
  exact ModTwoLocalClass.manifoldClass_ne_zero (E := E) n x
    ((ManifoldFundamentalClass.localize_fundamentalClass (E := E) n M x).symm.trans hf)

include E in
/-- The constructed lift has a nonzero actual integral localization at every point. -/
theorem exists_integral_class_nonzero_localizations :
    ∃ a : SingularHomology M (n + 3),
      reductionHomologyMap 2 M (n + 3) a = ManifoldFundamentalClass.fundamentalClass (E := E) n M ∧
        ∀ x : M, SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 3) a ≠ 0 := by
  obtain ⟨a, ha, _⟩ := exists_integral_lift_fundamentalClass (E := E) n M
  exact ⟨a, ha, localization_ne_zero_of_lift (E := E) n M a ha⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTopClassLift
