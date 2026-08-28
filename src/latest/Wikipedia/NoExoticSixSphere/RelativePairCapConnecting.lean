import Wikipedia.NoExoticSixSphere.RelativePairCapConnectingRepresentatives
import Wikipedia.NoExoticSixSphere.RelativeCoefficientConnecting
import Wikipedia.NoExoticSixSphere.RelativeModTwoPairConnectingCochains
import Wikipedia.NoExoticSixSphere.ModTwoCapDegree

/-!
# Cap compatibility for the two original connecting maps of a pair

The actual cochain and chain connecting lifts reduce the square to the
proved cap boundary primitive. All inputs are arbitrary classes in the
original homology and cohomology groups; no manifold hypothesis or
fundamental-class compatibility is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem pair_connecting_cap (p q : ℕ) (a : ModTwoCapProduct.Cohomology U p)
    (F : (RelativeCoefficients.complex Coefficient U).homology (p + q + 1)) :
    capProductInDegree U (p := p + 1) (q := q) (n := p + q + 1) (by omega)
        (RelativeModTwoCochains.connecting U p a) F =
      modHomologyMap 2 (subtypeInclusion U) q
        (ModTwoCapProduct.capProduct U p q a
          (RelativeCoefficients.connecting Coefficient U (p + q) F)) := by
  obtain ⟨α, rfl⟩ :=
    SingularCohomologyFree.cocycleClass_surjective (ModTwoCapProduct.cochainComplex U) p a
  obtain ⟨z, rfl⟩ :=
    ModuleHomology.cycleClass_surjective (RelativeCoefficients.complex Coefficient U) (p + q + 1) F
  obtain ⟨β, γ, hβ, hγ, hδ⟩ := RelativeModTwoCochains.exists_pair_connecting_cochains U p α
  obtain ⟨c, hc, w, hw, hboundary⟩ :=
    RelativeCoefficients.exists_connecting_lift Coefficient U (p + q) z
  rw [hδ, capProductInDegree_cocycle_cycle, hboundary, ModTwoCapProduct.capProduct_cocycle_cycle,
    ModTwoCapProduct.modHomologyMap_cycleClass]
  exact pair_connecting_cap_representatives U p q α β γ hβ hγ z c hc w hw

theorem pair_connecting_capInDegree {p q n : ℕ} (h : p + q = n)
    (a : ModTwoCapProduct.Cohomology U p)
    (F : (RelativeCoefficients.complex Coefficient U).homology (n + 1)) :
    capProductInDegree U (p := p + 1) (q := q) (n := n + 1) (by omega)
        (RelativeModTwoCochains.connecting U p a) F =
      modHomologyMap 2 (subtypeInclusion U) q
        (ModTwoCapProduct.capProductInDegree U h a
          (RelativeCoefficients.connecting Coefficient U n F)) := by
  subst n
  exact pair_connecting_cap U p q a F

theorem pair_connecting_cap_kernel {p q n : ℕ} (h : p + q = n)
    (a : ModTwoCapProduct.Cohomology U p)
    (F : (RelativeCoefficients.complex Coefficient U).homology (n + 1))
    (hi : Function.Injective (fun b : RelativeModTwoCochains.Cohomology U (p + 1) ↦
      capProductInDegree U (p := p + 1) (q := q) (n := n + 1) (by omega) b F)) :
    modHomologyMap 2 (subtypeInclusion U) q
        (ModTwoCapProduct.capProductInDegree U h a
          (RelativeCoefficients.connecting Coefficient U n F)) = 0 ↔
      ∃ b : ModTwoCapProduct.Cohomology X p,
        ModTwoCapProduct.cohomologyPullback (subtypeInclusion U) p b = a := by
  rw [← pair_connecting_capInDegree U h a F]
  have hz : capProductInDegree U (p := p + 1) (q := q) (n := n + 1) (by omega) 0 F = 0 :=
    congrArg (fun f ↦ f F)
      (capProductInDegree U (p := p + 1) (q := q) (n := n + 1) (by omega)).map_zero
  constructor
  · intro ha
    have hδ : a ∈ LinearMap.ker (RelativeModTwoCochains.connecting U p) :=
      hi (ha.trans hz.symm)
    rw [← RelativeModTwoCochains.exact_at_subspace] at hδ
    exact hδ
  · intro ha
    have hδ : a ∈ LinearMap.range
        (ModTwoCapProduct.cohomologyPullback (subtypeInclusion U) p) := ha
    rw [RelativeModTwoCochains.exact_at_subspace] at hδ
    change RelativeModTwoCochains.connecting U p a = 0 at hδ
    rw [hδ]
    exact hz

end NoExoticSixSphere.RelativeModTwoCap
