import Wikipedia.NoExoticSixSphere.RelativeModTwoCochains
import Wikipedia.NoExoticSixSphere.ModTwoCapChainNaturality
import Wikipedia.NoExoticSixSphere.ModTwoCapCochainExact

/-!
# Capping the actual relative chain quotient

A relative cochain annihilates subspace chains. Naturality of the
original cap operation therefore makes it factor through the actual
relative mod-two chain group, with values in absolute mod-two chains.
The differential formula is inherited from the original cap formula.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Capping with a relative cochain annihilates the actual subspace chains. -/
theorem capInDegree_inclusion_zero {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain U p) (c : ModTwoChains.Chains U n) :
    ModTwoCapProduct.capInDegree h (RelativeModTwoCochains.toAbsolute U p α)
      (((RelativeCoefficients.inclusion Coefficient U).f n).hom c) = 0 := by
  subst n
  have he := spaceMap_cap (subtypeInclusion U) p q
    (RelativeModTwoCochains.toAbsolute U p α) c
  rw [RelativeModTwoCochains.pullback_toAbsolute] at he
  change _ = ModTwoCapProduct.capInDegree rfl
    (RelativeModTwoCochains.toAbsolute U p α) _ at he
  simpa only [cap, capInDegree_zero, LinearMap.zero_apply, map_zero] using he.symm

/-- The original relative quotient kernel is killed by the original cap operation. -/
theorem quotient_ker_le_cap_ker {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain U p) :
    LinearMap.ker (RelativeCoefficients.quotientMap Coefficient U n) ≤
      LinearMap.ker (ModTwoCapProduct.capInDegree h
        (RelativeModTwoCochains.toAbsolute U p α)) := by
  intro c hc
  obtain ⟨d, rfl⟩ :=
    (RelativeCoefficients.quotientMap_eq_zero_iff Coefficient U n c).mp hc
  exact capInDegree_inclusion_zero U h α d

/-- The original cap operation factored through the genuine relative chain group. -/
def capInDegree {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain U p) :
    (RelativeCoefficients.complex Coefficient U).X n →ₗ[ℤ] ModTwoChains.Chains X q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((RelativeCoefficients.quotientMap Coefficient U n).toAddMonoidHom.liftOfSurjective
      (RelativeCoefficients.quotientMap_surjective Coefficient U n)
      ⟨(ModTwoCapProduct.capInDegree h
          (RelativeModTwoCochains.toAbsolute U p α)).toAddMonoidHom,
        fun _ hc => quotient_ker_le_cap_ker U h α hc⟩)

/-- Every ambient representative gives its original front/back cap chain. -/
theorem capInDegree_quotientMap {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain U p) (c : ModTwoChains.Chains X n) :
    capInDegree U h α (RelativeCoefficients.quotientMap Coefficient U n c) =
      ModTwoCapProduct.capInDegree h (RelativeModTwoCochains.toAbsolute U p α) c := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply
    (RelativeCoefficients.quotientMap Coefficient U n).toAddMonoidHom
    (Function.surjInv (RelativeCoefficients.quotientMap_surjective Coefficient U n))
    (Function.rightInverse_surjInv
      (RelativeCoefficients.quotientMap_surjective Coefficient U n))
    ⟨(ModTwoCapProduct.capInDegree h
        (RelativeModTwoCochains.toAbsolute U p α)).toAddMonoidHom,
      fun _ hc => quotient_ker_le_cap_ker U h α hc⟩ c

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U h (0 : RelativeModTwoCochains.Cochain U p) = 0 := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := RelativeCoefficients.quotientMap_surjective Coefficient U n c
  rw [capInDegree_quotientMap, map_zero, ModTwoCapProduct.capInDegree_zero]
  rfl

theorem capInDegree_add {p q n : ℕ} (h : p + q = n)
    (α β : RelativeModTwoCochains.Cochain U p) :
    capInDegree U h (α + β) = capInDegree U h α + capInDegree U h β := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := RelativeCoefficients.quotientMap_surjective Coefficient U n c
  rw [LinearMap.add_apply, capInDegree_quotientMap,
    capInDegree_quotientMap, capInDegree_quotientMap, map_add,
    ModTwoCapProduct.capInDegree_add, LinearMap.add_apply]

/-- The original relative differential satisfies the same cap boundary formula. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n)
    (α : RelativeModTwoCochains.Cochain U p)
    (c : (RelativeCoefficients.complex Coefficient U).X n) :
    ((modComplex 2 X).d (q + 1) q).hom
        (capInDegree U (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree U (p := p) (q := q) rfl α
        (((RelativeCoefficients.complex Coefficient U).d n (p + q)).hom c) +
      capInDegree U (p := p + 1) (q := q) (n := n) (by omega)
        (RelativeModTwoCochains.coboundary U α) c := by
  obtain ⟨b, rfl⟩ := RelativeCoefficients.quotientMap_surjective Coefficient U n c
  rw [RelativeCoefficients.boundary_quotientMap, capInDegree_quotientMap,
    capInDegree_quotientMap, capInDegree_quotientMap,
    RelativeModTwoCochains.toAbsolute_coboundary]
  exact ModTwoCapProduct.boundary_capInDegree h
    (RelativeModTwoCochains.toAbsolute U p α) b

end NoExoticSixSphere.RelativeModTwoCap
