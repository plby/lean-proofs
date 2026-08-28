import Wikipedia.NoExoticSixSphere.RelativeModTwoCapChains

/-!
# Actual subspace support of the original mod-two cap chain

The original cap naturality formula preserves the image of a subspace
chain inclusion. A cochain restricting to zero on a second subspace
annihilates its chains. Thus capping a sum of chains from those two
subspaces lands in the first original subspace chain group.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Capping preserves the actual chain image of the specified subspace. -/
theorem capInDegree_mem_inclusion_range {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (c : ModTwoChains.Chains X n)
    (hc : c ∈ LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f n).hom) :
    capInDegree h α c ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f q).hom := by
  subst n
  obtain ⟨b, rfl⟩ := hc
  exact ⟨cap (q := q) (pullback (subtypeInclusion U) p α) b,
    spaceMap_cap (subtypeInclusion U) p q α b⟩

/-- Actual subspace chains cap to zero when the original cochain restriction is zero. -/
theorem capInDegree_eq_zero_of_pullback_zero {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : pullback (subtypeInclusion V) p α = 0) (c : ModTwoChains.Chains X n)
    (hc : c ∈ LinearMap.range ((RelativeCoefficients.inclusion Coefficient V).f n).hom) :
    capInDegree h α c = 0 := by
  subst n
  obtain ⟨b, rfl⟩ := hc
  have he := spaceMap_cap (subtypeInclusion V) p q α b
  rw [hα] at he
  exact he.symm.trans (by rw [cap, capInDegree_zero, LinearMap.zero_apply, map_zero])

/-- On an actual two-subspace chain sum, vanishing on one piece localizes cap to the other. -/
theorem capInDegree_mem_range_of_mem_sup {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : pullback (subtypeInclusion V) p α = 0) (c : ModTwoChains.Chains X n)
    (hc : c ∈ LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f n).hom ⊔
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient V).f n).hom) :
    capInDegree h α c ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f q).hom := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, capInDegree_eq_zero_of_pullback_zero V h α hα b hb, add_zero]
  exact capInDegree_mem_inclusion_range U h α a ha

/-- The original relative cochain supplies the needed vanishing without an extra hypothesis. -/
theorem relative_capInDegree_mem_range {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : ModTwoChains.Chains X n)
    (hc : c ∈ LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f n).hom ⊔
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient V).f n).hom) :
    capInDegree h (RelativeModTwoCochains.toAbsolute V p α) c ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient U).f q).hom :=
  capInDegree_mem_range_of_mem_sup U V h (RelativeModTwoCochains.toAbsolute V p α)
    (RelativeModTwoCochains.pullback_toAbsolute V p α) c hc

end NoExoticSixSphere.ModTwoCapProduct
