import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapChains
import Wikipedia.NoExoticSixSphere.SmallCoefficientChainRange

/-!
# Actual subspace support of original integral cap chains

Original integral cap naturality preserves a subspace-chain image.
Vanishing of the cochain restriction annihilates that subspace's
chains. Consequently cap on a genuine sum of chains in two subspaces
lands in the first subspace when the cochain vanishes on the second.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyCup NoExoticSixSphere

abbrev Coefficient := ModuleCat.of ℤ ℤ

variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem capInDegree_mem_inclusion_range {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (c : Chains X n)
    (hc : c ∈ LinearMap.range (inducedChain (subtypeInclusion U) n)) :
    capInDegree h α c ∈
      LinearMap.range (inducedChain (subtypeInclusion U) q) := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨capInDegree h (pullback (subtypeInclusion U) p α) b,
    naturality h (subtypeInclusion U) α b⟩

theorem capInDegree_eq_zero_of_pullback_zero {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : pullback (subtypeInclusion V) p α = 0) (c : Chains X n)
    (hc : c ∈ LinearMap.range (inducedChain (subtypeInclusion V) n)) :
    capInDegree h α c = 0 := by
  obtain ⟨b, rfl⟩ := hc
  have he := naturality h (subtypeInclusion V) α b
  rw [hα, capInDegree_zero, LinearMap.zero_apply, map_zero] at he
  exact he.symm

theorem capInDegree_mem_range_of_mem_sup {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : pullback (subtypeInclusion V) p α = 0) (c : Chains X n)
    (hc : c ∈ LinearMap.range (inducedChain (subtypeInclusion U) n) ⊔
      LinearMap.range (inducedChain (subtypeInclusion V) n)) :
    capInDegree h α c ∈
      LinearMap.range (inducedChain (subtypeInclusion U) q) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, capInDegree_eq_zero_of_pullback_zero V h α hα b hb, add_zero]
  exact capInDegree_mem_inclusion_range U h α a ha

/-- An actual relative integral cochain supplies the vanishing needed for localization. -/
theorem relative_capInDegree_mem_range {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cochain V p) (c : Chains X n)
    (hc : c ∈ LinearMap.range (inducedChain (subtypeInclusion U) n) ⊔
      LinearMap.range (inducedChain (subtypeInclusion V) n)) :
    capInDegree h (RelativeIntegralCap.toAbsolute V p α) c ∈
      LinearMap.range (inducedChain (subtypeInclusion U) q) :=
  capInDegree_mem_range_of_mem_sup U V h (RelativeIntegralCap.toAbsolute V p α)
    (RelativeIntegralCap.pullback_toAbsolute V p α) c hc

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCap
