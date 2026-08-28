import Wikipedia.NoExoticSixSphere.RelativeSingularHomology
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Endpoint and prism operators preserve the actual subspace chains

The actual singular-chain image of a map taking values in the subspace
is supported there. Apply this to each subspace-preserving simplex
homotopy, then extend from singular generators by linearity. Both the
endpoint operator and the genuine prism operator preserve support.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexHomotopyChainSupport

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (U : Set X)

theorem inducedChain_mem (f : C(Z, X)) (hf : ∀ z, f z ∈ U) (n : ℕ) (c : Chains Z n) :
    inducedChain f n c ∈ supportedChainSubmodule U n := by
  let g : C(Z, U) := ⟨fun z ↦ ⟨f z, hf z⟩, f.continuous.subtype_mk _⟩
  have he : f = (subtypeInclusion U).comp g := rfl
  rw [he, inducedChain_comp]
  apply (subtypeInclusion_chain_range U n).le
  exact ⟨inducedChain g n c, rfl⟩

theorem simplexPrism_mem (n : ℕ) (H : C(I × Simplex n, X)) (hH : ∀ p, H p ∈ U) :
    simplexPrism n H ∈ supportedChainSubmodule U (n + 1) := by
  change inducedChain H (n + 1) _ ∈ supportedChainSubmodule U (n + 1)
  exact inducedChain_mem U H hH (n + 1) _

theorem endpoint_mem (n : ℕ) (H : C(Simplex n, X) → C(I × Simplex n, X))
    (hH : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, H smp p ∈ U)
    (t : I) (c : Chains X n) (hc : c ∈ supportedChainSubmodule U n) :
    simplexEndpointOperator n H t c ∈ supportedChainSubmodule U n := by
  have hle : supportedChainSubmodule U n ≤
      (supportedChainSubmodule U n).comap (simplexEndpointOperator n H t) := by
    rw [supportedChainSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨smp, hs, rfl⟩
    change simplexEndpointOperator n H t (simplexChain X n smp) ∈ supportedChainSubmodule U n
    rw [simplexEndpointOperator_simplex]
    apply simplexChain_mem_supported
    rintro _ ⟨s, rfl⟩
    exact hH smp (fun z ↦ hs ⟨z, rfl⟩) (t, s)
  exact hle hc

theorem prism_mem (n : ℕ) (H : C(Simplex n, X) → C(I × Simplex n, X))
    (hH : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, H smp p ∈ U)
    (c : Chains X n) (hc : c ∈ supportedChainSubmodule U n) :
    simplexPrismOperator n H c ∈ supportedChainSubmodule U (n + 1) := by
  have hle : supportedChainSubmodule U n ≤
      (supportedChainSubmodule U (n + 1)).comap (simplexPrismOperator n H) := by
    rw [supportedChainSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨smp, hs, rfl⟩
    change simplexPrismOperator n H (simplexChain X n smp) ∈ supportedChainSubmodule U (n + 1)
    rw [simplexPrismOperator_simplex]
    exact simplexPrism_mem U n (H smp) (hH smp (fun z ↦ hs ⟨z, rfl⟩))
  exact hle hc

end NoExoticSixSphere.SimplexHomotopyChainSupport
