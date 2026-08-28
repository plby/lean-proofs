import Wikipedia.HopfProblem.SingularMayerVietorisSubdivision
import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionHomotopy
import Wikipedia.HopfProblem.SingularMayerVietorisRealizationSupport
import Wikipedia.HopfProblem.SingularMayerVietorisMeshSubdivision

/-!
# Actual singular subdivision eventually lies in the small-chain subcomplex

Subdivision preserves the carrier of every singular simplex. Compactness
and the proved geometric mesh bound give a uniform subdivision stage for
the finite support of any actual singular chain. No excision or homology
equivalence is assumed in this chain-level result.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- Actual barycentric subdivision preserves chains carried by one subset. -/
theorem subdivision_mem_supported (U : Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ supportedChainSubmodule U n) :
    subdivision X k n c ∈ supportedChainSubmodule U n := by
  apply singularLinearMap_mem_of_supported U n (subdivision X k n)
    (supportedChainSubmodule U n) c hc
  intro σ hσ
  rw [subdivision_simplex]
  exact realizedChain_mem_supported U n n σ hσ _

/-- Once a chain is small, every actual subdivision remains small. -/
theorem subdivision_mem_small (U V : Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) : subdivision X k n c ∈ smallChainSubmodule U V n := by
  apply singularLinearMap_mem_of_small U V n (subdivision X k n)
    (smallChainSubmodule U V n) c hc
  intro σ hσ
  rw [subdivision_simplex]
  exact realizedChain_mem_small U V n n σ hσ _

/-- The explicit actual subdivision homotopy stays in the carrier of a
supported chain, one degree higher. -/
theorem subdivisionHomotopy_mem_supported (U : Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ supportedChainSubmodule U n) :
    subdivisionHomotopy X k n c ∈ supportedChainSubmodule U (n + 1) := by
  apply singularLinearMap_mem_of_supported U n (subdivisionHomotopy X k n)
    (supportedChainSubmodule U (n + 1)) c hc
  intro σ hσ
  rw [subdivisionHomotopy_simplex]
  exact realizedChain_mem_supported U n (n + 1) σ hσ _

/-- The actual homotopy between a small chain and its subdivision is itself
small. This supplies the boundary-lifting half of the small-chain theorem. -/
theorem subdivisionHomotopy_mem_small (U V : Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    subdivisionHomotopy X k n c ∈ smallChainSubmodule U V (n + 1) := by
  apply singularLinearMap_mem_of_small U V n (subdivisionHomotopy X k n)
    (smallChainSubmodule U V (n + 1)) c hc
  intro σ hσ
  rw [subdivisionHomotopy_simplex]
  exact realizedChain_mem_small U V n (n + 1) σ hσ _

/-- The actual chain of any one singular simplex eventually subdivides
into simplices lying in members of the given open cover of its image. -/
theorem eventually_subdivision_simplex_mem_small (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) (σ : SingularSimplex X n)
    (hcover : range σ ⊆ U ∪ V) :
    ∃ N : ℕ, ∀ k ≥ N, subdivision X k n (simplexChain X n σ) ∈ smallChainSubmodule U V n := by
  obtain ⟨N, hN⟩ := simplex_formalSubdivision_eventually_small σ hU hV hcover
  refine ⟨N, ?_⟩
  intro k hk
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U V n n σ
  intro v hv
  exact hN k hk (formalSimplex (stdVertices n)) v hv

/-- A uniform stage works for every coefficient of an actual finite
singular chain. This is the chain-level smallness theorem used in excision. -/
theorem eventually_subdivision_mem_small (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (n : ℕ) (c : Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N, subdivision X k n c ∈ smallChainSubmodule U V n := by
  classical
  have hc : ∀ σ ∈ (chainsEquivFinsupp X n c).support, range σ ⊆ U ∪ V := by
    intro σ hσ
    rw [hcover]
    exact subset_univ _
  obtain ⟨N, hN⟩ := finite_family_formalSubdivision_eventually_small
    (chainsEquivFinsupp X n c).support hU hV hc
  refine ⟨N, ?_⟩
  intro k hk
  apply singularLinearMap_mem_of_support n (subdivision X k n) (smallChainSubmodule U V n) c
  intro σ hσ
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U V n n σ
  intro v hv
  exact hN k hk σ hσ (formalSimplex (stdVertices n)) v hv

end Wikipedia.HopfProblem.SingularMayerVietoris
