import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSubdivisionMesh
import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionSupport

/-!
# Actual subdivision becomes small for arbitrary open covers

Subdivision and its original chain homotopy preserve the carrier of each
simplex. Compact-simplex mesh contraction supplies one subdivision stage
for the finite simplex support of any original chain, even when the open
cover itself is infinite.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {ι : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Membership in an actual small-chain span is checked on its original
small simplex generators. -/
theorem singularLinearMap_mem_of_small (U : ι → Set X) (n : ℕ)
    (f : Chains X n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U n)
    (hf : ∀ σ : SingularSimplex X n, (∃ i, range σ ⊆ U i) →
      f (simplexChain X n σ) ∈ P) : f c ∈ P := by
  have h : smallChainSubmodule U n ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- Realizing a finite affine chain is small if each of its nonzero terms
is carried by a member of the family. -/
theorem realizedChain_mem_small_of_support (U : ι → Set X) (p n : ℕ)
    (σ : C(Simplex p, X)) (c : FormalChains (Simplex p) (n + 1))
    (hc : ∀ v ∈ c.support, ∃ i, range (σ.comp (affineSimplex v)) ⊆ U i) :
    inducedChain σ n (affineChainMap p n c) ∈ smallChainSubmodule U n := by
  apply formalLinearMap_mem_of_support
    ((inducedChain σ n).comp (affineChainMap p n)) (smallChainSubmodule U n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex]
  exact simplexChain_mem_small U n (σ.comp (affineSimplex v)) (hc v hv)

/-- Actual subdivision preserves small chains for an arbitrary family. -/
theorem subdivision_mem_small (U : ι → Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U n) :
    subdivision X k n c ∈ smallChainSubmodule U n := by
  apply singularLinearMap_mem_of_small U n (subdivision X k n)
    (smallChainSubmodule U n) c hc
  rintro σ ⟨i, hσ⟩
  exact supportedChainSubmodule_le_small U i n
    (subdivision_mem_supported (U i) k n (simplexChain X n σ)
      (simplexChain_mem_supported (U i) n σ hσ))

/-- The actual subdivision homotopy stays in the small-chain subcomplex,
one degree higher. -/
theorem subdivisionHomotopy_mem_small (U : ι → Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U n) :
    subdivisionHomotopy X k n c ∈ smallChainSubmodule U (n + 1) := by
  apply singularLinearMap_mem_of_small U n (subdivisionHomotopy X k n)
    (smallChainSubmodule U (n + 1)) c hc
  rintro σ ⟨i, hσ⟩
  exact supportedChainSubmodule_le_small U i (n + 1)
    (subdivisionHomotopy_mem_supported (U i) k n (simplexChain X n σ)
      (simplexChain_mem_supported (U i) n σ hσ))

/-- Every simplex eventually subdivides into actual cover-small chains. -/
theorem eventually_subdivision_simplex_mem_small (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (n : ℕ) (σ : SingularSimplex X n)
    (hcover : range σ ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N,
      subdivision X k n (simplexChain X n σ) ∈ smallChainSubmodule U n := by
  obtain ⟨N, hN⟩ := simplex_formalSubdivision_eventually_small U σ hU hcover
  refine ⟨N, ?_⟩
  intro k hk
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U n n σ
  intro v hv
  exact hN k hk (formalSimplex (stdVertices n)) v hv

/-- A uniform subdivision stage works for every simplex with nonzero
coefficient in a chain. The open cover may be arbitrary and infinite. -/
theorem eventually_subdivision_mem_small (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)
    (n : ℕ) (c : Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N, subdivision X k n c ∈ smallChainSubmodule U n := by
  classical
  have hc : ∀ σ ∈ (chainsEquivFinsupp X n c).support, range σ ⊆ ⋃ i, U i := by
    intro σ hσ
    rw [hcover]
    exact subset_univ _
  obtain ⟨N, hN⟩ := finite_family_formalSubdivision_eventually_small U
    (chainsEquivFinsupp X n c).support hU hc
  refine ⟨N, ?_⟩
  intro k hk
  apply singularLinearMap_mem_of_support n (subdivision X k n) (smallChainSubmodule U n) c
  intro σ hσ
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U n n σ
  intro v hv
  exact hN k hk σ hσ (formalSimplex (stdVertices n)) v hv

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
