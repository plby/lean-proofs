import Wikipedia.HopfProblem.SingularMayerVietorisAffineChains
import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsSupport
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChains
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsBasis

/-!
# Support of realized singular subdivision chains

All memberships below concern the genuine small-chain submodules of the
actual singular complex. Finite coefficient support reduces membership to
the actual singular simplices occurring in an affine-chain realization.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {V M : Type*} [AddCommGroup M] [Module ℤ M]

/-- A linear image belongs to a submodule when the images of all its
nonzero formal simplex coefficients do. -/
theorem formalLinearMap_mem_of_support {n : ℕ}
    (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : FormalChains V n)
    (hf : ∀ v ∈ c.support, f (formalSimplex v) ∈ P) : f c ∈ P := by
  have h : Finsupp.supported ℤ ℤ (c.support : Set (Fin n → V)) ≤ P.comap f := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv
  exact h (fun _ hv => hv)

variable {X : Type} [TopologicalSpace X]

/-- The corresponding finite-support principle for Mathlib's actual
coproduct singular chain group, using its proved basis. -/
theorem singularLinearMap_mem_of_support (n : ℕ) (f : Chains X n →ₗ[ℤ] M)
    (P : Submodule ℤ M) (c : Chains X n)
    (hf : ∀ σ ∈ (chainsEquivFinsupp X n c).support, f (simplexChain X n σ) ∈ P) :
    f c ∈ P := by
  let S : Set (SingularSimplex X n) := (chainsEquivFinsupp X n c).support
  have hc : c ∈ Submodule.span ℤ (simplexChain X n '' S) :=
    (mem_simplex_span_iff X n S c).mpr (Subset.refl _)
  have h : Submodule.span ℤ (simplexChain X n '' S) ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- A linear map preserves membership for supported chains once checked
on the actual supported singular-simplex generators. -/
theorem singularLinearMap_mem_of_supported (U : Set X) (n : ℕ)
    (f : Chains X n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : Chains X n)
    (hc : c ∈ supportedChainSubmodule U n)
    (hf : ∀ σ : SingularSimplex X n, range σ ⊆ U → f (simplexChain X n σ) ∈ P) :
    f c ∈ P := by
  have h : supportedChainSubmodule U n ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- The analogous generator principle for the actual two-set small chains. -/
theorem singularLinearMap_mem_of_small (U V : Set X) (n : ℕ)
    (f : Chains X n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n)
    (hf : ∀ σ : SingularSimplex X n, (range σ ⊆ U ∨ range σ ⊆ V) →
      f (simplexChain X n σ) ∈ P) : f c ∈ P := by
  have h : smallChainSubmodule U V n ≤ P.comap f := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- Any affine-chain realization stays inside the carrier of the original
continuous singular simplex. -/
theorem realizedChain_mem_supported (U : Set X) (p n : ℕ)
    (σ : C(Simplex p, X)) (hσ : range σ ⊆ U) (c : FormalChains (Simplex p) (n + 1)) :
    inducedChain σ n (affineChainMap p n c) ∈ supportedChainSubmodule U n := by
  apply formalLinearMap_mem_of_support
    ((inducedChain σ n).comp (affineChainMap p n)) (supportedChainSubmodule U n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex]
  apply simplexChain_mem_supported
  rintro x ⟨t, rfl⟩
  exact hσ ⟨affineSimplex v t, rfl⟩

/-- If the original simplex is small, every affine-chain realization in
its parameter simplex remains small. -/
theorem realizedChain_mem_small (U V : Set X) (p n : ℕ)
    (σ : C(Simplex p, X)) (hσ : range σ ⊆ U ∨ range σ ⊆ V)
    (c : FormalChains (Simplex p) (n + 1)) :
    inducedChain σ n (affineChainMap p n c) ∈ smallChainSubmodule U V n := by
  rcases hσ with hσ | hσ
  · exact (le_sup_left : supportedChainSubmodule U n ≤ smallChainSubmodule U V n)
      (realizedChain_mem_supported U p n σ hσ c)
  · exact (le_sup_right : supportedChainSubmodule V n ≤ smallChainSubmodule U V n)
      (realizedChain_mem_supported V p n σ hσ c)

/-- More generally, the realization is small if every affine simplex with
a nonzero coefficient is mapped into one member of the cover. -/
theorem realizedChain_mem_small_of_support (U V : Set X) (p n : ℕ)
    (σ : C(Simplex p, X)) (c : FormalChains (Simplex p) (n + 1))
    (hc : ∀ v ∈ c.support, range (σ.comp (affineSimplex v)) ⊆ U ∨
      range (σ.comp (affineSimplex v)) ⊆ V) :
    inducedChain σ n (affineChainMap p n c) ∈ smallChainSubmodule U V n := by
  apply formalLinearMap_mem_of_support
    ((inducedChain σ n).comp (affineChainMap p n)) (smallChainSubmodule U V n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex]
  exact simplexChain_mem_small U V n (σ.comp (affineSimplex v)) (hc v hv)

end Wikipedia.HopfProblem.SingularMayerVietoris
