import Wikipedia.HopfProblem.SingularMayerVietorisSmallChains
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsBasis

/-!
# Chains supported in a subspace

Actual singular-chain maps of subtype inclusions are injective, and their
images are precisely the spans of simplices supported in the subspaces.
The common image for two subspaces is the image of their intersection.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

def subtypeInclusion (U : Set X) : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩

def restrictSimplex (U : Set X) (n : ℕ) (σ : SingularSimplex X n)
    (hσ : range σ ⊆ U) : SingularSimplex U n :=
  ⟨fun p => ⟨σ p, hσ ⟨p, rfl⟩⟩, σ.continuous.subtype_mk _⟩

@[simp] theorem subtypeInclusion_comp_restrictSimplex (U : Set X) (n : ℕ)
    (σ : SingularSimplex X n) (hσ : range σ ⊆ U) :
    (subtypeInclusion U).comp (restrictSimplex U n σ hσ) = σ := by
  ext p
  rfl

theorem range_subtypeInclusion_comp (U : Set X) (n : ℕ) (σ : SingularSimplex U n) :
    range ((subtypeInclusion U).comp σ) ⊆ U := by
  rintro x ⟨p, rfl⟩
  exact (σ p).2

@[simp] theorem restrictSimplex_inclusion (U : Set X) (n : ℕ) (σ : SingularSimplex U n)
    (hσ : range ((subtypeInclusion U).comp σ) ⊆ U) :
    restrictSimplex U n ((subtypeInclusion U).comp σ) hσ = σ := by
  ext p
  rfl

def simplexRetraction (U : Set X) (n : ℕ) (σ : SingularSimplex X n) : Chains U n := by
  classical
  exact if hσ : range σ ⊆ U then simplexChain U n (restrictSimplex U n σ hσ) else 0

/-- A degreewise linear retraction; it need not commute with the boundary. -/
def subtypeChainRetraction (U : Set X) (n : ℕ) : Chains X n →ₗ[ℤ] Chains U n :=
  chainLift X n (simplexRetraction U n)

theorem subtypeChainRetraction_inclusion_simplex (U : Set X) (n : ℕ)
    (σ : SingularSimplex U n) :
    subtypeChainRetraction U n (inducedChain (subtypeInclusion U) n (simplexChain U n σ)) =
      simplexChain U n σ := by
  rw [inducedChain_simplex]
  change chainLift X n (simplexRetraction U n) _ = _
  rw [chainLift_simplex]
  simp only [simplexRetraction, dif_pos (range_subtypeInclusion_comp U n σ),
    restrictSimplex_inclusion]

theorem subtypeChainRetraction_comp (U : Set X) (n : ℕ) :
    (subtypeChainRetraction U n).comp (inducedChain (subtypeInclusion U) n) = LinearMap.id := by
  apply chainMap_ext U n
  intro σ
  exact subtypeChainRetraction_inclusion_simplex U n σ

theorem subtypeInclusion_chain_injective (U : Set X) (n : ℕ) :
    Function.Injective (inducedChain (subtypeInclusion U) n) :=
  (show Function.LeftInverse (subtypeChainRetraction U n)
      (inducedChain (subtypeInclusion U) n) from
    fun c => LinearMap.congr_fun (subtypeChainRetraction_comp U n) c).injective

theorem subtypeInclusion_generator_image (U : Set X) (n : ℕ) :
    inducedChain (subtypeInclusion U) n '' Set.range (simplexChain U n) =
      simplexChain X n '' {σ : SingularSimplex X n | range σ ⊆ U} := by
  ext c
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨(subtypeInclusion U).comp σ, range_subtypeInclusion_comp U n σ,
      (inducedChain_simplex (subtypeInclusion U) n σ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨simplexChain U n (restrictSimplex U n σ hσ), ⟨_, rfl⟩, ?_⟩
    rw [inducedChain_simplex, subtypeInclusion_comp_restrictSimplex]

theorem subtypeInclusion_chain_range (U : Set X) (n : ℕ) :
    LinearMap.range (inducedChain (subtypeInclusion U) n) = supportedChainSubmodule U n := by
  rw [LinearMap.range_eq_map, ← simplexChain_span U n, Submodule.map_span,
    subtypeInclusion_generator_image]
  rfl

theorem supportedChainSubmodule_inf (U V : Set X) (n : ℕ) :
    supportedChainSubmodule U n ⊓ supportedChainSubmodule V n =
      supportedChainSubmodule (U ∩ V) n := by
  have hsets : ({σ : SingularSimplex X n | range σ ⊆ U} ∩
      {σ : SingularSimplex X n | range σ ⊆ V}) =
      {σ : SingularSimplex X n | range σ ⊆ U ∩ V} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.subset_inter_iff]
  unfold supportedChainSubmodule
  rw [simplex_span_inter, hsets]


end Wikipedia.HopfProblem.SingularMayerVietoris
