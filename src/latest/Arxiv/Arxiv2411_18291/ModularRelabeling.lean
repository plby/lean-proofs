import Arxiv.Arxiv2411_18291.ModularGeneratingData
import Arxiv.Arxiv2411_18291.CliqueFamilyRelabeling

/-!
# Relabeling modular generators

Transport on edge coordinates is an additive homomorphism. It sends a
clique vector to the vector of the relabeled clique, so it also transports
every relation in the generated subgroup. No independence is needed here.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r N : ℕ}

def relabelModularVector (N r : ℕ) (f : V ≃ W) :
    (Block V r → ZMod N) →+ (Block W r → ZMod N) where
  toFun := fun Φ e => Φ ((blockEquiv f).symm e)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype V] [Fintype W] in
theorem relabelModularVector_clique (f : V ≃ W) (Q : Block V q) :
    relabelModularVector N r f (modularCliqueVector N r Q) =
      modularCliqueVector N r (mapBlock f.toEmbedding Q) := by
  funext e
  obtain ⟨e, rfl⟩ := (blockEquiv (r := r) f).surjective e
  change modularCliqueVector N r Q ((blockEquiv f).symm ((blockEquiv f) e)) =
    modularCliqueVector N r (mapBlock f.toEmbedding Q) (mapBlock f.toEmbedding e)
  simp only [Equiv.symm_apply_apply, modularCliqueVector, mapBlock_subset_mapBlock]

omit [Fintype V] [Fintype W] in
theorem modular_generated_map (f : V ≃ W) (D : Finset (Block V q))
    {Φ : Block V r → ZMod N} (hΦ : Φ ∈ generatedSubgroup (modularCliqueVector N r) D) :
    relabelModularVector N r f Φ ∈
      generatedSubgroup (modularCliqueVector N r) (mapGraph f.toEmbedding D) := by
  have hle : generatedSubgroup (modularCliqueVector N r) D ≤
      (generatedSubgroup (modularCliqueVector N r) (mapGraph f.toEmbedding D)).comap
        (relabelModularVector N r f) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro Ψ ⟨Q, hQ, rfl⟩
    change relabelModularVector N r f (modularCliqueVector N r Q) ∈
      generatedSubgroup (modularCliqueVector N r) (mapGraph f.toEmbedding D)
    rw [relabelModularVector_clique]
    exact mem_generatedSubgroup _ ((mem_mapGraph _ _ _).mpr ⟨Q, hQ, rfl⟩)
  exact hle hΦ

omit [Fintype V] [Fintype W] in
theorem modularCliqueVector_generated_map (f : V ≃ W) (D : Finset (Block V q))
    {Q : Block V q} (hQ : modularCliqueVector N r Q ∈
      generatedSubgroup (modularCliqueVector N r) D) :
    modularCliqueVector N r (mapBlock f.toEmbedding Q) ∈
      generatedSubgroup (modularCliqueVector N r) (mapGraph f.toEmbedding D) := by
  simpa only [relabelModularVector_clique] using modular_generated_map f D hQ

def ModularGeneratingData.map {K : Hypergraph V (r + 1)} {D : Finset (Block V q)}
    (C : ModularGeneratingData K D N) (f : V ≃ W) :
    ModularGeneratingData (mapGraph f.toEmbedding K) (mapGraph f.toEmbedding D) N where
  generators := mapGraph f.toEmbedding C.generators
  saturated := mapGraph f.toEmbedding C.saturated
  good := mapGraph f.toEmbedding C.good
  generators_subset := mapGraph_mono _ C.generators_subset
  saturated_subset := mapGraph_mono _ C.saturated_subset
  good_subset := mapGraph_mono _ C.good_subset
  generates := by
    intro Q hQ
    have heq : mapGraph f.toEmbedding D \ mapGraph f.toEmbedding C.saturated =
        mapGraph f.toEmbedding (D \ C.saturated) := by
      exact (Finset.map_sdiff _ _).symm
    rw [heq] at hQ
    obtain ⟨P, hP, hPQ⟩ := (mem_mapGraph _ _ _).mp hQ
    rw [← hPQ]
    exact modularCliqueVector_generated_map f C.generators (C.generates P hP)

end Arxiv2411_18291
