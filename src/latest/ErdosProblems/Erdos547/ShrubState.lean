import ErdosProblems.Erdos547.ShrubIndex
import ErdosProblems.Erdos547.ShrubGlue

/-!
# Partial embeddings with a fixed head and a chosen tail for each shrub
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)}

structure ShrubState (P : FineTreePartition T r ℓ col) (G : SimpleGraph V)
    (C : I → Finset V) (head : ↥P.shrubs → I)
    (seed : (T.induce (P.seeds : Set U)).Copy G) where
  placed : Finset ↥P.shrubs
  tail : ↥P.shrubs → I
  copy : (T.induce ((P.shrubDomain placed : Finset U) : Set U)).Copy G
  seed_eq : ∀ v : ↥P.seeds,
    copy ⟨v.val, P.seeds_subset_shrubDomain placed v.property⟩ = seed v
  near_mem : ∀ S (hS : S ∈ placed) (v : ↥S.val), col v.val ≠ P.shrubColour S →
    copy ⟨v.val, P.shrub_subset_domain hS v.property⟩ ∈ C (head S)
  far_mem : ∀ S (hS : S ∈ placed) (v : ↥S.val), col v.val = P.shrubColour S →
    copy ⟨v.val, P.shrub_subset_domain hS v.property⟩ ∈ C (tail S)

namespace ShrubState

variable {P : FineTreePartition T r ℓ col} {G : SimpleGraph V}
  {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}
variable (E : ShrubState P G C head seed)

noncomputable def occupied : Finset V := Finset.univ.image E.copy

def seedVertex (v : ↥P.seeds) : ↥(P.shrubDomain E.placed) :=
  ⟨v.val, P.seeds_subset_shrubDomain E.placed v.property⟩

def shrubVertex (S : ↥P.shrubs) (hS : S ∈ E.placed) (v : ↥S.val) :
    ↥(P.shrubDomain E.placed) := ⟨v.val, P.shrub_subset_domain hS v.property⟩

noncomputable def shrubImage (S : ↥P.shrubs) (hS : S ∈ E.placed) : Finset V :=
  Finset.univ.image (fun v : ↥S.val ↦ E.copy (E.shrubVertex S hS v))

theorem image_mem_occupied (v : ↥(P.shrubDomain E.placed)) : E.copy v ∈ E.occupied :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem seed_mem_occupied (v : ↥P.seeds) : seed v ∈ E.occupied := by
  rw [← E.seed_eq v]
  exact E.image_mem_occupied _

theorem shrubImage_card (S : ↥P.shrubs) (hS : S ∈ E.placed) :
    (E.shrubImage S hS).card = S.val.card := by
  have hi : Function.Injective (fun v : ↥S.val ↦ E.copy (E.shrubVertex S hS v)) := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : ↥(P.shrubDomain E.placed) ↦ z.val)
      (E.copy.injective h))
  rw [shrubImage, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe]

theorem mem_occupied_iff (v : V) : v ∈ E.occupied ↔
    (∃ x : ↥P.seeds, seed x = v) ∨
    ∃ S, ∃ hS : S ∈ E.placed, v ∈ E.shrubImage S hS := by
  constructor
  · intro hv
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp x.property with hxW | hxS
    · left
      refine ⟨⟨x.val, hxW⟩, ?_⟩
      rw [← E.seed_eq ⟨x.val, hxW⟩]
      exact hx
    · obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hxS
      exact Or.inr ⟨S, hS, Finset.mem_image.mpr ⟨⟨x.val, hxS⟩, Finset.mem_univ _, hx⟩⟩
  · rintro (⟨x, rfl⟩ | ⟨S, hS, hv⟩)
    · exact E.seed_mem_occupied x
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      exact E.image_mem_occupied _

end ShrubState
end Erdos547
