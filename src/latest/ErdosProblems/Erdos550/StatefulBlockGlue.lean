import Mathlib
import ErdosProblems.Erdos550.StatefulSequentialBlockEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Image accounting for stateful block extensions

Besides injectivity and adjacency, the sharp matching proof must update the two
loads of the selected regular pair exactly.  These lemmas record that a fresh
block contributes its image-cardinality additively to every host region.
-/

open Finset

namespace Erdos550

open Classical

/-- Replace `f` by `g` on a newly embedded block. -/
def glueOnBlock
    {A V : Type*} [DecidableEq A]
    (B : Finset A) (f g : A → V) : A → V :=
  fun a => if a ∈ B then g a else f a

lemma image_glueOnBlock_union
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (S B : Finset A) (f g : A → V)
    (hBS : Disjoint B S) :
    (S ∪ B).image (glueOnBlock B f g) =
      S.image f ∪ B.image g := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp ha with haS | haB
    · have haNotB : a ∉ B :=
        fun haB => Finset.disjoint_left.mp hBS haB haS
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr
          ⟨a, haS, by simp [glueOnBlock, haNotB]⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr
          ⟨a, haB, by simp [glueOnBlock, haB]⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hvS | hvB
    · obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hvS
      have haNotB : a ∉ B :=
        fun haB => Finset.disjoint_left.mp hBS haB haS
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_union_left _ haS,
          by simp [glueOnBlock, haNotB]⟩
    · obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp hvB
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_union_right _ haB,
          by simp [glueOnBlock, haB]⟩

/-- Exact load update in an arbitrary host region. -/
lemma card_image_glueOnBlock_inter
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (S B : Finset A) (f g : A → V) (P : Finset V)
    (hBS : Disjoint B S)
    (himg : Disjoint (B.image g) (S.image f)) :
    ((S ∪ B).image (glueOnBlock B f g) ∩ P).card =
      (S.image f ∩ P).card + (B.image g ∩ P).card := by
  rw [image_glueOnBlock_union S B f g hBS]
  rw [Finset.union_inter_distrib_right]
  apply Finset.card_union_of_disjoint
  exact himg.symm.mono Finset.inter_subset_left Finset.inter_subset_left

/-- An injective local map contributes exactly the number of block vertices
whose images lie in a host region. -/
lemma card_image_inter_eq_card_filter
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (B : Finset A) (g : A → V) (P : Finset V)
    (hginj : Set.InjOn g B) :
    (B.image g ∩ P).card =
      (B.filter fun a => g a ∈ P).card := by
  have himage :
      B.image g ∩ P =
        (B.filter fun a => g a ∈ P).image g := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvImg, hvP⟩ := Finset.mem_inter.mp hv
      obtain ⟨a, haB, hav⟩ := Finset.mem_image.mp hvImg
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨haB, hav ▸ hvP⟩, hav⟩
    · intro hv
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr
          ⟨a, (Finset.mem_filter.mp ha).1, hav⟩,
          hav ▸ (Finset.mem_filter.mp ha).2⟩
  rw [himage]
  exact Finset.card_image_of_injOn
    (hginj.mono (Finset.filter_subset _ _))

end Erdos550
