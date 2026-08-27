import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Bounded groups for multiplicity reduction

A finite set of size at most `a*b` can be partitioned into at most `a`
nonempty groups, each of size at most `b`. In particular, `sqrt(x)+1`
bounds both the number and size of the groups, including the small cases
where the floor-square-root grouping in the printed proof does not fit.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {X : Type*} [DecidableEq X]

theorem exists_finpartition_bounded_size (s : Finset X) (a b : ℕ) (hs : s.card ≤ a * b) :
    ∃ P : Finpartition s, P.parts.card ≤ a ∧ ∀ c ∈ P.parts, c.card ≤ b := by
  classical
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le (α := s) (β := Fin a × Fin b)
    (by simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hs)
  let E (i : Fin a) := univ.filter fun x : s => (g x).1 = i
  let G (i : Fin a) : Finset X := (E i).map (Function.Embedding.subtype (· ∈ s))
  have hmem (i : Fin a) (x : s) : x.val ∈ G i ↔ (g x).1 = i := by
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ (mem_filter.mp hy).2
    · intro hx
      exact mem_map.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
  have hsub (i : Fin a) : G i ⊆ s := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact y.property
  have hcard (i : Fin a) : (G i).card ≤ b := by
    have hinj : Function.Injective (fun x : {y : s // (g y).1 = i} => (g x.val).2) := by
      intro x y hxy
      exact Subtype.ext (g.injective (Prod.ext (x.property.trans y.property.symm) hxy))
    have hcount := Fintype.card_le_of_injective _ hinj
    simpa only [G, card_map, E, Fintype.card_subtype, Fintype.card_fin] using hcount
  let parts := (univ.image G).erase ∅
  have hparts : ∀ c ∈ parts, c ⊆ s := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_erase.mp hc).2
    exact hsub i
  have hunique : ∀ x ∈ s, ∃! c ∈ parts, x ∈ c := by
    intro x hx
    let y : s := ⟨x, hx⟩
    let i := (g y).1
    have hxi : x ∈ G i := (hmem i y).mpr rfl
    have hne : G i ≠ ∅ := nonempty_iff_ne_empty.mp ⟨x, hxi⟩
    refine ⟨G i, ⟨mem_erase.mpr ⟨hne, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩, hxi⟩, ?_⟩
    intro c hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp (mem_erase.mp hc.1).2
    have hij : i = j := (hmem j y).mp hc.2
    exact congrArg G hij.symm
  let P := Finpartition.ofExistsUnique parts hparts hunique (notMem_erase ∅ _)
  refine ⟨P, ?_, ?_⟩
  · change parts.card ≤ a
    exact (card_le_card (erase_subset _ _)).trans
      (card_image_le.trans (by rw [card_univ, Fintype.card_fin]))
  · intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_erase.mp hc).2
    exact hcard i

theorem exists_finpartition_sqrt (s : Finset X) :
    ∃ P : Finpartition s, P.parts.card ≤ s.card.sqrt + 1 ∧
      ∀ c ∈ P.parts, c.card ≤ s.card.sqrt + 1 :=
  exists_finpartition_bounded_size s (s.card.sqrt + 1) (s.card.sqrt + 1)
    (Nat.lt_succ_sqrt s.card).le

end Arxiv2411_18291
