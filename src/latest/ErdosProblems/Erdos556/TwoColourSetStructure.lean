import ErdosProblems.Erdos556.TwoColourStructure
import ErdosProblems.Erdos556.ThreeColourTools

/-! Applying the two-colour structural theorem inside a vertex class. -/

namespace Erdos556

open SimpleGraph Finset

structure TwoColourSetPartition {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Finset V) (r : ℕ) (j k : Fin 3) where
  first : Finset V
  second : Finset V
  first_subset : first ⊆ A
  second_subset : second ⊆ A
  disjoint : Disjoint first second
  card_cover : A.card ≤ first.card + second.card + 1
  first_clique : (c.graph j).IsClique (first : Set V)
  second_clique : (c.graph j).IsClique (second : Set V)
  cross : ∀ u ∈ first, ∀ v ∈ second, (c.graph k).Adj u v
  first_card_le : first.card ≤ 2 * r
  second_card_le : second.card ≤ 2 * r

theorem ThreeColouring.induce_complement_of_excluded_colour {V : Type*}
    (c : ThreeColouring V) (A : Set V) (i j k : Fin 3)
    (hcol : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k) (hjk : j ≠ k)
    (hno : ∀ u ∈ A, ∀ v ∈ A, ¬ (c.graph i).Adj u v) :
    ((c.graph j).induce A)ᶜ = (c.graph k).induce A := by
  ext u v
  constructor
  · rintro ⟨hne, hj⟩
    have huv : u.val ≠ v.val := fun hh => hne (Subtype.ext hh)
    refine ⟨huv, ?_⟩
    rcases hcol (c.colour u.val v.val) with hi | he | hk
    · exact (hno u.val u.property v.val v.property ⟨huv, hi⟩).elim
    · exact (hj ⟨huv, he⟩).elim
    · exact hk
  · intro hk
    refine ⟨fun hh => hk.1 (congrArg Subtype.val hh), ?_⟩
    intro hj
    exact hjk (hj.2.symm.trans hk.2)

theorem two_colour_set_partition_of_induced {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Finset V) (r : ℕ) (j k : Fin 3)
    (hcomp : ((c.graph j).induce (A : Set V))ᶜ = (c.graph k).induce (A : Set V))
    (hpart : TwoCliquePartition ((c.graph j).induce (A : Set V)) r) :
    Nonempty (TwoColourSetPartition c A r j k) := by
  classical
  obtain ⟨S, T, Z, hZ, hdis, hcov, hS, hT, hcross, hSc, hTc⟩ := hpart
  let f : (A : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub (U : Finset (A : Set V)) : U.map f ⊆ A := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := mem_map.mp hu
    exact v.property
  have hclique (U : Finset (A : Set V))
      (hU : ((c.graph j).induce (A : Set V)).IsClique (U : Set (A : Set V))) :
      (c.graph j).IsClique ((U.map f : Finset V) : Set V) := by
    intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := mem_map.mp hv
    exact hU hu' hv' (fun hh => huv (congrArg f hh))
  refine ⟨{
    first := S.map f
    second := T.map f
    first_subset := hsub S
    second_subset := hsub T
    disjoint := ?_
    card_cover := ?_
    first_clique := hclique S hS
    second_clique := hclique T hT
    cross := ?_
    first_card_le := by simpa only [card_map] using hSc
    second_card_le := by simpa only [card_map] using hTc }⟩
  · apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨s, hs, hes⟩ := mem_map.mp hu
    obtain ⟨t, ht, het⟩ := mem_map.mp hv
    exact Finset.disjoint_left.mp hdis hs ((f.injective (het.trans hes.symm)) ▸ ht)
  · rw [card_map, card_map]
    have hh := congrArg Finset.card hcov
    rw [card_union_of_disjoint hdis, card_sdiff, inter_univ, card_univ] at hh
    have hcard : Fintype.card (A : Set V) = A.card := by
      calc
        _ = (A : Set V).ncard := Nat.card_eq_fintype_card.symm
        _ = A.card := Set.ncard_coe_finset A
    rw [hcard] at hh
    omega
  · intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := mem_map.mp hu
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hv
    have hh := hcross s hs t ht
    rw [hcomp] at hh
    exact hh

theorem exists_uniform_two_colour_set_structure :
    ∃ R₀ : ℕ, ∀ {V : Type*} [DecidableEq V]
      (c : ThreeColouring V) (A : Finset V) (r : ℕ) (i : Fin 3),
      R₀ ≤ r → 4 * (r + 1) - (r + 1) / 100000 ≤ A.card →
      (∀ u ∈ A, ∀ v ∈ A, ¬ (c.graph i).Adj u v) →
      (∀ a, ¬ cycleGraph (2 * r + 1) ⊑ c.graph a) →
      ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
        Nonempty (TwoColourSetPartition c A r j k) := by
  obtain ⟨R₀, hR₀⟩ := exists_uniform_two_colour_structure
  refine ⟨R₀, ?_⟩
  intro V _ c A r i hr hA hnoI hno
  classical
  have hcols : ∀ i : Fin 3, ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      ∀ a : Fin 3, a = i ∨ a = j ∨ a = k := by decide
  obtain ⟨j, k, hji, hki, hjk, hall⟩ := hcols i
  have hc := c.induce_complement_of_excluded_colour (A : Set V) i j k hall hjk hnoI
  have hn (a : Fin 3) : ¬ cycleGraph (2 * r + 1) ⊑ (c.graph a).induce (A : Set V) :=
    fun hh => hno a (hh.trans ⟨Copy.induce _ _⟩)
  have hcard : Fintype.card (A : Set V) = A.card := by
    calc
      _ = (A : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = A.card := Set.ncard_coe_finset A
  have hAc : 4 * (r + 1) - (r + 1) / 100000 ≤ Fintype.card (A : Set V) := by rwa [hcard]
  have hnc : ¬ cycleGraph (2 * r + 1) ⊑ ((c.graph j).induce (A : Set V))ᶜ := by
    rw [hc]
    exact hn k
  rcases hR₀ ((c.graph j).induce (A : Set V)) r hr hAc (hn j) hnc with hp | hp
  · exact ⟨j, k, hji, hki, hjk, two_colour_set_partition_of_induced c A r j k hc hp⟩
  · have hkc : ((c.graph k).induce (A : Set V))ᶜ = (c.graph j).induce (A : Set V) := by
      rw [← hc, compl_compl]
    rw [hc] at hp
    exact ⟨k, j, hki, hji, hjk.symm, two_colour_set_partition_of_induced c A r k j hkc hp⟩

#print axioms exists_uniform_two_colour_set_structure

end Erdos556
