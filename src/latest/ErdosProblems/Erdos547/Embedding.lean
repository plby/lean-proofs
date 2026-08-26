import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

/-!
# Finite tree embeddings for Erdős problem 547

These lemmas concern ordinary, not induced, copies. The rooted greedy argument
refines the leaf-deletion proof already used in `Erdos79.Forest`: a prescribed
tree vertex can be sent to any prescribed host vertex.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}

/-- A used vertex is not its own neighbour, so `|used| ≤ degree` leaves an
unused neighbour whenever the current vertex belongs to `used`. -/
theorem exists_unused_neighbor [Fintype V] [DecidableRel G.Adj]
    (used : Finset V) (v : V) (hv : v ∈ used) (hd : used.card ≤ G.degree v) :
    ∃ w, G.Adj v w ∧ w ∉ used := by
  classical
  have hnot : ¬ G.neighborFinset v ⊆ used := by
    intro hsub
    have heq : G.neighborFinset v = used :=
      Finset.eq_of_subset_of_card_le hsub (by simpa using hd)
    exact G.notMem_neighborFinset_self v (heq.symm ▸ hv)
  obtain ⟨w, hw, hwu⟩ := Finset.not_subset.mp hnot
  exact ⟨w, (G.mem_neighborFinset v w).mp hw, hwu⟩

/-- Excluding a used set costs at most its cardinality minus one neighbours,
because the current vertex belongs to the used set and is not its own neighbour. -/
theorem degree_add_one_le_unused_add_used [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (used : Finset V) (v : V) (hv : v ∈ used) :
    G.degree v + 1 ≤ (G.neighborFinset v \ used).card + used.card := by
  classical
  have hsub : G.neighborFinset v ∩ used ⊆ used.erase v := by
    intro x hx
    obtain ⟨hxn, hxu⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, hxu⟩
    intro hxv
    subst x
    exact G.notMem_neighborFinset_self v hxn
  have hbound := Finset.card_le_card hsub
  have herase := Finset.card_erase_of_mem hv
  have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset v) used
  rw [G.card_neighborFinset_eq_degree] at hsplit
  have husedpos : 0 < used.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Extend a copy after adding a vertex with exactly one possible neighbour.
Every previously embedded vertex retains its image. -/
theorem extend_leaf_copy (v : U) (p : ({v}ᶜ : Set U))
    (hp : ∀ x, T.Adj v x → x = p.val)
    (e : (T.induce ({v}ᶜ : Set U)).Copy G)
    (w : V) (hw : G.Adj (e p) w) (hwu : ∀ x, e x ≠ w) :
    ∃ f : T.Copy G, f v = w ∧ ∀ x : ({v}ᶜ : Set U), f x.val = e x := by
  classical
  let f : U → V := fun x ↦ if hx : x = v then w else e ⟨x, by simp [hx]⟩
  have hf_v : f v = w := by simp [f]
  have hf_ne (x : U) (hx : x ≠ v) : f x = e ⟨x, by simp [hx]⟩ := by
    simp [f, hx]
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = v
    · subst x
      by_cases hy : y = v
      · exact hy.symm
      · exact False.elim (hwu ⟨y, by simp [hy]⟩
          (by simpa [hf_v, hf_ne y hy] using hxy.symm))
    · by_cases hy : y = v
      · subst y
        exact False.elim (hwu ⟨x, by simp [hx]⟩
          (by simpa [hf_v, hf_ne x hx] using hxy))
      · exact congrArg Subtype.val (e.injective
          (by simpa [hf_ne x hx, hf_ne y hy] using hxy))
  have hp_ne : p.val ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using p.property
  have hf_adj {x y : U} (hxy : T.Adj x y) : G.Adj (f x) (f y) := by
    by_cases hx : x = v
    · subst x
      have hy : y = p.val := hp y hxy
      subst y
      simpa [hf_v, hf_ne p.val hp_ne] using hw.symm
    · by_cases hy : y = v
      · subst y
        have hx_p : x = p.val := hp x hxy.symm
        subst x
        simpa [hf_v, hf_ne p.val hp_ne] using hw
      · have hxy' : (T.induce ({v}ᶜ : Set U)).Adj
            ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ := hxy
        simpa [hf_ne x hx, hf_ne y hy] using e.toHom.map_adj hxy'
  refine ⟨⟨⟨f, fun h ↦ hf_adj h⟩, hf_inj⟩, hf_v, ?_⟩
  intro x
  exact hf_ne x.val (by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property)

/-- The minimum-degree greedy tree embedding can preserve any chosen root. -/
theorem exists_rooted_copy_of_minDegree [Fintype U] [Fintype V]
    [DecidableRel G.Adj] (hT : T.IsTree)
    (hd : Fintype.card U - 1 ≤ G.minDegree) (r : U) (z : V) :
    ∃ f : T.Copy G, f r = z := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (W : Type _) [Fintype W] (S : SimpleGraph W),
      Fintype.card W = n → S.IsTree →
      Fintype.card W - 1 ≤ G.minDegree →
      ∀ r : W, ∃ f : S.Copy G, f r = z
  suffices hP : P (Fintype.card U) from hP U T rfl hT hd r
  apply Nat.strong_induction_on (p := P) (Fintype.card U)
  intro n ih W _ S hn hS hdeg root
  by_cases hW : Nontrivial W
  · let : Nontrivial W := hW
    obtain ⟨u, v, huv, hu, hv⟩ := hS.exists_ne_and_degree_eq_one
    have hleaf : ∃ v : W, v ≠ root ∧ S.degree v = 1 := by
      by_cases hur : u = root
      · exact ⟨v, by simpa [hur] using huv.symm, hv⟩
      · exact ⟨u, hur, hu⟩
    obtain ⟨v, hvr, hv⟩ := hleaf
    let W' := ({v}ᶜ : Set W)
    let S' : SimpleGraph W' := S.induce ({v}ᶜ : Set W)
    let root' : W' := ⟨root, by simpa [W'] using hvr.symm⟩
    have hS' : S'.IsTree :=
      ⟨hS.connected.induce_compl_singleton_of_degree_eq_one hv, hS.isAcyclic.induce _⟩
    have hcard : Fintype.card W' = n - 1 := by
      change Fintype.card ↑({v}ᶜ : Set W) = n - 1
      rw [Fintype.card_compl_set]
      simp [hn]
    have hnpos : 0 < n := by
      rw [← hn]
      exact Fintype.card_pos_iff.mpr ⟨root⟩
    have hlt : Fintype.card W' < n := by omega
    have hdeg' : Fintype.card W' - 1 ≤ G.minDegree := by omega
    obtain ⟨e, he⟩ := ih (Fintype.card W') hlt W' S' rfl hS' hdeg' root'
    obtain ⟨p, hvp, hp⟩ := S.degree_eq_one_iff_existsUnique_adj.mp hv
    let p' : W' := ⟨p, by simpa [W'] using hvp.ne'⟩
    let used : Finset V := Finset.univ.image e
    have hused : used.card = Fintype.card W' := by
      simpa [used] using
        Finset.card_image_of_injective (Finset.univ : Finset W') e.injective
    have hcount : used.card ≤ G.degree (e p') := by
      rw [hused, hcard]
      have hmin : n - 1 ≤ G.minDegree := by simpa [hn] using hdeg
      exact hmin.trans (G.minDegree_le_degree (e p'))
    obtain ⟨w, hw, hwu⟩ := exists_unused_neighbor used (e p') (by simp [used]) hcount
    obtain ⟨f, _, hf⟩ := extend_leaf_copy v p' hp e w hw (by
      intro x hx
      apply hwu
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
    exact ⟨f, (hf root').trans he⟩
  · let : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
    refine ⟨{
      toHom := {
        toFun := fun _ ↦ z
        map_rel' := fun {a b} hab ↦
          (S.loopless.irrefl a (Subsingleton.elim b a ▸ hab)).elim }
      injective' := fun _ _ _ ↦ Subsingleton.elim _ _ }, rfl⟩

/-- The unrooted greedy embedding, with the nonempty-host hypothesis explicit. -/
theorem isContained_of_isTree_of_minDegree [Fintype U] [Fintype V]
    [Nonempty V] [DecidableRel G.Adj] (hT : T.IsTree)
    (hd : Fintype.card U - 1 ≤ G.minDegree) : T ⊑ G := by
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨z⟩ := (inferInstance : Nonempty V)
  obtain ⟨f, _⟩ := exists_rooted_copy_of_minDegree hT hd r z
  exact ⟨f⟩

end Erdos547

#print axioms Erdos547.extend_leaf_copy
#print axioms Erdos547.exists_rooted_copy_of_minDegree
