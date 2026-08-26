import ErdosProblems.Erdos19.BoundedColoring
import ErdosProblems.Erdos19.PermutationAvoidance
import ErdosProblems.Erdos19.GreedyLists

/-!
# Correcting sparse forbidden colors

An ordinary edge coloring can be globally permuted so that the forbidden
edges have small maximum degree. A disjoint reserve palette then colors those
edges greedily. This is proved for arbitrary bounded-rank finite hypergraphs;
linearity is not needed for the correction itself.
-/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem card_filter_injective_preimage_le {A B : Type*} [Fintype A]
    [DecidableEq A] [DecidableEq B] (j : A → B) (hj : Function.Injective j)
    (S : Finset B) : (univ.filter fun a ↦ j a ∈ S).card ≤ S.card := by
  classical
  rw [← card_image_of_injective _ hj]
  apply card_le_card
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  exact (mem_filter.mp ha).2

/-- Sparse forbidden colors can be repaired in a separate palette of size
greater than `r * s + f`, provided `|V(H)| * f^s < s!`. -/
theorem exists_edgeColoring_avoiding_sparse {V E A B : Type*}
    [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (H : FiniteHypergraph V E) (r f s : ℕ) (hbound : H.IsBounded r)
    (c : H.conflictGraph.Coloring A) (F : E → Finset (A ⊕ B))
    (hF : ∀ e, (F e).card ≤ f)
    (hsmall : H.vertexSet.card * f ^ s < s.factorial)
    (hreserve : r * s + f < Fintype.card B) :
    ∃ d : H.conflictGraph.Coloring (A ⊕ B), ∀ e, d e ∉ F e := by
  classical
  let I := ↥H.vertexSet
  let T : I → Finset E := fun v ↦ univ.filter fun e ↦ v.val ∈ H.support e
  have hc : ∀ v : I, Set.InjOn c (T v) := by
    intro v e he g hg hcg
    by_contra hne
    apply c.valid ⟨hne, ?_⟩ hcg
    exact not_disjoint_iff.mpr
      ⟨v.val, (mem_filter.mp he).2, (mem_filter.mp hg).2⟩
  let Fmain : E → Finset A := fun e ↦ univ.filter fun a ↦ Sum.inl a ∈ F e
  have hFmain : ∀ e, (Fmain e).card ≤ f := by
    intro e
    exact (card_filter_injective_preimage_le Sum.inl Sum.inl_injective (F e)).trans (hF e)
  obtain ⟨p, hp⟩ := exists_permutation_few_forbidden T c hc Fmain f s
    (fun _ e _ ↦ hFmain e) (by simpa [I] using hsmall)
  let bad : E → Prop := fun e ↦ Sum.inl (p (c e)) ∈ F e
  let EB := {e : E // bad e}
  let HB : FiniteHypergraph V EB :=
    { vertexSet := H.vertexSet
      support := fun e ↦ H.support e.val
      support_subset_vertexSet := fun e ↦ H.support_subset_vertexSet e.val }
  have hdeg : ∀ v ∈ HB.vertexSet, HB.edgeDegree v ≤ s := by
    intro v hv
    have htail : ((T ⟨v, hv⟩).filter bad).card < s := by
      simpa only [Fmain, mem_filter, mem_univ, true_and, bad] using hp ⟨v, hv⟩
    have hinc : HB.edgeDegree v ≤ ((T ⟨v, hv⟩).filter bad).card := by
      unfold edgeDegree
      rw [← card_image_of_injective _ (@Subtype.val_injective E bad)]
      apply card_le_card
      intro e he
      obtain ⟨g, hg, rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hg).2⟩,
        g.property⟩
    exact hinc.trans htail.le
  let Fres : EB → Finset B := fun e ↦ univ.filter fun b ↦ Sum.inr b ∈ F e.val
  have hFres : ∀ e : EB, (Fres e).card ≤ f := by
    intro e
    exact (card_filter_injective_preimage_le Sum.inr Sum.inr_injective (F e.val)).trans
      (hF e.val)
  have hBpos : 0 < Fintype.card B := (Nat.zero_le _).trans_lt hreserve
  have : Nonempty B := Fintype.card_pos_iff.mp hBpos
  have hsize : ∀ e : EB,
      (univ.filter (HB.conflictGraph.Adj e)).card + (Fres e).card < Fintype.card B := by
    intro e
    have hconf : HB.conflictDegree e ≤ r * s :=
      (HB.conflictDegree_le_card_mul hdeg e).trans (Nat.mul_le_mul_right s (hbound e.val))
    exact (Nat.add_le_add hconf (hFres e)).trans_lt hreserve
  obtain ⟨bcolor, hbcolor⟩ := exists_coloring_avoiding_of_degree_add_forbidden_lt
    HB.conflictGraph Fres hsize
  let paint : E → A ⊕ B := fun e ↦
    if he : bad e then Sum.inr (bcolor ⟨e, he⟩) else Sum.inl (p (c e))
  have hproper : ∀ {e g : E}, H.Conflicts e g → paint e ≠ paint g := by
    intro e g heg
    by_cases he : bad e
    · by_cases hg : bad g
      · have hconf : HB.Conflicts ⟨e, he⟩ ⟨g, hg⟩ :=
          ⟨fun h ↦ heg.1 (congrArg Subtype.val h), heg.2⟩
        simpa only [paint, dif_pos he, dif_pos hg, ne_eq, Sum.inr.injEq] using
          bcolor.valid hconf
      · simp only [paint, dif_pos he, dif_neg hg, ne_eq, reduceCtorEq, not_false_eq_true]
    · by_cases hg : bad g
      · simp only [paint, dif_neg he, dif_pos hg, ne_eq, reduceCtorEq, not_false_eq_true]
      · have hne : p (c e) ≠ p (c g) := fun h ↦ c.valid heg (p.injective h)
        simpa only [paint, dif_neg he, dif_neg hg, ne_eq, Sum.inl.injEq] using hne
  refine ⟨SimpleGraph.Coloring.mk paint hproper, ?_⟩
  intro e
  change paint e ∉ F e
  by_cases he : bad e
  · have h := hbcolor ⟨e, he⟩
    simpa only [Fres, mem_filter, mem_univ, true_and, paint, dif_pos he] using h
  · simpa only [paint, dif_neg he] using he

/-- The disjoint palettes may be embedded into any sufficiently large target
palette. All forbidden sets are interpreted in that target palette. -/
theorem exists_edgeColoring_avoiding_sparse_palette {V E P : Type*}
    [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (H : FiniteHypergraph V E) (r f s q : ℕ) (hbound : H.IsBounded r)
    (c : H.EdgeColoring q) (F : E → Finset P) (hF : ∀ e, (F e).card ≤ f)
    (hsmall : H.vertexSet.card * f ^ s < s.factorial)
    (hpalette : q + (r * s + f + 1) ≤ Fintype.card P) :
    ∃ d : H.conflictGraph.Coloring P, ∀ e, d e ∉ F e := by
  classical
  let t := r * s + f + 1
  have hjcard : Fintype.card (Fin q ⊕ Fin t) ≤ Fintype.card P := by
    simpa only [Fintype.card_sum, Fintype.card_fin, t] using hpalette
  obtain ⟨j : (Fin q ⊕ Fin t) ↪ P⟩ := Function.Embedding.nonempty_of_card_le hjcard
  let F' : E → Finset (Fin q ⊕ Fin t) := fun e ↦ univ.filter fun a ↦ j a ∈ F e
  have hF' : ∀ e, (F' e).card ≤ f := fun e ↦
    (card_filter_injective_preimage_le j j.injective (F e)).trans (hF e)
  obtain ⟨d, hd⟩ := exists_edgeColoring_avoiding_sparse H r f s hbound c F' hF' hsmall
    (by simpa only [Fintype.card_fin, t] using Nat.lt_succ_self (r * s + f))
  refine ⟨SimpleGraph.Coloring.mk (fun e ↦ j (d e))
    (fun {e g} h heq ↦ d.valid h (j.injective heq)), ?_⟩
  intro e
  change j (d e) ∉ F e
  simpa only [F', mem_filter, mem_univ, true_and] using hd e

#print axioms exists_edgeColoring_avoiding_sparse
#print axioms exists_edgeColoring_avoiding_sparse_palette

end Erdos19
