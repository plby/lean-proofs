/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawSignedFreshness

/-!
# Exact balance of a fresh signed word

This calculation permits repeated physical vertices. Same-colour edge
freshness and biuniqueness make edge-set indicators agree with the list
sum, and signed continuity telescopes that sum to the two endpoints.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u

variable {V : Type u}

private theorem edgeBalance_empty (x : V) : edgeBalance (∅ : Set (V × V)) x = 0 := by
  simp [edgeBalance, HasOutgoing, HasIncoming, propInt]

private theorem edgeBalance_singleton (e : V × V) (x : V) :
    edgeBalance {e} x = propInt (x = e.1) - propInt (x = e.2) := by
  rcases e with ⟨a, b⟩
  simp [edgeBalance, HasOutgoing, HasIncoming, Prod.mk.injEq]

private theorem biUnique_subset {E F : Set (V × V)} (hEF : E ⊆ F)
    (hF : Relator.BiUnique (fun x y ↦ (x, y) ∈ F)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
  ⟨fun _ _ _ h₁ h₂ ↦ hF.1 (hEF h₁) (hEF h₂),
    fun _ _ _ h₁ h₂ ↦ hF.2 (hEF h₁) (hEF h₂)⟩

/-- A fresh single edge adds its literal endpoint indicators to a
biunique relation. -/
private theorem edgeBalance_insert_of_fresh {E : Set (V × V)} {e : V × V}
    (hfresh : e ∉ E)
    (hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ ({e} ∪ E))) (x : V) :
    edgeBalance ({e} ∪ E) x =
      edgeBalance E x + propInt (x = e.1) - propInt (x = e.2) := by
  have hE := biUnique_subset (show E ⊆ {e} ∪ E from Set.subset_union_right) hbi
  have hrev : Relator.BiUnique (fun x y ↦ (x, y) ∈ E ∪ {e}) := by
    simpa only [Set.union_comm] using hbi
  have hdisj : Disjoint (E \ ∅) {e} := by
    apply Set.disjoint_left.2
    intro f hf hfe
    have hfe' : f = e := Set.mem_singleton_iff.1 hfe
    exact hfresh (hfe' ▸ hf.1)
  have hcalc := edgeBalance_sdiff_union_eq_add_sub
    (E := E) (B := ∅) (F := {e}) (Set.empty_subset E) hE.2 hE.1
    (by simpa only [Set.sdiff_empty] using hrev.2)
    (by simpa only [Set.sdiff_empty] using hrev.1) hdisj x
  have hcalc' : edgeBalance ({e} ∪ E) x =
      edgeBalance E x + edgeBalance {e} x := by
    simpa only [Set.sdiff_empty, Set.union_comm, edgeBalance_empty, sub_zero] using hcalc
  rw [hcalc', edgeBalance_singleton]
  omega

private theorem signedEdge_eq_of_edge_direction {s t : SignedEdge V}
    (he : s.edge = t.edge) (hd : s.direction = t.direction) : s = t := by
  cases s
  cases t
  cases he
  cases hd
  rfl

private theorem directedSignedEdgeSet_tail_subset (d : Direction)
    (s : SignedEdge V) (q : List (SignedEdge V)) :
    directedSignedEdgeSet d q ⊆ directedSignedEdgeSet d (s :: q) := by
  rintro e ⟨t, ht, hd, he⟩
  exact ⟨t, List.mem_cons_of_mem s ht, hd, he⟩

/-- Exact edge-set balance of a fresh finite signed list. -/
theorem signedList_edgeBalance_eq_sum
    (q : List (SignedEdge V)) (hq : q.Nodup)
    (hF : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ directedSignedEdgeSet .forward q))
    (hB : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ directedSignedEdgeSet .backward q)) (x : V) :
    edgeBalance (directedSignedEdgeSet .forward q) x -
      edgeBalance (directedSignedEdgeSet .backward q) x =
    (q.map (fun s ↦ propInt (x = s.entry) - propInt (x = s.exit))).sum := by
  induction q with
  | nil => simp [edgeBalance_empty]
  | cons s q ih =>
      obtain ⟨hfresh, hq⟩ := List.nodup_cons.1 hq
      have hFq := biUnique_subset (directedSignedEdgeSet_tail_subset .forward s q) hF
      have hBq := biUnique_subset (directedSignedEdgeSet_tail_subset .backward s q) hB
      have hsum := ih hq hFq hBq
      simp only [SignedEdge.entry, SignedEdge.exit] at hsum
      have hnot : s.edge ∉ directedSignedEdgeSet s.direction q := by
        rintro ⟨t, ht, hd, he⟩
        have hts : t = s := signedEdge_eq_of_edge_direction he hd
        exact hfresh (hts ▸ ht)
      cases hdir : s.direction with
      | forward =>
          have hbi : Relator.BiUnique
              (fun a b ↦ (a, b) ∈ {s.edge} ∪ directedSignedEdgeSet .forward q) := by
            simpa only [directedSignedEdgeSet_cons, hdir, if_pos] using hF
          have hadd := edgeBalance_insert_of_fresh (hdir ▸ hnot) hbi x
          simp only [directedSignedEdgeSet_cons, hdir, reduceCtorEq, ↓reduceIte,
            Set.empty_union, List.map_cons, List.sum_cons, SignedEdge.entry, SignedEdge.exit]
          rw [hadd]
          omega
      | backward =>
          have hbi : Relator.BiUnique
              (fun a b ↦ (a, b) ∈ {s.edge} ∪ directedSignedEdgeSet .backward q) := by
            simpa only [directedSignedEdgeSet_cons, hdir, if_pos] using hB
          have hadd := edgeBalance_insert_of_fresh (hdir ▸ hnot) hbi x
          simp only [directedSignedEdgeSet_cons, hdir, reduceCtorEq, ↓reduceIte,
            Set.empty_union, List.map_cons, List.sum_cons, SignedEdge.entry, SignedEdge.exit]
          rw [hadd]
          omega

/-- Traversal continuity telescopes the signed list sum, including when
an original vertex occurs several times. -/
theorem RunsFromTo.sum_endpoint_balance {a b : V} {q : List (SignedEdge V)}
    (h : RunsFromTo a b q) (x : V) :
    (q.map (fun s ↦ propInt (x = s.entry) - propInt (x = s.exit))).sum =
      propInt (x = a) - propInt (x = b) := by
  induction h with
  | nil a => simp
  | @cons s b q h ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- The exact endpoint balance of a fresh, colourwise biunique signed
route. No injectivity of the original vertex sequence is assumed. -/
theorem RunsFromTo.edgeBalance_forward_sub_backward
    {a b : V} {q : List (SignedEdge V)} (h : RunsFromTo a b q)
    (hq : q.Nodup)
    (hF : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ directedSignedEdgeSet .forward q))
    (hB : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ directedSignedEdgeSet .backward q)) (x : V) :
    edgeBalance (directedSignedEdgeSet .forward q) x -
      edgeBalance (directedSignedEdgeSet .backward q) x =
      propInt (x = a) - propInt (x = b) := by
  rw [signedList_edgeBalance_eq_sum q hq hF hB]
  exact h.sum_endpoint_balance x

end PopularAuxiliary.Input
end Erdos599

#print axioms Erdos599.PopularAuxiliary.Input.signedList_edgeBalance_eq_sum
#print axioms Erdos599.PopularAuxiliary.Input.RunsFromTo.edgeBalance_forward_sub_backward
