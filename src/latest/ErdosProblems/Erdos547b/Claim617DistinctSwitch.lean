/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma611Full

/-!
# A Claim-6.17 switch on distinct original matching edges

Heavy vertices are first thinned on their incident edge set. The subsequent
Hall injection therefore frees one distinct old partner per new edge.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoClaim617DistinctSwitch

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable (M : R.Subgraph) (L : Finset K)

def incidentEdges (H : Finset K) : Finset (MatchingEdge M) :=
  (allMatchingEdges M).filter fun e => ∃ c : Fin 2, orientedEndpoint M L e c ∈ H

theorem card_le_twice_incidentEdges (hM : M.IsMatching) (H : Finset K)
    (hH : H ⊆ matchingSupport M) : H.card ≤ 2 * (incidentEdges M L H).card := by
  have hsub : H ⊆ matchingSupport (edgeFinsetSubgraph M L (incidentEdges M L H)) := by
    intro x hx
    obtain ⟨y, hxy, _⟩ := hM ((mem_matchingSupport M x).mp (hH hx))
    let e : MatchingEdge M := ⟨s(x, y), hxy⟩
    have hxEnds : x = orientedEndpoint M L e 0 ∨ x = orientedEndpoint M L e 1 := by
      have hmem : x ∈ (e.1 : Sym2 K) := Sym2.mem_mk_left x y
      rw [← orientedEndpoint_pair_eq M L e] at hmem
      simpa using hmem
    have he : e ∈ incidentEdges M L H := by
      apply Finset.mem_filter.mpr
      refine ⟨mem_allMatchingEdges M e, ?_⟩
      rcases hxEnds with h | h
      · exact ⟨0, h ▸ hx⟩
      · exact ⟨1, h ▸ hx⟩
    exact (mem_matchingSupport _ x).mpr ⟨e, he, hxEnds⟩
  exact (Finset.card_le_card hsub).trans_eq (edgeFinsetSubgraph_support_card M hM L _)

structure DistinctSwitch (S W : Finset K) (m : ℕ) where
  edges : Finset (MatchingEdge M)
  card_edges : edges.card = m
  side : {e // e ∈ edges} → Fin 2
  source_mem : ∀ e, orientedEndpoint M L e.1 (side e) ∈ S
  target : {e // e ∈ edges} → K
  target_mem : ∀ e, target e ∈ W
  target_injective : Function.Injective target
  adjacent : ∀ e, R.Adj (orientedEndpoint M L e.1 (side e)) (target e)

theorem exists_distinctSwitch_of_many_heavy (hM : M.IsMatching)
    (S W : Finset K) (m : ℕ) (hS : S ⊆ matchingSupport M)
    (hmany : 2 * m ≤ (Erdos547EC2.crossHeavy R S W m).card) :
    Nonempty (DistinctSwitch M L S W m) := by
  let H := Erdos547EC2.crossHeavy R S W m
  have hH : H ⊆ matchingSupport M := (Erdos547EC2.crossHeavy_subset R S W m).trans hS
  have hcount := card_le_twice_incidentEdges M L hM H hH
  change 2 * m ≤ H.card at hmany
  have hm : m ≤ (incidentEdges M L H).card := by omega
  obtain ⟨E, hE, hEcard⟩ := Finset.exists_subset_card_eq hm
  have hside : ∀ e : {e // e ∈ E}, ∃ c : Fin 2, orientedEndpoint M L e.1 c ∈ H := by
    intro e
    exact (Finset.mem_filter.mp (hE e.2)).2
  let side : {e // e ∈ E} → Fin 2 := fun e => Classical.choose (hside e)
  have hs (e : {e // e ∈ E}) : orientedEndpoint M L e.1 (side e) ∈ H :=
    Classical.choose_spec (hside e)
  let choices : {e // e ∈ E} → Finset K := fun e =>
    W.filter (R.Adj (orientedEndpoint M L e.1 (side e)))
  have hc (e : {e // e ∈ E}) : m ≤ (choices e).card :=
    (Finset.mem_filter.mp (hs e)).2
  have hHall : ∀ A : Finset {e // e ∈ E}, A.card ≤ (A.biUnion choices).card := by
    intro A
    by_cases hA : A = ∅
    · simp only [hA, Finset.card_empty, Nat.zero_le]
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      calc
        A.card ≤ Fintype.card {e // e ∈ E} := Finset.card_le_univ _
        _ = m := (Fintype.card_coe E).trans hEcard
        _ ≤ (choices e).card := hc e
        _ ≤ (A.biUnion choices).card := Finset.card_le_card (Finset.subset_biUnion_of_mem choices he)
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  exact ⟨{ edges := E
           card_edges := hEcard
           side := side
           source_mem := fun e => (Finset.mem_filter.mp (hs e)).1
           target := f
           target_mem := fun e => (Finset.mem_filter.mp (hfmem e)).1
           target_injective := hfinj
           adjacent := fun e => (Finset.mem_filter.mp (hfmem e)).2 }⟩

namespace DistinctSwitch

variable {M L} {S W : Finset K} {m : ℕ} (D : DistinctSwitch M L S W m)

def source (e : {e // e ∈ D.edges}) : K := orientedEndpoint M L e.1 (D.side e)

def partner (e : {e // e ∈ D.edges}) : K :=
  orientedEndpoint M L e.1 (if D.side e = 0 then 1 else 0)

theorem source_injective (hM : M.IsMatching) : Function.Injective D.source := by
  intro e f h
  change orientedEndpoint M L e.1 (D.side e) = orientedEndpoint M L f.1 (D.side f) at h
  have hpair : (e.1, D.side e) = (f.1, D.side f) := orientedEndpoint_injective M hM L h
  exact Subtype.ext (congrArg Prod.fst hpair)

theorem partner_injective (hM : M.IsMatching) : Function.Injective D.partner := by
  intro e f h
  change orientedEndpoint M L e.1 (if D.side e = 0 then 1 else 0) =
    orientedEndpoint M L f.1 (if D.side f = 0 then 1 else 0) at h
  have hpair : (e.1, if D.side e = 0 then (1 : Fin 2) else 0) =
      (f.1, if D.side f = 0 then 1 else 0) := orientedEndpoint_injective M hM L h
  exact Subtype.ext (congrArg Prod.fst hpair)

theorem source_partner_adj (e : {e // e ∈ D.edges}) : M.Adj (D.source e) (D.partner e) := by
  unfold source partner
  generalize D.side e = c
  fin_cases c
  · simpa using orientedEndpoint_adj M L e.1
  · simpa using (orientedEndpoint_adj M L e.1).symm

theorem source_ne_partner (hM : M.IsMatching) (e f : {e // e ∈ D.edges}) :
    D.source e ≠ D.partner f := by
  intro h
  have heq : (e.1, D.side e) = (f.1, if D.side f = 0 then 1 else 0) :=
    orientedEndpoint_injective M hM L h
  have hef : e = f := Subtype.ext (congrArg Prod.fst heq)
  subst f
  exact (D.source_partner_adj e).ne h

theorem partner_mem_large (hM : M.IsMatching) (hS : S ⊆ sourceS1 M L)
    (e : {e // e ∈ D.edges}) : D.partner e ∈ L := by
  obtain ⟨x, hx, hxadj⟩ := (Finset.mem_filter.mp (hS (D.source_mem e))).2
  have heq : D.partner e = x := hM.eq_of_adj_left (D.source_partner_adj e) hxadj.symm
  exact heq ▸ hx

end DistinctSwitch

end Erdos547b.ZhaoClaim617DistinctSwitch

#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.exists_distinctSwitch_of_many_heavy
#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch.partner_mem_large
