/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import ErdosProblems.Erdos622.External.Erdos570.Increasing
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic

/-!
# Bondy--Chvátal theorem

This is the proved Mathlib development by Shuhao Song from commit
`c83689ab8f` of the `meow-sister/BondyChvatal_PR` branch, vendored here
because the theorem is not part of the Mathlib v4.33.0 module set.
-/

namespace SimpleGraph

open Classical Walk Function
open scoped List
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

local notation "‖" X "‖" => Fintype.card X

def closureNewEdges :=
  { (u, v) : V × V | G.degree u + G.degree v ≥ ‖V‖ ∧ u ≠ v ∧ ¬G.Adj u v }

noncomputable def closureStep : SimpleGraph V :=
  if h : (closureNewEdges G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G

lemma self_le_closureStep : G ≤ closureStep G := by
  unfold closureStep
  split_ifs with h
  repeat simp

noncomputable def closure := Function.eventualValue self_le_closureStep G

lemma closureStep_diff_atmost_one : (closureStep G \ G).edgeSet.Subsingleton := by
  unfold closureStep
  split_ifs with h
  · simp only [sup_sdiff_left_self, edgeSet_sdiff]
    apply Set.Subsingleton.anti (t := (edge h.some.1 h.some.2).edgeSet)
    · have : h.some.1 ≠ h.some.2 := h.some_mem.2.1
      simp [edge_edgeSet_of_ne this]
    · apply Set.diff_subset
  · simp

lemma closureStep_deleteEdge {u v : V} (huv : ¬G.Adj u v)
    (huv' : G.closureStep.Adj u v) :
    G.closureStep.deleteEdges {s(u, v)} = G := by
  rw [← edgeSet_inj]
  ext e
  simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
  apply Iff.intro
  · rintro ⟨he₁, he₂⟩
    by_contra he₃
    have mem₁ : e ∈ (closureStep G \ G).edgeSet := by simpa using ⟨he₁, he₃⟩
    have mem₂ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simpa using ⟨huv', huv⟩
    exact he₂ <| (closureStep_diff_atmost_one G) mem₁ mem₂
  · intro he
    apply And.intro (edgeSet_mono (self_le_closureStep G) he)
    intro he'
    simp only [he', mem_edgeSet] at he
    exact huv he

lemma closureStep_eq_iff' : closureStep G = G ↔ closureNewEdges G = ∅ := by
  unfold closureStep
  split_ifs with h
  · have : (G ⊔ edge h.some.1 h.some.2 = G) ↔ False := by
      rw [sup_eq_left, iff_false]
      intro hle
      have hedge : (edge h.some.1 h.some.2).Adj h.some.1 h.some.2 :=
        (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, h.some_mem.2.1⟩
      exact h.some_mem.2.2 (hle hedge)
    simp only [this, false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h

lemma closureStep_eq_iff : closureStep G = G ↔
    ∀ {u} {v}, u ≠ v → G.degree u + G.degree v ≥ ‖V‖ → G.Adj u v := by
  rw [closureStep_eq_iff']
  constructor
  · intro hempty u v huv hdeg
    by_contra hadj
    have hmem : (u, v) ∈ closureNewEdges G := ⟨hdeg, huv, hadj⟩
    rw [hempty] at hmem
    exact hmem
  · intro h
    ext ⟨u, v⟩
    constructor
    · intro huv
      exact (huv.2.2 (h huv.2.1 huv.1)).elim
    · intro hfalse
      exact hfalse.elim

lemma closureStep_deg_sum {u v : V} (huv : ¬G.Adj u v)
    (huv' : G.closureStep.Adj u v) :
    G.degree u + G.degree v ≥ ‖V‖ := by
  have ne : (closureNewEdges G).Nonempty := by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty, ← closureStep_eq_iff', Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w := ne.some
  have prop₁ : G.degree w.1 + G.degree w.2 ≥ ‖V‖ := ne.some_mem.1
  have mem₁ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simpa using ⟨huv', huv⟩
  have mem₂ : s(w.1, w.2) ∈ (closureStep G \ G).edgeSet := by
    have prop₂ : w.1 ≠ w.2 := ne.some_mem.2.1
    have prop₃ : ¬G.Adj w.1 w.2 := ne.some_mem.2.2
    have G_eq : G.closureStep = G ⊔ edge w.1 w.2 := by simp [closureStep, ne, w]
    simpa [-Prod.mk.eta, G_eq, edge_adj] using And.intro prop₂ prop₃
  have edge_eq := (closureStep_diff_atmost_one G mem₁ mem₂).symm
  simp only [Prod.mk.eta, Sym2.eq, Sym2.rel_iff'] at edge_eq
  cases' edge_eq with h h
  · rw [h] at prop₁
    simpa using prop₁
  · rw [h] at prop₁
    rw [add_comm]
    simpa using prop₁

lemma self_le_closure : G ≤ closure G := by
  rw [closure]
  apply Function.self_le_eventualValue

lemma closure_spec : ∀ {u} {v}, u ≠ v →
    G.closure.degree u + G.closure.degree v ≥ ‖V‖ → G.closure.Adj u v := by
  have : closureStep (closure G) = closure G := isFixedPt_eventualValue self_le_closureStep G
  rwa [closureStep_eq_iff] at this

variable {G}

namespace Walk

variable {a : V} {p : G.Walk a a}

protected theorem IsHamiltonianCycle.transfer (hp : p.IsHamiltonianCycle)
    {H : SimpleGraph V} (h : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (p.transfer H h).IsHamiltonianCycle := by
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hp.isCycle.transfer h, by simpa using hp.length_eq⟩

private lemma IsCycle.dart_eq_of_fst_eq (hp : p.IsCycle)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (hfst : d.fst = e.fst) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hget : p.getVert i = p.getVert j := by
    simpa [p.darts_getElem_eq_getVert i hi, p.darts_getElem_eq_getVert j hj] using hfst
  have hi' : i ≤ p.length - 1 := by
    have hi_len : i < p.length := by simpa using hi
    omega
  have hj' : j ≤ p.length - 1 := by
    have hj_len : j < p.length := by simpa using hj
    omega
  have hij := hp.getVert_injOn' hi' hj' hget
  subst j
  rfl

private lemma IsCycle.dart_eq_of_snd_eq (hp : p.IsCycle)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (hsnd : d.snd = e.snd) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hget : p.getVert (i + 1) = p.getVert (j + 1) := by
    simpa [p.darts_getElem_eq_getVert i hi, p.darts_getElem_eq_getVert j hj] using hsnd
  have hi' : i < p.length := by simpa using hi
  have hj' : j < p.length := by simpa using hj
  have hij := hp.getVert_injOn
    (show 1 ≤ i + 1 ∧ i + 1 ≤ p.length by omega)
    (show 1 ≤ j + 1 ∧ j + 1 ≤ p.length by omega) hget
  have : i = j := Nat.add_right_cancel hij
  subst j
  rfl

private lemma dart_eq_of_fst_eq_of_nodup_dropLast {u v : V}
    {r : G.Walk u v} (hnodup : r.support.dropLast.Nodup)
    {d e : G.Dart} (hd : d ∈ r.darts) (he : e ∈ r.darts)
    (hfst : d.fst = e.fst) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hi' : i < r.support.dropLast.length := by simpa using hi
  have hj' : j < r.support.dropLast.length := by simpa using hj
  have hget : r.support.dropLast[i]'hi' = r.support.dropLast[j]'hj' := by
    simpa [r.fst_darts_getElem hi, r.fst_darts_getElem hj] using hfst
  have hij := (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl

private theorem isHamiltonianCycle_of_length_and_tail_toFinset
    (hp : p.length = Fintype.card V) (hV : 3 ≤ Fintype.card V)
    (hsupport : p.support.tail.toFinset = Finset.univ) :
    p.IsHamiltonianCycle := by
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, hp⟩
  rw [isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by omega⟩
  apply IsPath.mk'
  rw [support_tail_of_not_nil p (by rw [not_nil_iff_lt_length, hp]; omega)]
  have hcard : p.support.tail.toFinset.card = p.support.tail.length := by
    rw [hsupport]
    simp [hp]
  have hmulti : ((p.support.tail : Multiset V).toFinset.card =
      (p.support.tail : Multiset V).card) := by simpa using hcard
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp hmulti

namespace IsHamiltonianCycle

variable (b : V)

private lemma mem_tail_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.tail := by
  rw [← support_tail_of_not_nil p hp.not_nil]
  exact hp.isHamiltonian_tail.mem_support b

private lemma mem_dropLast_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.dropLast := by
  have hb : b ∈ p.tail.support := by
    simpa [support_tail_of_not_nil p hp.not_nil] using hp.mem_tail_support b
  have hb' : b ∈ p.dropLast.support :=
    (List.Perm.mem_iff (support_tail_perm_support_dropLast p)).mp hb
  simpa [support_dropLast hp.not_nil] using hb'

noncomputable def dartWithFst (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃ d ∈ p.darts, d.fst = b by
    simpa [← Walk.map_fst_darts] using hp.mem_dropLast_support b

noncomputable def next (hp : p.IsHamiltonianCycle) : V :=
  (hp.dartWithFst b).snd

lemma self_next_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = b ∧ d.snd = hp.next b := by
  unfold next dartWithFst
  generalize_proofs hd
  have hspec := hd.choose_spec
  set d := hd.choose
  exact ⟨d, hspec.1, hspec.2, rfl⟩

lemma next_inj (hp : p.IsHamiltonianCycle) : Function.Injective hp.next := by
  intro v₁ v₂ hnext
  obtain ⟨d₁, hd₁, hd₁fst, hd₁snd⟩ := hp.self_next_in_darts v₁
  obtain ⟨d₂, hd₂, hd₂fst, hd₂snd⟩ := hp.self_next_in_darts v₂
  have heq : d₁ = d₂ := hp.isCycle.dart_eq_of_snd_eq hd₁ hd₂ <| by
    rw [hd₁snd, hd₂snd]
    exact hnext
  rw [← hd₁fst, ← hd₂fst, heq]

lemma getVert_succ_eq_next (hp : p.IsHamiltonianCycle)
    {i : ℕ} (hi : i < p.length) (hi' : p.getVert i = b) :
    p.getVert (i + 1) = hp.next b := by
  have hiD : i < p.darts.length := by simpa using hi
  have hdi : p.darts[i] ∈ p.darts := List.getElem_mem hiD
  obtain ⟨d, hd, hdfst, hdsnd⟩ := hp.self_next_in_darts b
  have hfst : p.darts[i].fst = d.fst := by
    rw [p.darts_getElem_eq_getVert i hiD, hdfst]
    exact hi'
  have heq := hp.isCycle.dart_eq_of_fst_eq hdi hd hfst
  have hsnd := congrArg (fun z : G.Dart ↦ z.snd) heq
  rw [p.darts_getElem_eq_getVert i hiD, hdsnd] at hsnd
  exact hsnd

lemma rotate_next (hp : p.IsHamiltonianCycle) (hb : b ∈ p.support) (c : V) :
    ((hp.rotate hb).next c) = hp.next c := by
  obtain ⟨d₁, hd₁, hd₁fst, hd₁snd⟩ := (hp.rotate hb).self_next_in_darts c
  obtain ⟨d₂, hd₂, hd₂fst, hd₂snd⟩ := hp.self_next_in_darts c
  have hd₁' : d₁ ∈ p.darts := by
    simpa using (List.IsRotated.mem_iff (rotate_darts p b hb)).mp hd₁
  have heq : d₁ = d₂ := hp.isCycle.dart_eq_of_fst_eq hd₁' hd₂ <| by
    rw [hd₁fst, hd₂fst]
  rw [← hd₁snd, ← hd₂snd, heq]

variable {b}

theorem next_ne (hp : p.IsHamiltonianCycle) : hp.next b ≠ b := by
  obtain ⟨d, -, hdfst, hdsnd⟩ := hp.self_next_in_darts b
  intro h
  exact d.adj.ne (hdfst.trans (hdsnd.trans h).symm)

theorem next_next_ne (hp : p.IsHamiltonianCycle) : hp.next (hp.next b) ≠ b := by
  have hb : b ∈ p.support := hp.mem_support b
  let q := p.rotate b hb
  have hq : q.IsHamiltonianCycle := hp.rotate hb
  have hlen : 3 ≤ q.length := hq.isCycle.three_le_length
  have hq0 : q.getVert 0 = b := by simp [q]
  have hq1 : q.getVert 1 = hq.next b :=
    hq.getVert_succ_eq_next b (i := 0) (by omega) hq0
  have hq2 : q.getVert 2 = hq.next (hq.next b) :=
    hq.getVert_succ_eq_next (hq.next b) (i := 1) (by omega) hq1
  have hrot : ∀ c, hq.next c = hp.next c := by
    intro c
    change (hp.rotate hb).next c = hp.next c
    exact IsHamiltonianCycle.rotate_next b hp hb c
  simp only [hrot] at hq1 hq2
  intro h
  have h02 : q.getVert 0 = q.getVert 2 := by rw [hq0, hq2, h]
  have := hq.isCycle.getVert_injOn'
    (show 0 ≤ q.length - 1 by omega)
    (show 2 ≤ q.length - 1 by omega) h02
  omega

end IsHamiltonianCycle

end Walk

private theorem from_ClosureStep_aux
    {u u' v v' : V} {p : G.Walk u u'}
    (hV : ‖V‖ ≥ 3) (hp : p.support ~ Finset.univ.toList)
    (ne : v ≠ u') (vu' : G.Adj v u') (v'u : G.Adj v' u)
    (d : G.Dart) (hd : d ∈ p.darts) (hd₁ : d.fst = v) (hd₂ : d.snd = v') :
    IsHamiltonian G := by
  have hv : v ∈ p.support := by simp [List.Perm.mem_iff hp]
  have not_nil : ¬(p.dropUntil v hv).Nil := not_nil_of_ne ne
  have snd_eq_v' : (p.dropUntil v hv).getVert 1 = v' := by
    have hsupport : p.support.Nodup := by
      rw [List.Perm.nodup_iff hp]
      apply Finset.nodup_toList
    have hdrop : p.support.dropLast.Nodup := p.support.dropLast_prefix.nodup hsupport
    have hfirst : (p.dropUntil v hv).firstDart not_nil ∈ p.darts :=
      p.darts_dropUntil_subset_darts hv
        ((p.dropUntil v hv).firstDart_mem_darts not_nil)
    have heq : (p.dropUntil v hv).firstDart not_nil = d :=
      dart_eq_of_fst_eq_of_nodup_dropLast hdrop hfirst hd (by simp [hd₁])
    have hsnd := congrArg (fun z : G.Dart ↦ z.snd) heq
    simpa [hd₂] using hsnd
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ ↦ ⟨u, q, this⟩
  apply isHamiltonianCycle_of_length_and_tail_toFinset
  · have hsum : (p.takeUntil v hv).length + (p.dropUntil v hv).length = p.length := by
      have hwalk := congrArg Walk.length (p.take_spec hv)
      simpa only [Walk.length_append] using hwalk
    have := calc
      p.length + 1 = p.support.length := by simp
      _ = Finset.univ.toList.length := by apply List.Perm.length_eq hp
      _ = ‖V‖ := by simp
    have := Walk.length_tail_add_one not_nil
    simp [q, add_assoc]
    omega
  · assumption
  · simp only [tail_support_append, support_cons, support_nil, List.tail_cons, support_copy,
      support_reverse, List.tails_reverse, List.append_assoc, List.singleton_append,
      List.cons_append, List.toFinset_append, List.toFinset_cons, List.toFinset_reverse,
      List.toFinset_nil, insert_empty_eq, Finset.union_insert, Finset.eq_univ_iff_forall,
      Finset.mem_insert, Finset.mem_union, List.mem_toFinset, Finset.mem_singleton,
      Finset.notMem_empty, false_or, q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁, hw₂, hw₃, hw₄⟩
    have mem_tail : w ∈ p.support.tail := by
      have mem : w ∈ p.support := by simp [List.Perm.mem_iff hp]
      rw [Walk.support_eq_cons] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop : w ∉ (p.dropUntil v hv).support.tail := by
      have tail_not_nil : (p.dropUntil v hv).support.tail ≠ [] := by
        have hpos : 0 < (p.dropUntil v hv).length :=
          not_nil_iff_lt_length.mp not_nil
        apply List.ne_nil_of_length_pos
        rw [List.length_tail, length_support]
        omega
      have : (p.dropUntil v hv).support.tail.getLast tail_not_nil = u' := by
        rw [List.getLast_tail, getLast_support]
      have hw_dropLast :
          w ∉ (p.dropUntil v hv).support.tail.dropLast := by
        simpa only [List.tail_reverse, List.mem_reverse,
          support_tail_of_not_nil _ not_nil] using hw₃
      intro hwmem
      rw [← List.dropLast_append_getLast tail_not_nil, this,
        List.mem_append, List.mem_singleton] at hwmem
      exact hwmem.elim hw_dropLast hw₁
    have append : p.support.tail =
        (p.takeUntil v hv).support.tail ++ (p.dropUntil v hv).support.tail := by
      rw [← tail_support_append, take_spec]
    simp only [append, List.mem_append] at mem_tail
    cases' mem_tail with h h
    exact hw₂ h
    exact not_mem_drop h

private theorem from_ClosureStep_aux'
    {u v : V} {q : G.closureStep.Walk u u} (hq : q.IsHamiltonianCycle)
    (hV : ‖V‖ ≥ 3) (huv : G.degree u + G.degree v ≥ ‖V‖)
    (hv : v = hq.next u) (not_adj : ¬G.Adj u v) :
    ∃ w w' d, G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst = w' ∧ d.snd = w := by
  let X := (hq.next ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.next v}
  have cardX : G.degree u - 1 ≤ X.toFinset.card := calc
    _ = (G.neighborFinset u).card - 1 := by simp
    _ = (Finset.univ.filter (G.Adj u)).card - 1 := by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.next ·)).card - ({u} : Finset _).card := by
      simp [Finset.card_image_of_injective _ hq.next_inj]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.next ·)) \ {u}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [X]
  have cardY : G.degree v - 1 ≤ Y.toFinset.card := calc
    _ = (G.neighborFinset v).card - 1 := by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card - ({hq.next v} : Finset _).card := by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.next v}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [Y]
  have card_union : (X ∪ Y).toFinset.card ≤ ‖V‖ - 3 := calc
    _ ≤ ({v, hq.next v, u}ᶜ : Finset _).card := by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq, Set.toFinset_union,
        Set.toFinset_diff, Set.toFinset_image, Set.toFinset_setOf, Set.toFinset_singleton,
        Finset.compl_union, Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        Decidable.not_not, forall_exists_index, and_imp, X, Y] at hw ⊢
      apply And.intro
      · intro w' adj next
        rcases hw with hw | hw | hw
        · rw [hw, hv] at next
          rw [hq.next_inj next] at adj
          simp at adj
        · rw [hw] at next
          rw [hq.next_inj next] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _ = _ := by
      suffices ({v, hq.next v, u} : Finset _).card = 3 by rw [Finset.card_compl, this]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
      · simp
      · simpa [hv] using hq.next_next_ne
      · simpa [hv] using And.intro hq.next_ne.symm hq.next_ne
  have non_empty : (X ∩ Y).toFinset.card ≠ 0 := fun h ↦ by
    suffices ‖V‖ - 2 ≤ ‖V‖ - 3 by omega
    calc
      _ ≤ (G.degree u + G.degree v) - 2 := Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u - 1) + (G.degree v - 1) := by omega
      _ ≤ X.toFinset.card + Y.toFinset.card := add_le_add cardX cardY
      _ = (X ∪ Y).toFinset.card + (X ∩ Y).toFinset.card := by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ ‖V‖ - 3 + 0 := add_le_add card_union (le_of_eq h)
      _ = ‖V‖ - 3 := by simp
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp non_empty
  simp only [Set.mem_setOf_eq, Set.toFinset_inter, Set.toFinset_diff, Set.toFinset_image,
    Set.toFinset_setOf, Set.toFinset_singleton, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    X, Y] at hw
  rcases hw with ⟨⟨⟨w', hw'₁, hw'₂⟩, -⟩, hw₂, -⟩
  obtain ⟨d, hd₁, hd₂⟩ := hq.self_next_in_darts w'
  rw [hw'₂] at hd₂
  exact ⟨w, w', d, hw₂.symm, hw'₁.symm, hd₁, hd₂⟩

theorem from_ClosureStep (hG : IsHamiltonian (closureStep G)) : IsHamiltonian G := by
  by_cases trivial : Fintype.card V = 1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a, p, hp⟩ := hG trivial
    obtain ⟨d, hd, hd'⟩ : ∃ d ∈ p.darts, ¬G.Adj d.fst d.snd := by
      by_contra h
      simp only [not_exists, not_and, Decidable.not_not] at h
      have edgeSubset (e) (he : e ∈ p.edges) : e ∈ G.edgeSet := by
        simp only [edges, List.mem_map] at he
        obtain ⟨d, hd, hd'⟩ := he
        rw [← hd']
        exact h _ hd
      let q := p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ ↦ ⟨a, q, this⟩)
      exact hp.transfer edgeSubset
    set u := d.fst
    set v := d.snd
    have hu : u ∈ p.support := Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q := p.rotate u hu
    have hq : q.IsHamiltonianCycle := hp.rotate hu
    have hd_q : d ∈ q.darts := by
      simpa [q] using List.IsRotated.mem_iff (rotate_darts p u hu) |>.mpr hd
    have q_not_nil : ¬q.Nil := by
      erw [nil_rotate]
      exact hp.1.not_nil
    have next_u_eq_v : q.getVert 1 = v := by
      have heq : q.firstDart q_not_nil = d :=
        hq.isCycle.dart_eq_of_fst_eq (q.firstDart_mem_darts q_not_nil) hd_q (by simp [u])
      have hsnd := congrArg (fun z : G.closureStep.Dart ↦ z.snd) heq
      simpa [v] using hsnd
    have uv_not_edge : s(u, v) ∉ q.tail.edges := by
      have : q = cons (q.adj_snd q_not_nil) q.tail := by
        exact (q.cons_tail_eq q_not_nil).symm
      have : q.edges = s(u, v) :: q.tail.edges := by
        simp only [this, edges_cons]
        simpa using Or.inl next_u_eq_v
      intro h
      have nodup := hq.1.edges_nodup
      rw [this] at nodup
      exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del : G.closureStep.deleteEdges {s(u, v)} = G := by
      exact closureStep_deleteEdge _ hd' d.adj
    let q' := q.tail
      |>.toDeleteEdge s(u, v) uv_not_edge
      |>.transfer G (by
        simp (config := {singlePass := true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q' : q'.support ~ Finset.univ.toList := by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer, support_copy, support_transfer,
        List.perm_iff_count, q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV : ‖V‖ ≥ 3 := hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum := closureStep_deg_sum G hd' d.adj
    have next_u : v = hq.next u := by
      obtain ⟨d', hd'₁, hd'₂, hd'₃⟩ := hq.self_next_in_darts u
      have heq : d = d' :=
        hq.isCycle.dart_eq_of_fst_eq hd_q hd'₁ (by simpa [u] using hd'₂.symm)
      change d.snd = hq.next u
      rw [← hd'₃]
      exact congrArg (fun z : G.closureStep.Dart ↦ z.snd) heq
    obtain ⟨w, w', d', hw, hw', d'_mem, hd'₁, hd'₂⟩ :=
      from_ClosureStep_aux' hq hV deg_sum next_u hd'
    have q'_support : q'.support = q.support.tail := by
      simp [q', support_tail_of_not_nil _ q_not_nil]
    obtain ⟨i, i_lt, hi⟩ := List.getElem_of_mem d'_mem
    simp only [length_darts] at i_lt
    have hi_darts : i < q.darts.length := by simpa using i_lt
    rw [← hi, q.darts_getElem_eq_getVert i hi_darts] at hd'₂
    rw [← hi, q.darts_getElem_eq_getVert i hi_darts] at hd'₁
    change q.getVert i = w' at hd'₁
    change q.getVert (i + 1) = w at hd'₂
    have i_nz : i ≠ 0 := by
      rintro rfl
      have huw' : u = w' := by simpa using hd'₁
      exact G.loopless.irrefl _ (huw' ▸ hw'.symm)
    have i_min_1 : i - 1 < q'.darts.length := by
      have q'_length : q'.length = q.length - 1 := by
        have hlen := length_tail_add_one q_not_nil
        simpa [transfer_transfer, length_copy, length_transfer, q'] using hlen
      simp [q'_length]
      omega
    have hd''₁ : (q'.darts[i - 1]).fst = w' := by
      rw [q'.darts_getElem_eq_getVert (i - 1) i_min_1]
      change q'.getVert (i - 1) = w'
      rw [show q'.getVert (i - 1) = q.tail.getVert (i - 1) by
        simp only [Walk.getVert_eq_getD_support, support_copy, support_transfer, q']]
      rw [q.getVert_tail, show i - 1 + 1 = i by omega, hd'₁]
    have hd''₂ : (q'.darts[i - 1]).snd = w := by
      rw [q'.darts_getElem_eq_getVert (i - 1) i_min_1]
      change q'.getVert (i - 1 + 1) = w
      rw [show q'.getVert (i - 1 + 1) = q.tail.getVert (i - 1 + 1) by
        simp only [Walk.getVert_eq_getD_support, support_copy, support_transfer, q']]
      rw [q.getVert_tail, show i - 1 + 1 + 1 = i + 1 by omega, hd'₂]
    have w'_ne_u : w' ≠ u := fun eq ↦ by simp [eq] at hw'
    have Hamiltonian :=
      from_ClosureStep_aux hV perm_q' w'_ne_u hw' hw q'.darts[i - 1]
      (List.getElem_mem i_min_1) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian

private theorem from_closure_aux {n} (hG : ¬IsHamiltonian G) :
    ¬IsHamiltonian (closureStep^[n] G) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply, iterate_one, Decidable.not_not] at ih ⊢
    exact from_ClosureStep ih

theorem from_closure_iff : IsHamiltonian (closure G) ↔ IsHamiltonian G := by
  apply Iff.intro <;> intro hG
  · unfold closure Function.eventualValue at hG
    contrapose hG
    exact from_closure_aux hG
  · exact IsHamiltonian.mono (self_le_closure _) hG

private theorem complete_graph_hamiltonian (hV : 3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian := by
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card V = r + 3 :=
    ⟨Fintype.card V - 3, by omega⟩
  let e : Fin (r + 3) ≃ V := by
    simpa [hr] using (Fintype.equivFin V).symm
  let f : cycleGraph (r + 3) →g (⊤ : SimpleGraph V) :=
    ⟨fun x ↦ e x, fun {a b} hab ↦ by
      simp only [top_adj, ne_eq]
      exact e.injective.ne hab.ne⟩
  let p := (cycleGraph.cycle r).map f
  intro _
  refine ⟨f 0, p, ?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · exact cycleGraph.isCycle_cycle.map e.injective
  · simp [p, hr]

/-- Dirac's theorem: a finite graph on at least three vertices whose every
degree is at least half its order is Hamiltonian. -/
theorem dirac_theorem [DecidableEq V] [DecidableRel G.Adj] (hV : ‖V‖ ≥ 3)
    (hG : ∀ u, 2 * G.degree u ≥ ‖V‖) : G.IsHamiltonian := by
  suffices G.closure = (⊤ : SimpleGraph V) from
    from_closure_iff.mp (this ▸ complete_graph_hamiltonian hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj, ne_eq] at ne
  apply closure_spec G ne
  calc
    ‖V‖ ≤ G.degree u + G.degree v := by
      have := hG u
      have := hG v
      omega
    _ ≤ G.closure.degree u + G.closure.degree v :=
      add_le_add (G.degree_le_of_le (v := u) (self_le_closure G))
        (G.degree_le_of_le (v := v) (self_le_closure G))

/-- Ore's degree-sum criterion for Hamiltonicity. -/
theorem ore_theorem (hV : ‖V‖ ≥ 3)
    (hG : ∀ {u} {v}, ¬G.Adj u v → G.degree u + G.degree v ≥ ‖V‖) :
    G.IsHamiltonian := by
  suffices G.closure = (⊤ : SimpleGraph V) from
    from_closure_iff.mp (this ▸ complete_graph_hamiltonian hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj, ne_eq] at ne
  by_cases adj : G.Adj u v
  · exact self_le_closure G adj
  · apply closure_spec G ne
    calc
      ‖V‖ ≤ G.degree u + G.degree v := hG adj
      _ ≤ G.closure.degree u + G.closure.degree v :=
        add_le_add (G.degree_le_of_le (v := u) (self_le_closure G))
          (G.degree_le_of_le (v := v) (self_le_closure G))

end SimpleGraph
