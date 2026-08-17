/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos58.CycleArcs
import ErdosProblems.Erdos58.Fan
import ErdosProblems.Erdos58.Menger
import ErdosProblems.Erdos58.Structural.LongestCycleBridge
import ErdosProblems.Erdos58.Structural.OutsideCycle

/-!
# Constructing the two-cycle splice

This file discharges the graph-geometric obligation left in
`OutsideCycle`: two vertex-disjoint linking paths and the complementary arcs
of two disjoint cycles really do produce four simple cycles.  The theorem's
inputs are actual cycles and a `TwoLinkage`; it takes no pre-certified splice
or cycle-family hypothesis.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Every actual exterior cycle has at least two carrier vertices.  This is
the endpoint-cardinality input needed by the set form of Menger's theorem. -/
lemma ExteriorOddCycle.two_le_ncard_carrier
    {C : Erdos58.LongestOddCycle G} (D : ExteriorOddCycle C) :
    2 ≤ D.carrier.ncard := by
  have hne : D.base ≠ D.cycle.snd :=
    (D.cycle.adj_snd D.isCycle.not_nil).ne
  have hsub : ({D.base, D.cycle.snd} : Set V) ⊆ D.carrier := by
    intro x hx
    rcases hx with rfl | hx
    · exact D.cycle.start_mem_support
    · have : x = D.cycle.snd := by simpa using hx
      subst x
      exact D.cycle.getVert_mem_support 1
  have hcard : ({D.base, D.cycle.snd} : Set V).ncard = 2 := by
    simp [hne]
  rw [← hcard]
  exact Set.ncard_le_ncard hsub D.finite_carrier

/-- The designated longest cycle likewise has enough vertices to be one
side of a two-linkage. -/
lemma LongestOddCycle.two_le_ncard_carrier
    (C : Erdos58.LongestOddCycle G) : 2 ≤ C.carrier.ncard := by
  rw [C.ncard_carrier]
  have hthree := C.three_le
  omega

/-- A non-endpoint vertex of a walk lies in the list used by the linkage
interior convention. -/
private lemma mem_tail_dropLast_of_mem_support_of_ne
    {a b x : V} (p : G.Walk a b) (hab : a ≠ b)
    (hx : x ∈ p.support) (hxa : x ≠ a) (hxb : x ≠ b) :
    x ∈ p.support.tail.dropLast := by
  have htailne : p.support.tail ≠ [] := by
    intro hnil
    have hb : b ∈ p.support.tail := p.end_mem_tail_support_of_ne hab
    simpa [hnil] using hb
  have hxdrop : x ∈ p.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast hx (by simpa using hxb)
  rw [← p.cons_tail_support, List.dropLast_cons_of_ne_nil htailne] at hxdrop
  exact (List.mem_cons.mp hxdrop).resolve_left hxa

/-- Two paths which meet only at their common endpoint concatenate to a
simple path. -/
private lemma isPath_append_of_inter_eq_end
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x : V, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro x hxp hxq
  have hxq' : x ∈ q.support := List.tail_subset _ hxq
  have hxb : x = b := hinter x hxp hxq'
  subst x
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hxq

namespace TwoLinkage

variable {A B : Set V}

private lemma endpoints_cross_ne (L : TwoLinkage G A B) (hAB : Disjoint A B) :
    L.a₁ ≠ L.b₁ ∧ L.a₂ ≠ L.b₂ := by
  constructor
  · intro h
    exact Set.disjoint_left.mp hAB L.a₁_mem (h ▸ L.b₁_mem)
  · intro h
    exact Set.disjoint_left.mp hAB L.a₂_mem (h ▸ L.b₂_mem)

private lemma p_meets_left_only (L : TwoLinkage G A B) (hAB : Disjoint A B)
    {x : V} (hxp : x ∈ L.p.support) (hxA : x ∈ A) : x = L.a₁ := by
  by_cases hxa : x = L.a₁
  · exact hxa
  by_cases hxb : x = L.b₁
  · subst x
    exact (Set.disjoint_left.mp hAB hxA L.b₁_mem).elim
  · have hxint := mem_tail_dropLast_of_mem_support_of_ne L.p
        (endpoints_cross_ne L hAB).1 hxp hxa hxb
    exact (L.p_interior x hxint (Or.inl hxA)).elim

private lemma p_meets_right_only (L : TwoLinkage G A B) (hAB : Disjoint A B)
    {x : V} (hxp : x ∈ L.p.support) (hxB : x ∈ B) : x = L.b₁ := by
  by_cases hxb : x = L.b₁
  · exact hxb
  by_cases hxa : x = L.a₁
  · subst x
    exact (Set.disjoint_left.mp hAB L.a₁_mem hxB).elim
  · have hxint := mem_tail_dropLast_of_mem_support_of_ne L.p
        (endpoints_cross_ne L hAB).1 hxp hxa hxb
    exact (L.p_interior x hxint (Or.inr hxB)).elim

private lemma q_meets_left_only (L : TwoLinkage G A B) (hAB : Disjoint A B)
    {x : V} (hxq : x ∈ L.q.support) (hxA : x ∈ A) : x = L.a₂ := by
  by_cases hxa : x = L.a₂
  · exact hxa
  by_cases hxb : x = L.b₂
  · subst x
    exact (Set.disjoint_left.mp hAB hxA L.b₂_mem).elim
  · have hxint := mem_tail_dropLast_of_mem_support_of_ne L.q
        (endpoints_cross_ne L hAB).2 hxq hxa hxb
    exact (L.q_interior x hxint (Or.inl hxA)).elim

private lemma q_meets_right_only (L : TwoLinkage G A B) (hAB : Disjoint A B)
    {x : V} (hxq : x ∈ L.q.support) (hxB : x ∈ B) : x = L.b₂ := by
  by_cases hxb : x = L.b₂
  · exact hxb
  by_cases hxa : x = L.a₂
  · subst x
    exact (Set.disjoint_left.mp hAB L.a₂_mem hxB).elim
  · have hxint := mem_tail_dropLast_of_mem_support_of_ne L.q
        (endpoints_cross_ne L hAB).2 hxq hxa hxb
    exact (L.q_interior x hxint (Or.inr hxB)).elim

end TwoLinkage

/-- Four simple pieces close to a simple cycle when the two middle pieces
stay in the disjoint endpoint sets of a truncated two-linkage.  This public
form is also used to glue path families from the bipartite-fan branch. -/
theorem linkage_close_isCycle
    {A B : Set V} (L : TwoLinkage G A B) (hAB : Disjoint A B)
    (c : G.Walk L.a₁ L.a₂) (d : G.Walk L.b₁ L.b₂)
    (hc : c.IsPath) (hd : d.IsPath)
    (hcA : ∀ x ∈ c.support, x ∈ A)
    (hdB : ∀ x ∈ d.support, x ∈ B) :
    (SpliceData.close L.p d L.q c).IsCycle := by
  have hpdMeet : ∀ x : V, x ∈ L.p.support → x ∈ d.support → x = L.b₁ := by
    intro x hxp hxd
    exact TwoLinkage.p_meets_right_only L hAB hxp (hdB x hxd)
  have hpdPath : (L.p.append d).IsPath :=
    isPath_append_of_inter_eq_end L.p_isPath hd hpdMeet
  have hpdqMeet : ∀ x : V, x ∈ (L.p.append d).support →
      x ∈ L.q.reverse.support → x = L.b₂ := by
    intro x hxpd hxq
    have hxq' : x ∈ L.q.support := by simpa using hxq
    rcases (SimpleGraph.Walk.mem_support_append_iff L.p d).mp hxpd with hxp | hxd
    · exact (L.disjoint_support hxp hxq').elim
    · exact TwoLinkage.q_meets_right_only L hAB hxq' (hdB x hxd)
  let r : G.Walk L.a₁ L.a₂ := (L.p.append d).append L.q.reverse
  have hrPath : r.IsPath := by
    exact isPath_append_of_inter_eq_end hpdPath L.q_isPath.reverse hpdqMeet
  have hrcMeet : ∀ x : V, x ∈ r.support → x ∈ c.reverse.support →
      x = L.a₁ ∨ x = L.a₂ := by
    intro x hxr hxc
    have hxc' : x ∈ c.support := by simpa using hxc
    have hxA : x ∈ A := hcA x hxc'
    change x ∈ ((L.p.append d).append L.q.reverse).support at hxr
    rcases (SimpleGraph.Walk.mem_support_append_iff (L.p.append d) L.q.reverse).mp hxr with
      hxpd | hxq
    · rcases (SimpleGraph.Walk.mem_support_append_iff L.p d).mp hxpd with hxp | hxd
      · exact Or.inl (TwoLinkage.p_meets_left_only L hAB hxp hxA)
      · exact (Set.disjoint_left.mp hAB hxA (hdB x hxd)).elim
    · have hxq' : x ∈ L.q.support := by simpa using hxq
      exact Or.inr (TwoLinkage.q_meets_left_only L hAB hxq' hxA)
  have htails : r.support.tail.Disjoint c.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxr hxc
    have hxr' : x ∈ r.support := List.tail_subset _ hxr
    have hxc' : x ∈ c.reverse.support := List.tail_subset _ hxc
    rcases hrcMeet x hxr' hxc' with hxa | hxa
    · have hn := hrPath.support_nodup.rel_head_tail hxr
      exact hn (by simpa using hxa.symm)
    · have hn := hc.reverse.support_nodup.rel_head_tail hxc
      exact hn (by simpa using hxa.symm)
  have hrLong : 1 < r.length := by
    have hp := L.p_nonempty hAB
    have hq := L.q_nonempty hAB
    simp only [r, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  change (r.append c.reverse).IsCycle
  exact hrPath.isCycle_append hc.reverse htails (Or.inl hrLong)

/-- Complementary arcs of two disjoint actual cycles construct the full
`TwoCycleSplice` certificate. -/
theorem twoCycleSplice_of_cycles
    {A B : Set V} {cBase dBase : V}
    (c : G.Walk cBase cBase) (d : G.Walk dBase dBase)
    (hc : c.IsCycle) (hd : d.IsCycle)
    (L : TwoLinkage G A B) (hAB : Disjoint A B)
    (hA : ∀ x : V, x ∈ A ↔ x ∈ c.support)
    (hB : ∀ x : V, x ∈ B ↔ x ∈ d.support) :
    Nonempty (TwoCycleSplice L c.length d.length) := by
  have ha₁ : L.a₁ ∈ c.support := (hA L.a₁).mp L.a₁_mem
  have ha₂ : L.a₂ ∈ c.support := (hA L.a₂).mp L.a₂_mem
  have hb₁ : L.b₁ ∈ d.support := (hB L.b₁).mp L.b₁_mem
  have hb₂ : L.b₂ ∈ d.support := (hB L.b₂).mp L.b₂_mem
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁pos, hc₂pos, hcLen, hcMeet, hcSupp,
      hc₁Edges, hc₂Edges⟩ :=
    exists_path_arcs_of_cycle hc ha₁ ha₂ L.a_ne
  obtain ⟨d₁, d₂, hd₁, hd₂, hd₁pos, hd₂pos, hdLen, hdMeet, hdSupp,
      hd₁Edges, hd₂Edges⟩ :=
    exists_path_arcs_of_cycle hd hb₁ hb₂ L.b_ne
  have hc₁A : ∀ x ∈ c₁.support, x ∈ A := by
    intro x hx
    exact (hA x).mpr ((hcSupp x).mpr (Or.inl hx))
  have hc₂A : ∀ x ∈ c₂.support, x ∈ A := by
    intro x hx
    exact (hA x).mpr ((hcSupp x).mpr (Or.inr hx))
  have hd₁B : ∀ x ∈ d₁.support, x ∈ B := by
    intro x hx
    exact (hB x).mpr ((hdSupp x).mpr (Or.inl hx))
  have hd₂B : ∀ x ∈ d₂.support, x ∈ B := by
    intro x hx
    exact (hB x).mpr ((hdSupp x).mpr (Or.inr hx))
  exact ⟨{
    c₁ := c₁
    c₂ := c₂
    d₁ := d₁
    d₂ := d₂
    c_length_sum := hcLen
    d_length_sum := hdLen
    parallel₁_isCycle := linkage_close_isCycle L hAB c₁ d₁ hc₁ hd₁ hc₁A hd₁B
    parallel₂_isCycle := linkage_close_isCycle L hAB c₂ d₂ hc₂ hd₂ hc₂A hd₂B
    crossed₁_isCycle := linkage_close_isCycle L hAB c₁ d₂ hc₁ hd₂ hc₁A hd₂B
    crossed₂_isCycle := linkage_close_isCycle L hAB c₂ d₁ hc₂ hd₁ hc₂A hd₁B }⟩

/-- A same-parity, length-injective path family on one side of a two-linkage
closes against one of the two arcs of an odd cycle to give a family of odd
cycles with distinct lengths.  The support hypothesis is the precise
fan-carrier condition needed for simplicity. -/
theorem oddCycleFamily_of_pathFamily_linkage
    {A B : Set V} {cBase : V} {I : Type*} [Nonempty I]
    (c : G.Walk cBase cBase) (hc : c.IsCycle) (hcOdd : Odd c.length)
    (L : TwoLinkage G A B) (hAB : Disjoint A B)
    (hA : ∀ x : V, x ∈ A ↔ x ∈ c.support)
    (P : PathFamily G L.b₁ L.b₂ I)
    (hPB : ∀ i x, x ∈ (P.path i).support → x ∈ B) :
    Nonempty (OddCycleFamily G I) := by
  have ha₁ : L.a₁ ∈ c.support := (hA L.a₁).mp L.a₁_mem
  have ha₂ : L.a₂ ∈ c.support := (hA L.a₂).mp L.a₂_mem
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁pos, hc₂pos, hcLen, hcMeet, hcSupp,
      hc₁Edges, hc₂Edges⟩ :=
    exists_path_arcs_of_cycle hc ha₁ ha₂ L.a_ne
  have hc₁A : ∀ x ∈ c₁.support, x ∈ A := by
    intro x hx
    exact (hA x).mpr ((hcSupp x).mpr (Or.inl hx))
  have hc₂A : ∀ x ∈ c₂.support, x ∈ A := by
    intro x hx
    exact (hA x).mpr ((hcSupp x).mpr (Or.inr hx))
  let close (arc : G.Walk L.a₁ L.a₂) (i : I) : G.Walk L.a₁ L.a₁ :=
    SpliceData.close L.p (P.path i) L.q arc
  have hcloseCycle (arc : G.Walk L.a₁ L.a₂) (harc : arc.IsPath)
      (harcA : ∀ x ∈ arc.support, x ∈ A) (i : I) :
      (close arc i).IsCycle := by
    exact linkage_close_isCycle L hAB arc (P.path i) harc (P.isPath i)
      harcA (hPB i)
  let i₀ : I := Classical.choice inferInstance
  have hsum : Odd ((close c₁ i₀).length + (close c₂ i₀).length) := by
    have heq : (close c₁ i₀).length + (close c₂ i₀).length =
        2 * (L.p.length + L.q.length + (P.path i₀).length) + c.length := by
      simp only [close, SpliceData.length_close]
      omega
    rw [heq]
    have heven : Even (2 * (L.p.length + L.q.length + (P.path i₀).length)) :=
      ⟨L.p.length + L.q.length + (P.path i₀).length, by omega⟩
    exact heven.add_odd hcOdd
  have hsame (arc : G.Walk L.a₁ L.a₂) (i : I) :
      (close arc i).length % 2 = (close arc i₀).length % 2 := by
    simp only [close, SpliceData.length_close]
    have hp := P.sameParity i i₀
    omega
  have makeFamily (arc : G.Walk L.a₁ L.a₂) (harc : arc.IsPath)
      (harcA : ∀ x ∈ arc.support, x ∈ A)
      (hodd₀ : Odd (close arc i₀).length) : OddCycleFamily G I :=
    { vertex := fun _ ↦ L.a₁
      cycle := fun i ↦ close arc i
      isCycle := hcloseCycle arc harc harcA
      odd_length := by
        intro i
        rw [Nat.odd_iff] at hodd₀ ⊢
        rw [hsame arc i]
        exact hodd₀
      length_injective := by
        intro i k hik
        apply P.length_injective
        simp only [close, SpliceData.length_close] at hik
        change L.p.length + (P.path i).length + L.q.length + arc.length =
          L.p.length + (P.path k).length + L.q.length + arc.length at hik
        change (P.path i).length = (P.path k).length
        omega }
  by_cases hodd₁ : Odd (close c₁ i₀).length
  · exact ⟨makeFamily c₁ hc₁ hc₁A hodd₁⟩
  · have heven₁ : Even (close c₁ i₀).length :=
      Nat.not_odd_iff_even.mp hodd₁
    have hodd₂ : Odd (close c₂ i₀).length :=
      (Nat.odd_add'.mp hsum).mpr heven₁
    exact ⟨makeFamily c₂ hc₂ hc₂A hodd₂⟩

/-- Specialization to the longest-cycle/exterior-cycle objects used in
Gyárfás's proof.  In particular, the splice is now constructed rather than
assumed in the outside-cycle lemma. -/
theorem twoCycleSplice_longest_exterior
    {C : Erdos58.LongestOddCycle G} (D : ExteriorOddCycle C)
    (L : TwoLinkage G C.carrier D.carrier) :
    Nonempty (TwoCycleSplice L C.length D.cycle.length) := by
  have hA : ∀ x : V, x ∈ C.carrier ↔ x ∈ C.walk.support := by
    intro x
    exact (mem_toEndpointLongestOddCycle_support_iff C x).symm
  have hB : ∀ x : V, x ∈ D.carrier ↔ x ∈ D.cycle.support := by
    intro x
    rfl
  simpa only [Erdos58.LongestOddCycle.walk_length] using
    twoCycleSplice_of_cycles C.walk D.cycle C.walk_isCycle D.isCycle L
      D.disjoint_longest_carrier hA hB

/-- An exterior odd cycle linked twice to the longest odd cycle is strictly
shorter.  This is the unconditional geometric form of the outside-cycle
lemma: no splice certificate remains in the hypotheses. -/
theorem outside_odd_cycle_is_shorter_of_twoLinkage
    {C : Erdos58.LongestOddCycle G} (D : ExteriorOddCycle C)
    (L : TwoLinkage G C.carrier D.carrier) :
    D.cycle.length < C.length :=
  outside_odd_cycle_is_shorter_of_splice D L
    (twoCycleSplice_longest_exterior D L).some

/-- Odd parity upgrades strict shortness to a gap of two. -/
theorem outside_odd_cycle_add_two_le_of_twoLinkage
    {C : Erdos58.LongestOddCycle G} (D : ExteriorOddCycle C)
    (L : TwoLinkage G C.carrier D.carrier) :
    D.cycle.length + 2 ≤ C.length :=
  outside_odd_cycle_add_two_le_of_splice D L
    (twoCycleSplice_longest_exterior D L).some

/-- The actual outside-cycle lemma from Gyárfás's proof.  Two-connectedness
supplies the linkage by the proved finite set-Menger theorem; the preceding
construction supplies all four simple splices. -/
theorem outside_odd_cycle_is_shorter_of_twoConnected
    (hG : TwoConnected G) {C : Erdos58.LongestOddCycle G}
    (D : ExteriorOddCycle C) :
    D.cycle.length < C.length := by
  obtain ⟨L⟩ := hG.exists_twoLinkage
    (LongestOddCycle.two_le_ncard_carrier C)
    (ExteriorOddCycle.two_le_ncard_carrier D)
  exact outside_odd_cycle_is_shorter_of_twoLinkage D L

/-- Gap-of-two form of the unconditional two-connected outside-cycle
lemma. -/
theorem outside_odd_cycle_add_two_le_of_twoConnected
    (hG : TwoConnected G) {C : Erdos58.LongestOddCycle G}
    (D : ExteriorOddCycle C) :
    D.cycle.length + 2 ≤ C.length := by
  have hlt := outside_odd_cycle_is_shorter_of_twoConnected hG D
  rcases D.odd_length with ⟨d, hd⟩
  rcases C.odd with ⟨c, hc⟩
  omega

end

end Erdos58.Structural
