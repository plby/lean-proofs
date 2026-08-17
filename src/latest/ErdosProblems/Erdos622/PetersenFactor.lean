import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Regular bipartite factor theorem

This file supplies the finite factor lemma used in the standard proof of
Petersen's factor theorem: a positive regular bipartite incidence relation has
a perfect matching.  It is stated for two possibly different finite types, so
it can be applied directly to the two copies occurring in a split-vertex
construction.
-/

open Function

namespace Erdos622

namespace PetersenFactor

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A positive `d`-regular bipartite relation has a system of distinct
representatives.  The proof is Hall's theorem, with Hall's inequality obtained
by double-counting the incidences between a set and its neighbourhood. -/
theorem exists_injective_matching_of_biregular
    (r : α → β → Prop) [DecidableRel r] {d : ℕ} (hd : 0 < d)
    (hleft : ∀ a, ((Finset.univ : Finset β).filter (r a)).card = d)
    (hright : ∀ b, ((Finset.univ : Finset α).filter (fun a ↦ r a b)).card = d) :
    ∃ f : α → β, Injective f ∧ ∀ a, r a (f a) := by
  classical
  let N : α → Finset β := fun a ↦ {b | r a b}
  have hHall : ∀ s : Finset α, s.card ≤ (s.biUnion N).card := by
    intro s
    have hmul : s.card * d ≤ (s.biUnion N).card * d := by
      have hdc := Finset.card_nsmul_le_card_nsmul
        (R := ℕ) (r := r) (s := s) (t := s.biUnion N) (m := d) (n := d)
        (fun a ha ↦ by
          have hsub : N a ⊆ (s.biUnion N).bipartiteAbove r a := by
            intro b hb
            rw [Finset.mem_bipartiteAbove]
            exact ⟨Finset.mem_biUnion.mpr ⟨a, ha, hb⟩, by simpa [N] using hb⟩
          calc
            d = (N a).card := (hleft a).symm
            _ ≤ ((s.biUnion N).bipartiteAbove r a).card := Finset.card_le_card hsub)
        (fun b hb ↦ by
          have hsub : s.bipartiteBelow r b ⊆
              (Finset.univ : Finset α).filter (fun a ↦ r a b) := by
            intro a ha
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, (Finset.mem_bipartiteBelow _).mp ha |>.2⟩
          calc
            (s.bipartiteBelow r b).card ≤
                ((Finset.univ : Finset α).filter (fun a ↦ r a b)).card :=
              Finset.card_le_card hsub
            _ = d := hright b)
      simpa [nsmul_eq_mul] using hdc
    exact Nat.le_of_mul_le_mul_right hmul hd
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  exact ⟨f, hf, fun a ↦ by simpa [N] using hmem a⟩

/-- Perfect-matching form of the regular bipartite factor theorem.  Equality
of the two part sizes follows by double-counting all incidences, after which
the injective Hall matching is automatically bijective. -/
theorem exists_bijective_matching_of_biregular
    (r : α → β → Prop) [DecidableRel r] {d : ℕ} (hd : 0 < d)
    (hleft : ∀ a, ((Finset.univ : Finset β).filter (r a)).card = d)
    (hright : ∀ b, ((Finset.univ : Finset α).filter (fun a ↦ r a b)).card = d) :
    ∃ f : α → β, Bijective f ∧ ∀ a, r a (f a) := by
  classical
  obtain ⟨f, hf, hfr⟩ :=
    exists_injective_matching_of_biregular r hd hleft hright
  have hcard_mul : Fintype.card α * d = Fintype.card β * d := by
    calc
      Fintype.card α * d =
          ∑ a : α, ((Finset.univ : Finset β).filter (r a)).card := by simp [hleft]
      _ = ∑ b : β, ((Finset.univ : Finset α).filter (fun a ↦ r a b)).card := by
        simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (r := r) (s := (Finset.univ : Finset α))
            (t := (Finset.univ : Finset β)))
      _ = Fintype.card β * d := by simp [hright]
  have hcard : Fintype.card α = Fintype.card β := by
    exact Nat.eq_of_mul_eq_mul_right hd hcard_mul
  exact ⟨f, (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩, hfr⟩

end PetersenFactor

namespace PetersenFactor

open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An orientation represented by the chosen head of every edge.  Exactly `k`
edges point into each vertex. -/
structure BalancedOrientation (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) where
  head : G.edgeFinset → V
  head_mem : ∀ e : G.edgeFinset, head e ∈ (e : Sym2 V)
  card_head : ∀ v,
    ((Finset.univ : Finset G.edgeFinset).filter (fun e ↦ head e = v)).card = k

namespace BalancedOrientation

variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- The tail is the other endpoint of an oriented edge. -/
noncomputable def tail (O : BalancedOrientation G k) (e : G.edgeFinset) : V :=
  Sym2.Mem.other' (O.head_mem e)

theorem tail_mem (O : BalancedOrientation G k) (e : G.edgeFinset) :
    O.tail e ∈ (e : Sym2 V) :=
  Sym2.other_mem' (O.head_mem e)

theorem tail_ne_head (O : BalancedOrientation G k) (e : G.edgeFinset) :
    O.tail e ≠ O.head e := by
  unfold tail
  rw [← Sym2.other_eq_other' (O.head_mem e)]
  exact Sym2.other_ne (G.not_isDiag_of_mem_edgeFinset e.prop) (O.head_mem e)

theorem edge_eq_of_head_eq_tail_eq (O : BalancedOrientation G k)
    {e f : G.edgeFinset} (hh : O.head e = O.head f) (ht : O.tail e = O.tail f) : e = f := by
  apply Subtype.ext
  calc
    (e : Sym2 V) = s(O.head e, O.tail e) := by
      exact (Sym2.other_spec' (O.head_mem e)).symm
    _ = s(O.head f, O.tail f) := by rw [hh, ht]
    _ = (f : Sym2 V) := Sym2.other_spec' (O.head_mem f)

theorem mem_edge_iff (O : BalancedOrientation G k) (e : G.edgeFinset) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = O.head e ∨ v = O.tail e := by
  have heq : (e : Sym2 V) = s(O.head e, O.tail e) :=
    (Sym2.other_spec' (O.head_mem e)).symm
  constructor
  · intro hv
    have hv' : v ∈ s(O.head e, O.tail e) := heq ▸ hv
    simpa using hv'
  · intro hv
    have hv' : v ∈ s(O.head e, O.tail e) := by simpa using hv
    exact heq.symm ▸ hv'

/-- A balanced orientation has the same number of outgoing and incoming
edges at every vertex. -/
theorem card_tail (O : BalancedOrientation G k) (hreg : G.IsRegularOfDegree (2 * k)) (v : V) :
    ((Finset.univ : Finset G.edgeFinset).filter (fun e ↦ O.tail e = v)).card = k := by
  classical
  let I := (Finset.univ : Finset G.edgeFinset).filter
    (fun e : G.edgeFinset ↦ v ∈ (e : Sym2 V))
  let H := (Finset.univ : Finset G.edgeFinset).filter (fun e : G.edgeFinset ↦ O.head e = v)
  let T := (Finset.univ : Finset G.edgeFinset).filter (fun e : G.edgeFinset ↦ O.tail e = v)
  have hdisj : Disjoint H T := by
    rw [Finset.disjoint_left]
    intro e heH heT
    have hh : O.head e = v := (Finset.mem_filter.mp heH).2
    have ht : O.tail e = v := (Finset.mem_filter.mp heT).2
    exact O.tail_ne_head e (ht.trans hh.symm)
  have hunion : H ∪ T = I := by
    ext e
    simp only [H, T, I, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [O.mem_edge_iff]
    aesop
  have hI : I.card = 2 * k := by
    have hmap : I.map ⟨Subtype.val, Subtype.val_injective⟩ = G.incidenceFinset v := by
      ext e
      simp [I, SimpleGraph.incidenceSet, and_comm]
    calc
      I.card = (I.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
      _ = (G.incidenceFinset v).card := congrArg Finset.card hmap
      _ = G.degree v := G.card_incidenceFinset_eq_degree v
      _ = 2 * k := hreg v
  have hadd : H.card + T.card = I.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hH : H.card = k := by simpa [H] using O.card_head v
  have hT : T.card = k := by omega
  simpa [T] using hT

/-- The directed adjacency relation represented by the orientation. -/
def IsArc (O : BalancedOrientation G k) (u v : V) : Prop :=
  ∃ e : G.edgeFinset, O.tail e = u ∧ O.head e = v

theorem isArc_irrefl (O : BalancedOrientation G k) : Std.Irrefl O.IsArc where
  irrefl v := by
    rintro ⟨e, ht, hh⟩
    exact O.tail_ne_head e (ht.trans hh.symm)

theorem isArc_adj (O : BalancedOrientation G k) {u v : V} (h : O.IsArc u v) : G.Adj u v := by
  obtain ⟨e, ht, hh⟩ := h
  have heq : (e : Sym2 V) = s(u, v) := by
    calc
      (e : Sym2 V) = s(O.head e, O.tail e) :=
        (Sym2.other_spec' (O.head_mem e)).symm
      _ = s(v, u) := by rw [hh, ht]
      _ = s(u, v) := Sym2.eq_swap
  rw [← G.mem_edgeSet, ← heq]
  exact G.mem_edgeFinset.mp e.prop

theorem card_isArc_right (O : BalancedOrientation G k) (hreg : G.IsRegularOfDegree (2 * k))
    (u : V) :
    ((Finset.univ : Finset V).filter (O.IsArc u)).card = k := by
  classical
  let E := (Finset.univ : Finset G.edgeFinset).filter (fun e ↦ O.tail e = u)
  have hcard : E.card = ((Finset.univ : Finset V).filter (O.IsArc u)).card := by
    apply Finset.card_bij (fun e _ ↦ O.head e)
    · intro e he
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨e, (Finset.mem_filter.mp he).2, rfl⟩⟩
    · intro e he f hf hef
      apply O.edge_eq_of_head_eq_tail_eq hef
      exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
    · intro v hv
      obtain ⟨e, ht, hh⟩ := (Finset.mem_filter.mp hv).2
      exact ⟨e, by simp [E, ht], hh⟩
  calc
    ((Finset.univ : Finset V).filter (O.IsArc u)).card = E.card := hcard.symm
    _ = k := by simpa [E] using O.card_tail hreg u

theorem card_isArc_left (O : BalancedOrientation G k) (v : V) :
    ((Finset.univ : Finset V).filter (fun u ↦ O.IsArc u v)).card = k := by
  classical
  let E := (Finset.univ : Finset G.edgeFinset).filter (fun e ↦ O.head e = v)
  have hcard : E.card =
      ((Finset.univ : Finset V).filter (fun u ↦ O.IsArc u v)).card := by
    apply Finset.card_bij (fun e _ ↦ O.tail e)
    · intro e he
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨e, rfl, (Finset.mem_filter.mp he).2⟩⟩
    · intro e he f hf hef
      apply O.edge_eq_of_head_eq_tail_eq
      · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      · exact hef
    · intro u hu
      obtain ⟨e, ht, hh⟩ := (Finset.mem_filter.mp hu).2
      exact ⟨e, by simp [E, hh], ht⟩
  calc
    ((Finset.univ : Finset V).filter (fun u ↦ O.IsArc u v)).card = E.card := hcard.symm
    _ = k := by simpa [E] using O.card_head v

theorem not_isArc_symm (O : BalancedOrientation G k) {u v : V}
    (huv : O.IsArc u v) : ¬O.IsArc v u := by
  rintro hvu
  obtain ⟨e, het, heh⟩ := huv
  obtain ⟨f, hft, hfh⟩ := hvu
  have heval : (e : Sym2 V) = s(u, v) := by
    calc
      (e : Sym2 V) = s(O.head e, O.tail e) :=
        (Sym2.other_spec' (O.head_mem e)).symm
      _ = s(v, u) := by rw [heh, het]
      _ = s(u, v) := Sym2.eq_swap
  have hfval : (f : Sym2 V) = s(u, v) := by
    calc
      (f : Sym2 V) = s(O.head f, O.tail f) :=
        (Sym2.other_spec' (O.head_mem f)).symm
      _ = s(u, v) := by rw [hfh, hft]
  have hef : e = f := Subtype.ext (heval.trans hfval.symm)
  subst f
  exact O.tail_ne_head e (het.trans hfh.symm)

/-- Selecting one outgoing arc at every vertex while also selecting every
head once is the directed form of a spanning two-factor. -/
theorem exists_arc_equiv (O : BalancedOrientation G k) (hk : 0 < k)
    (hreg : G.IsRegularOfDegree (2 * k)) :
    ∃ p : V ≃ V, ∀ u, O.IsArc u (p u) := by
  classical
  obtain ⟨f, hf, hrel⟩ := exists_bijective_matching_of_biregular O.IsArc hk
    (O.card_isArc_right hreg) O.card_isArc_left
  exact ⟨Equiv.ofBijective f hf, hrel⟩

/-- The undirected graph obtained from the arcs of a permutation. -/
def arcFactor (O : BalancedOrientation G k) (p : V ≃ V)
    (hp : ∀ u, O.IsArc u (p u)) : SimpleGraph V where
  Adj u v := p u = v ∨ p v = u
  symm.symm := by
    intro u v h
    exact h.elim Or.inr Or.inl
  loopless.irrefl := by
    intro u h
    rcases h with h | h
    · exact O.isArc_irrefl.irrefl u (by simpa [h] using hp u)
    · exact O.isArc_irrefl.irrefl u (by simpa [h] using hp u)

theorem arcFactor_le (O : BalancedOrientation G k) (p : V ≃ V)
    (hp : ∀ u, O.IsArc u (p u)) : O.arcFactor p hp ≤ G := by
  intro u v huv
  rcases huv with h | h
  · exact O.isArc_adj (h ▸ hp u)
  · exact (O.isArc_adj (h ▸ hp v)).symm

theorem arcFactor_regular (O : BalancedOrientation G k) (p : V ≃ V)
    (hp : ∀ u, O.IsArc u (p u)) : (O.arcFactor p hp).IsRegularOfDegree 2 := by
  classical
  intro u
  have hne : p u ≠ p.symm u := by
    intro h
    have hforward : O.IsArc u (p u) := hp u
    have hbackward : O.IsArc (p.symm u) u := by simpa using hp (p.symm u)
    exact O.not_isArc_symm hforward (h ▸ hbackward)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hn : (O.arcFactor p hp).neighborFinset u = {p u, p.symm u} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    change (p u = v ∨ p v = u) ↔ v ∈ ({p u, p.symm u} : Finset V)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [p.eq_symm_apply]
    tauto
  rw [hn]
  simp [hne]

end BalancedOrientation

/-- Every finite `2k`-regular simple graph has a balanced orientation.  The
proof assigns the `k` slots at every vertex bijectively to the edge set.  A
slot may receive precisely an edge incident with its vertex.  Both sides of
this incidence relation have degree `2k`, so the regular bipartite factor
theorem above supplies the required bijection. -/
theorem exists_balancedOrientation (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 0 < k) (hreg : G.IsRegularOfDegree (2 * k)) :
    Nonempty (BalancedOrientation G k) := by
  classical
  let inc : (V × Fin k) → G.edgeFinset → Prop := fun x e ↦ x.1 ∈ (e : Sym2 V)
  have hleft : ∀ x,
      ((Finset.univ : Finset G.edgeFinset).filter (inc x)).card = 2 * k := by
    intro x
    let q := (Finset.univ : Finset G.edgeFinset).filter (inc x)
    have hmap : q.map ⟨Subtype.val, Subtype.val_injective⟩ = G.incidenceFinset x.1 := by
      ext e
      simp [q, inc, SimpleGraph.incidenceSet, and_comm]
    calc
      ((Finset.univ : Finset G.edgeFinset).filter (inc x)).card = q.card := rfl
      _ = (q.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
      _ = (G.incidenceFinset x.1).card := congrArg Finset.card hmap
      _ = G.degree x.1 := G.card_incidenceFinset_eq_degree x.1
      _ = 2 * k := hreg x.1
  have hright : ∀ e,
      ((Finset.univ : Finset (V × Fin k)).filter (fun x ↦ inc x e)).card = 2 * k := by
    intro e
    have heq :
        (Finset.univ : Finset (V × Fin k)).filter (fun x ↦ inc x e) =
          (e : Sym2 V).toFinset ×ˢ (Finset.univ : Finset (Fin k)) := by
      ext x
      simp [inc]
    rw [heq, Finset.card_product, G.card_toFinset_mem_edgeFinset e,
      Finset.card_univ, Fintype.card_fin]
  obtain ⟨assign, hassign, hassigned⟩ :=
    exists_bijective_matching_of_biregular inc (by omega : 0 < 2 * k)
      hleft hright
  let assignment : (V × Fin k) ≃ G.edgeFinset := Equiv.ofBijective assign hassign
  let head : G.edgeFinset → V := fun e ↦ (assignment.symm e).1
  refine ⟨⟨head, ?_, ?_⟩⟩
  · intro e
    have hm := hassigned (assignment.symm e)
    have ha : assign (assignment.symm e) = e := by
      exact assignment.apply_symm_apply e
    simpa [inc, head, assignment, ha] using hm
  · intro v
    have hmap :
        ((Finset.univ : Finset G.edgeFinset).filter (fun e ↦ head e = v)).map
            assignment.symm.toEmbedding =
          (Finset.univ : Finset (V × Fin k)).filter (fun x ↦ x.1 = v) := by
      ext x
      simp [head]
    calc
      ((Finset.univ : Finset G.edgeFinset).filter (fun e ↦ head e = v)).card =
          (((Finset.univ : Finset G.edgeFinset).filter (fun e ↦ head e = v)).map
            assignment.symm.toEmbedding).card := (Finset.card_map _).symm
      _ = ((Finset.univ : Finset (V × Fin k)).filter (fun x ↦ x.1 = v)).card :=
        congrArg Finset.card hmap
      _ = k := by
        have hv :
            (Finset.univ : Finset (V × Fin k)).filter (fun x ↦ x.1 = v) =
              ({v} : Finset V) ×ˢ (Finset.univ : Finset (Fin k)) := by
          ext x
          rcases x with ⟨x, i⟩
          simp [eq_comm]
        rw [hv, Finset.card_product]
        simp

/-- The one-step Petersen factor theorem. -/
theorem exists_twoFactor (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (hreg : G.IsRegularOfDegree (2 * k)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsRegularOfDegree 2 := by
  obtain ⟨O⟩ := exists_balancedOrientation G k hk hreg
  obtain ⟨p, hp⟩ := O.exists_arc_equiv hk hreg
  exact ⟨O.arcFactor p hp, O.arcFactor_le p hp, O.arcFactor_regular p hp⟩

theorem sdiff_twoFactor_regular {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {k : ℕ}
    (hle : H ≤ G) (hG : G.IsRegularOfDegree (2 * (k + 1)))
    (hH : H.IsRegularOfDegree 2) : (G \ H).IsRegularOfDegree (2 * k) := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [SimpleGraph.neighborFinset_sdiff]
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hle hw
  rw [Finset.card_sdiff_of_subset hsub]
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
    hG v, hH v]
  omega

/-- An edge partition into spanning two-factors. -/
structure TwoFactorization (G : SimpleGraph V) (k : ℕ) where
  factor : Fin k → SimpleGraph V
  factor_le : ∀ i, factor i ≤ G
  regular : ∀ i, (factor i).IsRegularOfDegree 2
  disjoint : ∀ i j, i ≠ j → Disjoint (factor i) (factor j)
  iSup_eq : ⨆ i, factor i = G

/-- Petersen's factorization theorem: every finite `2k`-regular simple graph
is the edge-disjoint union of `k` spanning two-factors. -/
theorem exists_twoFactorization (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hreg : G.IsRegularOfDegree (2 * k)) : Nonempty (TwoFactorization G k) := by
  classical
  induction k generalizing G with
  | zero =>
      have hGbot : G = ⊥ := by
        apply le_antisymm
        · intro u v huv
          have hv : v ∈ G.neighborFinset u :=
            (SimpleGraph.mem_neighborFinset (G := G) u v).mpr huv
          have hpos : 0 < G.degree u := by
            rw [← G.card_neighborFinset_eq_degree]
            exact Finset.card_pos.mpr ⟨v, hv⟩
          have hz : G.degree u = 0 := by simpa using hreg u
          omega
        · exact bot_le
      let F : Fin 0 → SimpleGraph V := fun i ↦ Fin.elim0 i
      refine ⟨⟨F, ?_, ?_, ?_, ?_⟩⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simpa [F, hGbot]
  | succ k ih =>
      obtain ⟨H, hHG, hHreg⟩ := exists_twoFactor G (k + 1) (by omega) hreg
      let R : SimpleGraph V := G \ H
      have hRreg : R.IsRegularOfDegree (2 * k) := by
        exact sdiff_twoFactor_regular hHG hreg hHreg
      obtain ⟨D⟩ := ih R hRreg
      let F : Fin (k + 1) → SimpleGraph V := Fin.cases H D.factor
      refine ⟨⟨F, ?_, ?_, ?_, ?_⟩⟩
      · intro i
        refine Fin.cases hHG (fun j ↦ ?_) i
        exact (D.factor_le j).trans sdiff_le
      · intro i
        exact Fin.cases hHreg (fun j ↦ D.regular j) i
      · intro i
        refine Fin.cases ?_ (fun a ↦ ?_) i
        · intro j
          refine Fin.cases ?_ (fun b ↦ ?_) j
          · intro h
            exact False.elim (h rfl)
          · intro _
            change Disjoint H (D.factor b)
            exact disjoint_sdiff_self_right.mono_right (D.factor_le b)
        · intro j
          refine Fin.cases ?_ (fun b ↦ ?_) j
          · intro _
            change Disjoint (D.factor a) H
            exact (disjoint_sdiff_self_right.mono_right (D.factor_le a)).symm
          · intro h
            change Disjoint (D.factor a) (D.factor b)
            apply D.disjoint a b
            intro hab
            apply h
            exact congrArg Fin.succ hab
      · apply le_antisymm
        · apply iSup_le
          intro i
          exact Fin.cases hHG (fun j ↦ (D.factor_le j).trans sdiff_le) i
        · have hsplit : H ⊔ R = G := by
            exact sup_sdiff_cancel_right hHG
          rw [← hsplit]
          apply sup_le
          · exact le_iSup F 0
          · rw [← D.iSup_eq]
            apply iSup_le
            intro i
            exact le_iSup_of_le i.succ (by rfl)

end PetersenFactor
end Erdos622
