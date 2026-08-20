import ErdosProblems.Erdos746.PathMax
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Pósa rotations and boosters

This file contains the deterministic graph theory used in the proof of Erdős
problem 746.  In particular, all neighbourhoods below are *external*
neighbourhoods.
-/

open scoped Sym2
open Finset
open Erdos746.PathMax

namespace SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The external neighbourhood of a finite set of vertices. -/
def outerNeighborFinset (G : SimpleGraph V) (S : Finset V) : Finset V :=
  by
    classical
    exact (S.biUnion fun u ↦ Finset.univ.filter (G.Adj u)) \ S

@[simp] theorem mem_outerNeighborFinset {G : SimpleGraph V} {S : Finset V} {v : V} :
    v ∈ outerNeighborFinset G S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  classical
  simp [outerNeighborFinset, SimpleGraph.adj_comm, and_comm]

/-- `G` expands every set of at most `k` vertices by a factor of two. -/
def IsTwoExpanderUpTo (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → 2 * S.card ≤ (outerNeighborFinset G S).card

/-- A walk from a set to its complement crosses the edge boundary. -/
theorem Walk.exists_adj_mem_notMem {G : SimpleGraph V} {u v : V}
    (q : G.Walk u v) (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction q with
  | nil => exact (hv hu).elim
  | @cons u w v huw q ih =>
      by_cases hw : w ∈ S
      · exact ih hw hv
      · exact ⟨u, hu, w, hw, huw⟩

/-- A nonempty proper vertex set in a connected graph has a boundary edge. -/
theorem Connected.exists_adj_mem_notMem (G : SimpleGraph V) (hG : G.Connected)
    (S : Finset V) (u : V) (hu : u ∈ S) (w : V) (hw : w ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  exact (hG.preconnected u w).elim fun q ↦ q.exists_adj_mem_notMem S hu hw

namespace Walk

variable {G : SimpleGraph V} {a b : V}

/-- A Pósa rotation fixes the first vertex and uses an edge from the old last
vertex to an internal pivot. -/
def posaRotate (p : G.Walk a b) (x : V) (hx : x ∈ p.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hbx : G.Adj b x) :
    G.Walk a ((p.dropUntil x hx).snd) :=
  (p.takeUntil x hx).append
    (Walk.cons hbx.symm (p.dropUntil x hx).tail.reverse)

@[simp] theorem length_posaRotate (p : G.Walk a b) (x : V) (hx : x ∈ p.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hbx : G.Adj b x) :
    (p.posaRotate x hx hxa hxb hbx).length = p.length := by
  simp [posaRotate]
  have hd : ¬ (p.dropUntil x hx).Nil := Walk.not_nil_of_ne hxb
  have hdlen : 0 < (p.dropUntil x hx).length := Walk.not_nil_iff_lt_length.mp hd
  have hsplit := congrArg Walk.length (Walk.take_spec p hx)
  simp only [Walk.length_append] at hsplit
  omega

theorem isPath_posaRotate (p : G.Walk a b) (hp : p.IsPath) (x : V) (hx : x ∈ p.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hbx : G.Adj b x) :
    (p.posaRotate x hx hxa hxb hbx).IsPath := by
  rw [Walk.isPath_def]
  have hd : ¬ (p.dropUntil x hx).Nil := Walk.not_nil_of_ne hxb
  have hperm : (p.posaRotate x hx hxa hxb hbx).support.Perm p.support := by
    rw [posaRotate, Walk.support_append, Walk.support_cons, List.tail_cons,
      Walk.support_reverse, Walk.support_tail_of_not_nil _ hd]
    have hr := List.Perm.append_left (p.takeUntil x hx).support
      (p.dropUntil x hx).support.tail.reverse_perm
    rw [← Walk.support_append, Walk.take_spec] at hr
    exact hr
  exact hperm.nodup_iff.mpr hp.support_nodup

theorem support_posaRotate_perm (p : G.Walk a b) (x : V) (hx : x ∈ p.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hbx : G.Adj b x) :
    (p.posaRotate x hx hxa hxb hbx).support.Perm p.support := by
  have hd : ¬ (p.dropUntil x hx).Nil := Walk.not_nil_of_ne hxb
  rw [posaRotate, Walk.support_append, Walk.support_cons, List.tail_cons,
    Walk.support_reverse, Walk.support_tail_of_not_nil _ hd]
  have hr := List.Perm.append_left (p.takeUntil x hx).support
    (p.dropUntil x hx).support.tail.reverse_perm
  rw [← Walk.support_append, Walk.take_spec] at hr
  exact hr

/-- A rotation deletes only the old path edge immediately after the pivot. -/
theorem mem_edges_posaRotate_of_ne (p : G.Walk a b) (x : V) (hx : x ∈ p.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hbx : G.Adj b x) (e : Sym2 V)
    (he : e ∈ p.edges)
    (hne : e ≠ s(x, (p.dropUntil x hx).snd)) :
    e ∈ (p.posaRotate x hx hxa hxb hbx).edges := by
  have hd : ¬ (p.dropUntil x hx).Nil := Walk.not_nil_of_ne hxb
  have hsplit := congrArg Walk.edges (Walk.take_spec p hx)
  rw [Walk.edges_append] at hsplit
  rw [← hsplit] at he
  rw [posaRotate, Walk.edges_append, Walk.edges_cons, Walk.edges_reverse,
    Walk.edges_tail]
  simp only [List.mem_append, List.mem_cons, List.mem_reverse]
  by_cases ht : e ∈ (p.takeUntil x hx).edges
  · exact Or.inl ht
  · right
    have hedrop : e ∈ (p.dropUntil x hx).edges :=
      (List.mem_append.mp he).resolve_left ht
    have hd_eq := p.dropUntil x hx |>.cons_tail_eq hd
    have hedges := congrArg Walk.edges hd_eq
    rw [Walk.edges_cons, Walk.edges_tail] at hedges
    rw [← hedges] at hedrop
    have hne' : e ≠ s(x, (p.dropUntil x hx).snd) := hne
    exact Or.inr ((List.mem_cons.mp hedrop).resolve_left hne')

/-- Paths obtainable by a finite sequence of Pósa rotations fixing the first
vertex. -/
inductive IsPosaReachable (p : G.Walk a b) : {c : V} → G.Walk a c → Prop
  | refl : IsPosaReachable p p
  | rotate {c : V} {q : G.Walk a c} (hq : IsPosaReachable p q)
      (x : V) (hx : x ∈ q.support) (hxa : x ≠ a) (hxc : x ≠ c)
      (hcx : G.Adj c x) :
      IsPosaReachable p (q.posaRotate x hx hxa hxc hcx)

/-- Endpoints obtainable by rotations of `p` which keep its first vertex
fixed. -/
def posaEndpointFinset (p : G.Walk a b) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun c ↦ ∃ q : G.Walk a c, IsPosaReachable p q

@[simp] theorem mem_posaEndpointFinset (p : G.Walk a b) (c : V) :
    c ∈ p.posaEndpointFinset ↔ ∃ q : G.Walk a c, IsPosaReachable p q := by
  simp [posaEndpointFinset]

/-- Neighbours of `u` using only the edges of the path `p`. -/
def pathNeighborFinset (p : G.Walk a b) (u : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter (p.toSubgraph.Adj u)

@[simp] theorem mem_pathNeighborFinset (p : G.Walk a b) (u v : V) :
    v ∈ p.pathNeighborFinset u ↔ s(u, v) ∈ p.edges := by
  simp only [pathNeighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Walk.adj_toSubgraph_iff_mem_edges]

/-- The path-neighbourhood of a set. -/
def pathNeighborhood (p : G.Walk a b) (S : Finset V) : Finset V :=
  S.biUnion p.pathNeighborFinset

@[simp] theorem mem_pathNeighborhood (p : G.Walk a b) (S : Finset V) (v : V) :
    v ∈ p.pathNeighborhood S ↔ ∃ u ∈ S, s(u, v) ∈ p.edges := by
  simp [pathNeighborhood]

theorem IsPath.card_pathNeighborFinset_end_le_one {p : G.Walk a b}
    (hp : p.IsPath) (hn : ¬ p.Nil) : (p.pathNeighborFinset b).card ≤ 1 := by
  have hs := hp.neighborSet_toSubgraph_endpoint hn
  have heq : p.pathNeighborFinset b = {p.penultimate} := by
    ext v
    rw [mem_pathNeighborFinset]
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    simpa only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
      Finset.mem_singleton] using Set.ext_iff.mp hs v
  simp [heq]

theorem IsPath.card_pathNeighborFinset_le_two {p : G.Walk a b}
    (hp : p.IsPath) {u : V} (hu : u ∈ p.support) : (p.pathNeighborFinset u).card ≤ 2 := by
  rw [Walk.mem_support_iff_exists_getVert] at hu
  obtain ⟨i, hi, hil⟩ := hu
  subst u
  by_cases hi0 : i = 0
  · subst i
    by_cases hn : p.Nil
    · have hedge : p.edges = [] := List.eq_nil_of_length_eq_zero (by
        simpa [Walk.length_edges] using hn.length_eq_zero)
      have hzero : p.pathNeighborFinset (p.getVert 0) = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr fun v hv ↦ by
          rw [mem_pathNeighborFinset, hedge] at hv
          simpa using hv
      rw [hzero]
      simp
    · have hs := hp.neighborSet_toSubgraph_startpoint hn
      have heq : p.pathNeighborFinset a = {p.snd} := by
        ext v
        rw [mem_pathNeighborFinset]
        rw [← Walk.adj_toSubgraph_iff_mem_edges]
        simpa only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
          Finset.mem_singleton] using Set.ext_iff.mp hs v
      rw [p.getVert_zero, heq]
      simp
  · by_cases hil' : i = p.length
    · subst i
      rw [p.getVert_length]
      by_cases hn : p.Nil
      · have hedge : p.edges = [] := List.eq_nil_of_length_eq_zero (by
          simpa [Walk.length_edges] using hn.length_eq_zero)
        have hzero : p.pathNeighborFinset b = ∅ :=
          Finset.eq_empty_iff_forall_notMem.mpr fun v hv ↦ by
            rw [mem_pathNeighborFinset, hedge] at hv
            simpa using hv
        rw [hzero]
        simp
      · exact hp.card_pathNeighborFinset_end_le_one hn |>.trans (by omega)
    · have hs := hp.neighborSet_toSubgraph_internal hi0 (by omega)
      have heq : p.pathNeighborFinset (p.getVert i) =
          {p.getVert (i - 1), p.getVert (i + 1)} := by
        ext v
        rw [mem_pathNeighborFinset]
        rw [← Walk.adj_toSubgraph_iff_mem_edges]
        simpa only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
          Finset.mem_insert, Finset.mem_singleton] using
          Set.ext_iff.mp hs v
      rw [heq]
      exact Finset.card_le_two

theorem IsPath.card_pathNeighborFinset_eq_two {p : G.Walk a b}
    (hp : p.IsPath) {u : V} (hu : u ∈ p.support) (hua : u ≠ a) (hub : u ≠ b) :
    (p.pathNeighborFinset u).card = 2 := by
  rw [Walk.mem_support_iff_exists_getVert] at hu
  obtain ⟨i, rfl, hil⟩ := hu
  have hi0 : i ≠ 0 := by
    intro hi
    subst i
    exact hua (by simp)
  have hil' : i < p.length := by
    apply lt_of_le_of_ne hil
    intro heq
    exact hub (by simpa [heq])
  rw [← Set.ncard_coe_finset]
  have hset : ((p.pathNeighborFinset (p.getVert i) : Finset V) : Set V) =
      p.toSubgraph.neighborSet (p.getVert i) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_pathNeighborFinset,
      Subgraph.mem_neighborSet, Walk.adj_toSubgraph_iff_mem_edges]
  rw [hset, hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil']

theorem IsPath.card_pathNeighborhood_lt_two_mul {p : G.Walk a b}
    (hp : p.IsPath) (hn : ¬ p.Nil) (S : Finset V) (hb : b ∈ S)
    (hS : ∀ u ∈ S, u ∈ p.support) :
    (p.pathNeighborhood S).card < 2 * S.card := by
  calc
    (p.pathNeighborhood S).card ≤ ∑ u ∈ S, (p.pathNeighborFinset u).card := by
      exact Finset.card_biUnion_le
    _ = (p.pathNeighborFinset b).card +
          ∑ u ∈ S.erase b, (p.pathNeighborFinset u).card := by
      rw [← Finset.sum_insert (s := S.erase b) (f := fun u ↦ (p.pathNeighborFinset u).card)
        (Finset.notMem_erase b S), Finset.insert_erase hb]
    _ ≤ 1 + 2 * (S.erase b).card := by
      gcongr
      · exact hp.card_pathNeighborFinset_end_le_one hn
      · calc
          ∑ u ∈ S.erase b, (p.pathNeighborFinset u).card ≤
              ∑ _u ∈ S.erase b, 2 := by
                exact Finset.sum_le_sum fun u hu ↦
                  hp.card_pathNeighborFinset_le_two (hS u (Finset.mem_of_mem_erase hu))
          _ = 2 * (S.erase b).card := by simp [mul_comm]
    _ < 2 * S.card := by
      rw [Finset.card_erase_of_mem hb]
      have : 0 < S.card := Finset.card_pos.mpr ⟨b, hb⟩
      omega

theorem IsPosaReachable.isPath {p : G.Walk a b} (hp : p.IsPath)
    {c : V} {q : G.Walk a c} (hq : IsPosaReachable p q) : q.IsPath := by
  induction hq with
  | refl => exact hp
  | rotate hreach x hx hxa hxc hcx ih =>
      exact isPath_posaRotate _ ih x hx hxa hxc hcx

theorem IsPosaReachable.length_eq {p : G.Walk a b}
    {c : V} {q : G.Walk a c} (hq : IsPosaReachable p q) : q.length = p.length := by
  induction hq with
  | refl => rfl
  | rotate hreach x hx hxa hxc hcx ih =>
      exact (length_posaRotate _ x hx hxa hxc hcx).trans ih

theorem IsPosaReachable.support_perm {p : G.Walk a b} (hp : p.IsPath)
    {c : V} {q : G.Walk a c} (hq : IsPosaReachable p q) : q.support.Perm p.support := by
  induction hq with
  | refl => exact .refl _
  | @rotate c q hreach x hx hxa hxc hcx ih =>
      exact (q.support_posaRotate_perm x hx hxa hxc hcx).trans ih

@[simp] theorem end_mem_posaEndpointFinset (p : G.Walk a b) :
    b ∈ p.posaEndpointFinset := by
  exact mem_posaEndpointFinset p b |>.mpr ⟨p, .refl⟩

/-- Every edge of the original path which has been broken during rotations has
an endpoint among the obtainable endpoints. -/
theorem IsPosaReachable.endpoint_of_missing_edge {p : G.Walk a b}
    {c : V} {q : G.Walk a c} (hq : IsPosaReachable p q)
    (e : Sym2 V) (hep : e ∈ p.edges) (heq : e ∉ q.edges) :
    ∃ u ∈ p.posaEndpointFinset, ∃ v : V, e = s(u, v) := by
  induction hq with
  | refl => exact (heq hep).elim
  | @rotate c q hreach x hx hxa hxc hcx ih =>
      let z : V := (q.dropUntil x hx).snd
      by_cases he : e = s(x, z)
      · refine ⟨z, ?_, x, ?_⟩
        · rw [mem_posaEndpointFinset]
          exact ⟨q.posaRotate x hx hxa hxc hcx, .rotate hreach x hx hxa hxc hcx⟩
        · simpa [z, Sym2.eq_swap] using he
      · apply ih
        intro heold
        exact heq (q.mem_edges_posaRotate_of_ne x hx hxa hxc hcx e heold (by simpa [z]))

/-- In a connected non-Hamiltonian graph, the endpoints of a longest path of
length at least two cannot be adjacent. -/
theorem not_adj_end_start_of_longest_path {p : G.Walk a b}
    (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length)
    (hconn : G.Connected) (hnham : ¬ G.IsHamiltonian) : ¬ G.Adj b a := by
  intro hba
  have hedge : s(a, b) ∉ p.edges := by
    intro hedge
    have := hp.length_eq_one_of_mem_edges hedge
    omega
  let c : G.Walk b b := Walk.cons hba p
  have hc : c.IsCycle := by
    exact SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hba (by simpa [Sym2.eq_swap] using hedge)
  by_cases hall : ∀ v : V, v ∈ p.support
  · apply hnham
    intro _hcard
    refine ⟨b, c, ?_⟩
    refine ⟨hc, ?_⟩
    intro v
    simpa [c, Walk.IsHamiltonian] using hp.isHamiltonian_of_mem hall v
  · push_neg at hall
    obtain ⟨w, hw⟩ := hall
    let S : Finset V := p.support.toFinset
    obtain ⟨x, hxS, y, hyS, hxy⟩ :=
      Connected.exists_adj_mem_notMem G hconn S a (by simp [S]) w (by simpa [S] using hw)
    have hxp : x ∈ p.support := by simpa [S] using hxS
    have hxc : x ∈ c.support := by simp [c, hxp]
    let cr : G.Walk x x := c.rotate x hxc
    have hcr : cr.IsCycle := by
      exact hc.rotate hxc
    have hyr : y ∉ cr.tail.support := by
      intro hyr
      have hycr : y ∈ cr.support := by
        rw [cr.support_tail_of_not_nil hcr.not_nil] at hyr
        exact List.mem_of_mem_tail hyr
      have hyc : y ∈ c.support := by
        exact (c.mem_support_rotate_iff x hxc).mp hycr
      have hyp : y ∈ p.support := by
        simp only [c, Walk.support_cons, List.mem_cons] at hyc
        exact hyc.elim (fun h ↦ h ▸ p.end_mem_support) id
      exact hyS (by simpa [S] using hyp)
    have hlong : (cr.tail.concat hxy).IsPath :=
      hcr.isPath_tail.concat hyr hxy
    have hle := hmax _ _ (cr.tail.concat hxy) hlong
    have hcrnil : ¬ cr.Nil := hcr.not_nil
    have htail := Walk.length_tail_add_one hcrnil
    simp only [Walk.length_concat] at hle
    have hrot : cr.length = c.length := by simp [cr]
    have hclen : c.length = p.length + 1 := by simp [c]
    omega

/-- The external neighbourhood of the set of rotation endpoints is contained
in its neighbourhood along the original path.  The last hypothesis excludes
the separate cycle-closing case; it is discharged from connectedness and
non-Hamiltonicity when the booster theorem is applied. -/
theorem posa_outerNeighbor_subset_pathNeighborhood {p : G.Walk a b}
    (hp : p.IsPath) (hn : ¬ p.Nil)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length)
    (hclose : ∀ (c : V) (q : G.Walk a c), IsPosaReachable p q → ¬ G.Adj c a) :
    outerNeighborFinset G p.posaEndpointFinset ⊆
      p.pathNeighborhood p.posaEndpointFinset := by
  intro y hy
  rw [mem_outerNeighborFinset] at hy
  obtain ⟨hyR, c, hcR, hcy⟩ := hy
  rw [mem_posaEndpointFinset] at hcR
  obtain ⟨q, hq⟩ := hcR
  have hqp : q.IsPath := hq.isPath hp
  have hyq : y ∈ q.support := by
    by_contra hyq
    have hlong := hmax a y (q.concat hcy) (hqp.concat hyq hcy)
    rw [Walk.length_concat, hq.length_eq] at hlong
    omega
  have hya : y ≠ a := by
    intro hya
    subst y
    exact hclose c q hq hcy
  have hyc : y ≠ c := hcy.ne.symm
  let z : V := (q.dropUntil y hyq).snd
  have hzR : z ∈ p.posaEndpointFinset := by
    rw [mem_posaEndpointFinset]
    exact ⟨q.posaRotate y hyq hya hyc hcy,
      IsPosaReachable.rotate hq y hyq hya hyc hcy⟩
  have hd : ¬ (q.dropUntil y hyq).Nil := Walk.not_nil_of_ne hyc
  have hyzq : s(y, z) ∈ q.edges := by
    exact q.edges_dropUntil_subset_edges hyq
      ((q.dropUntil y hyq).mk_start_snd_mem_edges hd)
  by_cases hyzp : z ∈ p.pathNeighborFinset y
  · rw [mem_pathNeighborhood]
    refine ⟨z, hzR, ?_⟩
    rw [mem_pathNeighborFinset] at hyzp
    simpa [Sym2.eq_swap] using hyzp
  · have hyb : y ≠ b := by
      intro hyb
      subst y
      exact hyR (end_mem_posaEndpointFinset p)
    have hyp : y ∈ p.support := hq.support_perm hp |>.mem_iff.mp hyq
    have hcardP : (p.pathNeighborFinset y).card = 2 :=
      hp.card_pathNeighborFinset_eq_two hyp hya hyb
    have hcardQ : (q.pathNeighborFinset y).card ≤ 2 :=
      hqp.card_pathNeighborFinset_le_two hyq
    have hzQ : z ∈ q.pathNeighborFinset y := by
      rw [mem_pathNeighborFinset]
      exact hyzq
    have hnsub : ¬ p.pathNeighborFinset y ⊆ q.pathNeighborFinset y := by
      intro hsub
      have hins : insert z (p.pathNeighborFinset y) ⊆ q.pathNeighborFinset y :=
        Finset.insert_subset hzQ hsub
      have hc := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hyzp, hcardP] at hc
      omega
    obtain ⟨w, hwP, hwQ⟩ := Finset.not_subset.mp hnsub
    have hywP : s(y, w) ∈ p.edges := mem_pathNeighborFinset p y w |>.mp hwP
    have hywQ : s(y, w) ∉ q.edges := by
      intro he
      exact hwQ (mem_pathNeighborFinset q y w |>.mpr he)
    obtain ⟨u, huR, v, huv⟩ := hq.endpoint_of_missing_edge s(y, w) hywP hywQ
    have hwR : w ∈ p.posaEndpointFinset := by
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at huv
      rcases huv with ⟨hyu, hwv⟩ | ⟨hyv, hwu⟩
      · subst u
        exact (hyR huR).elim
      · subst u
        exact huR
    rw [mem_pathNeighborhood]
    refine ⟨w, hwR, ?_⟩
    simpa [Sym2.eq_swap] using hywP

/-- Pósa's endpoint-neighbourhood lemma in cardinal form. -/
theorem card_outerNeighbor_posaEndpoint_lt_two_mul {p : G.Walk a b}
    (hp : p.IsPath) (hn : ¬ p.Nil)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length)
    (hclose : ∀ (c : V) (q : G.Walk a c), IsPosaReachable p q → ¬ G.Adj c a) :
    (outerNeighborFinset G p.posaEndpointFinset).card <
      2 * p.posaEndpointFinset.card := by
  have hsub := posa_outerNeighbor_subset_pathNeighborhood hp hn hmax hclose
  refine (Finset.card_le_card hsub).trans_lt ?_
  apply hp.card_pathNeighborhood_lt_two_mul hn p.posaEndpointFinset
    (end_mem_posaEndpointFinset p)
  intro u hu
  rw [mem_posaEndpointFinset] at hu
  obtain ⟨q, hq⟩ := hu
  exact hq.support_perm hp |>.mem_iff.mp q.end_mem_support

/-- Expansion at a singleton forces every longest path to have at least two
edges. -/
theorem IsTwoExpanderUpTo.two_le_longest_path {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsTwoExpanderUpTo k) (hk : 1 ≤ k) (v : V)
    {a b : V} {p : G.Walk a b}
    (hmax : ∀ (u w : V) (q : G.Walk u w), q.IsPath → q.length ≤ p.length) :
    2 ≤ p.length := by
  have hexpand := hG {v} (by simp; omega)
  have hcard : 1 < (G.outerNeighborFinset {v}).card := by
    simp only [Finset.card_singleton, mul_one] at hexpand
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  rw [mem_outerNeighborFinset] at hx hy
  obtain ⟨hxv, ux, hux, hvx⟩ := hx
  obtain ⟨hyv, uy, huy, hvy⟩ := hy
  simp only [Finset.mem_singleton] at hux huy
  subst ux
  subst uy
  have hxne : x ≠ v := by simpa using hxv
  have hyne : y ≠ v := by simpa using hyv
  have hvyne : v ≠ y := hyne.symm
  let q : G.Walk x y := Walk.cons hvx.symm (Walk.cons hvy Walk.nil)
  have hq : q.IsPath := by
    simp [q, hxne, hvyne, hxy]
  have := hmax x y q hq
  simpa [q] using this

/-- A longest path in a connected non-Hamiltonian two-expander has at least
`k+1` endpoints obtainable by Pósa rotations. -/
theorem IsTwoExpanderUpTo.le_card_posaEndpointFinset {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsTwoExpanderUpTo k) (hk : 1 ≤ k) (hconn : G.Connected)
    (hnham : ¬ G.IsHamiltonian) {a b : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length) :
    k + 1 ≤ p.posaEndpointFinset.card := by
  have hlen : 2 ≤ p.length :=
    IsTwoExpanderUpTo.two_le_longest_path hG hk a hmax
  have hn : ¬ p.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    omega
  have hclose : ∀ (c : V) (q : G.Walk a c), IsPosaReachable p q → ¬ G.Adj c a := by
    intro c q hq
    have hmaxq : ∀ (u v : V) (r : G.Walk u v), r.IsPath → r.length ≤ q.length := by
      intro u v r hr
      rw [hq.length_eq]
      exact hmax u v r hr
    apply not_adj_end_start_of_longest_path (hq.isPath hp)
      (by rw [hq.length_eq]; exact hlen) hmaxq hconn hnham
  have hposa := card_outerNeighbor_posaEndpoint_lt_two_mul hp hn hmax hclose
  by_contra hle
  have hcard : p.posaEndpointFinset.card ≤ k := by omega
  have hexpand := hG p.posaEndpointFinset hcard
  omega

/-- Joining the fixed endpoint of a longest path to any endpoint obtainable by
rotations is a booster. -/
theorem isBooster_mk_of_isPosaReachable {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} {q : G.Walk a c}
    (hp : p.IsPath)
    (hmax : ∀ (u v : V) (r : G.Walk u v), r.IsPath → r.length ≤ p.length)
    (hconn : G.Connected) (hnham : ¬ G.IsHamiltonian)
    (hlen : 2 ≤ p.length) (hq : Walk.IsPosaReachable p q) :
    IsBooster G s(a, c) := by
  have hqp : q.IsPath := hq.isPath hp
  have hqlen : q.length = p.length := hq.length_eq
  have hmaxq : ∀ (u v : V) (r : G.Walk u v), r.IsPath → r.length ≤ q.length := by
    intro u v r hr
    rw [hqlen]
    exact hmax u v r hr
  have hnac : ¬ G.Adj c a :=
    not_adj_end_start_of_longest_path hqp (by omega) hmaxq hconn hnham
  have hac : a ≠ c := by
    intro hac
    subst c
    have : q = Walk.nil := Subtype.ext_iff.mp (SimpleGraph.Path.loop_eq ⟨q, hqp⟩)
    have hzero : q.length = 0 := by simpa [this]
    omega
  refine ⟨⟨?_, by simpa [Sym2.mk_isDiag_iff] using hac⟩, ?_⟩
  · intro he
    exact hnac ((SimpleGraph.mem_edgeSet (G := G)).mp (by simpa [Sym2.eq_swap] using he))
  · let H : SimpleGraph V := addEdge G s(a, c)
    let qH : H.Walk a c := q.mapLe (le_addEdge G s(a, c))
    have hqHp : qH.IsPath := hqp.mapLe (le_addEdge G s(a, c))
    have hcaH : H.Adj c a := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [H, Sym2.eq_swap] using
        (mem_edgeSet_addEdge_self (G := G) (e := s(a, c)) (by simpa [Sym2.mk_isDiag_iff] using hac))
    have hedge : s(a, c) ∉ qH.edges := by
      intro hedge
      have hone := hqHp.length_eq_one_of_mem_edges hedge
      simp only [qH, Walk.length_map] at hone
      omega
    let cyc : H.Walk c c := Walk.cons hcaH qH
    have hcyc : cyc.IsCycle := by
      exact SimpleGraph.Path.cons_isCycle ⟨qH, hqHp⟩ hcaH
        (by simpa [Sym2.eq_swap] using hedge)
    by_cases hall : ∀ v : V, v ∈ q.support
    · left
      intro _hcard
      refine ⟨c, cyc, hcyc, ?_⟩
      intro v
      have hhamq := hqp.isHamiltonian_of_mem hall
      simpa [cyc, qH, Walk.IsHamiltonian] using hhamq v
    · right
      push_neg at hall
      obtain ⟨w, hw⟩ := hall
      let S : Finset V := q.support.toFinset
      obtain ⟨x, hxS, y, hyS, hxy⟩ :=
        Connected.exists_adj_mem_notMem G hconn S a (by simp [S]) w (by simpa [S] using hw)
      have hxq : x ∈ q.support := by simpa [S] using hxS
      have hxc : x ∈ cyc.support := by simp [cyc, qH, hxq]
      let cr : H.Walk x x := cyc.rotate x hxc
      have hcr : cr.IsCycle := hcyc.rotate hxc
      have hyr : y ∉ cr.tail.support := by
        intro hyr
        have hycr : y ∈ cr.support := by
          rw [cr.support_tail_of_not_nil hcr.not_nil] at hyr
          exact List.mem_of_mem_tail hyr
        have hycyc : y ∈ cyc.support := (cyc.mem_support_rotate_iff x hxc).mp hycr
        have hyq : y ∈ q.support := by
          have hmap : qH.support = q.support := by simp [qH]
          simp only [cyc, Walk.support_cons, List.mem_cons] at hycyc
          rw [hmap] at hycyc
          exact hycyc.elim (fun h ↦ h ▸ q.end_mem_support) id
        exact hyS (by simpa [S] using hyq)
      have hxyH : H.Adj x y := (le_addEdge G s(a, c)) hxy
      have hlong : (cr.tail.concat hxyH).IsPath := hcr.isPath_tail.concat hyr hxyH
      have hle := path_length_le_maxPathLength hlong
      have hpLong : IsLongestPath p := isLongestPath_iff.mpr ⟨hp, hmax⟩
      have htail := Walk.length_tail_add_one hcr.not_nil
      have hrot : cr.length = cyc.length := by simp [cr]
      have hclen : cyc.length = q.length + 1 := by simp [cyc, qH]
      simp only [Walk.length_concat] at hle
      have hle' : cr.tail.length + 1 ≤ maxPathLength (addEdge G s(a, c)) := by
        simpa [H] using hle
      rw [← hpLong.length_eq]
      omega

end Walk

end

end SimpleGraph
