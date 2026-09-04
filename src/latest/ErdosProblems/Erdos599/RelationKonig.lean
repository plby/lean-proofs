/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Data.List.Duplicate
import Mathlib.Order.KonigLemma

/-!
# Kőnig's lemma for a locally finite directed relation

This file supplies the graph-theoretic formulation of Kőnig's infinity
lemma that is currently only listed as a TODO in `Mathlib.Order.KonigLemma`.
The proof applies Mathlib's order-theoretic theorem to the prefix order on
finite, vertex-simple directed paths from a fixed root.
-/

namespace Erdos599
namespace RelationKonig

open Set

universe u

variable {A : Type u} {r : A → A → Prop} {root : A}

/-- Removing a repeated vertex from a directed chain preserves its two
endpoints and strictly decreases its length. -/
private theorem exists_shorter_chain_of_duplicate
    {x : A} {l : List A}
    (hdup : List.Duplicate x l) (hchain : l.IsChain r) :
    ∃ l' : List A, l' ≠ [] ∧ l'.IsChain r ∧
      l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧
      l'.length < l.length := by
  induction hdup with
  | @cons_mem tail hx =>
      obtain ⟨pre, post, htail⟩ := List.append_of_mem hx
      subst tail
      let l' := x :: post
      refine ⟨l', by simp [l'], ?_, ?_, ?_, ?_⟩
      · apply hchain.suffix
        exact ⟨x :: pre, by simp [l', List.cons_append]⟩
      · simp [l']
      · rw [show x :: (pre ++ x :: post) =
          (x :: pre) ++ (x :: post) by simp]
        rw [List.getLast?_append_of_ne_nil (x :: pre)
          (by simp : x :: post ≠ [])]
      · simp [l']
  | @cons_duplicate y tail hdup ih =>
      obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
        ih hchain.tail
      refine ⟨y :: l', by simp, ?_, ?_, ?_, ?_⟩
      · apply hl'chain.cons
        intro z hz
        apply hchain.rel_head?
        rw [← hl'head]
        exact hz
      · simp
      · rw [show y :: l' = [y] ++ l' by rfl,
          List.getLast?_append_of_ne_nil [y] hl'ne]
        rw [show y :: tail = [y] ++ tail by rfl,
          List.getLast?_append_of_ne_nil [y] hdup.ne_nil]
        exact hl'last
      · simp only [List.length_cons]
        omega

/-- Every finite reflexive-transitive chain admits a vertex-simple list
realization with the same endpoints. -/
private theorem exists_nodup_chain_of_reflTransGen
    {a b : A} (h : Relation.ReflTransGen r a b) :
    ∃ l : List A, l ≠ [] ∧ l.IsChain r ∧
      l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup := by
  classical
  obtain ⟨l₀, hl₀ne, hl₀chain, hl₀head, hl₀last⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  let P : ℕ → Prop := fun n ↦
    ∃ l : List A, l ≠ [] ∧ l.IsChain r ∧
      l.head? = some a ∧ l.getLast? = some b ∧ l.length = n
  have hP : ∃ n, P n := by
    refine ⟨l₀.length, l₀, hl₀ne, hl₀chain, ?_, ?_, rfl⟩
    · rw [List.head?_eq_some_head hl₀ne, hl₀head]
    · rw [List.getLast?_eq_some_getLast hl₀ne, hl₀last]
  let n := Nat.find hP
  obtain ⟨l, hlne, hlchain, hlhead, hllast, hlen⟩ := Nat.find_spec hP
  refine ⟨l, hlne, hlchain, hlhead, hllast, ?_⟩
  by_contra hnot
  obtain ⟨x, hxdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hnot
  obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
    exists_shorter_chain_of_duplicate hxdup hlchain
  have hmin : n ≤ l'.length := Nat.find_min' hP
    ⟨l', hl'ne, hl'chain, by simpa [hlhead] using hl'head,
      by simpa [hllast] using hl'last, rfl⟩
  omega

/-- A finite vertex-simple `r`-path starting at `root`. -/
structure RootedSimplePath (r : A → A → Prop) (root : A) where
  vertices : List A
  ne_nil : vertices ≠ []
  head_eq : vertices.head ne_nil = root
  chain : vertices.IsChain r
  nodup : vertices.Nodup

namespace RootedSimplePath

@[ext]
theorem ext {p q : RootedSimplePath r root}
    (h : p.vertices = q.vertices) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The terminal vertex of a rooted simple path. -/
def terminal (p : RootedSimplePath r root) : A :=
  p.vertices.getLast p.ne_nil

instance : PartialOrder (RootedSimplePath r root) where
  le p q := p.vertices <+: q.vertices
  le_refl p := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm p q hpq hqp := by
    apply ext
    exact hpq.eq_of_length (hpq.length_le.antisymm hqp.length_le)

/-- The one-vertex root path is the bottom of the prefix order. -/
instance : OrderBot (RootedSimplePath r root) where
  bot := ⟨[root], by simp, by simp, by simp, by simp⟩
  bot_le p := by
    obtain ⟨x, xs, hx⟩ : ∃ x xs, p.vertices = x :: xs := by
      cases h : p.vertices with
      | nil => exact False.elim (p.ne_nil h)
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hxroot : x = root := by
      have := p.head_eq
      simp [hx] at this
      exact this
    subst x
    exact ⟨xs, by simpa using hx.symm⟩

/-- Prefixing a rooted simple path at a positive length again gives a rooted
simple path. -/
def take (p : RootedSimplePath r root) (n : ℕ) (hn : 0 < n)
    (hnp : n ≤ p.vertices.length) : RootedSimplePath r root where
  vertices := p.vertices.take n
  ne_nil := by
    intro hnil
    have := congr_arg List.length hnil
    simp only [List.length_take, List.length_nil] at this
    have hpos : 0 < min n p.vertices.length :=
      Nat.lt_min.mpr ⟨hn, List.length_pos_iff.mpr p.ne_nil⟩
    omega
  head_eq := by
    have ht : p.vertices.take n ≠ [] := by
      intro hnil
      have := congr_arg List.length hnil
      simp only [List.length_take, List.length_nil] at this
      have hpos : 0 < min n p.vertices.length :=
        Nat.lt_min.mpr ⟨hn, List.length_pos_iff.mpr p.ne_nil⟩
      omega
    rw [List.head_take ht]
    exact p.head_eq
  chain := p.chain.take n
  nodup := p.nodup.sublist (List.take_sublist _ _)

@[simp]
theorem take_vertices (p : RootedSimplePath r root) (n : ℕ)
    (hn : 0 < n) (hnp : n ≤ p.vertices.length) :
    (p.take n hn hnp).vertices = p.vertices.take n := rfl

/-- The prefix order on finite rooted simple paths is strongly atomic. -/
instance : IsStronglyAtomic (RootedSimplePath r root) where
  exists_covBy_le_of_lt p q hpq := by
    have hlen : p.vertices.length < q.vertices.length := by
      have hle := hpq.le.length_le
      exact hle.lt_of_ne (fun h ↦ hpq.ne (ext (hpq.le.eq_of_length h)))
    let s := q.take (p.vertices.length + 1) (by omega) (by omega)
    have hslen : s.vertices.length = p.vertices.length + 1 := by
      simp only [s, take_vertices, List.length_take]
      rw [Nat.min_eq_left (by omega)]
    refine ⟨s, ?_, ?_⟩
    · rw [covBy_iff_lt_and_eq_or_eq]
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · show p.vertices <+: s.vertices
          have hpTake : p.vertices.take (p.vertices.length + 1) = p.vertices :=
            List.take_of_length_le (by omega)
          rw [← hpTake]
          simpa [s, take] using hpq.le.take (p.vertices.length + 1)
        · intro hsp
          have := hsp.length_le
          omega
      · intro z hpz hzs
        by_cases hzp : z = p
        · exact Or.inl hzp
        · right
          apply ext
          have hplen : p.vertices.length < z.vertices.length := by
            by_contra hnlt
            have heqLen : p.vertices.length = z.vertices.length :=
              Nat.le_antisymm hpz.length_le (Nat.le_of_not_gt hnlt)
            exact hzp (ext (hpz.eq_of_length heqLen).symm)
          have hzlen : z.vertices.length ≤ p.vertices.length + 1 :=
            hzs.length_le.trans_eq hslen
          have heq : z.vertices.length = p.vertices.length + 1 := by omega
          exact hzs.eq_of_length (heq.trans hslen.symm)
    · show s.vertices <+: q.vertices
      simpa [s, take] using q.vertices.take_prefix (p.vertices.length + 1)

/-- Every reachable vertex is the terminal vertex of a finite rooted simple
path. -/
theorem exists_terminal_eq_of_reflTransGen
    {x : A} (hx : Relation.ReflTransGen r root x) :
    ∃ p : RootedSimplePath r root, p.terminal = x := by
  obtain ⟨l, hlne, hlchain, hlhead, hllast, hnodup⟩ :=
    exists_nodup_chain_of_reflTransGen hx
  refine ⟨⟨l, hlne, ?_, hlchain, hnodup⟩, ?_⟩
  · have hhead := hlhead
    rw [List.head?_eq_some_head hlne] at hhead
    exact Option.some.inj hhead
  · change l.getLast hlne = x
    have hlast := hllast
    rw [List.getLast?_eq_some_getLast hlne] at hlast
    exact Option.some.inj hlast

/-- Infinitely many vertices reachable from the root give infinitely many
finite rooted simple paths. -/
theorem infinite_rootedSimplePath
    (hinf : {x | Relation.ReflTransGen r root x}.Infinite) :
    Infinite (RootedSimplePath r root) := by
  by_contra hnot
  let : Finite (RootedSimplePath r root) := Finite.of_not_infinite hnot
  apply hinf
  refine (Set.finite_range (fun p : RootedSimplePath r root ↦ p.terminal)).subset ?_
  intro x hx
  obtain ⟨p, hp⟩ := exists_terminal_eq_of_reflTransGen hx
  exact ⟨p, hp⟩

/-- A cover in the prefix order appends precisely its new terminal vertex. -/
theorem vertices_eq_append_terminal_of_covBy
    {p q : RootedSimplePath r root} (hpq : p ⋖ q) :
    q.vertices = p.vertices ++ [q.terminal] := by
  have hpref : p.vertices <+: q.vertices := hpq.lt.le
  obtain ⟨suffix, hsuffix⟩ := hpref
  have hsuffix_ne : suffix ≠ [] := by
    intro hs
    exact hpq.lt.ne (ext (by simpa [hs] using hsuffix))
  obtain ⟨x, xs, hsx⟩ : ∃ x xs, suffix = x :: xs := by
    cases suffix with
    | nil => exact False.elim (hsuffix_ne rfl)
    | cons x xs => exact ⟨x, xs, rfl⟩
  subst suffix
  let z := q.take (p.vertices.length + 1)
    (by have := p.ne_nil; simpa using List.length_pos.2 this)
    (by rw [← hsuffix]; simp)
  have hpz : p ≤ z := by
    show p.vertices <+: z.vertices
    have hpTake : p.vertices.take (p.vertices.length + 1) = p.vertices :=
      List.take_of_length_le (by omega)
    rw [← hpTake]
    simpa [z, take] using hpq.lt.le.take (p.vertices.length + 1)
  have hzq : z ≤ q := by
    show z.vertices <+: q.vertices
    simpa [z, take] using q.vertices.take_prefix (p.vertices.length + 1)
  have hzp_or_zq := hpq.eq_or_eq hpz hzq
  have hzp : z ≠ p := by
    intro h
    have hle := congr_arg (fun w : RootedSimplePath r root ↦ w.vertices.length) h
    simp [z, take, ← hsuffix] at hle
  have hzq_eq : z = q := hzp_or_zq.resolve_left hzp
  have hzlen : z.vertices.length = p.vertices.length + 1 := by
    simp only [z, take_vertices, List.length_take]
    rw [Nat.min_eq_left]
    rw [← hsuffix]
    simp
  have hxs : xs = [] := by
    have hqLen : q.vertices.length = p.vertices.length + 1 := by
      rw [← hzq_eq]
      exact hzlen
    have hsLen := congr_arg List.length hsuffix
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp at hsLen
    omega
  subst xs
  simp [terminal, ← hsuffix]

/-- A cover in the prefix order extends a path by exactly one outgoing edge. -/
theorem covBy_terminal
    {p q : RootedSimplePath r root} (hpq : p ⋖ q) :
    r p.terminal q.terminal := by
  have hvertices := vertices_eq_append_terminal_of_covBy hpq
  have hchain : (p.vertices ++ [q.terminal]).IsChain r := by
    rw [← hvertices]
    exact q.chain
  have hrel := (List.isChain_append.mp hchain).2.2
    p.terminal (by
      rw [Option.mem_def, List.getLast?_eq_some_getLast p.ne_nil]
      simp [terminal])
    q.terminal (by simp)
  exact hrel

/-- Strictly extending a vertex-simple path changes its terminal vertex. -/
theorem terminal_ne_of_lt
    {p q : RootedSimplePath r root} (hpq : p < q) :
    p.terminal ≠ q.terminal := by
  obtain ⟨suffix, hsuffix⟩ := hpq.le
  have hsuffix_ne : suffix ≠ [] := by
    intro hs
    apply hpq.ne
    apply ext
    simpa [hs] using hsuffix
  have hnodup : (p.vertices ++ suffix).Nodup := by
    rw [hsuffix]
    exact q.nodup
  have hsep := (List.nodup_append.mp hnodup).2.2
  intro heq
  have hqterm : q.terminal = suffix.getLast hsuffix_ne := by
    change q.vertices.getLast q.ne_nil = suffix.getLast hsuffix_ne
    apply Option.some.inj
    rw [← List.getLast?_eq_some_getLast q.ne_nil,
      ← List.getLast?_eq_some_getLast hsuffix_ne, ← hsuffix]
    exact List.getLast?_append_of_ne_nil p.vertices hsuffix_ne
  exact (hsep p.terminal (List.getLast_mem p.ne_nil)
    (suffix.getLast hsuffix_ne) (List.getLast_mem hsuffix_ne))
    (heq.trans hqterm)

end RootedSimplePath

/-- Graph-theoretic Kőnig infinity lemma for a directed relation with
finite outgoing neighbourhoods. -/
theorem exists_injective_ray_of_finite_out
    (hfin : ∀ a : A, {b | r a b}.Finite)
    (hinf : {b | Relation.ReflTransGen r root b}.Infinite) :
    ∃ f : ℕ → A,
      f 0 = root ∧ Function.Injective f ∧
        ∀ n, r (f n) (f (n + 1)) := by
  classical
  let _ : Infinite (RootedSimplePath r root) :=
    RootedSimplePath.infinite_rootedSimplePath hinf
  have hcovers : ∀ p : RootedSimplePath r root, {q | p ⋖ q}.Finite := by
    intro p
    apply Set.Finite.of_finite_image
      ((hfin p.terminal).subset (fun b hb ↦ by
        obtain ⟨q, hq, rfl⟩ := hb
        exact RootedSimplePath.covBy_terminal hq))
    intro q hq q' hq' heq
    change q.terminal = q'.terminal at heq
    apply RootedSimplePath.ext
    rw [RootedSimplePath.vertices_eq_append_terminal_of_covBy hq,
      RootedSimplePath.vertices_eq_append_terminal_of_covBy hq']
    exact congrArg (fun x ↦ p.vertices ++ [x]) heq
  obtain ⟨P, hP0, hPstep⟩ :=
    exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hcovers
  let f : ℕ → A := fun n ↦ (P n).terminal
  refine ⟨f, ?_, ?_, ?_⟩
  · change (P 0).terminal = root
    rw [hP0]
    rfl
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · exact RootedSimplePath.terminal_ne_of_lt (P.strictMono hijlt) hij
    · exact RootedSimplePath.terminal_ne_of_lt (P.strictMono hjilt) hij.symm
  · intro n
    exact RootedSimplePath.covBy_terminal (hPstep n)

end RelationKonig
end Erdos599
