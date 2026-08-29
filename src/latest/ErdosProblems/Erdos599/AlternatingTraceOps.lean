/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Operations on finite and infinite alternating traces

This file supplies the elementary constructors used by the recursive
alternating-path argument.  In particular, it proves that a link can be
appended to a finite trace once the new join, alternation, and all new
ordered-compatibility obligations have been discharged.  It also packages
a coherent family of finite prefixes and turns it into an infinite trace.
-/

namespace Erdos599.Alternating

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

/-- The compatibility obligations between every old link of `Q` and a new
last link `l`.  The displayed proposition records precisely when that pair
is adjacent in the extended trace. -/
def SnocCompatible (Q : FiniteTrace D) (l : Link D) : Prop :=
  ∀ i : Fin (Q.lastIndex + 1),
    CompatibleInOrder (Q.lastIndex + 1 = i.1 + 1) (Q.link i) l

/-- Append a link to a finite alternating trace. -/
def snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) : FiniteTrace D where
  lastIndex := Q.lastIndex + 1
  link := Fin.snoc Q.link l
  joins := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using Q.joins i
    · simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
      have hlast :
          (⟨Q.lastIndex, Nat.lt_succ_self Q.lastIndex⟩ : Fin (Q.lastIndex + 1)) =
            Fin.last Q.lastIndex := by
        ext
        rfl
      simpa only [terminal, lastLink, hlast] using hjoin
  alternates := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using Q.alternates i
    · simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
      have hlast :
          (⟨Q.lastIndex, Nat.lt_succ_self Q.lastIndex⟩ : Fin (Q.lastIndex + 1)) =
            Fin.last Q.lastIndex := by
        ext
        rfl
      simpa only [lastLink, hlast] using halt
  compatible := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        change CompatibleInOrder (j.1 = i.1 + 1) (Q.link i) (Q.link j)
        exact Q.compatible i j (by simpa using hij)
      · exact False.elim ((not_lt_of_ge (Fin.castSucc_lt_last j).le) hij)
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        change CompatibleInOrder (Q.lastIndex + 1 = i.1 + 1) (Q.link i) l
        exact hcompat i
      · exact False.elim (lt_irrefl _ hij)

@[simp]
theorem snoc_lastIndex (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).lastIndex = Q.lastIndex + 1 :=
  rfl

@[simp]
theorem snoc_link_castSucc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) (i : Fin (Q.lastIndex + 1)) :
    (Q.snoc l hjoin halt hcompat).link i.castSucc = Q.link i := by
  simp [snoc]

@[simp]
theorem snoc_link_last (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).link (Fin.last (Q.lastIndex + 1)) = l := by
  simp [snoc]

@[simp]
theorem firstLink_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).firstLink = Q.firstLink := by
  change (Q.snoc l hjoin halt hcompat).link
      ⟨0, Nat.zero_lt_succ (Q.lastIndex + 1)⟩ =
    Q.link ⟨0, Nat.zero_lt_succ Q.lastIndex⟩
  simpa using snoc_link_castSucc Q l hjoin halt hcompat
    (⟨0, Nat.zero_lt_succ Q.lastIndex⟩ : Fin (Q.lastIndex + 1))

@[simp]
theorem lastLink_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).lastLink = l := by
  change (Q.snoc l hjoin halt hcompat).link (Fin.last (Q.lastIndex + 1)) = l
  exact snoc_link_last Q l hjoin halt hcompat

@[simp]
theorem initial_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).initial = Q.initial := by
  simp [initial]

@[simp]
theorem terminal_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).terminal = l.exit := by
  simp [terminal]

@[simp]
theorem links_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).links = Q.links ∪ {l} := by
  change Set.range (Fin.snoc Q.link l) = Set.range Q.link ∪ {l}
  ext k
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast i => exact Or.inl ⟨i, by simp⟩
  · intro hk
    rcases hk with hk | hk
    · rcases hk with ⟨i, rfl⟩
      exact ⟨i.castSucc, by simp⟩
    · have : k = l := by simpa using hk
      subst k
      exact ⟨Fin.last (Q.lastIndex + 1), by simp⟩

@[simp]
theorem vertexSet_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).vertexSet =
      Q.vertexSet ∪ l.path.support := by
  simp only [vertexSet, snoc]
  ext v
  constructor
  · intro hv
    rcases Set.mem_iUnion.1 hv with ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi)
    | cast i => exact Or.inl (Set.mem_iUnion.2 ⟨i, by simpa using hi⟩)
  · rintro (hv | hv)
    · rcases Set.mem_iUnion.1 hv with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i.castSucc, by simpa using hi⟩
    · exact Set.mem_iUnion.2 ⟨Fin.last (Q.lastIndex + 1), by simpa⟩

@[simp]
theorem edgeSet_snoc (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.terminal = l.entry)
    (halt : Q.lastLink.direction ≠ l.direction)
    (hcompat : Q.SnocCompatible l) :
    (Q.snoc l hjoin halt hcompat).edgeSet =
      Q.edgeSet ∪ l.path.edgeSet := by
  simp only [edgeSet, snoc]
  ext e
  constructor
  · intro he
    rcases Set.mem_iUnion.1 he with ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi)
    | cast i => exact Or.inl (Set.mem_iUnion.2 ⟨i, by simpa using hi⟩)
  · rintro (he | he)
    · rcases Set.mem_iUnion.1 he with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i.castSucc, by simpa using hi⟩
    · exact Set.mem_iUnion.2 ⟨Fin.last (Q.lastIndex + 1), by simpa⟩

end FiniteTrace

/-! ## Coherent finite prefixes -/

/-- The data and laws of an alternating trace with exactly `n + 1` links.
Unlike `FiniteTrace`, the final index is exposed in the type, which makes
families of finite prefixes painless to use. -/
structure FinitePrefix (D : Digraph V) (n : ℕ) where
  link : Fin (n + 1) → Link D
  joins : ∀ i : Fin n,
    (link i.castSucc).exit = (link i.succ).entry
  alternates : ∀ i : Fin n,
    (link i.castSucc).direction ≠ (link i.succ).direction
  compatible : ∀ (i j : Fin (n + 1)), i < j →
    CompatibleInOrder (j.1 = i.1 + 1) (link i) (link j)

namespace FinitePrefix

/-- Reindex a `FiniteTrace` whose last index is known to be `n`. -/
def ofFiniteTrace (Q : FiniteTrace D) {n : ℕ} (hindex : Q.lastIndex = n) :
    FinitePrefix D n := by
  subst n
  exact {
    link := Q.link
    joins := Q.joins
    alternates := Q.alternates
    compatible := Q.compatible }

/-- Forget the type-level final index. -/
def toFiniteTrace (Q : FinitePrefix D n) : FiniteTrace D where
  lastIndex := n
  link := Q.link
  joins := Q.joins
  alternates := Q.alternates
  compatible := Q.compatible

@[simp]
theorem toFiniteTrace_lastIndex (Q : FinitePrefix D n) :
    Q.toFiniteTrace.lastIndex = n :=
  rfl

@[simp]
theorem toFiniteTrace_link (Q : FinitePrefix D n) (i : Fin (n + 1)) :
    Q.toFiniteTrace.link i = Q.link i :=
  rfl

@[simp]
theorem ofFiniteTrace_link (Q : FiniteTrace D) {n : ℕ}
    (hindex : Q.lastIndex = n) (i : Fin (n + 1)) :
    (ofFiniteTrace Q hindex).link i =
      Q.link (Fin.cast (congrArg (fun k ↦ k + 1) hindex.symm) i) := by
  subst n
  rfl

end FinitePrefix

/-- A coherent ω-sequence of finite alternating prefixes.  The equation
`prefix_link` says that every prefix is literally the restriction of one
global link sequence; in particular successive prefixes are coherent. -/
structure PrefixChain (D : Digraph V) where
  link : ℕ → Link D
  prefixes : (n : ℕ) → FinitePrefix D n
  prefix_link : ∀ n (i : Fin (n + 1)), (prefixes n).link i = link i.1

namespace PrefixChain

/-- Build coherent finite prefixes from a global sequence whose every pair
of successive links joins and alternates and whose ordered pairs satisfy the
collision rule. -/
def ofLinks (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) : PrefixChain D where
  link := f
  prefixes := fun n ↦ {
    link := fun i ↦ f i.1
    joins := by
      intro i
      simpa using hjoins i.1
    alternates := by
      intro i
      simpa using halts i.1
    compatible := by
      intro i j hij
      exact hcompat i.1 j.1 (by simpa using hij) }
  prefix_link := fun _ _ ↦ rfl

/-- Package an already constructed coherent family of finite traces.  The
equation `hlink` is the only cross-prefix coherence obligation. -/
def ofFiniteTraces (f : ℕ → Link D) (Q : ℕ → FiniteTrace D)
    (hindex : ∀ n, (Q n).lastIndex = n)
    (hlink : ∀ n (i : Fin (n + 1)),
      (FinitePrefix.ofFiniteTrace (Q n) (hindex n)).link i = f i.1) :
    PrefixChain D where
  link := f
  prefixes := fun n ↦ FinitePrefix.ofFiniteTrace (Q n) (hindex n)
  prefix_link := hlink

@[simp]
theorem ofLinks_link (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) (n : ℕ) :
    (ofLinks f hjoins halts hcompat).link n = f n :=
  rfl

/-- Every link of a prefix is identified with the global link sequence. -/
@[simp]
theorem prefix_link_eq (C : PrefixChain D) (n : ℕ) (i : Fin (n + 1)) :
    (C.prefixes n).link i = C.link i.1 :=
  C.prefix_link n i

/-- Turn a coherent family of all finite prefixes into an infinite
alternating trace. -/
def toInfiniteTrace (C : PrefixChain D) : InfiniteTrace D where
  link := C.link
  joins := by
    intro n
    have h := (C.prefixes (n + 1)).joins (Fin.last n)
    simpa using h
  alternates := by
    intro n
    have h := (C.prefixes (n + 1)).alternates (Fin.last n)
    simpa using h
  compatible := by
    intro i j hij
    let i' : Fin (j + 1) := ⟨i, Nat.lt_succ_iff.2 (Nat.le_of_lt hij)⟩
    let j' : Fin (j + 1) := Fin.last j
    have h := (C.prefixes j).compatible i' j' (by
      change i < j
      exact hij)
    simpa [i', j'] using h

@[simp]
theorem toInfiniteTrace_link (C : PrefixChain D) (n : ℕ) :
    C.toInfiniteTrace.link n = C.link n :=
  rfl

@[simp]
theorem toInfiniteTrace_initial (C : PrefixChain D) :
    C.toInfiniteTrace.initial = ((C.prefixes 0).link 0).entry := by
  simp [InfiniteTrace.initial, toInfiniteTrace]

@[simp]
theorem toInfiniteTrace_links (C : PrefixChain D) :
    C.toInfiniteTrace.links = Set.range C.link :=
  rfl

@[simp]
theorem toInfiniteTrace_vertexSet (C : PrefixChain D) :
    C.toInfiniteTrace.vertexSet = ⋃ n, (C.link n).path.support :=
  rfl

@[simp]
theorem toInfiniteTrace_edgeSet (C : PrefixChain D) :
    C.toInfiniteTrace.edgeSet = ⋃ n, (C.link n).path.edgeSet :=
  rfl

end PrefixChain

namespace InfiniteTrace

/-- Convenience constructor for an infinite alternating trace from its
global link sequence and the three defining laws. -/
def ofLinks (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) : InfiniteTrace D :=
  (PrefixChain.ofLinks f hjoins halts hcompat).toInfiniteTrace

@[simp]
theorem ofLinks_link (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) (n : ℕ) :
    (ofLinks f hjoins halts hcompat).link n = f n :=
  rfl

@[simp]
theorem ofLinks_initial (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) :
    (ofLinks f hjoins halts hcompat).initial = (f 0).entry :=
  rfl

@[simp]
theorem ofLinks_vertexSet (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) :
    (ofLinks f hjoins halts hcompat).vertexSet =
      ⋃ n, (f n).path.support :=
  rfl

@[simp]
theorem ofLinks_edgeSet (f : ℕ → Link D)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j)) :
    (ofLinks f hjoins halts hcompat).edgeSet =
      ⋃ n, (f n).path.edgeSet :=
  rfl

end InfiniteTrace

end Erdos599.Alternating
namespace Erdos599.DirectedPath

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace Walk

private theorem edgeSet_append_trace {a b c : V} (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp
  | cons h p ih =>
      ext e
      simp [ih, or_assoc]

theorem start_not_mem_support_tail {a b : V} (p : Walk D a b)
    (hp : p.IsPath) : a ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons h tail =>
      exact (List.nodup_cons.mp hp).1

theorem edgeSet_castStart {a a' b : V} (h : a = a') (p : Walk D a b) :
    (RelationalRoof.castStart D.Adj h p).edgeSet = p.edgeSet := by
  subst a'
  rfl

/-- Every edge of a finite walk occurs at two consecutive positions in its
ordered support. -/
theorem exists_adjacent_getElem_of_mem_edgeSet {a b x y : V}
    (p : Walk D a b) (hxy : (x, y) ∈ p.edgeSet) :
    ∃ n, ∃ hn : n + 1 < p.support.length,
      p.support[n] = x ∧ p.support[n + 1] = y := by
  induction p with
  | nil => simp at hxy
  | @cons a c b h tail ih =>
      simp only [edgeSet_cons, Set.mem_union, Set.mem_singleton_iff,
        Prod.mk.injEq] at hxy
      rcases hxy with hxy | hxy
      · refine ⟨0, ?_, ?_, ?_⟩
        · simp only [support_cons, List.length_cons]
          have ht : 0 < tail.support.length :=
            List.length_pos_iff.mpr tail.support_ne_nil
          omega
        · simpa using hxy.1.symm
        · have ht : 0 < tail.support.length :=
            List.length_pos_iff.mpr tail.support_ne_nil
          have hc : tail.support[0]'ht = c := by
            exact (List.getElem_zero ht).trans
              tail.head_support
          simpa using hc.trans hxy.2.symm
      · obtain ⟨n, hn, hnx, hny⟩ := ih hxy
        refine ⟨n + 1, ?_, ?_, ?_⟩
        · simp only [support_cons, List.length_cons]
          omega
        · simpa [Walk.support_cons] using hnx
        · simpa [Walk.support_cons, Nat.add_assoc] using hny

/-- A walk using only edges of a finite simple path moves weakly forward in
the ambient path's ordered support. -/
theorem position_mono_in_finitePath (P : FinitePath D)
    {a b : V} (w : Walk D a b) (hedge : w.edgeSet ⊆ P.edgeSet)
    (ia ib : Fin P.walk.support.length)
    (hia : P.walk.support.get ia = a) (hib : P.walk.support.get ib = b) :
    ia ≤ ib := by
  induction w generalizing ia with
  | nil =>
      have hget : P.walk.support.get ia = P.walk.support.get ib := hia.trans hib.symm
      exact (P.isPath.get_inj_iff.mp hget).le
  | @cons a c b h tail ih =>
      have hac : (a, c) ∈ P.edgeSet := hedge (by simp)
      obtain ⟨n, hn, hna, hnc⟩ :=
        P.walk.exists_adjacent_getElem_of_mem_edgeSet hac
      let ic : Fin P.walk.support.length := ⟨n + 1, hn⟩
      let ina : Fin P.walk.support.length := ⟨n, by omega⟩
      have hiaeq : ia = ina := by
        apply P.isPath.get_inj_iff.mp
        simpa [ina] using hia.trans hna.symm
      have htail : tail.edgeSet ⊆ P.edgeSet := by
        intro e he
        exact hedge (Set.mem_union_right _ he)
      have hic : P.walk.support.get ic = c := by simpa [ic] using hnc
      have hle := ih htail ic hic hib
      rw [hiaeq]
      change n ≤ ib.1
      change n + 1 ≤ ib.1 at hle
      omega

/-- A walk using only edges of a ray moves weakly forward in its ray index. -/
theorem position_mono_in_ray (r : Ray D)
    {a b : V} (w : Walk D a b) (hedge : w.edgeSet ⊆ r.edgeSet)
    (ia ib : ℕ) (hia : r ia = a) (hib : r ib = b) : ia ≤ ib := by
  induction w generalizing ia with
  | nil =>
      exact (r.injective (hia.trans hib.symm)).le
  | @cons a c b h tail ih =>
      have hac : (a, c) ∈ r.edgeSet := hedge (by simp)
      rcases hac with ⟨n, hn⟩
      have hian : ia = n := r.injective <|
        hia.trans (congrArg Prod.fst hn)
      have htail : tail.edgeSet ⊆ r.edgeSet := by
        intro e he
        exact hedge (Set.mem_union_right _ he)
      have hnc : r (n + 1) = c := (congrArg Prod.snd hn).symm
      have hle := ih htail (n + 1) hnc hib
      rw [hian]
      omega

end Walk

namespace FinitePath

/-- Two fragments of one directed simple path, the first ending where the
second starts, meet only at that joining vertex. -/
theorem support_inter_subset_singleton_of_isSubpathOf
    (q r : FinitePath D) (P : Path D)
    (hq : q.IsSubpathOf P) (hr : r.IsSubpathOf P)
    (hjoin : q.finish = r.start) :
    q.support ∩ r.support ⊆ {q.finish} := by
  intro x hx
  have hxq := hx.1
  have hxr := hx.2
  rcases P with P | R
  · obtain ⟨ix, hix, hixval⟩ := List.mem_iff_getElem.mp (hq.1 hxq)
    obtain ⟨ij, hij, hijval⟩ := List.mem_iff_getElem.mp (hq.1 q.finish_mem_support)
    let fix : Fin P.walk.support.length := ⟨ix, hix⟩
    let fij : Fin P.walk.support.length := ⟨ij, hij⟩
    let qs := q.suffixFrom x hxq
    have hqsedge : qs.walk.edgeSet ⊆ P.edgeSet :=
      (q.suffixFrom_edgeSet_subset x hxq).trans hq.2
    have hxi : fix ≤ fij := by
      apply Walk.position_mono_in_finitePath P qs.walk hqsedge fix fij
      · exact hixval.trans (q.suffixFrom_start x hxq).symm
      · exact hijval.trans (q.suffixFrom_finish x hxq).symm
    obtain ⟨ix', hix', hix'val⟩ := List.mem_iff_getElem.mp (hr.1 hxr)
    obtain ⟨ij', hij', hij'val⟩ := List.mem_iff_getElem.mp (hr.1 r.start_mem_support)
    let fix' : Fin P.walk.support.length := ⟨ix', hix'⟩
    let fij' : Fin P.walk.support.length := ⟨ij', hij'⟩
    have hfix : fix = fix' := by
      apply P.isPath.get_inj_iff.mp
      simpa [fix, fix'] using hixval.trans hix'val.symm
    have hfij : fij = fij' := by
      apply P.isPath.get_inj_iff.mp
      simpa [fij, fij'] using hijval.trans (hjoin.trans hij'val.symm)
    let rm := r.walk.firstHit ({x} : Set V) ⟨x, hxr, Set.mem_singleton x⟩
    have hrmedge : rm.walk.edgeSet ⊆ P.edgeSet :=
      (Walk.edgeSet_subset_of_support_prefix rm.walk r.walk rm.support_prefix).trans hr.2
    have hijx : fij' ≤ fix' := by
      apply Walk.position_mono_in_finitePath P rm.walk hrmedge fij' fix'
      · simpa [fij', hjoin] using hij'val
      · have hend : rm.endpoint = x := Set.mem_singleton_iff.mp rm.endpoint_mem
        simpa [fix', hend] using hix'val
    have heq : fix = fij := le_antisymm hxi (by simpa [hfix, hfij] using hijx)
    have hxfinish : x = q.finish := by
      calc
        x = P.walk.support.get fix := by simpa [fix] using hixval.symm
        _ = P.walk.support.get fij := congrArg _ heq
        _ = q.finish := by simpa [fij] using hijval
    simpa [hxfinish]
  · rcases hq.1 hxq with ⟨ix, hixval⟩
    rcases hq.1 q.finish_mem_support with ⟨ij, hijval⟩
    let qs := q.suffixFrom x hxq
    have hqsedge : qs.walk.edgeSet ⊆ R.edgeSet :=
      (q.suffixFrom_edgeSet_subset x hxq).trans hq.2
    have hxi : ix ≤ ij := by
      apply Walk.position_mono_in_ray R qs.walk hqsedge ix ij
      · exact hixval.trans (q.suffixFrom_start x hxq).symm
      · exact hijval.trans (q.suffixFrom_finish x hxq).symm
    rcases hr.1 hxr with ⟨ix', hix'val⟩
    rcases hr.1 r.start_mem_support with ⟨ij', hij'val⟩
    have hixeq : ix = ix' := R.injective (hixval.trans hix'val.symm)
    have hijeq : ij = ij' :=
      R.injective (hijval.trans (hjoin.trans hij'val.symm))
    let rm := r.walk.firstHit ({x} : Set V) ⟨x, hxr, Set.mem_singleton x⟩
    have hrmedge : rm.walk.edgeSet ⊆ R.edgeSet :=
      (Walk.edgeSet_subset_of_support_prefix rm.walk r.walk rm.support_prefix).trans hr.2
    have hijx : ij' ≤ ix' := by
      apply Walk.position_mono_in_ray R rm.walk hrmedge ij' ix'
      · simpa [hjoin] using hij'val
      · have hend : rm.endpoint = x := Set.mem_singleton_iff.mp rm.endpoint_mem
        simpa [hend] using hix'val
    have heq : ix = ij := le_antisymm hxi (by omega)
    have hxfinish : x = q.finish := by
      calc
        x = R ix := hixval.symm
        _ = R ij := congrArg R.toFun heq
        _ = q.finish := hijval
    simpa [hxfinish]

/-- Append two ambient-path fragments which meet end-to-start. -/
theorem exists_append_isSubpathOf
    (q r : FinitePath D) (P : Path D)
    (hq : q.IsSubpathOf P) (hr : r.IsSubpathOf P)
    (hjoin : q.finish = r.start) :
    ∃ s : FinitePath D,
      s.start = q.start ∧ s.finish = r.finish ∧ s.IsSubpathOf P ∧
      s.support = q.support ∪ r.support ∧
      s.edgeSet = q.edgeSet ∪ r.edgeSet := by
  have hinter : q.support ∩ r.support ⊆ {q.finish} :=
    support_inter_subset_singleton_of_isSubpathOf q r P hq hr hjoin
  let rw : Walk D q.finish r.finish :=
    RelationalRoof.castStart D.Adj hjoin.symm r.walk
  have hrwsupport : rw.support = r.walk.support :=
    RelationalRoof.support_castStart D.Adj hjoin.symm r.walk
  have hrwedge : rw.edgeSet = r.walk.edgeSet :=
    Walk.edgeSet_castStart hjoin.symm r.walk
  have hdisjoint : q.walk.support.Disjoint r.walk.support.tail := by
    rw [List.disjoint_left]
    intro x hxq hxrw
    have hxrtail : x ∈ r.walk.support.tail := hxrw
    have hxr : x ∈ r.support := List.mem_of_mem_tail hxrtail
    have hxfinish : x = q.finish := by simpa using hinter ⟨hxq, hxr⟩
    have hxstart : x = r.start := hxfinish.trans hjoin
    exact r.walk.start_not_mem_support_tail r.isPath (hxstart ▸ hxrtail)
  let s : FinitePath D :=
    { start := q.start
      finish := r.finish
      walk := q.walk.append rw
      isPath := by
        rw [Walk.IsPath, Walk.support_append, hrwsupport]
        exact q.isPath.append r.isPath.tail hdisjoint }
  have hqedge : q.walk.edgeSet ⊆ P.edgeSet := by
    simpa only [FinitePath.IsSubpathOf, Path.IsSubpathOf,
      Path.edgeSet_finite, FinitePath.edgeSet] using hq.2
  have hredge : r.walk.edgeSet ⊆ P.edgeSet := by
    simpa only [FinitePath.IsSubpathOf, Path.IsSubpathOf,
      Path.edgeSet_finite, FinitePath.edgeSet] using hr.2
  refine ⟨s, rfl, rfl, ?_, ?_, ?_⟩
  · constructor
    · intro x hx
      change x ∈ (q.walk.append rw).support at hx
      rw [Walk.support_append, hrwsupport] at hx
      rcases List.mem_append.mp hx with hxq | hxr
      · exact hq.1 hxq
      · exact hr.1 (List.mem_of_mem_tail hxr)
    · intro e he
      change e ∈ (q.walk.append rw).edgeSet at he
      rw [Walk.edgeSet_append_trace, hrwedge] at he
      exact he.elim (fun heq ↦ hqedge heq) (fun her ↦ hredge her)
  · ext x
    change (x ∈ (q.walk.append rw).support) ↔ x ∈ q.support ∪ r.support
    rw [Walk.support_append, hrwsupport]
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hxq | hxr
      · exact Or.inl hxq
      · exact Or.inr (List.mem_of_mem_tail hxr)
    · rintro (hxq | hxr)
      · exact List.mem_append_left _ hxq
      · by_cases hx : x = r.start
        · apply List.mem_append_left
          simpa [hx, ← hjoin] using q.finish_mem_support
        · apply List.mem_append_right
          change x ∈ r.walk.support at hxr
          have hrdecomp : r.walk.support = r.start :: r.walk.support.tail := by
            exact (List.cons_head_tail r.walk.support_ne_nil).symm.trans <|
              congrArg (fun z ↦ z :: r.walk.support.tail) r.walk.head_support
          rw [hrdecomp] at hxr
          simpa [hx] using hxr
  · change (q.walk.append rw).edgeSet = q.walk.edgeSet ∪ r.walk.edgeSet
    rw [Walk.edgeSet_append_trace, hrwedge]

end FinitePath

end Erdos599.DirectedPath

namespace Erdos599.Alternating

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

/-- The initial trace ending with link `k`. -/
def takeThrough (Q : FiniteTrace D) (k : Fin (Q.lastIndex + 1)) :
    FiniteTrace D where
  lastIndex := k.1
  link i := Q.link ⟨i.1, by omega⟩
  joins := by
    intro i
    let j : Fin Q.lastIndex := ⟨i.1, by omega⟩
    simpa [j] using Q.joins j
  alternates := by
    intro i
    let j : Fin Q.lastIndex := ⟨i.1, by omega⟩
    simpa [j] using Q.alternates j
  compatible := by
    intro i j hij
    let i' : Fin (Q.lastIndex + 1) := ⟨i.1, by omega⟩
    let j' : Fin (Q.lastIndex + 1) := ⟨j.1, by omega⟩
    change CompatibleInOrder (j.1 = i.1 + 1) (Q.link i') (Q.link j')
    exact Q.compatible i' j' (by simpa [i', j'] using hij)

@[simp]
theorem takeThrough_lastIndex (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).lastIndex = k.1 :=
  rfl

@[simp]
theorem takeThrough_link (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) (i : Fin (k.1 + 1)) :
    (Q.takeThrough k).link i =
      Q.link ⟨i.1, by omega⟩ :=
  rfl

@[simp]
theorem firstLink_takeThrough (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).firstLink = Q.firstLink := by
  change Q.link ⟨0, _⟩ = Q.link 0
  rfl

@[simp]
theorem lastLink_takeThrough (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).lastLink = Q.link k := by
  change Q.link ⟨k.1, _⟩ = Q.link k
  apply congrArg Q.link
  apply Fin.ext
  rfl

@[simp]
theorem initial_takeThrough (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).initial = Q.initial := by
  simp [initial]

@[simp]
theorem terminal_takeThrough (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).terminal = (Q.link k).exit := by
  simp [terminal]

theorem links_takeThrough_subset (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).links ⊆ Q.links := by
  rintro l ⟨i, rfl⟩
  have hi : i.1 < k.1 + 1 := by
    simpa only [takeThrough_lastIndex] using i.2
  exact ⟨⟨i.1, by omega⟩, rfl⟩

theorem vertexSet_takeThrough_subset (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).vertexSet ⊆ Q.vertexSet := by
  intro v hv
  rcases Set.mem_iUnion.1 hv with ⟨i, hi⟩
  have hibound : i.1 < k.1 + 1 := by
    simpa only [takeThrough_lastIndex] using i.2
  exact Set.mem_iUnion.2 ⟨⟨i.1, by omega⟩, hi⟩

theorem edgeSet_takeThrough_subset (Q : FiniteTrace D)
    (k : Fin (Q.lastIndex + 1)) :
    (Q.takeThrough k).edgeSet ⊆ Q.edgeSet := by
  intro e he
  rcases Set.mem_iUnion.1 he with ⟨i, hi⟩
  have hibound : i.1 < k.1 + 1 := by
    simpa only [takeThrough_lastIndex] using i.2
  exact Set.mem_iUnion.2 ⟨⟨i.1, by omega⟩, hi⟩

end FiniteTrace

variable {Γ : DWeb V}

/-- An initial trace ending with a backward link is again literally
bracket-alternating. -/
theorem IsBracketAlternating.takeThrough_of_backward
    {U Y : Set Γ.DPath} {Q : FiniteTrace Γ.graph}
    (hQ : IsBracketAlternating U Y (.finite Q))
    (k : Fin (Q.lastIndex + 1))
  (hkback : (Q.link k).direction = .backward) :
    IsBracketAlternating U Y (.finite (Q.takeThrough k)) := by
  rcases hQ with ⟨hAlt, hForwardU⟩
  rcases hAlt with ⟨hYWarp, hBackwardY, hInitial, hTerminal⟩
  refine ⟨⟨hYWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hldir
    exact hBackwardY l (Q.links_takeThrough_subset k hl) hldir
  · intro hfirst
    apply hInitial
    simpa [AltPath.firstDirection?] using hfirst
  · intro t ht hlast
    have hlastBack : (Q.takeThrough k).lastLink.direction = .backward := by
      simpa using hkback
    change some (Q.takeThrough k).lastLink.direction = some .forward at hlast
    have hcontra := Option.some.inj hlast
    rw [hlastBack] at hcontra
    contradiction
  · intro l hl hldir
    exact hForwardU l (Q.links_takeThrough_subset k hl) hldir

/-! ## First collision of a finite trace with a finite path -/

/-- A trace link meeting `q`, with proof that every strictly earlier link
is disjoint from `q`. -/
structure FirstCollision (Q : FiniteTrace D)
    (q : DirectedPath.FinitePath D) where
  index : Fin (Q.lastIndex + 1)
  meets : ((Q.link index).path.support ∩ q.support).Nonempty
  earlier_disjoint : ∀ j : Fin (Q.lastIndex + 1), j < index →
    Disjoint (Q.link j).path.support q.support

/-- A nonempty set of link/path collisions has a least link index. -/
noncomputable def firstCollision (Q : FiniteTrace D)
    (q : DirectedPath.FinitePath D)
    (hne : ∃ i : Fin (Q.lastIndex + 1),
      ((Q.link i).path.support ∩ q.support).Nonempty) :
    FirstCollision Q q := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ h : n < Q.lastIndex + 1,
      ((Q.link ⟨n, h⟩).path.support ∩ q.support).Nonempty
  have hP : ∃ n, P n := by
    rcases hne with ⟨i, hi⟩
    exact ⟨i.1, i.2, hi⟩
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  let hn : n < Q.lastIndex + 1 := Classical.choose hnP
  let hi : Fin (Q.lastIndex + 1) := ⟨n, hn⟩
  refine {
    index := hi
    meets := Classical.choose_spec hnP
    earlier_disjoint := ?_ }
  intro j hj
  rw [Set.disjoint_iff_inter_eq_empty]
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hjmeet
  have hjP : P j.1 := ⟨j.2, hjmeet⟩
  have hle : n ≤ j.1 := Nat.find_min' hP hjP
  have hjn : j.1 < n := by
    change j.1 < n at hj
    exact hj
  exact (Nat.not_lt_of_ge hle) hjn

/-- The endpoint equality `Q.terminal = q.finish` supplies a collision at
the final link, hence a canonical first collision. -/
noncomputable def firstCollisionOfTerminal (Q : FiniteTrace D)
    (q : DirectedPath.FinitePath D) (hterminal : Q.terminal = q.finish) :
    FirstCollision Q q :=
  firstCollision Q q <| by
    let i : Fin (Q.lastIndex + 1) :=
      ⟨Q.lastIndex, Nat.lt_succ_self Q.lastIndex⟩
    refine ⟨i, Q.terminal, ?_, ?_⟩
    · exact Q.terminal_mem_vertexSet |> fun h ↦ by
        simpa only [FiniteTrace.vertexSet, Set.mem_iUnion] using
          (show Q.terminal ∈ (Q.link i).path.support from
            Q.lastLink.exit_mem_support)
    · exact hterminal.symm ▸ q.finish_mem_support

end Erdos599.Alternating

namespace Erdos599.DirectedPath

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace Walk

private theorem exists_prefix_segment_of_support_eq
    {x b y : V} (p : Walk D x b) (middle after : List V)
    (hsupport : p.support = x :: middle ++ y :: after) :
    ∃ q : Walk D x y,
      q.support = x :: middle ++ [y] ∧ q.edgeSet ⊆ p.edgeSet := by
  induction middle generalizing x with
  | nil =>
      cases p with
      | nil => simp at hsupport
      | @cons _ z _ h tail =>
          simp only [support_cons] at hsupport
          have htail : tail.support = y :: after := (List.cons.inj hsupport).2
          have hzy : z = y := by
            apply Option.some.inj
            calc
              some z = tail.support.head? := by
                rw [List.head?_eq_some_head tail.support_ne_nil, tail.head_support]
              _ = (y :: after).head? := congrArg List.head? htail
              _ = some y := rfl
          subst y
          refine ⟨.cons h .nil, ?_, ?_⟩
          · simp
          · intro e he
            simp only [edgeSet_cons, edgeSet_nil, union_empty] at he ⊢
            exact Or.inl he
  | cons z middle ih =>
      cases p with
      | nil => simp at hsupport
      | @cons _ w _ h tail =>
          simp only [support_cons, List.cons_append] at hsupport
          have htail : tail.support = z :: middle ++ y :: after :=
            (List.cons.inj hsupport).2
          have hwz : w = z := by
            apply Option.some.inj
            calc
              some w = tail.support.head? := by
                rw [List.head?_eq_some_head tail.support_ne_nil, tail.head_support]
              _ = (z :: middle ++ y :: after).head? := congrArg List.head? htail
              _ = some z := rfl
          subst z
          obtain ⟨q, hqsupport, hqedge⟩ := ih tail htail
          refine ⟨.cons h q, ?_, ?_⟩
          · simp [hqsupport]
          · intro e he
            simp only [edgeSet_cons, Set.mem_union, Set.mem_singleton_iff] at he ⊢
            exact he.elim Or.inl (fun heq ↦ Or.inr (hqedge heq))

/-- Extract the directed segment whose endpoints and intervening vertices
occur contiguously in the displayed decomposition of the support. -/
theorem exists_segment_of_support_eq
    {a b x y : V} (p : Walk D a b) (before middle after : List V)
    (hsupport : p.support = before ++ x :: middle ++ y :: after) :
    ∃ q : Walk D x y,
      q.support = x :: middle ++ [y] ∧ q.edgeSet ⊆ p.edgeSet := by
  induction before generalizing a with
  | nil =>
      have hax : a = x := by
        apply Option.some.inj
        calc
          some a = p.support.head? := by
            rw [List.head?_eq_some_head p.support_ne_nil, p.head_support]
          _ = (x :: middle ++ y :: after).head? := by
            simpa using congrArg List.head? hsupport
          _ = some x := rfl
      subst x
      exact exists_prefix_segment_of_support_eq p middle after hsupport
  | cons z before ih =>
      cases p with
      | nil => simp at hsupport
      | @cons _ w _ h tail =>
          simp only [support_cons, List.cons_append] at hsupport
          have htail : tail.support = before ++ x :: middle ++ y :: after :=
            (List.cons.inj hsupport).2
          obtain ⟨q, hqsupport, hqedge⟩ := ih tail htail
          refine ⟨q, hqsupport, ?_⟩
          intro e he
          exact Set.mem_union_right _ (hqedge he)

end Walk

namespace FinitePath

/-- Data witnessing that `x` occurs strictly before `y` on the ordered
support of `p`; `middle` is exactly the list of intervening vertices. -/
structure OrderedOccurrence (p : FinitePath D) (x y : V) where
  before : List V
  middle : List V
  after : List V
  support_eq : p.walk.support = before ++ x :: middle ++ y :: after

namespace OrderedOccurrence

/-- Reassociate a customary suffix decomposition into an ordered occurrence. -/
def of_suffix_decomposition {p : FinitePath D} {x y : V}
    (before middle after : List V)
    (hsupport : p.walk.support = before ++ x :: (middle ++ y :: after)) :
    OrderedOccurrence p x y where
  before := before
  middle := middle
  after := after
  support_eq := by simpa [List.append_assoc] using hsupport

/-- An occurrence of `x` together with membership of `y` in the remaining
suffix determines an ordered occurrence of `x,y`. -/
theorem nonempty_of_mem_suffix {p : FinitePath D} {x y : V}
    (before suffix : List V)
    (hsupport : p.walk.support = before ++ x :: suffix) (hy : y ∈ suffix) :
    Nonempty (OrderedOccurrence p x y) := by
  rcases List.mem_iff_append.mp hy with ⟨middle, after, hsuffix⟩
  refine ⟨of_suffix_decomposition before middle after ?_⟩
  rw [hsupport, hsuffix]

theorem ne {p : FinitePath D} {x y : V} (hxy : OrderedOccurrence p x y) :
    x ≠ y := by
  intro h
  subst y
  have hp : p.walk.support.Nodup := p.isPath
  rw [hxy.support_eq] at hp
  have hseg : (x :: hxy.middle ++ [x]).Nodup :=
    (List.infix_append hxy.before (x :: hxy.middle ++ [x]) hxy.after).sublist.nodup <|
      by simpa [List.append_assoc] using hp
  have hxnot : x ∉ hxy.middle ++ [x] := (List.nodup_cons.mp hseg).1
  exact hxnot (by simp)

end OrderedOccurrence

/-- The subpath of `p` from the earlier occurrence `x` to the later
occurrence `y`. -/
noncomputable def between (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) : FinitePath D :=
  let hexists := p.walk.exists_segment_of_support_eq
    hxy.before hxy.middle hxy.after hxy.support_eq
  let q := Classical.choose hexists
  let hq := Classical.choose_spec hexists
  { start := x
    finish := y
    walk := q
    isPath := by
      rw [Walk.IsPath, hq.1]
      apply (List.infix_append hxy.before (x :: hxy.middle ++ [y]) hxy.after).sublist.nodup
      have hp : p.walk.support.Nodup := p.isPath
      rw [hxy.support_eq] at hp
      simpa [List.append_assoc] using hp }

@[simp] theorem between_start (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) : (p.between hxy).start = x := rfl

@[simp] theorem between_finish (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) : (p.between hxy).finish = y := rfl

theorem between_support_eq (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) :
    (p.between hxy).walk.support = x :: hxy.middle ++ [y] := by
  simp only [between]
  exact (Classical.choose_spec (p.walk.exists_segment_of_support_eq
    hxy.before hxy.middle hxy.after hxy.support_eq)).1

theorem between_support_subset (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) : (p.between hxy).support ⊆ p.support := by
  change (p.between hxy).walk.support ⊆ p.walk.support
  rw [p.between_support_eq hxy, hxy.support_eq]
  simpa [List.append_assoc] using
    (List.infix_append hxy.before (x :: hxy.middle ++ [y]) hxy.after).subset

theorem between_edgeSet_subset (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) : (p.between hxy).edgeSet ⊆ p.edgeSet := by
  change (p.between hxy).walk.edgeSet ⊆ p.walk.edgeSet
  simp only [between]
  exact (Classical.choose_spec (p.walk.exists_segment_of_support_eq
    hxy.before hxy.middle hxy.after hxy.support_eq)).2

theorem between_isSubpathOf (p : FinitePath D) {x y : V}
    (hxy : OrderedOccurrence p x y) :
    (p.between hxy).IsSubpathOf (Sum.inl p) :=
  ⟨p.between_support_subset hxy, p.between_edgeSet_subset hxy⟩

end FinitePath

end Erdos599.DirectedPath

namespace Erdos599.Alternating

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- Package a strict ordered segment of a finite path as an alternating link. -/
noncomputable def Link.between (p : FinitePath D) {x y : V}
    (hxy : FinitePath.OrderedOccurrence p x y) (direction : Direction) : Link D where
  path := p.between hxy
  direction := direction
  nontrivial := by simpa using hxy.ne

@[simp] theorem Link.between_path (p : FinitePath D) {x y : V}
    (hxy : FinitePath.OrderedOccurrence p x y) (direction : Direction) :
    (Link.between p hxy direction).path = p.between hxy := rfl

end Erdos599.Alternating

namespace Erdos599.DirectedPath

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace List

/-- A nonempty meeting of a list with a set has a first meeting, with an
explicit decomposition and no earlier meeting. -/
theorem exists_first_mem_decomposition (S : Set V) :
    ∀ (l : List V), (∃ w ∈ l, w ∈ S) →
      ∃ before w after, l = before ++ w :: after ∧
        w ∈ S ∧ ∀ z ∈ before, z ∉ S := by
  intro l
  induction l with
  | nil => simp
  | cons a tail ih =>
      intro hmeet
      by_cases ha : a ∈ S
      · exact ⟨[], a, tail, rfl, ha, by simp⟩
      · have htail : ∃ w ∈ tail, w ∈ S := by
          rcases hmeet with ⟨w, hw, hwS⟩
          simp only [List.mem_cons] at hw
          exact hw.elim (fun haw ↦ (ha (haw ▸ hwS)).elim)
            (fun hwt ↦ ⟨w, hwt, hwS⟩)
        rcases ih htail with ⟨before, w, after, hdecomp, hwS, hbefore⟩
        refine ⟨a :: before, w, after, ?_, hwS, ?_⟩
        · simp [hdecomp]
        · intro z hz hzS
          simp only [List.mem_cons] at hz
          exact hz.elim (fun hza ↦ ha (hza ▸ hzS))
            (fun hzb ↦ hbefore z hzb hzS)

end List

namespace FinitePath

/-- `w` occurs at or after `x` in the ordered support of `p`. -/
def AtOrAfter (p : FinitePath D) (x w : V) : Prop :=
  w = x ∨ Nonempty (OrderedOccurrence p x w)

/-- Starting from a displayed occurrence of `x`, choose the first later-or-
equal vertex belonging to `S`.  If it is not `x`, this supplies the strict
ordered occurrence needed by `between`; the resulting segment contains no
other `S`-vertex. -/
theorem exists_firstContact_of_suffix (p : FinitePath D) (S : Set V)
    (x : V) (before suffix : List V)
    (hsupport : p.walk.support = before ++ x :: suffix)
    (hmeet : ∃ w ∈ x :: suffix, w ∈ S) :
    ∃ w, w ∈ S ∧
      (w = x ∨ ∃ h : OrderedOccurrence p x w,
        ∀ ⦃z⦄, z ∈ (p.between h).support → z ∈ S → z = w) := by
  rcases List.exists_first_mem_decomposition S (x :: suffix) hmeet with
    ⟨middle, w, after, hfirst, hwS, hmiddle⟩
  cases middle with
  | nil =>
      have hxw : x = w := (List.cons.inj (by simpa using hfirst)).1
      exact ⟨w, hwS, Or.inl hxw.symm⟩
  | cons x' inner =>
      have hxx' : x = x' := (List.cons.inj (by simpa using hfirst)).1
      subst x'
      have hsuffix : suffix = inner ++ w :: after :=
        by simpa using hfirst
      let hocc : OrderedOccurrence p x w :=
        { before := before
          middle := inner
          after := after
          support_eq := by rw [hsupport, hsuffix]; simp [List.append_assoc] }
      refine ⟨w, hwS, Or.inr ⟨hocc, ?_⟩⟩
      intro z hz hzS
      have hzlist : z ∈ x :: inner ++ [w] := by
        change z ∈ (p.between hocc).walk.support at hz
        rw [p.between_support_eq hocc] at hz
        exact hz
      have hzsplit : z ∈ x :: inner ∨ z = w := by
        simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] using hzlist
      exact hzsplit.elim
        (fun hzearly ↦ (hmiddle z (by simpa using hzearly) hzS).elim) id

/-- First-contact wrapper stated only in terms of ordered occurrence.  The
extra support hypothesis is convenient at call sites and records explicitly
that the starting vertex lies on the path. -/
theorem exists_firstContact (p : FinitePath D) (S : Set V) (x : V)
    (_hx : x ∈ p.support)
    (hmeet : ∃ w ∈ S, p.AtOrAfter x w) :
    ∃ w, w ∈ S ∧
      (w = x ∨ ∃ h : OrderedOccurrence p x w,
        ∀ ⦃z⦄, z ∈ (p.between h).support → z ∈ S → z = w) := by
  rcases hmeet with ⟨w, hwS, hwx | hocc⟩
  · subst w
    exact ⟨x, hwS, Or.inl rfl⟩
  · rcases hocc with ⟨hocc⟩
    apply p.exists_firstContact_of_suffix S x hocc.before
      (hocc.middle ++ w :: hocc.after)
      (by simpa [List.append_assoc] using hocc.support_eq)
    exact ⟨w, by simp, hwS⟩

/-- Every noninitial support vertex has an immediate predecessor.  The
`OrderedOccurrence` has empty middle, hence `between` is the one-edge
segment from `y` to `w`. -/
theorem exists_predecessor_orderedOccurrence (p : FinitePath D) {w : V}
    (hw : w ∈ p.support) (hne : w ≠ p.start) :
    ∃ y, ∃ h : OrderedOccurrence p y w,
      h.middle = [] ∧
      (p.between h).walk.support = [y, w] ∧ D.Adj y w := by
  change w ∈ p.walk.support at hw
  rcases List.mem_iff_append.mp hw with ⟨pre, after, hsupport⟩
  have hpre : pre ≠ [] := by
    intro hp
    subst pre
    have hstartw : p.start = w := by
      apply Option.some.inj
      calc
        some p.start = p.walk.support.head? := by
          rw [List.head?_eq_some_head p.walk.support_ne_nil, p.walk.head_support]
        _ = (w :: after).head? := by simpa using congrArg List.head? hsupport
        _ = some w := rfl
    exact hne hstartw.symm
  rcases pre.eq_nil_or_concat with hp | ⟨before, y, hp⟩
  · exact (hpre hp).elim
  · let hocc : OrderedOccurrence p y w :=
      { before := before
        middle := []
        after := after
        support_eq := by rw [hsupport, hp]; simp }
    have hpair : (p.between hocc).walk.support = [y, w] := by
      simpa [hocc] using p.between_support_eq hocc
    have hadj : D.Adj y w := by
      let q := (p.between hocc).walk
      cases hq : q with
      | nil => simp [q, hq] at hpair
      | @cons _ z _ e tail =>
          have htail : tail.support = [w] := by
            have := hpair
            simp only [q, hq, Walk.support_cons, List.cons.injEq] at this
            exact this.2
          have hzw : z = w := by
            apply Option.some.inj
            calc
              some z = tail.support.head? := by
                rw [List.head?_eq_some_head tail.support_ne_nil, tail.head_support]
              _ = ([w] : List V).head? := congrArg List.head? htail
              _ = some w := rfl
          simpa [hzw] using e
    exact ⟨y, hocc, rfl, hpair, hadj⟩

end FinitePath

end Erdos599.DirectedPath

namespace Erdos599.Alternating

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace Direction

def flip : Direction → Direction
  | .forward => .backward
  | .backward => .forward

@[simp] theorem flip_forward : flip .forward = .backward := rfl
@[simp] theorem flip_backward : flip .backward = .forward := rfl
@[simp] theorem flip_flip (d : Direction) : d.flip.flip = d := by cases d <;> rfl

theorem flip_injective : Function.Injective flip := by
  intro d e h
  cases d <;> cases e <;> simp_all

end Direction

namespace Link

def reverse (l : Link D) : Link D where
  path := l.path
  direction := l.direction.flip
  nontrivial := l.nontrivial

@[simp] theorem reverse_path (l : Link D) : l.reverse.path = l.path := rfl
@[simp] theorem reverse_direction (l : Link D) : l.reverse.direction = l.direction.flip := rfl
@[simp] theorem reverse_entry (l : Link D) : l.reverse.entry = l.exit := by
  rcases l with ⟨p, d, h⟩
  cases d <;> rfl
@[simp] theorem reverse_exit (l : Link D) : l.reverse.exit = l.entry := by
  rcases l with ⟨p, d, h⟩
  cases d <;> rfl
@[simp] theorem reverse_reverse (l : Link D) : l.reverse.reverse = l := by
  rcases l with ⟨p, d, h⟩
  cases d <;> rfl

theorem reverse_injective : Function.Injective (reverse : Link D → Link D) := by
  exact Function.Involutive.injective reverse_reverse

theorem entry_not_mem_interior (l : Link D) : l.entry ∉ l.interior := by
  cases hd : l.direction <;> simp [interior, endpoints, entry, hd]

theorem exit_not_mem_interior (l : Link D) : l.exit ∉ l.interior := by
  cases hd : l.direction <;> simp [interior, endpoints, exit, hd]

end Link

private theorem compatibleInOrder_reverse
    {adjacent : Prop} {l r : Link D}
    (hjoin : adjacent → l.exit = r.entry)
    (h : CompatibleInOrder adjacent l r) :
    CompatibleInOrder adjacent r.reverse l.reverse := by
  cases hl : l.direction <;> cases hr : r.direction
  · simp only [CompatibleInOrder, Link.reverse_direction, hl, hr,
      Direction.flip_forward, Link.reverse_entry, Link.reverse_exit] at h ⊢
    intro v hvr hvl
    rcases h hvl hvr with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  · simp only [CompatibleInOrder, Link.reverse_direction, hl, hr,
      Direction.flip_forward, Direction.flip_backward, Link.reverse_path,
      Link.reverse_exit] at h ⊢
    constructor
    · intro hadj
      have hj := hjoin hadj
      rw [Set.inter_comm, h.1 hadj, hj]
    · intro hnadj
      exact (h.2 hnadj).symm
  · simp only [CompatibleInOrder, Link.reverse_direction, hl, hr,
      Direction.flip_forward, Direction.flip_backward, Link.reverse_path,
      Link.reverse_exit, Link.interior] at h ⊢
    constructor
    · intro hadj v hvr hvl
      have hj := hjoin hadj
      rcases h.1 hadj hvl hvr with hv | hv
      · exact Or.inl (hv.trans hj)
      · exact Or.inr ⟨hv.2, hv.1⟩
    · intro hnadj v hv
      have hv' := h.2 hnadj
      have := hv' ⟨hv.2, hv.1⟩
      exact ⟨this.2, this.1⟩
  · simp only [CompatibleInOrder, Link.reverse_direction, hl, hr,
      Direction.flip_backward, Link.reverse_entry, Link.reverse_exit] at h ⊢
    intro v hvr hvl
    rcases h hvl hvr with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩

namespace FiniteTrace

theorem join_of_adjacent (Q : FiniteTrace D) {i j : Fin (Q.lastIndex + 1)}
    (hij : j.1 = i.1 + 1) : (Q.link i).exit = (Q.link j).entry := by
  have hi : i.1 < Q.lastIndex := by omega
  let k : Fin Q.lastIndex := ⟨i.1, hi⟩
  have hki : k.castSucc = i := by ext; rfl
  have hkj : k.succ = j := by ext; exact hij.symm
  simpa [hki, hkj] using Q.joins k

def reverse (Q : FiniteTrace D) : FiniteTrace D where
  lastIndex := Q.lastIndex
  link i := (Q.link i.rev).reverse
  joins := by
    intro i
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Link.reverse_exit,
      Link.reverse_entry] using (Q.joins i.rev).symm
  alternates := by
    intro i h
    have h' : (Q.link i.rev.succ).direction =
        (Q.link i.rev.castSucc).direction := by
      apply Direction.flip_injective
      simpa only [Fin.rev_castSucc, Fin.rev_succ, Link.reverse_direction] using h
    exact Q.alternates i.rev h'.symm
  compatible := by
    intro i j hij
    have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hadj : (i.rev.1 = j.rev.1 + 1) ↔ (j.1 = i.1 + 1) := by
      simp only [Fin.rev]
      omega
    rw [← hadj]
    apply compatibleInOrder_reverse
    · exact fun ha ↦ Q.join_of_adjacent ha
    · exact Q.compatible j.rev i.rev hrev

@[simp] theorem reverse_lastIndex (Q : FiniteTrace D) : Q.reverse.lastIndex = Q.lastIndex := rfl

@[simp] theorem reverse_link (Q : FiniteTrace D) (i : Fin (Q.lastIndex + 1)) :
    Q.reverse.link i = (Q.link i.rev).reverse := rfl

@[simp] theorem firstLink_reverse (Q : FiniteTrace D) :
    Q.reverse.firstLink = Q.lastLink.reverse := by
  change (Q.link (Fin.rev 0)).reverse =
    (Q.link ⟨Q.lastIndex, Nat.lt_succ_self _⟩).reverse
  congr 2

@[simp] theorem lastLink_reverse (Q : FiniteTrace D) :
    Q.reverse.lastLink = Q.firstLink.reverse := by
  change (Q.link (Fin.rev ⟨Q.lastIndex, Nat.lt_succ_self _⟩)).reverse =
    (Q.link ⟨0, Nat.zero_lt_succ _⟩).reverse
  have hlast : (⟨Q.lastIndex, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 1)) =
      Fin.last Q.lastIndex := by ext; rfl
  rw [hlast, Fin.rev_last]
  congr 2

@[simp] theorem initial_reverse (Q : FiniteTrace D) : Q.reverse.initial = Q.terminal := by
  simp [initial, terminal]

@[simp] theorem terminal_reverse (Q : FiniteTrace D) : Q.reverse.terminal = Q.initial := by
  simp [initial, terminal]

@[simp] theorem reverse_reverse (Q : FiniteTrace D) : Q.reverse.reverse = Q := by
  cases Q with
  | mk n link joins alternates compatible =>
      simp only [reverse]
      congr 1
      funext i
      simp

theorem links_reverse (Q : FiniteTrace D) :
    Q.reverse.links = Link.reverse '' Q.links := by
  ext l
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Q.link i.rev, ⟨i.rev, rfl⟩, rfl⟩
  · rintro ⟨l, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.rev, by simp⟩

@[simp] theorem vertexSet_reverse (Q : FiniteTrace D) :
    Q.reverse.vertexSet = Q.vertexSet := by
  ext v
  simp only [vertexSet, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.rev, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.rev, by simpa using hi⟩

@[simp] theorem edgeSet_reverse (Q : FiniteTrace D) :
    Q.reverse.edgeSet = Q.edgeSet := by
  ext e
  simp only [edgeSet, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.rev, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.rev, by simpa using hi⟩

end FiniteTrace

namespace AltPath

@[simp] theorem initial_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).initial = Q.terminal :=
  Q.initial_reverse

@[simp] theorem terminal?_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).terminal? = some Q.initial := by
  simp

@[simp] theorem firstDirection?_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).firstDirection? = some Q.lastLink.direction.flip := by
  simp [firstDirection?]

@[simp] theorem lastDirection?_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).lastDirection? = some Q.firstLink.direction.flip := by
  simp [lastDirection?]

@[simp] theorem vertexSet_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).vertexSet = (AltPath.finite Q).vertexSet :=
  Q.vertexSet_reverse

@[simp] theorem edgeSet_finite_reverse (Q : FiniteTrace D) :
    (AltPath.finite Q.reverse).edgeSet = (AltPath.finite Q).edgeSet :=
  Q.edgeSet_reverse

theorem directionVertices_finite_reverse (Q : FiniteTrace D) (d : Direction) :
    (AltPath.finite Q.reverse).directionVertices d =
      (AltPath.finite Q).directionVertices d.flip := by
  ext v
  simp only [directionVertices, links, FiniteTrace.links, Set.mem_iUnion,
    Set.mem_range, FiniteTrace.reverse_link, Link.reverse_direction,
    Link.reverse_path]
  constructor
  · rintro ⟨l, ⟨i, rfl⟩, hdir, hv⟩
    change (Q.link i.rev).direction.flip = d at hdir
    change v ∈ (Q.link i.rev).path.support at hv
    refine ⟨Q.link i.rev, ⟨i.rev, rfl⟩, ?_, hv⟩
    apply Direction.flip_injective
    simpa using hdir
  · rintro ⟨l, ⟨i, rfl⟩, hdir, hv⟩
    refine ⟨(Q.link i).reverse, ⟨i.rev, by simp⟩, ?_, hv⟩
    simpa [hdir]

theorem directionEdges_finite_reverse (Q : FiniteTrace D) (d : Direction) :
    (AltPath.finite Q.reverse).directionEdges d =
      (AltPath.finite Q).directionEdges d.flip := by
  ext e
  simp only [directionEdges, links, FiniteTrace.links, Set.mem_iUnion,
    Set.mem_range, FiniteTrace.reverse_link, Link.reverse_direction,
    Link.reverse_path]
  constructor
  · rintro ⟨l, ⟨i, rfl⟩, hdir, he⟩
    change (Q.link i.rev).direction.flip = d at hdir
    change e ∈ (Q.link i.rev).path.edgeSet at he
    refine ⟨Q.link i.rev, ⟨i.rev, rfl⟩, ?_, he⟩
    apply Direction.flip_injective
    simpa using hdir
  · rintro ⟨l, ⟨i, rfl⟩, hdir, he⟩
    refine ⟨(Q.link i).reverse, ⟨i.rev, by simp⟩, ?_, he⟩
    simpa [hdir]

end AltPath

end Erdos599.Alternating

namespace Erdos599.DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace Walk


theorem exists_outgoing_edge_of_mem_of_ne_finish
    {a b x : V} (p : Walk D a b) (hx : x ∈ p.support) (hxb : x ≠ b) :
    ∃ y, (x, y) ∈ p.edgeSet := by
  induction p with
  | nil => exact (hxb (by simpa using hx)).elim
  | @cons a c b h tail ih =>
      simp only [support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ := ih hx hxb
        exact ⟨y, Set.mem_union_right _ hy⟩

theorem outgoing_edge_unique {a b x y z : V} (p : Walk D a b)
    (hp : p.IsPath) (hxy : (x, y) ∈ p.edgeSet) (hxz : (x, z) ∈ p.edgeSet) : y = z := by
  induction p with
  | nil => simp at hxy
  | @cons a c b h tail ih =>
      have htailpath : tail.IsPath := by
        rw [IsPath] at hp ⊢
        exact (List.nodup_cons.mp hp).2
      simp only [edgeSet_cons, Set.mem_union, Set.mem_singleton_iff,
        Prod.mk.injEq] at hxy hxz
      rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
      · exact hxy.2.trans hxz.2.symm
      · have ha : a ∈ tail.support := by
          simpa [hxy.1] using (tail.edgeSet_subset_support_prod hxz).1
        exact ((List.nodup_cons.mp hp).1 ha).elim
      · have ha : a ∈ tail.support := by
          simpa [hxz.1] using (tail.edgeSet_subset_support_prod hxy).1
        exact ((List.nodup_cons.mp hp).1 ha).elim
      · exact ih htailpath hxy hxz

theorem fst_ne_finish_of_mem_edge {a b x y : V} (p : Walk D a b)
    (hp : p.IsPath) (hxy : (x, y) ∈ p.edgeSet) : x ≠ b := by
  induction p with
  | nil => simp at hxy
  | @cons a c b h tail ih =>
      have htailpath : tail.IsPath := by
        rw [IsPath] at hp ⊢
        exact (List.nodup_cons.mp hp).2
      simp only [edgeSet_cons, Set.mem_union, Set.mem_singleton_iff,
        Prod.mk.injEq] at hxy
      rcases hxy with hxy | hxy
      · intro hab
        have ha : a ∈ tail.support := by
          have hb := tail.end_mem_support
          have hab' : a = b := hxy.1.symm.trans hab
          exact hab'.symm ▸ hb
        exact (List.nodup_cons.mp hp).1 ha
      · exact ih htailpath hxy

end Walk

theorem FinitePath.outgoing_edge_unique (p : FinitePath D)
    {x y z : V} (hxy : (x, y) ∈ p.edgeSet) (hxz : (x, z) ∈ p.edgeSet) : y = z :=
  p.walk.outgoing_edge_unique p.isPath hxy hxz

theorem FinitePath.fst_ne_finish_of_mem_edge (p : FinitePath D)
    {x y : V} (hxy : (x, y) ∈ p.edgeSet) : x ≠ p.finish :=
  p.walk.fst_ne_finish_of_mem_edge p.isPath hxy

theorem Ray.outgoing_edge_unique (r : Ray D)
    {x y z : V} (hxy : (x, y) ∈ r.edgeSet) (hxz : (x, z) ∈ r.edgeSet) : y = z := by
  rcases hxy with ⟨n, hn⟩
  rcases hxz with ⟨m, hm⟩
  have hnm : n = m := r.injective <|
    (congrArg Prod.fst hn).symm.trans (congrArg Prod.fst hm)
  subst m
  exact (congrArg Prod.snd hn).trans (congrArg Prod.snd hm).symm

theorem Path.outgoing_edge_unique (p : Path D)
    {x y z : V} (hxy : (x, y) ∈ p.edgeSet) (hxz : (x, z) ∈ p.edgeSet) : y = z := by
  rcases p with p | r
  · exact p.outgoing_edge_unique hxy hxz
  · exact r.outgoing_edge_unique hxy hxz

theorem FinitePath.edge_mem_of_isSubpathOf_of_mem_of_ne_finish
    (q : FinitePath D) (p : Path D) {x y : V}
    (hsub : q.IsSubpathOf p) (hx : x ∈ q.support) (hne : x ≠ q.finish)
    (hxy : (x, y) ∈ p.edgeSet) : (x, y) ∈ q.edgeSet := by
  obtain ⟨z, hxz⟩ := q.walk.exists_outgoing_edge_of_mem_of_ne_finish hx hne
  have hxzp : (x, z) ∈ p.edgeSet := hsub.2 hxz
  have hzy : z = y := p.outgoing_edge_unique hxzp hxy
  change (x, y) ∈ q.walk.edgeSet
  simpa [hzy] using hxz

end Erdos599.DirectedPath

namespace Erdos599.Alternating

open Set
open DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The old backward links avoid `U` once every contact with `U` is
covered by an old forward link. -/
theorem backwardLinksOff_of_symmetric_coverage
    {U Y : Set Γ.DPath} {Q : FiniteTrace Γ.graph}
    (hU : Γ.IsWarp U)
    (hQ : IsBracketAlternating U Y (.finite Q))
    (hOff : ForwardLinksOff Y (.finite Q))
    (hcover : (AltPath.finite Q).directionVertices .backward ∩ Γ.vertexSet U ⊆
      (AltPath.finite Q).directionVertices .forward) :
    ∀ l ∈ (AltPath.finite Q).links, l.direction = .backward →
      Disjoint l.path.edgeSet (familyEdges U) := by
  intro l hl hldir
  rcases hl with ⟨i, rfl⟩
  rw [Set.disjoint_left]
  rintro ⟨a, b⟩ he heU
  have haL : a ∈ (Q.link i).path.support :=
    ((Q.link i).path.edgeSet_subset_support_prod he).1
  have haB : a ∈ (AltPath.finite Q).directionVertices .backward := by
    simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
      Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.link i, ⟨i, rfl⟩, hldir, haL⟩
  simp only [familyEdges, Set.mem_iUnion] at heU
  rcases heU with ⟨p, hpU, hep⟩
  have haP : a ∈ p.support := (p.edgeSet_subset_support_prod hep).1
  have haU : a ∈ Γ.vertexSet U := ⟨p, hpU, haP⟩
  have haF := hcover ⟨haB, haU⟩
  simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at haF
  rcases haF with ⟨f, ⟨j, rfl⟩, hfjdir, haF⟩
  have hfragF : IsFragmentOf (Q.link j).path U :=
    hQ.2 (Q.link j) ⟨j, rfl⟩ hfjdir
  rcases hfragF with ⟨p', hp'U, hsubF⟩
  have hp'P : p' = p :=
    DWeb.IsWarp.eq_of_mem_support hU hp'U hpU (hsubF.1 haF) haP
  subst p'
  have haNotLEntry : a ≠ (Q.link i).entry := by
    simpa [Link.entry, hldir] using (Q.link i).path.fst_ne_finish_of_mem_edge he
  have hij : i < j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hij
    · subst j
      exact (by simp [hldir] at hfjdir)
    · have hc := Q.compatible j i hij
      simp only [CompatibleInOrder, hfjdir, hldir] at hc
      by_cases hadj : i.1 = j.1 + 1
      · have hmem : a ∈ (Q.link j).path.support ∩ (Q.link i).path.support :=
          ⟨haF, haL⟩
        have haexit : a = (Q.link j).exit := by
          rw [hc.1 hadj] at hmem
          simpa using hmem
        have hjoin := Q.join_of_adjacent hadj
        exact (haNotLEntry (haexit.trans hjoin)).elim
      · exact (Set.disjoint_left.1 (hc.2 hadj) haF haL).elim
  have hc := Q.compatible i j hij
  simp only [CompatibleInOrder, hldir, hfjdir] at hc
  have haNotFFinish : a ≠ (Q.link j).path.finish := by
    by_cases hadj : j.1 = i.1 + 1
    · rcases hc.1 hadj haL haF with haexit | hinterior
      · have hjoin := Q.join_of_adjacent hadj
        have haentry : a = (Q.link j).entry := haexit.trans hjoin
        have hne := (Q.link j).entry_ne_exit
        simpa [Link.entry, Link.exit, hfjdir, haentry] using hne
      · intro hafinish
        exact hinterior.2.2 (by simp [Link.endpoints, hafinish])
    · have hinterior := hc.2 hadj ⟨haL, haF⟩
      intro hafinish
      exact hinterior.2.2 (by simp [Link.endpoints, hafinish])
  have heF : (a, b) ∈ (Q.link j).path.edgeSet :=
    (Q.link j).path.edge_mem_of_isSubpathOf_of_mem_of_ne_finish
      p hsubF haF haNotFFinish hep
  have heY : (a, b) ∈ familyEdges Y := by
    have hback := hQ.1.2.1 (Q.link i) ⟨i, rfl⟩ hldir
    rcases hback with ⟨r, hrY, hsubR⟩
    exact Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hrY (hsubR.2 he))
  exact Set.disjoint_left.1 (hOff (Q.link j) ⟨j, rfl⟩ hfjdir) heF heY

theorem terminal_not_mem_of_symmetric_coverage
    {U Y : Set Γ.DPath} {Q : FiniteTrace Γ.graph}
    (hQ : IsBracketAlternating U Y (.finite Q))
    (hcover : (AltPath.finite Q).directionVertices .backward ∩ Γ.vertexSet U ⊆
      (AltPath.finite Q).directionVertices .forward)
    (hlast : Q.lastLink.direction = .backward) :
    Q.terminal ∉ Γ.vertexSet U := by
  intro htU
  have htL : Q.terminal ∈ Q.lastLink.path.support := Q.lastLink.exit_mem_support
  have htB : Q.terminal ∈ (AltPath.finite Q).directionVertices .backward := by
    simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
      Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.lastLink, ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, rfl⟩, hlast, htL⟩
  have htF := hcover ⟨htB, htU⟩
  simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at htF
  rcases htF with ⟨f, ⟨j, rfl⟩, hfjdir, htF⟩
  let k : Fin (Q.lastIndex + 1) := ⟨Q.lastIndex, Nat.lt_succ_self _⟩
  have hklast : Q.link k = Q.lastLink := rfl
  have hjk : j < k := by
    have hjle : j.1 ≤ k.1 := by
      simpa [k] using Nat.le_of_lt_succ j.isLt
    rcases lt_or_eq_of_le hjle with hjk | hjk
    · exact hjk
    · have hjkeq : j = k := Fin.ext hjk
      subst j
      exact (by simp [hklast, hlast] at hfjdir)
  have hc := Q.compatible j k hjk
  simp only [hfjdir, hklast, hlast, CompatibleInOrder] at hc
  by_cases hadj : k.1 = j.1 + 1
  · have hmem : Q.terminal ∈ (Q.link j).path.support ∩ Q.lastLink.path.support :=
      ⟨htF, htL⟩
    have htexit : Q.terminal = (Q.link j).exit := by
      rw [hc.1 hadj] at hmem
      simpa using hmem
    have hjoin := Q.join_of_adjacent hadj
    rw [hklast] at hjoin
    exact Q.lastLink.entry_ne_exit ((htexit.trans hjoin).symm.trans rfl)
  · exact Set.disjoint_left.1 (hc.2 hadj) htF htL

theorem initial_not_mem_of_symmetric_coverage
    {U Y : Set Γ.DPath} {Q : FiniteTrace Γ.graph}
    (hQ : IsBracketAlternating U Y (.finite Q))
    (hcover : (AltPath.finite Q).directionVertices .backward ∩ Γ.vertexSet U ⊆
      (AltPath.finite Q).directionVertices .forward)
    (hfirst : Q.firstLink.direction = .backward) :
    Q.initial ∉ Γ.vertexSet U := by
  intro hiU
  have hiL : Q.initial ∈ Q.firstLink.path.support := Q.firstLink.entry_mem_support
  have hiB : Q.initial ∈ (AltPath.finite Q).directionVertices .backward := by
    simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
      Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.firstLink, ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩, hfirst, hiL⟩
  have hiF := hcover ⟨hiB, hiU⟩
  simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hiF
  rcases hiF with ⟨f, ⟨j, rfl⟩, hfjdir, hiF⟩
  let k : Fin (Q.lastIndex + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hkfirst : Q.link k = Q.firstLink := rfl
  have hkj : k < j := by
    have hkle : k.1 ≤ j.1 := Nat.zero_le _
    rcases lt_or_eq_of_le hkle with hkj | hkj
    · exact hkj
    · have hkjeq : k = j := Fin.ext hkj
      subst j
      exact (by simp [hkfirst, hfirst] at hfjdir)
  have hc := Q.compatible k j hkj
  simp only [hkfirst, hfirst, hfjdir, CompatibleInOrder] at hc
  by_cases hadj : j.1 = k.1 + 1
  · rcases hc.1 hadj hiL hiF with hiexit | hiinterior
    · exact Q.firstLink.entry_ne_exit hiexit
    · exact Q.firstLink.entry_not_mem_interior hiinterior.1
  · have hiinterior := hc.2 hadj ⟨hiL, hiF⟩
    exact Q.firstLink.entry_not_mem_interior hiinterior.1

/-- Reversing a finite `[U,Y]`-alternating path produces a literal
`[Y,U]`-alternating path when the symmetric vertex-coverage condition holds.
No switching-ready edge/contact claim is made here: common edge occurrences
are allowed by the source predicate. -/
theorem IsBracketAlternating.reverse_finite
    {U Y : Set Γ.DPath} {Q : FiniteTrace Γ.graph}
    (hU : Γ.IsWarp U)
    (hQ : IsBracketAlternating U Y (.finite Q))
    (hcover : (AltPath.finite Q).directionVertices .backward ∩ Γ.vertexSet U ⊆
      (AltPath.finite Q).directionVertices .forward) :
    IsBracketAlternating Y U (.finite Q.reverse) := by
  refine ⟨?_, ?_⟩
  · refine ⟨hU, ?_, ?_, ?_⟩
    · intro l hl hldir
      change l ∈ Q.reverse.links at hl
      rw [FiniteTrace.links_reverse] at hl
      rcases hl with ⟨k, hk, rfl⟩
      have hkdir : k.direction = .forward := by
        cases hd : k.direction <;> simp [Link.reverse, hd] at hldir ⊢
      simpa using hQ.2 k hk hkdir
    · intro hfirst
      have hlast : Q.lastLink.direction = .backward := by
        cases hd : Q.lastLink.direction <;>
          simp [AltPath.firstDirection?_finite_reverse, hd] at hfirst ⊢
      simpa using terminal_not_mem_of_symmetric_coverage hQ hcover hlast
    · intro t hterminal hlastDir
      have ht : t = Q.initial := by
        simpa using Option.some.inj hterminal.symm
      have hfirst : Q.firstLink.direction = .backward := by
        cases hd : Q.firstLink.direction <;>
          simp [AltPath.lastDirection?_finite_reverse, hd] at hlastDir ⊢
      subst t
      simpa using initial_not_mem_of_symmetric_coverage hQ hcover hfirst
  · intro l hl hldir
    change l ∈ Q.reverse.links at hl
    rw [FiniteTrace.links_reverse] at hl
    rcases hl with ⟨k, hk, rfl⟩
    have hkdir : k.direction = .backward := by
      cases hd : k.direction <;> simp [Link.reverse, hd] at hldir ⊢
    simpa using hQ.1.2.1 k hk hkdir

end Erdos599.Alternating
