/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PathCoverGrouping

/-!
# Indexing the cycles and path slots in KSSS Lemma 4.3

The cycle-removal decomposition supplies fewer than `m²` cycles.  Cycle
number `c` uses slots `2c` and `2c+1` for every one of its root-to-internal
vertex paths.  Both slots lie in the universal supply of `6m²` paths, and
different cycle numbers receive disjoint slot pairs.

We also expose the canonical copy of a cycle graph determined by a Mathlib
simple-cycle walk.  Unlike a mere containment witness, this copy retains the
actual cyclic order of the walk and can therefore be augmented edge by edge.
-/

namespace Erdos207

open Finset

noncomputable section

def firstCyclePathSlot (m c : ℕ) (hc : c < m ^ 2) : Fin (6 * m ^ 2) :=
  ⟨2 * c, by omega⟩

def secondCyclePathSlot (m c : ℕ) (hc : c < m ^ 2) : Fin (6 * m ^ 2) :=
  ⟨2 * c + 1, by omega⟩

lemma firstCyclePathSlot_ne_second (m c : ℕ) (hc : c < m ^ 2) :
    firstCyclePathSlot m c hc ≠ secondCyclePathSlot m c hc := by
  intro h
  have := congrArg Fin.val h
  simp [firstCyclePathSlot, secondCyclePathSlot] at this

lemma firstCyclePathSlot_injective (m : ℕ) :
    Function.Injective
      (fun c : Fin (m ^ 2) => firstCyclePathSlot m c.1 c.2) := by
  intro c d h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [firstCyclePathSlot] at hval
  omega

lemma secondCyclePathSlot_injective (m : ℕ) :
    Function.Injective
      (fun c : Fin (m ^ 2) => secondCyclePathSlot m c.1 c.2) := by
  intro c d h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [secondCyclePathSlot] at hval
  omega

lemma cyclePathSlot_pairs_disjoint (m : ℕ) {c d : Fin (m ^ 2)}
    (hcd : c ≠ d) :
    Disjoint
      ({firstCyclePathSlot m c.1 c.2,
          secondCyclePathSlot m c.1 c.2} : Finset (Fin (6 * m ^ 2)))
      ({firstCyclePathSlot m d.1 d.2,
          secondCyclePathSlot m d.1 d.2} : Finset (Fin (6 * m ^ 2))) := by
  rw [Finset.disjoint_left]
  intro i hi hid
  simp only [mem_insert, mem_singleton] at hi hid
  rcases hi with rfl | rfl <;> rcases hid with h | h
  · exact hcd (firstCyclePathSlot_injective m h)
  · have hval := congrArg Fin.val h
    simp [firstCyclePathSlot, secondCyclePathSlot] at hval
    omega
  · have hval := congrArg Fin.val h
    simp [firstCyclePathSlot, secondCyclePathSlot] at hval
    omega
  · exact hcd (secondCyclePathSlot_injective m h)

lemma cyclePathSlots_ne (m : ℕ) {c d : Fin (m ^ 2)} (hcd : c ≠ d) :
    firstCyclePathSlot m c.1 c.2 ≠ firstCyclePathSlot m d.1 d.2 ∧
      firstCyclePathSlot m c.1 c.2 ≠ secondCyclePathSlot m d.1 d.2 ∧
      secondCyclePathSlot m c.1 c.2 ≠ firstCyclePathSlot m d.1 d.2 ∧
      secondCyclePathSlot m c.1 c.2 ≠ secondCyclePathSlot m d.1 d.2 := by
  constructor
  · intro h
    apply hcd
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp [firstCyclePathSlot] at hval
    omega
  constructor
  · intro h
    have hval := congrArg Fin.val h
    simp [firstCyclePathSlot, secondCyclePathSlot] at hval
    omega
  constructor
  · intro h
    have hval := congrArg Fin.val h
    simp [firstCyclePathSlot, secondCyclePathSlot] at hval
    omega
  · intro h
    apply hcd
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp [secondCyclePathSlot] at hval
    omega

/-! After `r` cycles have used the first `2r` slots, the remaining
`6m²-2r` slots split canonically into `3m²-r` consecutive pairs. -/

def unusedPathPairCount (m r : ℕ) : ℕ := 3 * m ^ 2 - r

def unusedPathPairFirst (m r : ℕ) (hr : r ≤ m ^ 2)
    (t : Fin (unusedPathPairCount m r)) : Fin (6 * m ^ 2) :=
  ⟨2 * r + 2 * t.1, by
    have ht : t.1 < 3 * m ^ 2 - r := by
      simpa [unusedPathPairCount] using t.2
    omega⟩

def unusedPathPairSecond (m r : ℕ) (hr : r ≤ m ^ 2)
    (t : Fin (unusedPathPairCount m r)) : Fin (6 * m ^ 2) :=
  ⟨2 * r + 2 * t.1 + 1, by
    have ht : t.1 < 3 * m ^ 2 - r := by
      simpa [unusedPathPairCount] using t.2
    omega⟩

lemma unusedPathPairFirst_ne_second (m r : ℕ) (hr : r ≤ m ^ 2)
    (t : Fin (unusedPathPairCount m r)) :
    unusedPathPairFirst m r hr t ≠ unusedPathPairSecond m r hr t := by
  intro h
  have := congrArg Fin.val h
  simp [unusedPathPairFirst, unusedPathPairSecond] at this

lemma unusedPathPairFirst_injective (m r : ℕ) (hr : r ≤ m ^ 2) :
    Function.Injective (unusedPathPairFirst m r hr) := by
  intro t u h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [unusedPathPairFirst] at hval
  omega

lemma unusedPathPairSecond_injective (m r : ℕ) (hr : r ≤ m ^ 2) :
    Function.Injective (unusedPathPairSecond m r hr) := by
  intro t u h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [unusedPathPairSecond] at hval
  omega

lemma unusedPathPair_disjoint (m r : ℕ) (hr : r ≤ m ^ 2)
    {t u : Fin (unusedPathPairCount m r)} (htu : t ≠ u) :
    Disjoint
      ({unusedPathPairFirst m r hr t, unusedPathPairSecond m r hr t} :
        Finset (Fin (6 * m ^ 2)))
      ({unusedPathPairFirst m r hr u, unusedPathPairSecond m r hr u} :
        Finset (Fin (6 * m ^ 2))) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  simp only [mem_insert, mem_singleton] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with h | h
  · exact htu (unusedPathPairFirst_injective m r hr h)
  · have hval := congrArg Fin.val h
    simp [unusedPathPairFirst, unusedPathPairSecond] at hval
    omega
  · have hval := congrArg Fin.val h
    simp [unusedPathPairFirst, unusedPathPairSecond] at hval
    omega
  · exact htu (unusedPathPairSecond_injective m r hr h)

lemma unusedPathPair_slots_ge (m r : ℕ) (hr : r ≤ m ^ 2)
    (t : Fin (unusedPathPairCount m r)) :
    2 * r ≤ (unusedPathPairFirst m r hr t).1 ∧
      2 * r ≤ (unusedPathPairSecond m r hr t).1 := by
  change 2 * r ≤ 2 * r + 2 * t.1 ∧
    2 * r ≤ 2 * r + 2 * t.1 + 1
  omega

lemma usedCycleSlot_lt_unused (m r c : ℕ) (hr : r ≤ m ^ 2)
    (hc : c < r) (hcm : c < m ^ 2)
    (t : Fin (unusedPathPairCount m r)) :
    firstCyclePathSlot m c hcm ≠ unusedPathPairFirst m r hr t ∧
      firstCyclePathSlot m c hcm ≠ unusedPathPairSecond m r hr t ∧
      secondCyclePathSlot m c hcm ≠ unusedPathPairFirst m r hr t ∧
      secondCyclePathSlot m c hcm ≠ unusedPathPairSecond m r hr t := by
  have hge := unusedPathPair_slots_ge m r hr t
  constructor
  · intro h
    have := congrArg Fin.val h
    simp [firstCyclePathSlot] at this
    omega
  constructor
  · intro h
    have := congrArg Fin.val h
    simp [firstCyclePathSlot] at this
    omega
  constructor
  · intro h
    have := congrArg Fin.val h
    simp [secondCyclePathSlot] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp [secondCyclePathSlot] at this
    omega

lemma iSup_pathSlots_eq_used_sup_unused
    {X : Type*} (m r : ℕ) (hr : r ≤ m ^ 2)
    (F : Fin (6 * m ^ 2) → SimpleGraph X) :
    (⨆ i, F i) =
      ((⨆ c : Fin r,
          F (firstCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr))) ⊔
        ⨆ c : Fin r,
          F (secondCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr))) ⊔
      ((⨆ t : Fin (unusedPathPairCount m r),
          F (unusedPathPairFirst m r hr t)) ⊔
        ⨆ t : Fin (unusedPathPairCount m r),
          F (unusedPathPairSecond m r hr t)) := by
  ext u v
  simp only [SimpleGraph.iSup_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hused : i.1 < 2 * r
    · let c : Fin r := ⟨i.1 / 2, by omega⟩
      have hmod := Nat.mod_two_eq_zero_or_one i.1
      have hdiv := Nat.mod_add_div i.1 2
      rcases hmod with hmod | hmod
      · left; left
        refine ⟨c, ?_⟩
        have heq : firstCyclePathSlot m c.1
            (lt_of_lt_of_le c.2 hr) = i := by
          apply Fin.ext
          simp only [firstCyclePathSlot, c]
          omega
        simpa only [heq] using hi
      · left; right
        refine ⟨c, ?_⟩
        have heq : secondCyclePathSlot m c.1
            (lt_of_lt_of_le c.2 hr) = i := by
          apply Fin.ext
          simp only [secondCyclePathSlot, c]
          omega
        simpa only [heq] using hi
    · let d := i.1 - 2 * r
      have hd : 2 * r + d = i.1 := by omega
      have hmod := Nat.mod_two_eq_zero_or_one d
      have hdiv := Nat.mod_add_div d 2
      have ht : d / 2 < unusedPathPairCount m r := by
        simp only [unusedPathPairCount]
        omega
      let t : Fin (unusedPathPairCount m r) := ⟨d / 2, ht⟩
      rcases hmod with hmod | hmod
      · right; left
        refine ⟨t, ?_⟩
        have heq : unusedPathPairFirst m r hr t = i := by
          apply Fin.ext
          simp only [unusedPathPairFirst, t]
          omega
        simpa only [heq] using hi
      · right; right
        refine ⟨t, ?_⟩
        have heq : unusedPathPairSecond m r hr t = i := by
          apply Fin.ext
          simp only [unusedPathPairSecond, t]
          omega
        simpa only [heq] using hi
  · intro h
    rcases h with (⟨c, hc⟩ | ⟨c, hc⟩) | ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨firstCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr), hc⟩
    · exact ⟨secondCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr), hc⟩
    · exact ⟨unusedPathPairFirst m r hr t, ht⟩
    · exact ⟨unusedPathPairSecond m r hr t, ht⟩

lemma pathCoverEdge_out_eq
    {V : Type*} [DecidableEq V]
    (e : (SimpleGraph.completeGraph V).edgeSet) :
    pathCoverEdge e.1.out.1 e.1.out.2 (edge_out_ne e) = e := by
  apply Subtype.ext
  change s(e.1.out.1, e.1.out.2) = e.1
  change Quot.mk _ e.1.out = e.1
  exact e.1.out_eq

def pathCoverPathAtEdge
    {V : Type*} [DecidableEq V] {k : ℕ}
    (e : (SimpleGraph.completeGraph V).edgeSet) (i : Fin k) :
    SimpleGraph (PathCoverVertex V k) :=
  pathCoverTwoEdgePath e.1.out.1 e.1.out.2 (edge_out_ne e) i

def pathCoverSlotGraph
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (i : Fin k) :
    SimpleGraph (PathCoverVertex V k) :=
  ⨆ e : (SimpleGraph.completeGraph V).edgeSet, pathCoverPathAtEdge e i

lemma pathCoverGraph_eq_iSup_pathCoverSlotGraph
    {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) :
    pathCoverGraph V k = ⨆ i : Fin k, pathCoverSlotGraph i := by
  have hrootmiddle
      (x : V) (e : (SimpleGraph.completeGraph V).edgeSet) (j : Fin k) :
      (pathCoverGraph V k).Adj (.root x) (.middle e j) ↔
        (⨆ i : Fin k, pathCoverSlotGraph i).Adj (.root x) (.middle e j) := by
    simp only [pathCoverGraph_adj_root_middle,
      SimpleGraph.iSup_adj, pathCoverSlotGraph,
      pathCoverPathAtEdge, pathCoverTwoEdgePath_adj_iff]
    constructor
    · intro hx
      rw [← e.1.out_eq, Sym2.mem_iff] at hx
      have hmiddle : pathCoverMiddleBetween e.1.out.1 e.1.out.2
          (edge_out_ne e) j = PathCoverVertex.middle e j := by
        unfold pathCoverMiddleBetween
        rw [pathCoverEdge_out_eq]
      rcases hx with hx | hx
      · exact ⟨j, e, Or.inl ⟨congrArg PathCoverVertex.root hx,
          hmiddle.symm⟩⟩
      · exact ⟨j, e, Or.inr (Or.inr (Or.inl
          ⟨congrArg PathCoverVertex.root hx, hmiddle.symm⟩))⟩
    · rintro ⟨i, f, h⟩
      simp only [pathCoverMiddleBetween, pathCoverEdge_out_eq] at h
      rcases h with h | h | h | h
      · have hmid : e = f := by
          have hm := congrArg
            (fun z : PathCoverVertex V k ↦ match z with
              | .root _ => none
              | .middle q _ => some q) h.2
          simpa using hm
        subst f
        rw [← e.1.out_eq, Sym2.mem_iff]
        exact Or.inl (PathCoverVertex.root.inj h.1)
      · simp at h
      · have hmid : e = f := by
          have hm := congrArg
            (fun z : PathCoverVertex V k ↦ match z with
              | .root _ => none
              | .middle q _ => some q) h.2
          simpa using hm
        subst f
        rw [← e.1.out_eq, Sym2.mem_iff]
        exact Or.inr (PathCoverVertex.root.inj h.1)
      · simp at h
  ext u v
  cases u with
  | root x =>
      cases v with
      | root y =>
          simp [pathCoverSlotGraph, pathCoverPathAtEdge,
            pathCoverTwoEdgePath_adj_iff, pathCoverMiddleBetween]
      | middle e j => exact hrootmiddle x e j
  | middle e i =>
      cases v with
      | root x =>
          constructor
          · intro h
            exact ((hrootmiddle x e i).mp h.symm).symm
          · intro h
            exact ((hrootmiddle x e i).mpr h.symm).symm
      | middle f j =>
          simp [pathCoverSlotGraph, pathCoverPathAtEdge,
            pathCoverTwoEdgePath_adj_iff, pathCoverMiddleBetween]

lemma pathCoverPathAtEdge_pathCoverEdge
    {V : Type*} [DecidableEq V] {k : ℕ}
    (a b : V) (hab : a ≠ b) (i : Fin k) :
    pathCoverPathAtEdge (pathCoverEdge a b hab) i =
      pathCoverTwoEdgePath a b hab i := by
  unfold pathCoverPathAtEdge
  apply pathCoverTwoEdgePath_eq_of_sym2_eq
  exact congrArg Subtype.val (pathCoverEdge_out_eq (pathCoverEdge a b hab))

/-- The four-cycle made from one canonical pair of unused paths over `e`. -/
def unusedPathC4
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    Fin 4 ↪ PathCoverVertex V (6 * m ^ 2) :=
  pairedPathC4Embedding e.1.out.1 e.1.out.2 (edge_out_ne e)
    (unusedPathPairFirst m r hr t) (unusedPathPairSecond m r hr t)
    (unusedPathPairFirst_ne_second m r hr t)

lemma unusedPathC4_edgeFaithful
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 4)
      (unusedPathC4 m r hr e t) := by
  unfold unusedPathC4
  apply pairedPathC4_edgeFaithful

lemma unusedPathC4_map_le_pathCover
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    (SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t) ≤
      pathCoverGraph V (6 * m ^ 2) := by
  unfold unusedPathC4
  apply pairedPathC4_map_le_pathCover

lemma unusedPathC4_map_eq_paths
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    (SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t) =
      pathCoverPathAtEdge e (unusedPathPairFirst m r hr t) ⊔
        pathCoverPathAtEdge e (unusedPathPairSecond m r hr t) := by
  unfold unusedPathC4 pathCoverPathAtEdge
  rw [pairedPathC4_map_eq]

lemma unusedPathC4Slots_eq
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    pairedPathC4Slots e.1.out.1 e.1.out.2 (edge_out_ne e)
      (unusedPathPairFirst m r hr t) (unusedPathPairSecond m r hr t) =
      {(e, unusedPathPairFirst m r hr t),
        (e, unusedPathPairSecond m r hr t)} := by
  simp [pairedPathC4Slots, pathCoverEdge_out_eq]

lemma unusedPathC4_slots_disjoint
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    {e f : (SimpleGraph.completeGraph V).edgeSet}
    {t u : Fin (unusedPathPairCount m r)}
    (hetu : (e, t) ≠ (f, u)) :
    Disjoint
      (pairedPathC4Slots e.1.out.1 e.1.out.2 (edge_out_ne e)
        (unusedPathPairFirst m r hr t) (unusedPathPairSecond m r hr t))
      (pairedPathC4Slots f.1.out.1 f.1.out.2 (edge_out_ne f)
        (unusedPathPairFirst m r hr u) (unusedPathPairSecond m r hr u)) := by
  rw [unusedPathC4Slots_eq, unusedPathC4Slots_eq,
    Finset.disjoint_left]
  intro z hz hz'
  simp only [mem_insert, mem_singleton] at hz hz'
  rcases hz with rfl | rfl <;> rcases hz' with h | h
  all_goals
    by_cases hef : e = f
  · subst f
    have htu : t ≠ u := by
      intro htu
      exact hetu (Prod.ext rfl htu)
    have hd := unusedPathPair_disjoint m r hr htu
    have hs := congrArg Prod.snd h
    change unusedPathPairFirst m r hr t =
      unusedPathPairFirst m r hr u at hs
    exact Finset.disjoint_left.mp hd
      (show unusedPathPairFirst m r hr t ∈
        {unusedPathPairFirst m r hr t,
          unusedPathPairSecond m r hr t} by simp)
      (show unusedPathPairFirst m r hr t ∈
        {unusedPathPairFirst m r hr u,
          unusedPathPairSecond m r hr u} by rw [hs]; simp)
  · exact hef (congrArg Prod.fst h)
  · subst f
    have htu : t ≠ u := by
      intro htu
      exact hetu (Prod.ext rfl htu)
    have hd := unusedPathPair_disjoint m r hr htu
    have hs := congrArg Prod.snd h
    change unusedPathPairFirst m r hr t =
      unusedPathPairSecond m r hr u at hs
    exact Finset.disjoint_left.mp hd
      (show unusedPathPairFirst m r hr t ∈
        {unusedPathPairFirst m r hr t,
          unusedPathPairSecond m r hr t} by simp)
      (show unusedPathPairFirst m r hr t ∈
        {unusedPathPairFirst m r hr u,
          unusedPathPairSecond m r hr u} by rw [hs]; simp)
  · exact hef (congrArg Prod.fst h)
  · subst f
    have htu : t ≠ u := by
      intro htu
      exact hetu (Prod.ext rfl htu)
    have hd := unusedPathPair_disjoint m r hr htu
    have hs := congrArg Prod.snd h
    change unusedPathPairSecond m r hr t =
      unusedPathPairFirst m r hr u at hs
    exact Finset.disjoint_left.mp hd
      (show unusedPathPairSecond m r hr t ∈
        {unusedPathPairFirst m r hr t,
          unusedPathPairSecond m r hr t} by simp)
      (show unusedPathPairSecond m r hr t ∈
        {unusedPathPairFirst m r hr u,
          unusedPathPairSecond m r hr u} by rw [hs]; simp)
  · exact hef (congrArg Prod.fst h)
  · subst f
    have htu : t ≠ u := by
      intro htu
      exact hetu (Prod.ext rfl htu)
    have hd := unusedPathPair_disjoint m r hr htu
    have hs := congrArg Prod.snd h
    change unusedPathPairSecond m r hr t =
      unusedPathPairSecond m r hr u at hs
    exact Finset.disjoint_left.mp hd
      (show unusedPathPairSecond m r hr t ∈
        {unusedPathPairFirst m r hr t,
          unusedPathPairSecond m r hr t} by simp)
      (show unusedPathPairSecond m r hr t ∈
        {unusedPathPairFirst m r hr u,
          unusedPathPairSecond m r hr u} by rw [hs]; simp)
  · exact hef (congrArg Prod.fst h)

lemma unusedPathC4_pairwise_disjoint
    {V : Type*} [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2)
    {e f : (SimpleGraph.completeGraph V).edgeSet}
    {t u : Fin (unusedPathPairCount m r)}
    (hetu : (e, t) ≠ (f, u)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t))
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr f u)) := by
  unfold unusedPathC4
  apply pairedPathC4_disjoint_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_of_slots_disjoint
  exact unusedPathC4_slots_disjoint m r hr hetu

def unusedPathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  ⨆ e : (SimpleGraph.completeGraph V).edgeSet,
    ⨆ t : Fin (unusedPathPairCount m r),
      (SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t)

lemma unusedPathGraph_eq_slotGraphs
    {V : Type*} [Fintype V] [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2) :
    unusedPathGraph (V := V) m r hr =
      (⨆ t : Fin (unusedPathPairCount m r),
          pathCoverSlotGraph (V := V) (unusedPathPairFirst m r hr t)) ⊔
        ⨆ t : Fin (unusedPathPairCount m r),
          pathCoverSlotGraph (V := V) (unusedPathPairSecond m r hr t) := by
  unfold unusedPathGraph pathCoverSlotGraph
  simp_rw [unusedPathC4_map_eq_paths]
  simp_rw [iSup_sup_eq]
  rw [iSup_comm (f := fun (e : (SimpleGraph.completeGraph V).edgeSet)
      (t : Fin (unusedPathPairCount m r)) ↦
        pathCoverPathAtEdge e (unusedPathPairFirst m r hr t)),
    iSup_comm (f := fun (e : (SimpleGraph.completeGraph V).edgeSet)
      (t : Fin (unusedPathPairCount m r)) ↦
        pathCoverPathAtEdge e (unusedPathPairSecond m r hr t))]

/-- The concrete cycle-graph copy in the order
`p.getVert 1, ..., p.getVert p.length`.  The last entry is the repeated
endpoint, so the wraparound source edge is the first edge of the walk. -/
def walkCycleCopy
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph p.length) G := by
  refine ⟨⟨fun n => p.support[n.succ]'(?_), ?_⟩, ?_⟩
  · grind [hp.three_le_length, SimpleGraph.Walk.length_tail_add_one,
      SimpleGraph.Walk.not_nil_iff_lt_length]
  · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hne : x ≠ y := fun h => by simp_all
    wlog hle : x > y
    · exact this p hp y hy x hx hxy.symm hne.symm (by lia) |>.symm
    rcases SimpleGraph.cycleGraph_adj'.mp hxy with hxy | hxy
    · simp_rw [show x = y + 1 by
        grind [Fin.sub_val_of_le]]
      exact p.isChain_adj_support.getElem _ _ |>.symm
    · rw [Fin.coe_sub_iff_lt.mpr hle] at hxy
      simp_rw [show x = p.length - 1 by lia,
        show y = 0 by lia, Fin.succ_mk,
        show p.length - 1 + 1 = p.length by lia]
      simp [p.adj_snd hp.not_nil]
  · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    change p.support[(⟨x, hx⟩ : Fin p.length).succ] =
      p.support[(⟨y, hy⟩ : Fin p.length).succ] at hxy
    have hgetx : p.support[(⟨x, hx⟩ : Fin p.length).succ] =
        p.getVert (x + 1) := by
      exact p.support_getElem_eq_getVert _
    have hgety : p.support[(⟨y, hy⟩ : Fin p.length).succ] =
        p.getVert (y + 1) := by
      exact p.support_getElem_eq_getVert _
    rw [hgetx, hgety] at hxy
    have hindex := hp.getVert_injOn
      (show 1 ≤ x + 1 ∧ x + 1 ≤ p.length by omega)
      (show 1 ≤ y + 1 ∧ y + 1 ≤ p.length by omega) hxy
    change x + 1 = y + 1 at hindex
    have hxyNat : x = y := by omega
    subst y
    rfl

def walkCycleEmbedding
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin p.length ↪ V :=
  (walkCycleCopy p hp).toEmbedding

lemma walkCycleEmbedding_adj
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) {i j : Fin p.length}
    (hij : (SimpleGraph.cycleGraph p.length).Adj i j) :
    G.Adj (walkCycleEmbedding p hp i) (walkCycleEmbedding p hp j) :=
  (walkCycleCopy p hp).toHom.map_adj hij

lemma walkCycleEmbedding_injective
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    Function.Injective (walkCycleEmbedding p hp) :=
  (walkCycleEmbedding p hp).injective

lemma walkCycleEmbedding_eq_getVert_succ
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin p.length) :
    walkCycleEmbedding p hp i = p.getVert (i.1 + 1) := by
  unfold walkCycleEmbedding walkCycleCopy
  exact p.support_getElem_eq_getVert _

/-! ## Exact edge decomposition of a finite cycle -/

def cycleLinearEdge (n : ℕ) (i : Fin (n - 1)) : SimpleGraph (Fin n) :=
  SimpleGraph.edge ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩

def cycleWrapEdge (n : ℕ) (hn : 3 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.edge ⟨n - 1, by omega⟩ ⟨0, by omega⟩

lemma pathGraph_eq_iSup_cycleLinearEdge (n : ℕ) :
    SimpleGraph.pathGraph n = ⨆ i : Fin (n - 1), cycleLinearEdge n i := by
  ext x y
  rw [SimpleGraph.pathGraph_adj, SimpleGraph.iSup_adj]
  constructor
  · intro h
    rcases h with h | h
    · let i : Fin (n - 1) := ⟨x.1, by omega⟩
      refine ⟨i, ?_⟩
      simp only [cycleLinearEdge, SimpleGraph.edge_adj]
      refine ⟨Or.inl ⟨rfl, Fin.ext ?_⟩, ?_⟩
      · exact h.symm
      · intro hxy
        have := congrArg Fin.val hxy
        omega
    · let i : Fin (n - 1) := ⟨y.1, by omega⟩
      refine ⟨i, ?_⟩
      simp only [cycleLinearEdge, SimpleGraph.edge_adj]
      refine ⟨Or.inr ⟨Fin.ext ?_, rfl⟩, ?_⟩
      · exact h.symm
      · intro hxy
        have := congrArg Fin.val hxy
        omega
  · rintro ⟨i, hi⟩
    simp only [cycleLinearEdge, SimpleGraph.edge_adj] at hi
    rcases hi.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma cycleGraph_eq_wrap_sup_pathGraph (n : ℕ) (hn : 3 ≤ n) :
    SimpleGraph.cycleGraph n =
      cycleWrapEdge n hn ⊔ SimpleGraph.pathGraph n := by
  ext x y
  rw [SimpleGraph.sup_adj]
  constructor
  · intro hxy
    have hne := hxy.ne
    wlog hle : x.1 > y.1 generalizing x y
    · have hyx := this y x hxy.symm hne.symm (by omega)
      rcases hyx with hyx | hyx
      · exact Or.inl hyx.symm
      · exact Or.inr hyx.symm
    rcases SimpleGraph.cycleGraph_adj'.mp hxy with hxy | hxy
    · right
      rw [SimpleGraph.pathGraph_adj]
      right
      grind [Fin.sub_val_of_le]
    · left
      rw [Fin.coe_sub_iff_lt.mpr hle] at hxy
      simp only [cycleWrapEdge, SimpleGraph.edge_adj]
      have hx : x.1 = n - 1 := by omega
      have hy : y.1 = 0 := by omega
      refine ⟨Or.inl ⟨Fin.ext hx, Fin.ext hy⟩, ?_⟩
      intro heq
      exact hne heq
  · intro hxy
    rcases hxy with hwrap | hpath
    · simp only [cycleWrapEdge, SimpleGraph.edge_adj] at hwrap
      rcases hwrap.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [SimpleGraph.cycleGraph_adj']
        right
        rw [Fin.coe_sub_iff_lt.mpr (show 0 < n - 1 by omega)]
        change n + 0 - (n - 1) = 1
        omega
      · have hlastzero : (SimpleGraph.cycleGraph n).Adj
            (⟨n - 1, by omega⟩ : Fin n) ⟨0, by omega⟩ := by
          rw [SimpleGraph.cycleGraph_adj']
          right
          rw [Fin.coe_sub_iff_lt.mpr (show 0 < n - 1 by omega)]
          change n + 0 - (n - 1) = 1
          omega
        exact hlastzero.symm
    · exact SimpleGraph.pathGraph_le_cycleGraph hpath

lemma cycleGraph_eq_wrap_sup_linearEdges (n : ℕ) (hn : 3 ≤ n) :
    SimpleGraph.cycleGraph n =
      cycleWrapEdge n hn ⊔ ⨆ i : Fin (n - 1), cycleLinearEdge n i := by
  rw [cycleGraph_eq_wrap_sup_pathGraph n hn,
    pathGraph_eq_iSup_cycleLinearEdge]

lemma iSup_fin_pred_eq_first_sup_succ
    {X : Type*} (n : ℕ) (hn : 3 ≤ n)
    (F : Fin (n - 1) → SimpleGraph X) :
    (⨆ i, F i) =
      F ⟨0, by omega⟩ ⊔ ⨆ j : Fin (n - 2), F ⟨j.1 + 1, by omega⟩ := by
  ext u v
  simp only [SimpleGraph.iSup_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hi0 : i.1 = 0
    · left
      have hieq : i = ⟨0, by omega⟩ := Fin.ext hi0
      simpa only [hieq] using hi
    · right
      let j : Fin (n - 2) := ⟨i.1 - 1, by omega⟩
      refine ⟨j, ?_⟩
      have hij : (⟨j.1 + 1, by omega⟩ : Fin (n - 1)) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      simpa only [hij] using hi
  · intro h
    rcases h with h | ⟨j, hj⟩
    · exact ⟨⟨0, by omega⟩, h⟩
    · exact ⟨⟨j.1 + 1, by omega⟩, hj⟩

lemma iSup_fin_pred_eq_last_sup_init
    {X : Type*} (n : ℕ) (hn : 3 ≤ n)
    (F : Fin (n - 1) → SimpleGraph X) :
    (⨆ i, F i) =
      F ⟨n - 2, by omega⟩ ⊔ ⨆ j : Fin (n - 2), F ⟨j.1, by omega⟩ := by
  ext u v
  simp only [SimpleGraph.iSup_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hilast : i.1 = n - 2
    · left
      have hieq : i = ⟨n - 2, by omega⟩ := Fin.ext hilast
      simpa only [hieq] using hi
    · right
      let j : Fin (n - 2) := ⟨i.1, by omega⟩
      refine ⟨j, ?_⟩
      have hij : (⟨j.1, by omega⟩ : Fin (n - 1)) = i := by
        apply Fin.ext
        rfl
      simpa only [hij] using hi
  · intro h
    rcases h with h | ⟨j, hj⟩
    · exact ⟨⟨n - 2, by omega⟩, h⟩
    · exact ⟨⟨j.1, by omega⟩, hj⟩

/-! ## The short pieces attached to one indexed cycle -/

def cycleAnchorIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin p.length :=
  ⟨p.length - 1, by
    have := hp.three_le_length
    omega⟩

def cycleFirstInternalIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin p.length :=
  ⟨0, by
    have := hp.three_le_length
    omega⟩

def cycleLastInternalIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin p.length :=
  ⟨p.length - 2, by
    have := hp.three_le_length
    omega⟩

lemma cycleAnchor_ne_first
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    cycleAnchorIndex p hp ≠ cycleFirstInternalIndex p hp := by
  intro h
  have := congrArg Fin.val h
  simp [cycleAnchorIndex, cycleFirstInternalIndex] at this
  have hlen := hp.three_le_length
  omega

lemma cycleAnchor_ne_lastInternal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    cycleAnchorIndex p hp ≠ cycleLastInternalIndex p hp := by
  intro h
  have := congrArg Fin.val h
  simp [cycleAnchorIndex, cycleLastInternalIndex] at this
  have hlen := hp.three_le_length
  omega

def firstCycleEndpointTriangle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    Fin 3 ↪ PathCoverVertex V (6 * m ^ 2) :=
  let f := walkCycleEmbedding p hp
  pathTriangleEmbedding
    (f (cycleAnchorIndex p hp)) (f (cycleFirstInternalIndex p hp))
    (f.injective.ne (cycleAnchor_ne_first p hp))
    (firstCyclePathSlot m c hc)

def lastCycleEndpointTriangle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    Fin 3 ↪ PathCoverVertex V (6 * m ^ 2) :=
  let f := walkCycleEmbedding p hp
  pathTriangleEmbedding
    (f (cycleAnchorIndex p hp)) (f (cycleLastInternalIndex p hp))
    (f.injective.ne (cycleAnchor_ne_lastInternal p hp))
    (secondCyclePathSlot m c hc)

lemma firstCycleEndpointTriangle_edgeFaithful
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 3)
      (firstCycleEndpointTriangle m c hc p hp) := by
  unfold firstCycleEndpointTriangle
  apply pathTriangle_edgeFaithful

lemma firstCycleEndpointTriangle_map_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp) =
      pathCoverTwoEdgePath
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleFirstInternalIndex p hp))
          ((walkCycleEmbedding p hp).injective.ne
            (cycleAnchor_ne_first p hp))
          (firstCyclePathSlot m c hc) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleFirstInternalIndex p hp)) := by
  unfold firstCycleEndpointTriangle
  apply pathTriangle_map_eq

lemma lastCycleEndpointTriangle_edgeFaithful
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 3)
      (lastCycleEndpointTriangle m c hc p hp) := by
  unfold lastCycleEndpointTriangle
  apply pathTriangle_edgeFaithful

lemma lastCycleEndpointTriangle_map_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp) =
      pathCoverTwoEdgePath
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleLastInternalIndex p hp))
          ((walkCycleEmbedding p hp).injective.ne
            (cycleAnchor_ne_lastInternal p hp))
          (secondCyclePathSlot m c hc) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleLastInternalIndex p hp)) := by
  unfold lastCycleEndpointTriangle
  apply pathTriangle_map_eq

lemma cycleGraph_adj_anchor_first
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph p.length).Adj
      (cycleAnchorIndex p hp) (cycleFirstInternalIndex p hp) := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  change ((p.length - (p.length - 1) + 0) % p.length) = 1
  have hlen := hp.three_le_length
  have hsub : p.length - (p.length - 1) = 1 := by omega
  rw [hsub]
  exact Nat.mod_eq_of_lt (by omega)

lemma cycleGraph_adj_anchor_lastInternal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph p.length).Adj
      (cycleAnchorIndex p hp) (cycleLastInternalIndex p hp) := by
  apply SimpleGraph.pathGraph_le_cycleGraph
  rw [SimpleGraph.pathGraph_adj]
  right
  simp only [cycleAnchorIndex, cycleLastInternalIndex]
  have hlen := hp.three_le_length
  omega

lemma firstCycleEndpointTriangle_map_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp) ≤
      pathCoverGraph V (6 * m ^ 2) ⊔
        G.map (pathCoverRootEmbedding (X := V) (k := 6 * m ^ 2)) := by
  unfold firstCycleEndpointTriangle
  apply pathTriangle_map_le G
  exact walkCycleEmbedding_adj p hp (cycleGraph_adj_anchor_first p hp)

lemma lastCycleEndpointTriangle_map_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp) ≤
      pathCoverGraph V (6 * m ^ 2) ⊔
        G.map (pathCoverRootEmbedding (X := V) (k := 6 * m ^ 2)) := by
  unfold lastCycleEndpointTriangle
  apply pathTriangle_map_le G
  exact walkCycleEmbedding_adj p hp
    (cycleGraph_adj_anchor_lastInternal p hp)

def cycleInternalIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    Fin p.length :=
  ⟨i.1, by omega⟩

def cycleInternalSuccIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    Fin p.length :=
  ⟨i.1 + 1, by omega⟩

lemma cycleAnchor_ne_internal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    cycleAnchorIndex p hp ≠ cycleInternalIndex p hp i := by
  intro h
  have := congrArg Fin.val h
  simp [cycleAnchorIndex, cycleInternalIndex] at this
  have hlen := hp.three_le_length
  omega

lemma cycleAnchor_ne_internalSucc
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    cycleAnchorIndex p hp ≠ cycleInternalSuccIndex p hp i := by
  intro h
  have := congrArg Fin.val h
  simp [cycleAnchorIndex, cycleInternalSuccIndex] at this
  have hlen := hp.three_le_length
  omega

lemma cycleInternal_ne_succ
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    cycleInternalIndex p hp i ≠ cycleInternalSuccIndex p hp i := by
  intro h
  have := congrArg Fin.val h
  simp [cycleInternalIndex, cycleInternalSuccIndex] at this

lemma cycleAnchorFirst_edge_ne_anchorLast
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    s(cycleAnchorIndex p hp, cycleFirstInternalIndex p hp) ≠
      s(cycleAnchorIndex p hp, cycleLastInternalIndex p hp) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  all_goals
    have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    simp [cycleAnchorIndex, cycleFirstInternalIndex,
      cycleLastInternalIndex] at h₁ h₂
    have hlen := hp.three_le_length
    omega

lemma cycleAnchorFirst_edge_ne_internal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    s(cycleAnchorIndex p hp, cycleFirstInternalIndex p hp) ≠
      s(cycleInternalIndex p hp i, cycleInternalSuccIndex p hp i) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hi := i.2
    have hlen := hp.three_le_length
    have h₁ := congrArg Fin.val h.1
    change p.length - 1 = i.1 at h₁
    omega
  · have hi := i.2
    have hlen := hp.three_le_length
    have h₁ := congrArg Fin.val h.1
    change p.length - 1 = i.1 + 1 at h₁
    omega

lemma cycleAnchorLast_edge_ne_internal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    s(cycleAnchorIndex p hp, cycleLastInternalIndex p hp) ≠
      s(cycleInternalIndex p hp i, cycleInternalSuccIndex p hp i) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hi := i.2
    have hlen := hp.three_le_length
    have h₁ := congrArg Fin.val h.1
    change p.length - 1 = i.1 at h₁
    omega
  · have hi := i.2
    have hlen := hp.three_le_length
    have h₁ := congrArg Fin.val h.1
    change p.length - 1 = i.1 + 1 at h₁
    omega

lemma cycleInternal_edges_ne
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    {i j : Fin (p.length - 2)} (hij : i ≠ j) :
    s(cycleInternalIndex p hp i, cycleInternalSuccIndex p hp i) ≠
      s(cycleInternalIndex p hp j, cycleInternalSuccIndex p hp j) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply hij
    apply Fin.ext
    have := congrArg Fin.val h.1
    simpa [cycleInternalIndex] using this
  · have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    simp [cycleInternalIndex, cycleInternalSuccIndex] at h₁ h₂
    omega

lemma cycleAnchorFirst_spoke_ne_internalSucc
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    s(cycleAnchorIndex p hp, cycleFirstInternalIndex p hp) ≠
      s(cycleAnchorIndex p hp, cycleInternalSuccIndex p hp i) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hi := i.2
    have hval := congrArg Fin.val h.2
    change 0 = i.1 + 1 at hval
    omega
  · exact cycleAnchor_ne_internalSucc p hp i h.1

lemma cycleAnchorLast_spoke_ne_internal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    s(cycleAnchorIndex p hp, cycleLastInternalIndex p hp) ≠
      s(cycleAnchorIndex p hp, cycleInternalIndex p hp i) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hi := i.2
    have hval := congrArg Fin.val h.2
    change p.length - 2 = i.1 at hval
    omega
  · exact cycleAnchor_ne_internal p hp i h.1

lemma cycleAnchorInternal_spokes_ne
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    {i j : Fin (p.length - 2)} (hij : i ≠ j) :
    s(cycleAnchorIndex p hp, cycleInternalIndex p hp i) ≠
      s(cycleAnchorIndex p hp, cycleInternalIndex p hp j) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply hij
    apply Fin.ext
    have := congrArg Fin.val h.2
    simpa [cycleInternalIndex] using this
  · exact cycleAnchor_ne_internal p hp j h.1

lemma cycleAnchorInternalSucc_spokes_ne
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    {i j : Fin (p.length - 2)} (hij : i ≠ j) :
    s(cycleAnchorIndex p hp, cycleInternalSuccIndex p hp i) ≠
      s(cycleAnchorIndex p hp, cycleInternalSuccIndex p hp j) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply hij
    apply Fin.ext
    have hval := congrArg Fin.val h.2
    change i.1 + 1 = j.1 + 1 at hval
    omega
  · exact cycleAnchor_ne_internalSucc p hp j h.1

lemma sym2_apply_ne_of_injective
    {A B : Type*} (f : A → B) (hf : Function.Injective f)
    {a b c d : A} (h : s(a, b) ≠ s(c, d)) :
    s(f a, f b) ≠ s(f c, f d) := by
  intro heq
  apply h
  rw [Sym2.eq_iff] at heq ⊢
  rcases heq with heq | heq
  · exact Or.inl ⟨hf heq.1, hf heq.2⟩
  · exact Or.inr ⟨hf heq.1, hf heq.2⟩

def cycleSpokeIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 1)) :
    Fin p.length :=
  ⟨i.1, by
    have hlen := hp.three_le_length
    omega⟩

lemma cycleAnchor_ne_spokeIndex
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 1)) :
    cycleAnchorIndex p hp ≠ cycleSpokeIndex p hp i := by
  intro h
  have hval := congrArg Fin.val h
  change p.length - 1 = i.1 at hval
  have hi := i.2
  omega

def cycleSpokeEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 1)) :
    (SimpleGraph.completeGraph V).edgeSet :=
  let f := walkCycleEmbedding p hp
  pathCoverEdge (f (cycleAnchorIndex p hp)) (f (cycleSpokeIndex p hp i))
    (f.injective.ne (cycleAnchor_ne_spokeIndex p hp i))

def cycleSpokeEdges
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    Finset (SimpleGraph.completeGraph V).edgeSet :=
  univ.image (cycleSpokeEdge p hp)

lemma cycleSpokeEdge_mem
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 1)) :
    cycleSpokeEdge p hp i ∈ cycleSpokeEdges p hp := by
  simp [cycleSpokeEdges]

def cycleFirstSpoke
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin (p.length - 1) :=
  ⟨0, by have := hp.three_le_length; omega⟩

def cycleLastSpoke
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : Fin (p.length - 1) :=
  ⟨p.length - 2, by have := hp.three_le_length; omega⟩

def cycleInternalSpoke
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    Fin (p.length - 1) :=
  ⟨i.1, by omega⟩

def cycleInternalSuccSpoke
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    Fin (p.length - 1) :=
  ⟨i.1 + 1, by omega⟩

@[simp] lemma cycleSpokeIndex_first
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    cycleSpokeIndex p hp (cycleFirstSpoke p hp) =
      cycleFirstInternalIndex p hp := rfl

@[simp] lemma cycleSpokeIndex_last
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    cycleSpokeIndex p hp (cycleLastSpoke p hp) =
      cycleLastInternalIndex p hp := rfl

@[simp] lemma cycleSpokeIndex_internal
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    cycleSpokeIndex p hp (cycleInternalSpoke p hp i) =
      cycleInternalIndex p hp i := rfl

@[simp] lemma cycleSpokeIndex_internalSucc
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    cycleSpokeIndex p hp (cycleInternalSuccSpoke p hp i) =
      cycleInternalSuccIndex p hp i := rfl

def cycleFirstSlotPath
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 1)) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  let f := walkCycleEmbedding p hp
  pathCoverTwoEdgePath (f (cycleAnchorIndex p hp))
    (f (cycleSpokeIndex p hp i))
    (f.injective.ne (cycleAnchor_ne_spokeIndex p hp i))
    (firstCyclePathSlot m c hc)

def cycleSecondSlotPath
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 1)) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  let f := walkCycleEmbedding p hp
  pathCoverTwoEdgePath (f (cycleAnchorIndex p hp))
    (f (cycleSpokeIndex p hp i))
    (f.injective.ne (cycleAnchor_ne_spokeIndex p hp i))
    (secondCyclePathSlot m c hc)

lemma cycleFirstSlotPath_eq_pathCoverPathAtEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 1)) :
    cycleFirstSlotPath m c hc p hp i =
      pathCoverPathAtEdge (cycleSpokeEdge p hp i)
        (firstCyclePathSlot m c hc) := by
  unfold cycleFirstSlotPath cycleSpokeEdge
  rw [pathCoverPathAtEdge_pathCoverEdge]

lemma cycleSecondSlotPath_eq_pathCoverPathAtEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 1)) :
    cycleSecondSlotPath m c hc p hp i =
      pathCoverPathAtEdge (cycleSpokeEdge p hp i)
        (secondCyclePathSlot m c hc) := by
  unfold cycleSecondSlotPath cycleSpokeEdge
  rw [pathCoverPathAtEdge_pathCoverEdge]

lemma firstCycleEndpointTriangle_map_eq_slot
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp) =
      cycleFirstSlotPath m c hc p hp (cycleFirstSpoke p hp) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleFirstInternalIndex p hp)) := by
  rw [firstCycleEndpointTriangle_map_eq]
  rfl

lemma lastCycleEndpointTriangle_map_eq_slot
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp) =
      cycleSecondSlotPath m c hc p hp (cycleLastSpoke p hp) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleLastInternalIndex p hp)) := by
  rw [lastCycleEndpointTriangle_map_eq]
  rfl

abbrev CycleResidualEdge
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :=
  {e : (SimpleGraph.completeGraph V).edgeSet // e ∉ cycleSpokeEdges p hp}

lemma iSup_completeEdges_eq_spokes_sup_residual
    {V X : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (F : (SimpleGraph.completeGraph V).edgeSet → SimpleGraph X) :
    (⨆ e : (SimpleGraph.completeGraph V).edgeSet, F e) =
      (⨆ i : Fin (p.length - 1), F (cycleSpokeEdge p hp i)) ⊔
        ⨆ e : CycleResidualEdge p hp, F e.1 := by
  ext a b
  simp only [SimpleGraph.iSup_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨e, he⟩
    by_cases hespoke : e ∈ cycleSpokeEdges p hp
    · rw [cycleSpokeEdges] at hespoke
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hespoke
      exact Or.inl ⟨i, he⟩
    · exact Or.inr ⟨⟨e, hespoke⟩, he⟩
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨e, he⟩
    · exact ⟨cycleSpokeEdge p hp i, hi⟩
    · exact ⟨e.1, he⟩

lemma CycleResidualEdge.ne_spoke
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} {hp : p.IsCycle} (e : CycleResidualEdge p hp)
    (i : Fin (p.length - 1)) : e.1 ≠ cycleSpokeEdge p hp i := by
  intro h
  apply e.2
  rw [h]
  exact cycleSpokeEdge_mem p hp i

lemma cycleResidual_pathCoverEdge_ne_spoke
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} {hp : p.IsCycle} (e : CycleResidualEdge p hp)
    (i : Fin (p.length - 1)) :
    pathCoverEdge e.1.1.out.1 e.1.1.out.2 (edge_out_ne e.1) ≠
      cycleSpokeEdge p hp i := by
  rw [pathCoverEdge_out_eq]
  exact e.ne_spoke i

/-- A pair of paths in cycle slot `c`, over a root edge which the augmented
cycle itself does not use as a spoke. -/
def cycleResidualC4
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    Fin 4 ↪ PathCoverVertex V (6 * m ^ 2) :=
  pairedPathC4Embedding e.1.1.out.1 e.1.1.out.2 (edge_out_ne e.1)
    (firstCyclePathSlot m c hc) (secondCyclePathSlot m c hc)
    (firstCyclePathSlot_ne_second m c hc)

lemma cycleResidualC4_edgeFaithful
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 4)
      (cycleResidualC4 m c hc p hp e) := by
  unfold cycleResidualC4
  apply pairedPathC4_edgeFaithful

lemma cycleResidualC4_map_le_pathCover
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    (SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e) ≤
      pathCoverGraph V (6 * m ^ 2) := by
  unfold cycleResidualC4
  apply pairedPathC4_map_le_pathCover

lemma cycleResidualC4_map_eq
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    (SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e) =
      pathCoverTwoEdgePath e.1.1.out.1 e.1.1.out.2 (edge_out_ne e.1)
          (firstCyclePathSlot m c hc) ⊔
        pathCoverTwoEdgePath e.1.1.out.1 e.1.1.out.2 (edge_out_ne e.1)
          (secondCyclePathSlot m c hc) := by
  unfold cycleResidualC4
  apply pairedPathC4_map_eq

lemma cycleResidualC4_map_eq_paths
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    (SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e) =
      pathCoverPathAtEdge e.1 (firstCyclePathSlot m c hc) ⊔
        pathCoverPathAtEdge e.1 (secondCyclePathSlot m c hc) := by
  rw [cycleResidualC4_map_eq]
  rfl

def cycleResidualGraph
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  ⨆ e : CycleResidualEdge p hp,
    (SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e)

/-- The `i`th five-cycle in the chain attached to `p`. -/
def cycleChainC5
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) : Fin 5 ↪ PathCoverVertex V (6 * m ^ 2) :=
  let f := walkCycleEmbedding p hp
  augmentedEdgeC5Embedding
    (f (cycleAnchorIndex p hp))
    (f (cycleInternalIndex p hp i))
    (f (cycleInternalSuccIndex p hp i))
    (f.injective.ne (cycleAnchor_ne_internal p hp i))
    (f.injective.ne (cycleAnchor_ne_internalSucc p hp i))
    (f.injective.ne (cycleInternal_ne_succ p hp i))
    (secondCyclePathSlot m c hc) (firstCyclePathSlot m c hc)

lemma cycleChainC5_edgeFaithful
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 5)
      (cycleChainC5 m c hc p hp i) := by
  unfold cycleChainC5
  apply augmentedEdgeC5_edgeFaithful

lemma cycleChainC5_map_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    (SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i) =
      (pathCoverTwoEdgePath
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleInternalIndex p hp i))
          ((walkCycleEmbedding p hp).injective.ne
            (cycleAnchor_ne_internal p hp i))
          (secondCyclePathSlot m c hc) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleInternalIndex p hp i))
          (walkCycleEmbedding p hp (cycleInternalSuccIndex p hp i))) ⊔
        pathCoverTwoEdgePath
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleInternalSuccIndex p hp i))
          ((walkCycleEmbedding p hp).injective.ne
            (cycleAnchor_ne_internalSucc p hp i))
          (firstCyclePathSlot m c hc) := by
  unfold cycleChainC5
  apply augmentedEdgeC5_map_eq

lemma cycleChainC5_map_eq_slots
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    (SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i) =
      (cycleSecondSlotPath m c hc p hp
          (cycleInternalSpoke p hp i) ⊔
        pathCoverRootEdgeGraph
          (walkCycleEmbedding p hp (cycleInternalIndex p hp i))
          (walkCycleEmbedding p hp (cycleInternalSuccIndex p hp i))) ⊔
        cycleFirstSlotPath m c hc p hp
          (cycleInternalSuccSpoke p hp i) := by
  rw [cycleChainC5_map_eq]
  rfl

lemma cycleGraph_adj_internal_succ
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    (SimpleGraph.cycleGraph p.length).Adj
      (cycleInternalIndex p hp i) (cycleInternalSuccIndex p hp i) := by
  apply SimpleGraph.pathGraph_le_cycleGraph
  rw [SimpleGraph.pathGraph_adj]
  left
  rfl

lemma walkCycleGraph_map_eq_spanningCoe
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph p.length).map (walkCycleEmbedding p hp) =
      p.toSubgraph.spanningCoe := by
  ext a b
  rw [SimpleGraph.map_adj]
  simp only [SimpleGraph.Subgraph.spanningCoe_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    rw [cycleGraph_eq_wrap_sup_linearEdges p.length hp.three_le_length] at hxy
    rcases hxy with hwrap | hlinear
    · simp only [cycleWrapEdge, SimpleGraph.edge_adj] at hwrap
      rcases hwrap.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        rw [walkCycleEmbedding_eq_getVert_succ,
          walkCycleEmbedding_eq_getVert_succ]
        rw [show p.length - 1 + 1 = p.length by omega,
          p.getVert_length]
        change p.toSubgraph.Adj v (p.getVert 1)
        simpa using p.toSubgraph_adj_getVert (i := 0) (by
          have := hp.three_le_length
          omega)
      · rcases h with ⟨rfl, rfl⟩
        rw [walkCycleEmbedding_eq_getVert_succ,
          walkCycleEmbedding_eq_getVert_succ]
        rw [show p.length - 1 + 1 = p.length by omega,
          p.getVert_length]
        change p.toSubgraph.Adj (p.getVert 1) v
        simpa [p.getVert_zero] using (p.toSubgraph_adj_getVert (i := 0) (by
          have := hp.three_le_length
          omega)).symm
    · obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hlinear
      simp only [cycleLinearEdge, SimpleGraph.edge_adj] at hi
      rcases hi.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa [walkCycleEmbedding_eq_getVert_succ] using
          p.toSubgraph_adj_getVert (i := i.1 + 1) (by omega)
      · rcases h with ⟨rfl, rfl⟩
        exact (by
          simpa [walkCycleEmbedding_eq_getVert_succ] using
            p.toSubgraph_adj_getVert (i := i.1 + 1) (by omega) :
              p.toSubgraph.Adj
                (walkCycleEmbedding p hp
                  (⟨i.1, by omega⟩ : Fin p.length))
                (walkCycleEmbedding p hp
                  (⟨i.1 + 1, by omega⟩ : Fin p.length))).symm
  · intro hab
    rw [p.toSubgraph_adj_iff] at hab
    obtain ⟨i, hedge, hi⟩ := hab
    by_cases hi0 : i = 0
    · subst i
      have hadj : ((SimpleGraph.cycleGraph p.length).map
          (walkCycleEmbedding p hp)).Adj
          (walkCycleEmbedding p hp (cycleAnchorIndex p hp))
          (walkCycleEmbedding p hp (cycleFirstInternalIndex p hp)) :=
        SimpleGraph.map_adj_apply.mpr (cycleGraph_adj_anchor_first p hp)
      have habmap := (((SimpleGraph.cycleGraph p.length).map
        (walkCycleEmbedding p hp)).adj_congr_of_sym2 (by
          simpa [walkCycleEmbedding_eq_getVert_succ, cycleAnchorIndex,
            cycleFirstInternalIndex,
            show p.length - 1 + 1 = p.length by omega,
            p.getVert_length, p.getVert_zero] using hedge)).mp hadj
      exact (SimpleGraph.map_adj (walkCycleEmbedding p hp)
        (SimpleGraph.cycleGraph p.length) a b).mp habmap
    · let j : Fin (p.length - 1) := ⟨i - 1, by omega⟩
      let x : Fin p.length := ⟨j.1, by omega⟩
      let y : Fin p.length := ⟨j.1 + 1, by omega⟩
      have hxy : (SimpleGraph.cycleGraph p.length).Adj x y := by
        apply SimpleGraph.pathGraph_le_cycleGraph
        rw [SimpleGraph.pathGraph_adj]
        left
        rfl
      have hadj : ((SimpleGraph.cycleGraph p.length).map
          (walkCycleEmbedding p hp)).Adj
          (walkCycleEmbedding p hp x) (walkCycleEmbedding p hp y) :=
        SimpleGraph.map_adj_apply.mpr hxy
      have habmap : ((SimpleGraph.cycleGraph p.length).map
          (walkCycleEmbedding p hp)).Adj a b := by
        apply (((SimpleGraph.cycleGraph p.length).map
          (walkCycleEmbedding p hp)).adj_congr_of_sym2 (w := a) (x := b) ?_).mp hadj
        simp only [walkCycleEmbedding_eq_getVert_succ, x, y, j]
        rw [show i - 1 + 1 = i by omega]
        exact hedge
      exact (SimpleGraph.map_adj (walkCycleEmbedding p hp)
        (SimpleGraph.cycleGraph p.length) a b).mp habmap

lemma cycleChainC5_map_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    (SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i) ≤
      pathCoverGraph V (6 * m ^ 2) ⊔
        G.map (pathCoverRootEmbedding (X := V) (k := 6 * m ^ 2)) := by
  unfold cycleChainC5
  apply augmentedEdgeC5_map_le G
  exact walkCycleEmbedding_adj p hp (cycleGraph_adj_internal_succ p hp i)

/-! ## Exact root-edge coverage of one augmented cycle -/

def walkCyclePathRootEmbedding
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V} {k : ℕ}
    (p : G.Walk v v) (hp : p.IsCycle) :
    Fin p.length ↪ PathCoverVertex V k :=
  (walkCycleEmbedding p hp).trans
    (pathCoverRootEmbedding (X := V) (k := k))

def cycleShortRootGraph
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V} {k : ℕ}
    (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph (PathCoverVertex V k) :=
  let f := walkCycleEmbedding p hp
  pathCoverRootEdgeGraph (f (cycleAnchorIndex p hp))
      (f (cycleFirstInternalIndex p hp)) ⊔
    (pathCoverRootEdgeGraph (f (cycleAnchorIndex p hp))
        (f (cycleLastInternalIndex p hp)) ⊔
      ⨆ i : Fin (p.length - 2),
        pathCoverRootEdgeGraph (f (cycleInternalIndex p hp i))
          (f (cycleInternalSuccIndex p hp i)))

lemma cycleShortRootGraph_eq_map_cycle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V} {k : ℕ}
    (p : G.Walk v v) (hp : p.IsCycle) :
    cycleShortRootGraph (k := k) p hp =
      (SimpleGraph.cycleGraph p.length).map
        (walkCyclePathRootEmbedding (k := k) p hp) := by
  ext u w
  rw [SimpleGraph.map_adj]
  constructor
  · intro huw
    simp only [cycleShortRootGraph, SimpleGraph.sup_adj,
      SimpleGraph.iSup_adj, pathCoverRootEdgeGraph,
      SimpleGraph.edge_adj] at huw
    rcases huw with hfirst | hlast | ⟨i, hi⟩
    · rcases hfirst.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleAnchorIndex p hp, cycleFirstInternalIndex p hp,
          cycleGraph_adj_anchor_first p hp, rfl, rfl⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleFirstInternalIndex p hp, cycleAnchorIndex p hp,
          (cycleGraph_adj_anchor_first p hp).symm, rfl, rfl⟩
    · rcases hlast.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleAnchorIndex p hp, cycleLastInternalIndex p hp,
          cycleGraph_adj_anchor_lastInternal p hp, rfl, rfl⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleLastInternalIndex p hp, cycleAnchorIndex p hp,
          (cycleGraph_adj_anchor_lastInternal p hp).symm, rfl, rfl⟩
    · rcases hi.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleInternalIndex p hp i,
          cycleInternalSuccIndex p hp i,
          cycleGraph_adj_internal_succ p hp i, rfl, rfl⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨cycleInternalSuccIndex p hp i,
          cycleInternalIndex p hp i,
          (cycleGraph_adj_internal_succ p hp i).symm, rfl, rfl⟩
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    simp only [cycleShortRootGraph, SimpleGraph.sup_adj,
      SimpleGraph.iSup_adj]
    rw [cycleGraph_eq_wrap_sup_linearEdges p.length hp.three_le_length] at hxy
    rcases hxy with hwrap | hlinear
    · left
      simp only [cycleWrapEdge, SimpleGraph.edge_adj] at hwrap
      simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
      rcases hwrap.1 with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inl ⟨rfl, rfl⟩,
          (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (cycleAnchor_ne_first p hp)⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inr ⟨rfl, rfl⟩,
          (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (cycleAnchor_ne_first p hp).symm⟩
    · obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hlinear
      simp only [cycleLinearEdge, SimpleGraph.edge_adj] at hi
      rcases hi.1 with h | h
      all_goals rcases h with ⟨rfl, rfl⟩
      all_goals by_cases hilast : i.1 = p.length - 2
      · right; left
        simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
        refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
        · apply congrArg PathCoverVertex.root
          apply congrArg (walkCycleEmbedding p hp)
          apply Fin.ext
          simpa [cycleLastInternalIndex] using hilast
        · apply congrArg PathCoverVertex.root
          apply congrArg (walkCycleEmbedding p hp)
          apply Fin.ext
          simp only [cycleAnchorIndex]
          omega
        · exact (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (by intro h; have := congrArg Fin.val h; omega)
      · right; right
        let j : Fin (p.length - 2) := ⟨i.1, by omega⟩
        refine ⟨j, ?_⟩
        simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
        refine ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
        · rfl
        · rfl
        · exact (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (by intro h; have := congrArg Fin.val h; omega)
      · right; left
        simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
        refine ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
        · apply congrArg PathCoverVertex.root
          apply congrArg (walkCycleEmbedding p hp)
          apply Fin.ext
          simp only [cycleAnchorIndex]
          omega
        · apply congrArg PathCoverVertex.root
          apply congrArg (walkCycleEmbedding p hp)
          apply Fin.ext
          simpa [cycleLastInternalIndex] using hilast
        · exact (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (by intro h; have := congrArg Fin.val h; omega)
      · right; right
        let j : Fin (p.length - 2) := ⟨i.1, by omega⟩
        refine ⟨j, ?_⟩
        simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
        refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
        · rfl
        · rfl
        · exact (walkCyclePathRootEmbedding (k := k) p hp).injective.ne
            (by intro h; have := congrArg Fin.val h; omega)

def cycleShortPieceGraph
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  (SimpleGraph.cycleGraph 3).map
      (firstCycleEndpointTriangle m c hc p hp) ⊔
    ((SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp) ⊔
      ⨆ i : Fin (p.length - 2),
        (SimpleGraph.cycleGraph 5).map
          (cycleChainC5 m c hc p hp i))

def cycleUsedSlotGraph
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  (⨆ i : Fin (p.length - 1), cycleFirstSlotPath m c hc p hp i) ⊔
    ⨆ i : Fin (p.length - 1), cycleSecondSlotPath m c hc p hp i

lemma cycleShortPieceGraph_eq_root_sup_usedSlots
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    cycleShortPieceGraph m c hc p hp =
      cycleShortRootGraph p hp ⊔ cycleUsedSlotGraph m c hc p hp := by
  unfold cycleShortPieceGraph cycleUsedSlotGraph
  rw [firstCycleEndpointTriangle_map_eq_slot,
    lastCycleEndpointTriangle_map_eq_slot]
  simp_rw [cycleChainC5_map_eq_slots]
  rw [iSup_fin_pred_eq_first_sup_succ p.length hp.three_le_length
      (cycleFirstSlotPath m c hc p hp),
    iSup_fin_pred_eq_last_sup_init p.length hp.three_le_length
      (cycleSecondSlotPath m c hc p hp)]
  unfold cycleShortRootGraph
  rw [iSup_sup_eq, iSup_sup_eq]
  simp only [cycleFirstSpoke, cycleLastSpoke, cycleInternalSpoke,
    cycleInternalSuccSpoke]
  ac_rfl

lemma cycleUsedSlotGraph_sup_residual_eq_slotGraphs
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    cycleUsedSlotGraph m c hc p hp ⊔ cycleResidualGraph m c hc p hp =
      pathCoverSlotGraph (firstCyclePathSlot m c hc) ⊔
        pathCoverSlotGraph (secondCyclePathSlot m c hc) := by
  unfold cycleUsedSlotGraph cycleResidualGraph pathCoverSlotGraph
  simp_rw [cycleFirstSlotPath_eq_pathCoverPathAtEdge,
    cycleSecondSlotPath_eq_pathCoverPathAtEdge,
    cycleResidualC4_map_eq_paths]
  rw [iSup_sup_eq,
    iSup_completeEdges_eq_spokes_sup_residual p hp
      (fun e ↦ pathCoverPathAtEdge e (firstCyclePathSlot m c hc)),
    iSup_completeEdges_eq_spokes_sup_residual p hp
      (fun e ↦ pathCoverPathAtEdge e (secondCyclePathSlot m c hc))]
  ac_rfl

def cycleAugmentedPieceGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  cycleShortPieceGraph m c hc p hp ⊔ cycleResidualGraph m c hc p hp

lemma cycleAugmentedPieceGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    cycleAugmentedPieceGraph m c hc p hp =
      (SimpleGraph.cycleGraph p.length).map
          (walkCyclePathRootEmbedding p hp) ⊔
        (pathCoverSlotGraph (firstCyclePathSlot m c hc) ⊔
          pathCoverSlotGraph (secondCyclePathSlot m c hc)) := by
  unfold cycleAugmentedPieceGraph
  rw [cycleShortPieceGraph_eq_root_sup_usedSlots,
    cycleShortRootGraph_eq_map_cycle,
    sup_assoc, cycleUsedSlotGraph_sup_residual_eq_slotGraphs]

lemma cycleEndpointTriangles_disjoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp))
      ((SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp)) := by
  unfold firstCycleEndpointTriangle lastCycleEndpointTriangle
  apply pathTriangle_disjoint_pathTriangle_of_parts_disjoint
  · apply pathTriangleMiddles_disjoint_of_ne
    apply pathCoverMiddleBetween_ne_of_slot_ne
    exact firstCyclePathSlot_ne_second m c hc
  · apply pathCoverRootEdgeGraph_disjoint_of_edge_ne
    apply sym2_apply_ne_of_injective
      (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
    exact cycleAnchorFirst_edge_ne_anchorLast p hp

lemma firstCycleEndpointTriangle_disjoint_cycleChainC5
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp))
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i)) := by
  unfold firstCycleEndpointTriangle cycleChainC5
  apply pathTriangle_disjoint_augmentedEdgeC5_of_parts_disjoint
  · apply pathTriangleMiddles_disjoint_augmentedEdgeC5Middles_of_ne
    · apply pathCoverMiddleBetween_ne_of_slot_ne
      exact firstCyclePathSlot_ne_second m c hc
    · apply pathCoverMiddleBetween_ne_of_edge_ne
      apply pathCoverEdge_ne_of_sym2_ne
      apply sym2_apply_ne_of_injective
        (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
      exact cycleAnchorFirst_spoke_ne_internalSucc p hp i
  · apply pathCoverRootEdgeGraph_disjoint_of_edge_ne
    apply sym2_apply_ne_of_injective
      (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
    exact cycleAnchorFirst_edge_ne_internal p hp i

lemma lastCycleEndpointTriangle_disjoint_cycleChainC5
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (i : Fin (p.length - 2)) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp))
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i)) := by
  unfold lastCycleEndpointTriangle cycleChainC5
  apply pathTriangle_disjoint_augmentedEdgeC5_of_parts_disjoint
  · apply pathTriangleMiddles_disjoint_augmentedEdgeC5Middles_of_ne
    · apply pathCoverMiddleBetween_ne_of_edge_ne
      apply pathCoverEdge_ne_of_sym2_ne
      apply sym2_apply_ne_of_injective
        (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
      exact cycleAnchorLast_spoke_ne_internal p hp i
    · apply pathCoverMiddleBetween_ne_of_slot_ne
      exact (firstCyclePathSlot_ne_second m c hc).symm
  · apply pathCoverRootEdgeGraph_disjoint_of_edge_ne
    apply sym2_apply_ne_of_injective
      (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
    exact cycleAnchorLast_edge_ne_internal p hp i

lemma cycleChainC5_pairwise_disjoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    {i j : Fin (p.length - 2)} (hij : i ≠ j) :
    Disjoint
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i))
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp j)) := by
  unfold cycleChainC5
  apply augmentedEdgeC5_disjoint_augmentedEdgeC5_of_parts_disjoint
  · apply augmentedEdgeC5Middles_disjoint_of_ne
    · apply pathCoverMiddleBetween_ne_of_edge_ne
      apply pathCoverEdge_ne_of_sym2_ne
      apply sym2_apply_ne_of_injective
        (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
      exact cycleAnchorInternal_spokes_ne p hp hij
    · apply pathCoverMiddleBetween_ne_of_slot_ne
      exact (firstCyclePathSlot_ne_second m c hc).symm
    · apply pathCoverMiddleBetween_ne_of_slot_ne
      exact firstCyclePathSlot_ne_second m c hc
    · apply pathCoverMiddleBetween_ne_of_edge_ne
      apply pathCoverEdge_ne_of_sym2_ne
      apply sym2_apply_ne_of_injective
        (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
      exact cycleAnchorInternalSucc_spokes_ne p hp hij
  · apply pathCoverRootEdgeGraph_disjoint_of_edge_ne
    apply sym2_apply_ne_of_injective
      (walkCycleEmbedding p hp) (walkCycleEmbedding_injective p hp)
    exact cycleInternal_edges_ne p hp hij

lemma cycleResidualC4_disjoint_firstCycleEndpointTriangle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e))
      ((SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp)) := by
  unfold cycleResidualC4 firstCycleEndpointTriangle
  apply pairedPathC4_disjoint_pathTriangle_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_pathTriangleMiddles_of_ne
  all_goals
    apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleFirstSpoke p hp)

lemma cycleResidualC4_disjoint_lastCycleEndpointTriangle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e))
      ((SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp)) := by
  unfold cycleResidualC4 lastCycleEndpointTriangle
  apply pairedPathC4_disjoint_pathTriangle_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_pathTriangleMiddles_of_ne
  all_goals
    apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleLastSpoke p hp)

lemma cycleResidualC4_disjoint_cycleChainC5
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    (e : CycleResidualEdge p hp) (i : Fin (p.length - 2)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e))
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i)) := by
  unfold cycleResidualC4 cycleChainC5
  apply pairedPathC4_disjoint_augmentedEdgeC5_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_augmentedEdgeC5Middles_of_ne
  · apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleInternalSpoke p hp i)
  · apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleInternalSuccSpoke p hp i)
  · apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleInternalSpoke p hp i)
  · apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa [cycleSpokeEdge] using
      cycleResidual_pathCoverEdge_ne_spoke e (cycleInternalSuccSpoke p hp i)

lemma cycleResidualC4_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m c : ℕ) (hc : c < m ^ 2) (p : G.Walk v v) (hp : p.IsCycle)
    {e f : CycleResidualEdge p hp} (hef : e ≠ f) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e))
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp f)) := by
  have hef' : e.1 ≠ f.1 := by
    intro h
    exact hef (Subtype.ext h)
  unfold cycleResidualC4
  apply pairedPathC4_disjoint_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_of_ne
  all_goals
    apply pathCoverMiddleBetween_ne_of_edge_ne
    simpa only [pathCoverEdge_out_eq] using hef'

lemma cycleResidualC4_disjoint_of_cycle_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} {v w : V}
    (m : ℕ) {c d : Fin (m ^ 2)} (hcd : c ≠ d)
    (p : G.Walk v v) (hp : p.IsCycle) (q : K.Walk w w) (hq : q.IsCycle)
    (e : CycleResidualEdge p hp) (f : CycleResidualEdge q hq) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (cycleResidualC4 m c.1 c.2 p hp e))
      ((SimpleGraph.cycleGraph 4).map
        (cycleResidualC4 m d.1 d.2 q hq f)) := by
  have hsep := cyclePathSlots_ne m hcd
  unfold cycleResidualC4
  apply pairedPathC4_disjoint_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_of_ne
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.2.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.2.2

lemma cycleResidualC4_disjoint_unusedPathC4
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m r c : ℕ) (hr : r ≤ m ^ 2) (hcr : c < r) (hc : c < m ^ 2)
    (p : G.Walk v v) (hp : p.IsCycle) (e : CycleResidualEdge p hp)
    (f : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (cycleResidualC4 m c hc p hp e))
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr f t)) := by
  have hsep := usedCycleSlot_lt_unused m r c hr hcr hc t
  unfold cycleResidualC4 unusedPathC4
  apply pairedPathC4_disjoint_of_middles_disjoint
  apply pairedPathC4Middles_disjoint_of_ne
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.2.1
  · apply pathCoverMiddleBetween_ne_of_slot_ne
    exact hsep.2.2.2

/-! ## Separation of used and unused path-cover pieces -/

lemma unusedPathC4_disjoint_firstCycleEndpointTriangle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m r c : ℕ) (hr : r ≤ m ^ 2) (hcr : c < r) (hc : c < m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r))
    (p : G.Walk v v) (hp : p.IsCycle) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t))
      ((SimpleGraph.cycleGraph 3).map
        (firstCycleEndpointTriangle m c hc p hp)) := by
  unfold unusedPathC4 firstCycleEndpointTriangle
  apply pairedPathC4_disjoint_pathTriangle_of_middles_disjoint
  have hsep := usedCycleSlot_lt_unused m r c hr hcr hc t
  apply pairedPathC4Middles_disjoint_pathTriangleMiddles_of_slot_ne
  · exact hsep.1
  · exact hsep.2.1

lemma unusedPathC4_disjoint_lastCycleEndpointTriangle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m r c : ℕ) (hr : r ≤ m ^ 2) (hcr : c < r) (hc : c < m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r))
    (p : G.Walk v v) (hp : p.IsCycle) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t))
      ((SimpleGraph.cycleGraph 3).map
        (lastCycleEndpointTriangle m c hc p hp)) := by
  unfold unusedPathC4 lastCycleEndpointTriangle
  apply pairedPathC4_disjoint_pathTriangle_of_middles_disjoint
  have hsep := usedCycleSlot_lt_unused m r c hr hcr hc t
  apply pairedPathC4Middles_disjoint_pathTriangleMiddles_of_slot_ne
  · exact hsep.2.2.1
  · exact hsep.2.2.2

lemma unusedPathC4_disjoint_cycleChainC5
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (m r c : ℕ) (hr : r ≤ m ^ 2) (hcr : c < r) (hc : c < m ^ 2)
    (e : (SimpleGraph.completeGraph V).edgeSet)
    (t : Fin (unusedPathPairCount m r))
    (p : G.Walk v v) (hp : p.IsCycle) (i : Fin (p.length - 2)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map (unusedPathC4 m r hr e t))
      ((SimpleGraph.cycleGraph 5).map (cycleChainC5 m c hc p hp i)) := by
  unfold unusedPathC4 cycleChainC5
  apply pairedPathC4_disjoint_augmentedEdgeC5_of_middles_disjoint
  have hsep := usedCycleSlot_lt_unused m r c hr hcr hc t
  apply pairedPathC4Middles_disjoint_augmentedEdgeC5Middles_of_slot_ne
  · exact hsep.2.2.1
  · exact hsep.2.2.2
  · exact hsep.1
  · exact hsep.2.1

end

end Erdos207
