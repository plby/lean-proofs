/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.AlternatingTraceOps
import ErdosProblems.Erdos599.RelationComponents

/-!
# Surviving fragments of a ladder ray

This file constructs the unique maximal component, after deleting
`GroundingCut.CE`, of a ladder ray which contains a prescribed vertex.
The component is a finite ray segment when there is a first deleted edge to
its right, and is a ray tail otherwise.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingRayFragment

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The edge of a ray beginning at index `n`. -/
def rayEdge (r : Ray Gamma.graph) (n : ℕ) : V × V :=
  (r n, r (n + 1))

theorem rayEdge_mem (r : Ray Gamma.graph) (n : ℕ) :
    rayEdge r n ∈ r.edgeSet :=
  ⟨n, rfl⟩

/-- The first `n` edges of a ray beginning at index `i`. -/
def raySegmentWalk (r : Ray Gamma.graph) (i : ℕ) :
    (n : ℕ) → Walk Gamma.graph (r i) (r (i + n))
  | 0 => .nil
  | n + 1 =>
      (raySegmentWalk r i n).concat (by
        simpa [Nat.add_assoc] using r.adj_succ (i + n))

@[simp] theorem raySegmentWalk_support
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentWalk r i n).support =
      List.ofFn (fun k : Fin (n + 1) ↦ r (i + k)) := by
  induction n with
  | zero => simp [raySegmentWalk]
  | succ n ih =>
      rw [raySegmentWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun k : Fin ((n + 1) + 1) ↦ r (i + k))]
      congr 1 <;> simp [Nat.add_assoc]

theorem raySegmentWalk_isPath
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentWalk r i n).IsPath := by
  rw [Walk.isPath_iff, raySegmentWalk_support]
  exact List.nodup_ofFn.mpr fun j k hjk ↦ by
    apply Fin.ext
    exact Nat.add_left_cancel (r.injective hjk)

/-- The finite path consisting of `n` consecutive ray edges from index `i`. -/
def raySegmentPath (r : Ray Gamma.graph) (i n : ℕ) :
    FinitePath Gamma.graph where
  start := r i
  finish := r (i + n)
  walk := raySegmentWalk r i n
  isPath := raySegmentWalk_isPath r i n

/-- Every intermediate ray edge occurs in a finite walk whose endpoints are
displayed ray vertices and all of whose edges belong to the ray. -/
theorem rayEdge_mem_walk_of_between
    (r : Ray Gamma.graph) {a b : V} (w : Walk Gamma.graph a b)
    (hedge : w.edgeSet ⊆ r.edgeSet) {i j t : ℕ}
    (ha : r i = a) (hb : r j = b) (hit : i ≤ t) (htj : t < j) :
    rayEdge r t ∈ w.edgeSet := by
  induction w generalizing i t with
  | nil =>
      have hij : i = j := r.injective (ha.trans hb.symm)
      omega
  | @cons a c b hac tail ih =>
      have hacRay : (a, c) ∈ r.edgeSet := hedge (by simp)
      rcases hacRay with ⟨n, hn⟩
      have hin : i = n := r.injective (ha.trans (congrArg Prod.fst hn))
      have hnc : r (n + 1) = c := (congrArg Prod.snd hn).symm
      have htail : tail.edgeSet ⊆ r.edgeSet := by
        intro e he
        exact hedge (Set.mem_union_right _ he)
      by_cases hti : t = i
      · subst t
        apply Set.mem_union_left
        rw [Set.mem_singleton_iff]
        apply Prod.ext
        · exact ha
        · change r (i + 1) = c
          rw [hin]
          exact hnc
      · apply Set.mem_union_right
        apply ih htail (i := i + 1) (t := t)
        · simpa [hin, Nat.add_comm] using hnc
        · exact hb
        · omega
        · exact htj

/-- Exact edge set of a finite ray segment. -/
theorem raySegmentPath_edgeSet_eq
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentPath r i n).edgeSet =
      {e | ∃ t, t < n ∧ e = rayEdge r (i + t)} := by
  induction n with
  | zero =>
      simp [raySegmentPath, raySegmentWalk, FinitePath.edgeSet]
  | succ n ih =>
      change (raySegmentWalk r i (n + 1)).edgeSet = _
      rw [raySegmentWalk,
        Alternating.RelationComponents.walkEdgeSetConcatRC]
      have ih' :
          (raySegmentWalk r i n).edgeSet =
            {e | ∃ t, t < n ∧ e = rayEdge r (i + t)} := by
        simpa [raySegmentPath, FinitePath.edgeSet] using ih
      rw [ih']
      ext e
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨t, ht, rfl⟩ | rfl)
        · exact ⟨t, by omega, rfl⟩
        · refine ⟨n, by omega, ?_⟩
          simp [rayEdge, Nat.add_assoc]
      · rintro ⟨t, ht, rfl⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with htn | rfl
        · exact Or.inl ⟨t, htn, rfl⟩
        · right
          simp [rayEdge, Nat.add_assoc]

/-- Exact support of a finite ray segment. -/
theorem mem_raySegmentPath_support_iff
    (r : Ray Gamma.graph) (i n : ℕ) (y : V) :
    y ∈ (raySegmentPath r i n).support ↔
      ∃ t, t ≤ n ∧ y = r (i + t) := by
  change y ∈ (raySegmentWalk r i n).support ↔ _
  rw [raySegmentWalk_support, List.mem_ofFn]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.1, by omega, ht.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, by omega⟩, rfl⟩

/-- A ray segment avoids the deleted edges when every ray edge in its index
interval does. -/
theorem raySegmentPath_disjoint
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph)
    (i n : ℕ)
    (hkeep : ∀ t, t < n →
      rayEdge r (i + t) ∉ GroundingCut.CE L C) :
    Disjoint (raySegmentPath r i n).edgeSet
      (GroundingCut.CE L C) := by
  rw [Set.disjoint_left]
  intro e he hCE
  rw [raySegmentPath_edgeSet_eq] at he
  rcases he with ⟨t, ht, rfl⟩
  exact hkeep t ht hCE

theorem rayTail_edgeSet_subset (r : Ray Gamma.graph) (i : ℕ) :
    (r.tail i).edgeSet ⊆ r.edgeSet := by
  rintro e ⟨n, rfl⟩
  refine ⟨i + n, ?_⟩
  simp [rayEdge, Nat.add_assoc]

theorem rayTail_disjoint
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph)
    (i : ℕ) (hkeep : ∀ t, i ≤ t →
      rayEdge r t ∉ GroundingCut.CE L C) :
    Disjoint (r.tail i).edgeSet
      (GroundingCut.CE L C) := by
  rw [Set.disjoint_left]
  rintro e ⟨n, rfl⟩ hCE
  exact hkeep (i + n) (by omega) (by simpa [rayEdge, Nat.add_assoc] using hCE)

/-- An index begins a surviving interval reaching the prescribed index `k`. -/
def LeftCandidate (L : Input Gamma I) (C : Set (LV L))
    (r : Ray Gamma.graph) (k i : ℕ) : Prop :=
  i ≤ k ∧ ∀ t, i ≤ t → t < k →
    rayEdge r t ∉ GroundingCut.CE L C

theorem exists_leftCandidate
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph) (k : ℕ) :
    ∃ i, LeftCandidate L C r k i := by
  refine ⟨k, le_rfl, ?_⟩
  intro t hkt htk
  omega

/-- The left endpoint of the deleted-edge component containing `r k`. -/
def rayLeftIndex (L : Input Gamma I) (C : Set (LV L))
    (r : Ray Gamma.graph) (k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_leftCandidate L C r k)

theorem rayLeftIndex_spec
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph) (k : ℕ) :
    LeftCandidate L C r k (rayLeftIndex L C r k) :=
  by
    classical
    exact Nat.find_spec (exists_leftCandidate L C r k)

theorem rayLeftIndex_min
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph) (k : ℕ)
    {i : ℕ} (hi : LeftCandidate L C r k i) :
    rayLeftIndex L C r k ≤ i :=
  by
    classical
    exact Nat.find_min' (exists_leftCandidate L C r k) hi

/-- A surviving walk which runs into the canonical left endpoint cannot
start strictly before that endpoint. -/
theorem rayLeftIndex_le_of_walk_to_left
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph) (k : ℕ)
    {j : ℕ} {a b : V} (q : Walk Gamma.graph a b)
    (hqEdge : q.edgeSet ⊆ r.edgeSet)
    (hqDisjoint : Disjoint q.edgeSet
      (GroundingCut.CE L C))
    (hstart : r j = a)
    (hfinish : r (rayLeftIndex L C r k) = b) :
    rayLeftIndex L C r k ≤ j := by
  let i := rayLeftIndex L C r k
  have hiSpec := rayLeftIndex_spec L C r k
  have hji : j ≤ i := by
    apply Walk.position_mono_in_ray r q hqEdge j i hstart
    exact hfinish
  apply rayLeftIndex_min L C r k
  refine ⟨hji.trans hiSpec.1, ?_⟩
  intro t hjt htk
  by_cases hti : t < i
  · have htq : rayEdge r t ∈ q.edgeSet := by
      apply rayEdge_mem_walk_of_between r q hqEdge hstart hfinish hjt hti
    exact fun htCE ↦ Set.disjoint_left.1 hqDisjoint htq htCE
  · exact hiSpec.2 t (by omega) htk

/-- The finite candidate component with vertex indices from `i` through
`n`, inclusive. -/
def finiteRayFragment
    (L : Input Gamma I) (r : Ray Gamma.graph)
    (hr : (Sum.inr r : Gamma.DPath) ∈ L.ladder.paths)
    (i n : ℕ) : L.Fragment where
  path := .inl (raySegmentPath r i (n - i))
  parent := .inr r
  parent_mem := hr
  support_subset := by
    intro y hy
    change y ∈ (raySegmentPath r i (n - i)).support at hy
    change y ∈ r.support
    rw [mem_raySegmentPath_support_iff] at hy
    rcases hy with ⟨t, _, hyt⟩
    exact ⟨i + t, hyt.symm⟩
  edges_subset := by
    intro e he
    change e ∈ (raySegmentPath r i (n - i)).edgeSet at he
    change e ∈ r.edgeSet
    rw [raySegmentPath_edgeSet_eq] at he
    rcases he with ⟨t, _, rfl⟩
    exact rayEdge_mem r (i + t)

/-- The infinite candidate component beginning at ray index `i`. -/
def tailRayFragment
    (L : Input Gamma I) (r : Ray Gamma.graph)
    (hr : (Sum.inr r : Gamma.DPath) ∈ L.ladder.paths)
    (i : ℕ) : L.Fragment where
  path := .inr (r.tail i)
  parent := .inr r
  parent_mem := hr
  support_subset := r.support_tail_subset i
  edges_subset := rayTail_edgeSet_subset r i

/-- If `n` is the first deleted edge weakly to the right of `k`, the finite
segment from the canonical left endpoint through `r n` is the whole surviving
component.  The hypotheses expose exactly the two interval facts used by the
construction. -/
theorem finiteRayFragment_mem_fragments
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph)
    (hr : (Sum.inr r : Gamma.DPath) ∈ L.ladder.paths)
    (k n : ℕ) (hkn : k ≤ n)
    (hkeep : ∀ t, rayLeftIndex L C r k ≤ t → t < n →
      rayEdge r t ∉ GroundingCut.CE L C)
    (hright : rayEdge r n ∈ GroundingCut.CE L C) :
    finiteRayFragment L r hr (rayLeftIndex L C r k) n ∈
      GroundingCut.fragments L C := by
  let i := rayLeftIndex L C r k
  have hik : i ≤ k := (rayLeftIndex_spec L C r k).1
  have hin : i ≤ n := hik.trans hkn
  constructor
  · change Disjoint (raySegmentPath r i (n - i)).edgeSet
      (GroundingCut.CE L C)
    apply raySegmentPath_disjoint L C r i (n - i)
    intro t ht
    apply hkeep (i + t)
    · simpa [i]
    · omega
  · change (raySegmentPath r i (n - i)).support =
      {y | y ∈ r.support ∧
        GroundingCut.SurvivingConnected L C (.inr r) (r i) y}
    ext y
    constructor
    · intro hy
      rw [mem_raySegmentPath_support_iff] at hy
      rcases hy with ⟨t, ht, hyt⟩
      have hitn : i + t ≤ n := by omega
      refine ⟨⟨i + t, hyt.symm⟩, ?_⟩
      let q := raySegmentPath r i t
      refine ⟨q, Or.inl ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
      · exact hyt.symm
      · intro z hz
        change z ∈ (raySegmentPath r i t).support at hz
        rw [mem_raySegmentPath_support_iff] at hz
        rcases hz with ⟨s, _, hzs⟩
        exact ⟨i + s, hzs.symm⟩
      · change (raySegmentPath r i t).edgeSet ⊆ r.edgeSet
        intro e he
        rw [raySegmentPath_edgeSet_eq] at he
        rcases he with ⟨s, _, rfl⟩
        exact rayEdge_mem r (i + s)
      · apply raySegmentPath_disjoint L C r i t
        intro s hs
        apply hkeep (i + s)
        · simpa [i]
        · omega
    · rintro ⟨⟨j, hjy⟩, q, hend, _, hqEdge, hqDisjoint⟩
      change q.edgeSet ⊆ r.edgeSet at hqEdge
      rw [mem_raySegmentPath_support_iff]
      rcases hend with hforward | hbackward
      · change q.start = r i ∧ q.finish = y at hforward
        have hstart : r i = q.start := hforward.1.symm
        have hfinish : r j = q.finish := hjy.trans hforward.2.symm
        have hij : i ≤ j :=
          Walk.position_mono_in_ray r q.walk hqEdge i j hstart hfinish
        have hjn : j ≤ n := by
          by_contra hnot
          have hnj : n < j := by omega
          have hnq : rayEdge r n ∈ q.edgeSet :=
            rayEdge_mem_walk_of_between r q.walk hqEdge hstart hfinish hin hnj
          exact Set.disjoint_left.1 hqDisjoint hnq hright
        refine ⟨j - i, by omega, ?_⟩
        calc
          y = r j := hjy.symm
          _ = r (i + (j - i)) := by congr 1 <;> omega
      · change q.start = y ∧ q.finish = r i at hbackward
        have hstart : r j = q.start := hjy.trans hbackward.1.symm
        have hfinish : r i = q.finish := hbackward.2.symm
        have hji : j ≤ i :=
          Walk.position_mono_in_ray r q.walk hqEdge j i hstart hfinish
        have hij : i ≤ j := by
          simpa [i] using
            rayLeftIndex_le_of_walk_to_left L C r k q.walk hqEdge
              hqDisjoint hstart (by simpa [i] using hfinish)
        have hjiEq : j = i := Nat.le_antisymm hji hij
        refine ⟨0, by omega, ?_⟩
        simpa [hjiEq] using hjy.symm

/-- If no deleted edge occurs to the right of the canonical left endpoint,
the corresponding ray tail is the whole surviving component. -/
theorem tailRayFragment_mem_fragments
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph)
    (hr : (Sum.inr r : Gamma.DPath) ∈ L.ladder.paths)
    (k : ℕ)
    (hkeep : ∀ t, rayLeftIndex L C r k ≤ t →
      rayEdge r t ∉ GroundingCut.CE L C) :
    tailRayFragment L r hr (rayLeftIndex L C r k) ∈
      GroundingCut.fragments L C := by
  let i := rayLeftIndex L C r k
  constructor
  · change Disjoint (r.tail i).edgeSet
      (GroundingCut.CE L C)
    apply rayTail_disjoint L C r i
    intro t hit
    exact hkeep t (by simpa [i] using hit)
  · change (r.tail i).support =
      {y | y ∈ r.support ∧
        GroundingCut.SurvivingConnected L C (.inr r) (r i) y}
    ext y
    constructor
    · rintro ⟨t, hty⟩
      have hyt : y = r (i + t) := by simpa using hty.symm
      refine ⟨⟨i + t, hyt.symm⟩, ?_⟩
      let q := raySegmentPath r i t
      refine ⟨q, Or.inl ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
      · exact hyt.symm
      · intro z hz
        change z ∈ (raySegmentPath r i t).support at hz
        rw [mem_raySegmentPath_support_iff] at hz
        rcases hz with ⟨s, _, hzs⟩
        exact ⟨i + s, hzs.symm⟩
      · change (raySegmentPath r i t).edgeSet ⊆ r.edgeSet
        intro e he
        rw [raySegmentPath_edgeSet_eq] at he
        rcases he with ⟨s, _, rfl⟩
        exact rayEdge_mem r (i + s)
      · apply raySegmentPath_disjoint L C r i t
        intro s _
        apply hkeep (i + s)
        simpa [i]
    · rintro ⟨⟨j, hjy⟩, q, hend, _, hqEdge, hqDisjoint⟩
      change q.edgeSet ⊆ r.edgeSet at hqEdge
      rcases hend with hforward | hbackward
      · change q.start = r i ∧ q.finish = y at hforward
        have hstart : r i = q.start := hforward.1.symm
        have hfinish : r j = q.finish := hjy.trans hforward.2.symm
        have hij : i ≤ j :=
          Walk.position_mono_in_ray r q.walk hqEdge i j hstart hfinish
        refine ⟨j - i, ?_⟩
        change r (i + (j - i)) = y
        simpa [Nat.add_sub_of_le hij] using hjy
      · change q.start = y ∧ q.finish = r i at hbackward
        have hstart : r j = q.start := hjy.trans hbackward.1.symm
        have hfinish : r i = q.finish := hbackward.2.symm
        have hji : j ≤ i :=
          Walk.position_mono_in_ray r q.walk hqEdge j i hstart hfinish
        have hij : i ≤ j := by
          simpa [i] using
            rayLeftIndex_le_of_walk_to_left L C r k q.walk hqEdge
              hqDisjoint hstart (by simpa [i] using hfinish)
        have hjiEq : j = i := Nat.le_antisymm hji hij
        refine ⟨0, ?_⟩
        simpa [hjiEq] using hjy

/-- Every vertex of a ladder ray lies in a maximal component after the
represented cut edges are deleted.  The returned fragment records the given
ray literally as its parent. -/
theorem exists_ray_fragment_containing
    (L : Input Gamma I) (C : Set (LV L)) (r : Ray Gamma.graph)
    (hr : (Sum.inr r : Gamma.DPath) ∈ L.ladder.paths)
    {x : V} (hx : x ∈ r.support) :
    ∃ P : L.Fragment,
      P.parent = .inr r ∧
        P ∈ GroundingCut.fragments L C ∧ x ∈ P.path.support := by
  classical
  rcases hx with ⟨k, hkx⟩
  let i := rayLeftIndex L C r k
  have hik : i ≤ k := (rayLeftIndex_spec L C r k).1
  by_cases hright : ∃ d,
      rayEdge r (k + d) ∈ GroundingCut.CE L C
  · let d := Nat.find hright
    let n := k + d
    have hnCut : rayEdge r n ∈ GroundingCut.CE L C := by
      simpa [n, d] using Nat.find_spec hright
    have hkn : k ≤ n := by simp [n]
    have hkeep : ∀ t, i ≤ t → t < n →
        rayEdge r t ∉ GroundingCut.CE L C := by
      intro t hit htn htCut
      by_cases htk : t < k
      · exact (rayLeftIndex_spec L C r k).2 t (by simpa [i] using hit) htk htCut
      · have hkt : k ≤ t := by omega
        let e := t - k
        have hte : k + e = t := by simp [e, Nat.add_sub_of_le hkt]
        have heCut : rayEdge r (k + e) ∈
            GroundingCut.CE L C := by
          simpa [hte] using htCut
        have hde : d ≤ e := Nat.find_min' hright heCut
        have hed : e < d := by
          dsimp [n, d] at htn
          dsimp [e]
          omega
        omega
    let P := finiteRayFragment L r hr i n
    refine ⟨P, rfl, ?_, ?_⟩
    · change finiteRayFragment L r hr i n ∈ GroundingCut.fragments L C
      simpa [i] using
        finiteRayFragment_mem_fragments L C r hr k n hkn
          (by simpa [i] using hkeep) hnCut
    · change x ∈ (raySegmentPath r i (n - i)).support
      rw [mem_raySegmentPath_support_iff]
      refine ⟨k - i, by omega, ?_⟩
      calc
        x = r k := hkx.symm
        _ = r (i + (k - i)) := by congr 1 <;> omega
  · have hkeep : ∀ t, i ≤ t →
        rayEdge r t ∉ GroundingCut.CE L C := by
      intro t hit htCut
      by_cases htk : t < k
      · exact (rayLeftIndex_spec L C r k).2 t (by simpa [i] using hit) htk htCut
      · have hkt : k ≤ t := by omega
        apply hright
        refine ⟨t - k, ?_⟩
        simpa [Nat.add_sub_of_le hkt] using htCut
    let P := tailRayFragment L r hr i
    refine ⟨P, rfl, ?_, ?_⟩
    · change tailRayFragment L r hr i ∈ GroundingCut.fragments L C
      simpa [i] using tailRayFragment_mem_fragments L C r hr k
        (by simpa [i] using hkeep)
    · change x ∈ (r.tail i).support
      refine ⟨k - i, ?_⟩
      simpa [Nat.add_sub_of_le hik] using hkx



end GroundingRayFragment
end Erdos599
