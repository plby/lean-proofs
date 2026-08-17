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
import ErdosProblems.Erdos58.Linkage
import Mathlib.Tactic

/-!
# The finite two-linkage interface

The `TwoLinkage` certificate in `Linkage.lean` uses *fully* vertex-disjoint
paths.  Consequently, two vertices are needed at each end: the often-quoted
version with merely nonempty connected sets is false when one of the sets is
a singleton.  This file records that sharp obstruction.

It also proves the two elementary pieces surrounding the set form of
Menger's theorem which are needed in the Erdős 58 application:

* two-connectivity and the two endpoint-cardinality hypotheses rule out an
  `A`--`B` separator having fewer than two vertices;
* any two fully disjoint `A`--`B` paths can be truncated at their first/last
  visits to the endpoint sets to give the stronger `TwoLinkage` certificate,
  including its interior-avoidance fields.

Mathlib v4.33 does not contain vertex Menger's theorem.  Accordingly the
packing statement is kept as an explicit hypothesis in
`TwoConnected.twoLinkage_of_rawPacking`; the graph-specific separator
condition which finite Menger consumes is proved below without any gap.
-/

namespace Erdos58

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {A B S : Set V}

namespace TwoLinkage

/-- Two fully support-disjoint paths force at least two vertices in their
left endpoint set. -/
theorem two_le_ncard_left (L : TwoLinkage G A B) : 2 ≤ A.ncard := by
  have hsub : ({L.a₁, L.a₂} : Set V) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact L.a₁_mem
    · exact L.a₂_mem
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite A)
  rw [Set.ncard_pair L.a_ne] at hcard
  exact hcard

/-- Two fully support-disjoint paths force at least two vertices in their
right endpoint set. -/
theorem two_le_ncard_right (L : TwoLinkage G A B) : 2 ≤ B.ncard := by
  have hsub : ({L.b₁, L.b₂} : Set V) ⊆ B := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact L.b₁_mem
    · exact L.b₂_mem
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite B)
  rw [Set.ncard_pair L.b_ne] at hcard
  exact hcard

theorem endpoint_cardinality (L : TwoLinkage G A B) :
    2 ≤ A.ncard ∧ 2 ≤ B.ncard :=
  ⟨L.two_le_ncard_left, L.two_le_ncard_right⟩

end TwoLinkage

/-! ## Separators of cardinality at most one -/

/-- `S` meets every walk whose first vertex lies in `A` and last vertex lies
in `B`.  This formulation permits separator vertices in `A` or `B`, as in
the set form of vertex Menger's theorem. -/
def IsABSeparator (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B →
    ∀ p : G.Walk a b, ∃ x, x ∈ S ∧ x ∈ p.support

namespace TwoConnected

/-- The exact graph-specific input to finite set-Menger: when both endpoint
sets have at least two vertices, deletion connectivity rules out every
separator of cardinality less than two.  No connectivity hypothesis on the
sets themselves is needed. -/
theorem not_isABSeparator_of_ncard_lt_two
    (hG : TwoConnected G) (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard)
    (hS : S.ncard < 2) : ¬IsABSeparator G A B S := by
  intro hsep
  have hSle : S.ncard ≤ 1 := by omega
  rcases Set.eq_empty_or_nonempty S with hSempty | ⟨z, hzS⟩
  · let z : V := Classical.choice hG.connected.nonempty
    obtain ⟨a, haA, -⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨b, hbB, -⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨p, hp⟩ := hG.connected.exists_isPath a b
    obtain ⟨x, hxS, -⟩ := hsep haA hbB p
    simp [hSempty] at hxS
  · have hSsub : S.Subsingleton :=
      (Set.ncard_le_one (Set.toFinite S)).mp hSle
    obtain ⟨a, haA, haz⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨b, hbB, hbz⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨p, hp, hpz⟩ := hG.exists_path_avoiding z haz hbz
    obtain ⟨x, hxS, hxp⟩ := hsep haA hbB p
    exact hpz (hSsub hxS hzS ▸ hxp)

theorem no_small_isABSeparator
    (hG : TwoConnected G) (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    ∀ S : Set V, IsABSeparator G A B S → 2 ≤ S.ncard := by
  intro S hsep
  by_contra h
  exact hG.not_isABSeparator_of_ncard_lt_two hA hB (by omega) hsep

end TwoConnected

/-! ## Truncating a raw path packing -/

/-- Two fully vertex-disjoint paths whose endpoints lie in `A` and `B`, but
whose interiors have not yet been cleaned of later visits to `A ∪ B`. -/
structure RawTwoPathPacking (G : SimpleGraph V) (A B : Set V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  p_isPath : p.IsPath
  q_isPath : q.IsPath
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  disjoint_support : p.support.Disjoint q.support

namespace RawTwoPathPacking

/-- The data returned by canonical first/last-hit truncation of one path. -/
structure CleanSubpath {a b : V} (p : G.Walk a b) (A B : Set V) where
  left : V
  right : V
  walk : G.Walk left right
  isPath : walk.IsPath
  left_mem : left ∈ A
  right_mem : right ∈ B
  support_subset : walk.support ⊆ p.support
  interior : ∀ x ∈ walk.support.tail.dropLast, x ∉ A ∪ B

/-- A path with endpoints in `A` and `B` has a subpath with the same endpoint
conditions, no internal visit to either endpoint set, and support contained
in the original support.  We first stop at the first `B`-vertex, then reverse
and stop at the first `A`-vertex. -/
private theorem exists_clean_subpath
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (ha : a ∈ A) (hb : b ∈ B) :
    Nonempty (CleanSubpath p A B) := by
  classical
  have hBmeet : {x ∈ B.toFinset | x ∈ p.support}.Nonempty := by
    refine ⟨b, ?_⟩
    simp [hb]
  obtain ⟨b', hb'B, hb'p, hfirstB⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq B.toFinset hBmeet
  let pB : G.Walk a b' := p.takeUntil b' hb'p
  have ha_pB : a ∈ pB.support := pB.start_mem_support
  have hAmeet : {x ∈ A.toFinset | x ∈ pB.reverse.support}.Nonempty := by
    refine ⟨a, ?_⟩
    simp_all
  obtain ⟨a', ha'A, ha'pr, hfirstA⟩ :=
    pB.reverse.exists_mem_support_forall_mem_support_imp_eq A.toFinset hAmeet
  let r₀ : G.Walk b' a' := pB.reverse.takeUntil a' ha'pr
  let r : G.Walk a' b' := r₀.reverse
  have hpB : pB.IsPath := hp.takeUntil hb'p
  have hr₀ : r₀.IsPath := hpB.reverse.takeUntil ha'pr
  have hr : r.IsPath := hr₀.reverse
  have hr₀_sub : r₀.support ⊆ pB.reverse.support :=
    pB.reverse.support_takeUntil_subset_support ha'pr
  have hpB_sub : pB.support ⊆ p.support :=
    p.support_takeUntil_subset_support hb'p
  have hr_sub : r.support ⊆ p.support := by
    intro x hxr
    have hxr₀ : x ∈ r₀.support := by simpa [r] using hxr
    have hxpBr : x ∈ pB.reverse.support := hr₀_sub hxr₀
    have hxpB : x ∈ pB.support := by simpa using hxpBr
    exact hpB_sub hxpB
  refine ⟨{
    left := a'
    right := b'
    walk := r
    isPath := hr
    left_mem := by simpa using ha'A
    right_mem := by simpa using hb'B
    support_subset := hr_sub
    interior := ?_ }⟩
  intro x hxint hxAB
  have htailne : r.support.tail ≠ [] := by
    intro h
    simp [h] at hxint
  have hxdrop : x ∈ r.support.dropLast := by
    rw [← r.cons_tail_support, List.dropLast_cons_of_ne_nil htailne]
    exact List.mem_cons_of_mem _ hxint
  have hxtail : x ∈ r.support.tail := List.mem_of_mem_dropLast hxint
  have hxane : x ≠ a' := by
    have hne := hr.support_nodup.rel_head_tail hxtail
    simpa using hne.symm
  have hxbne : x ≠ b' := by
    have hne := hr.support_nodup.rel_dropLast_getLast hxdrop
    simpa using hne
  have hxr₀ : x ∈ r₀.support := by
    have hxr : x ∈ r.support := List.mem_of_mem_tail hxtail
    simpa [r] using hxr
  rcases hxAB with hxA | hxB
  · have hxa' := hfirstA x (by simpa using hxA) hxr₀
    exact hxane hxa'
  · have hxpBr : x ∈ pB.reverse.support := hr₀_sub hxr₀
    have hxpB : x ∈ pB.support := by simpa using hxpBr
    have hxb' := hfirstB x (by simpa using hxB) hxpB
    exact hxbne hxb'

/-- The canonical cleaned subpath selected from one path. -/
noncomputable def cleanSubpath
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (ha : a ∈ A) (hb : b ∈ B) : CleanSubpath p A B :=
  Classical.choice (exists_clean_subpath p hp ha hb)

/-- Cleaning the interiors of the two raw paths preserves full support
disjointness and yields the repository's downstream `TwoLinkage`
certificate. -/
noncomputable def toTwoLinkage (P : RawTwoPathPacking G A B) :
    TwoLinkage G A B := by
  let P₁ := cleanSubpath P.p P.p_isPath P.a₁_mem P.b₁_mem
  let P₂ := cleanSubpath P.q P.q_isPath P.a₂_mem P.b₂_mem
  exact
    { a₁ := P₁.left
      a₂ := P₂.left
      b₁ := P₁.right
      b₂ := P₂.right
      p := P₁.walk
      q := P₂.walk
      p_isPath := P₁.isPath
      q_isPath := P₂.isPath
      a₁_mem := P₁.left_mem
      a₂_mem := P₂.left_mem
      b₁_mem := P₁.right_mem
      b₂_mem := P₂.right_mem
      disjoint_support := fun x hxp hxq ↦
        P.disjoint_support (P₁.support_subset hxp) (P₂.support_subset hxq)
      p_interior := P₁.interior
      q_interior := P₂.interior }

end RawTwoPathPacking

/-! ## The finite set-Menger interface -/

/-- The cardinal-two instance of finite set-Menger, formulated using the
walk and separator types of this development.  Keeping this proposition
named makes the one theorem absent from Mathlib v4.33 an explicit dependency
of the final existence result. -/
def SatisfiesSetMengerTwo (G : SimpleGraph V) : Prop :=
  ∀ A B : Set V,
    (∀ S : Set V, IsABSeparator G A B S → 2 ≤ S.ncard) →
      Nonempty (RawTwoPathPacking G A B)

namespace TwoConnected

/-- The post-Menger step: once the finite set form of Menger supplies two
fully support-disjoint `A`--`B` paths, their canonical truncations form a
`TwoLinkage`. -/
theorem twoLinkage_of_rawPacking (_hG : TwoConnected G)
    (P : RawTwoPathPacking G A B) : Nonempty (TwoLinkage G A B) := by
  exact ⟨P.toTwoLinkage⟩

/-- Set-Menger plus the checked deletion-connectivity argument gives the
desired linkage.  The endpoint-cardinality assumptions are sharp by
`TwoLinkage.endpoint_cardinality`. -/
theorem twoLinkage_of_setMenger (hG : TwoConnected G)
    (hMenger : SatisfiesSetMengerTwo G)
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (TwoLinkage G A B) := by
  obtain ⟨P⟩ := hMenger A B (hG.no_small_isABSeparator hA hB)
  exact hG.twoLinkage_of_rawPacking P

/-- Under finite set-Menger, the two cardinality bounds are not only
sufficient but exactly characterize existence of the full-support-disjoint
linkage certificate. -/
theorem twoLinkage_iff_endpoint_cardinality (hG : TwoConnected G)
    (hMenger : SatisfiesSetMengerTwo G) :
    Nonempty (TwoLinkage G A B) ↔ 2 ≤ A.ncard ∧ 2 ≤ B.ncard := by
  constructor
  · rintro ⟨L⟩
    exact L.endpoint_cardinality
  · rintro ⟨hA, hB⟩
    exact hG.twoLinkage_of_setMenger hMenger hA hB

end TwoConnected

end Erdos58
