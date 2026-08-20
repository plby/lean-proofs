/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.CyclicSkeleton

/-!
# Closure in a finite cyclic order

The canonical cyclic successor of a finite set equipped with a separating
real coordinate consists of one cycle.  Consequently every nonempty finite
subset closed under successor is the whole cyclically ordered set.  This is
the finite closure principle used by the literal Stage-4 line belt.
-/

open Classical
noncomputable section

namespace Erdos735.ChartOrder

universe uV

variable {V : Type uV} [DecidableEq V]

/-- The cyclic successor acts injectively on a separated finite set. -/
theorem cyclicSuccessor_injective (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) :
    Function.Injective (cyclicSuccessor coord S) := by
  intro x y hxy
  have := congrArg (cyclicPredecessor coord S) hxy
  simpa [cyclicPredecessor_successor coord S hinj] using this

/-- A nonempty subset of a finite separated cyclic order which is closed
under the canonical successor is the entire set. -/
theorem eq_univ_of_nonempty_of_cyclicSuccessor_closed
    (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V))
    (U : Finset {x // x ∈ S}) (hne : U.Nonempty)
    (hclosed : ∀ x ∈ U, cyclicSuccessor coord S x ∈ U) :
    U = Finset.univ := by
  have hsuccInj : Function.Injective (cyclicSuccessor coord S) :=
    cyclicSuccessor_injective coord S hinj
  have himageSub : U.image (cyclicSuccessor coord S) ⊆ U := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hclosed x hx
  have himageEq : U.image (cyclicSuccessor coord S) = U := by
    apply Finset.eq_of_subset_of_card_le himageSub
    rw [Finset.card_image_of_injective _ hsuccInj]
  have hpredClosed : ∀ y ∈ U, cyclicPredecessor coord S y ∈ U := by
    intro y hy
    have hyImage : y ∈ U.image (cyclicSuccessor coord S) := by
      rw [himageEq]
      exact hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyImage
    have hxp : x = cyclicPredecessor coord S y := by
      apply hsuccInj
      rw [hxy, cyclicSuccessor_predecessor coord S hinj]
    simpa [← hxp] using hx
  obtain ⟨t, htU, htmax⟩ := U.exists_max_image (fun x ↦ coord x.1) hne
  have htmaxS : ∀ x ∈ S, coord x ≤ coord t.1 := by
    intro x hx
    apply le_of_not_gt
    intro htx
    have hspec := cyclicSuccessor_spec coord S t
    have hsuccU := hclosed t htU
    have hmaxSucc := htmax (cyclicSuccessor coord S t) hsuccU
    rcases hspec with hord | hwrap
    · exact (not_lt_of_ge hmaxSucc) hord.lt
    · exact (not_lt_of_ge (hwrap.2.2.1 x hx)) htx
  let z := cyclicSuccessor coord S t
  have hzU : z ∈ U := hclosed t htU
  have hzminS : ∀ x ∈ S, coord z.1 ≤ coord x := by
    have hspec := cyclicSuccessor_spec coord S t
    rcases hspec with hord | hwrap
    · exact ((not_lt_of_ge (htmaxS z.1 z.2)) hord.lt).elim
    · exact hwrap.2.2.2
  by_contra hU
  have hproper : (Finset.univ \ U : Finset {x // x ∈ S}).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    exact fun hsub ↦ hU
      (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
  obtain ⟨y, hyOut, hymin⟩ :=
    (Finset.univ \ U).exists_min_image (fun x ↦ coord x.1) hproper
  have hyNotU : y ∉ U := (Finset.mem_sdiff.mp hyOut).2
  have hyne : z ≠ y := by
    intro hzy
    subst y
    exact hyNotU hzU
  have hzlt : coord z.1 < coord y.1 := by
    exact lt_of_le_of_ne (hzminS y.1 y.2) (fun h ↦
      hyne (Subtype.ext (hinj z.2 y.2 h)))
  let p := cyclicPredecessor coord S y
  have hpU : p ∈ U := by
    have hspec := cyclicPredecessor_spec coord S y
    rcases hspec with hord | hwrap
    · by_contra hpNot
      have hpOut : p ∈ (Finset.univ \ U : Finset {x // x ∈ S}) := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNot⟩
      exact (not_lt_of_ge (hymin p hpOut)) hord.lt
    · exact ((not_lt_of_ge (hwrap.2.2.2 z.1 z.2)) hzlt).elim
  have hsuccPU := hclosed p hpU
  rw [cyclicSuccessor_predecessor coord S hinj] at hsuccPU
  exact hyNotU hsuccPU

/-- If two distinct cyclic intervals are the two distinct neighbors of a
third interval, one of them is its forward successor.  The hypothesis is
orientation-free, matching the endpoint-sharing facts produced by the
literal polar geometry. -/
theorem finish_eq_start_of_two_distinct_neighbors
    {L : Type*} [Fintype V] [Fintype L] [DecidableEq L]
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (e y z : CyclicSkeletonEdge vertices onLine)
    (hlineY : cyclicEdgeLine y = cyclicEdgeLine e)
    (hlineZ : cyclicEdgeLine z = cyclicEdgeLine e)
    (heneY : e ≠ y) (heneZ : e ≠ z)
    (hyz : y ≠ z)
    (hy : e = y ∨
      cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart y ∨
      cyclicEdgeFinish vertices onLine coord y = cyclicEdgeStart e)
    (hz : e = z ∨
      cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart z ∨
      cyclicEdgeFinish vertices onLine coord z = cyclicEdgeStart e) :
    cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart y ∨
      cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart z := by
  rcases hy with heqY | heY | hYe
  · exact (heneY heqY).elim
  · exact Or.inl heY
  · rcases hz with heqZ | heZ | hZe
    · exact (heneZ heqZ).elim
    · exact Or.inr heZ
    · exfalso
      apply hyz
      rcases e with ⟨le, se⟩
      rcases y with ⟨ly, sy⟩
      rcases z with ⟨lz, sz⟩
      change ly = le at hlineY
      change lz = le at hlineZ
      subst ly
      subst lz
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply cyclicConsecutive_left_unique coord
          (verticesOn vertices onLine le)
          (hinj.mono (Finset.filter_subset _ _))
        · have hs := cyclicEdgeFinish_spec vertices onLine coord
            (⟨le, sy⟩ : CyclicSkeletonEdge vertices onLine)
          rw [hYe] at hs
          exact hs
        · have hs := cyclicEdgeFinish_spec vertices onLine coord
            (⟨le, sz⟩ : CyclicSkeletonEdge vertices onLine)
          rw [hZe] at hs
          exact hs

/-- Two distinct intervals on one supporting line with the same unordered
endpoint pair traverse that pair in opposite directions. -/
theorem finish_eq_start_of_distinct_of_vertices_eq
    {L : Type*} [Fintype V] [Fintype L] [DecidableEq L]
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ)
    (e y : CyclicSkeletonEdge vertices onLine)
    (hline : cyclicEdgeLine e = cyclicEdgeLine y)
    (hne : e ≠ y)
    (hvertices : cyclicEdgeVertices vertices onLine coord e =
      cyclicEdgeVertices vertices onLine coord y) :
    cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart y := by
  have hymem : cyclicEdgeStart y ∈
      cyclicEdgeVertices vertices onLine coord e := by
    rw [hvertices, cyclicEdgeVertices]
    simp
  simp only [cyclicEdgeVertices, Finset.mem_insert,
    Finset.mem_singleton] at hymem
  rcases hymem with hstart | hfinish
  · exfalso
    apply hne
    rcases e with ⟨le, se⟩
    rcases y with ⟨ly, sy⟩
    change le = ly at hline
    subst ly
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact hstart.symm
  · exact hfinish.symm

/-- Two distinct cyclic intervals on one line which contain the same two
distinct vertices traverse that common endpoint pair in opposite
directions.  This is the collision-safe form used when two graph neighbors
collapse to one projective interval. -/
theorem finish_eq_start_of_distinct_of_two_common_vertices
    {L : Type*} [Fintype V] [Fintype L] [DecidableEq L]
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (htwo : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (e y : CyclicSkeletonEdge vertices onLine)
    (hline : cyclicEdgeLine e = cyclicEdgeLine y)
    (hne : e ≠ y)
    (v u : V) (hvu : v ≠ u)
    (hve : v ∈ cyclicEdgeVertices vertices onLine coord e)
    (hue : u ∈ cyclicEdgeVertices vertices onLine coord e)
    (hvy : v ∈ cyclicEdgeVertices vertices onLine coord y)
    (huy : u ∈ cyclicEdgeVertices vertices onLine coord y) :
    cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart y := by
  have hcardPair : ({v, u} : Finset V).card = 2 := by
    simp [hvu]
  have hpairE : ({v, u} : Finset V) =
      cyclicEdgeVertices vertices onLine coord e := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hve
      · exact hue
    · rw [cyclicEdgeVertices_card vertices onLine coord hinj htwo e,
        hcardPair]
  have hpairY : ({v, u} : Finset V) =
      cyclicEdgeVertices vertices onLine coord y := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvy
      · exact huy
    · rw [cyclicEdgeVertices_card vertices onLine coord hinj htwo y,
        hcardPair]
  exact finish_eq_start_of_distinct_of_vertices_eq
    vertices onLine coord e y hline hne (hpairE.symm.trans hpairY)

end Erdos735.ChartOrder
