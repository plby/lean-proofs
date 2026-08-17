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
import ErdosProblems.Erdos58.EndpointCount
import ErdosProblems.Erdos58.Independent

/-!
# Bridging the two longest-odd-cycle representations

The independent-exterior part of the proof represents a chosen cycle by a
copy of `cycleGraph`; the endpoint-counting part represents it by a Mathlib
closed walk.  `LongestOddCycle.walk` is the canonical walk obtained by
mapping the standard cycle through that copy.  This file records that it has
exactly the same vertex carrier and packages it for `EndpointCount`.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The canonical walk associated to a copy-valued longest odd cycle has
support equal to the range of the copy. -/
lemma longestOddCycle_walk_support (C : Erdos58.LongestOddCycle G) :
    {v | v ∈ C.walk.support} = C.carrier := by
  classical
  ext v
  simp only [Erdos58.LongestOddCycle.walk,
    SimpleGraph.Walk.support_map, Erdos58.LongestOddCycle.carrier,
    Set.mem_ofPred_eq, Set.mem_range, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Fin.cast (Nat.sub_add_cancel C.three_le) z, by
      simp [Erdos58.LongestOddCycle.normalizedCopy_apply]⟩
  · rintro ⟨z, rfl⟩
    let z' : Fin (C.length - 3 + 3) :=
      Fin.cast (Nat.sub_add_cancel C.three_le).symm z
    refine ⟨z', ?_, ?_⟩
    · let m := C.length - 3 + 3 - z'.val
      have hm : m ≤ C.length - 3 + 3 := Nat.sub_le _ _
      have hmem :=
        (SimpleGraph.cycleGraph.cycle (C.length - 3)).getVert_mem_support m
      have hget :
          (SimpleGraph.cycleGraph.cycle (C.length - 3)).getVert m = z' := by
        rw [SimpleGraph.cycleGraph.getVert_cycle hm]
        apply Fin.ext
        change ((C.length - 3 + 3 - m) % (C.length - 3 + 3)) = z'.val
        have hsub : C.length - 3 + 3 - m = z'.val := by
          simp only [m]
          omega
        rw [hsub, Nat.mod_eq_of_lt z'.isLt]
      rwa [hget] at hmem
    · simp [z', Erdos58.LongestOddCycle.normalizedCopy_apply]

/-- The copy-valued longest odd cycle, viewed in the walk-valued endpoint
counting interface. -/
def toEndpointLongestOddCycle (C : Erdos58.LongestOddCycle G) :
    Erdos58.EndpointCount.LongestOddCycle G where
  base := C.normalizedCopy 0
  cycle := C.walk
  isCycle := C.walk_isCycle
  odd_length := by simpa using C.odd
  longest := by
    intro n hn
    simpa using C.maximal hn

/-- The walk-valued longest-cycle interface, rebased at an arbitrary index
of the copy-valued cycle and oriented in increasing `Fin` order. -/
def toEndpointLongestOddCycleAt (C : Erdos58.LongestOddCycle G)
    (x : Fin C.length) : Erdos58.EndpointCount.LongestOddCycle G where
  base := C.copy x
  cycle := C.rimWalkFrom x
  isCycle := C.rimWalkFrom_isCycle x
  odd_length := by simpa using C.odd
  longest := by
    intro n hn
    simpa using C.maximal hn

@[simp] lemma toEndpointLongestOddCycleAt_length
    (C : Erdos58.LongestOddCycle G) (x : Fin C.length) :
    (toEndpointLongestOddCycleAt C x).cycle.length = C.length := by
  simp [toEndpointLongestOddCycleAt]

@[simp] lemma toEndpointLongestOddCycleAt_getVert
    (C : Erdos58.LongestOddCycle G) (x : Fin C.length)
    (i : ℕ) (hi : i ≤ C.length) :
    (toEndpointLongestOddCycleAt C x).cycle.getVert i =
      C.copy (x + ⟨i % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) :=
  C.rimWalkFrom_getVert x i hi

lemma mem_toEndpointLongestOddCycleAt_support_iff
    (C : Erdos58.LongestOddCycle G) (x : Fin C.length) (v : V) :
    v ∈ (toEndpointLongestOddCycleAt C x).cycle.support ↔
      v ∈ C.carrier := by
  exact Set.ext_iff.mp (C.rimWalkFrom_support x) v

/-- Rebase the walk-valued longest odd cycle at a vertex of its support.
The underlying oriented cycle is unchanged, so its length, oddness, support,
and maximality properties are preserved. -/
def rotateEndpointLongestOddCycle
    [DecidableEq V] (C : Erdos58.EndpointCount.LongestOddCycle G) (x : V)
    (hx : x ∈ C.cycle.support) :
    Erdos58.EndpointCount.LongestOddCycle G where
  base := x
  cycle := C.cycle.rotate x hx
  isCycle := C.isCycle.rotate hx
  odd_length := by simpa using C.odd_length
  longest := by
    intro n hn
    simpa using C.longest hn

@[simp] lemma rotateEndpointLongestOddCycle_length
    [DecidableEq V] (C : Erdos58.EndpointCount.LongestOddCycle G) (x : V)
    (hx : x ∈ C.cycle.support) :
    (rotateEndpointLongestOddCycle C x hx).cycle.length = C.cycle.length := by
  simp [rotateEndpointLongestOddCycle]

lemma mem_rotateEndpointLongestOddCycle_support_iff
    [DecidableEq V] (C : Erdos58.EndpointCount.LongestOddCycle G) (x : V)
    (hx : x ∈ C.cycle.support) (v : V) :
    v ∈ (rotateEndpointLongestOddCycle C x hx).cycle.support ↔
      v ∈ C.cycle.support := by
  exact C.cycle.mem_support_rotate_iff x hx

@[simp] lemma rotateEndpointLongestOddCycle_getVert_zero
    [DecidableEq V] (C : Erdos58.EndpointCount.LongestOddCycle G) (x : V)
    (hx : x ∈ C.cycle.support) :
    (rotateEndpointLongestOddCycle C x hx).cycle.getVert 0 = x := by
  simp [rotateEndpointLongestOddCycle]

@[simp] lemma rotateEndpointLongestOddCycle_getVert_length
    [DecidableEq V] (C : Erdos58.EndpointCount.LongestOddCycle G) (x : V)
    (hx : x ∈ C.cycle.support) :
    (rotateEndpointLongestOddCycle C x hx).cycle.getVert
        (rotateEndpointLongestOddCycle C x hx).cycle.length = x := by
  rw [SimpleGraph.Walk.getVert_length]
  rfl

@[simp] lemma toEndpointLongestOddCycle_length
    (C : Erdos58.LongestOddCycle G) :
    (toEndpointLongestOddCycle C).cycle.length = C.length :=
  C.walk_length

lemma mem_toEndpointLongestOddCycle_support_iff
    (C : Erdos58.LongestOddCycle G) (v : V) :
    v ∈ (toEndpointLongestOddCycle C).cycle.support ↔ v ∈ C.carrier := by
  exact Set.ext_iff.mp (longestOddCycle_walk_support C) v

end

end Erdos58.Structural
