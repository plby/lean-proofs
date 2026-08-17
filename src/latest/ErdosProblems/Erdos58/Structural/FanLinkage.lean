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
import ErdosProblems.Erdos58.Structural.FanApplication
import ErdosProblems.Erdos58.Structural.CaseAssembly
import ErdosProblems.Erdos58.Structural.SpliceConstruction

/-!
# Closing an endpoint fan through two-connectivity

This file connects the actual-walk endpoint fan construction to the finite
set-Menger theorem.  It also records the support fact needed to apply the
outside-cycle lemma to the mixed-parity two-spoke cycles.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {j : ℕ}

namespace EndpointFanData

/-- The two-spoke cycles of a fan outside `C` are genuine exterior odd
cycles, so two-connectivity makes them strictly shorter than `C`. -/
lemma betweenCycle_lt_longest (hG : TwoConnected G)
    {C : Erdos58.LongestOddCycle G} (D : EndpointFanData G x y j)
    (houtside : ∀ v ∈ D.path.support, v ∉ C.carrier)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i')
    (hodd : Odd (D.betweenCycle i i' hii').length) :
    (D.betweenCycle i i' hii').length < C.length := by
  let E : ExteriorOddCycle C :=
    { base := x
      cycle := D.betweenCycle i i' hii'
      isCycle := D.betweenCycle_isCycle i i' hii'
      odd_length := hodd
      support_outside := fun v hv ↦
        houtside v (D.betweenCycle_support_subset i i' hii' hv) }
  exact Structural.outside_odd_cycle_is_shorter_of_twoConnected hG E

/-- A finite realization supplies the corresponding lower bound for the
global odd-cycle-length set. -/
lemma ncard_oddCycleLengths_ge_of_realizes {r : ℕ}
    (h : RealizesOddCycleLengths G r) :
    r ≤ (oddCycleLengths G).ncard := by
  obtain ⟨lengths, hcard, hreal⟩ := h
  have hsub : (lengths : Set ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    obtain ⟨v, c, hc, hodd, rfl⟩ := hreal n hn
    exact ⟨hodd, v, c, hc, rfl⟩
  exact hcard.trans (by
    simpa using Set.ncard_le_ncard hsub (oddCycleLengths_finite G))

/-- The all-odd branch of the endpoint fan, closed through the actual
two-linkage supplied by two-connectivity. -/
theorem allOddSupportedPaths_force_many_lengths
    (hG : TwoConnected G) {C : Erdos58.LongestOddCycle G}
    (D : EndpointFanData G x y j)
    (houtside : ∀ v ∈ D.path.support, v ∉ C.carrier)
    (hpositive : 0 < D.path.length)
    (hpaths : ∀ {a b : ℕ}, a ≤ D.path.length → b ≤ D.path.length → a ≠ b →
      Nonempty (FanSupportedPathFamily D (D.path.getVert a)
        (D.path.getVert b) (j + 1))) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  let B : Set V := {v | v ∈ D.path.support}
  have hAB : Disjoint C.carrier B := by
    rw [Set.disjoint_left]
    intro v hvC hvB
    exact houtside v hvB hvC
  have hxy : x ≠ y := by
    intro hxy
    have hindex := D.isPath.getVert_injOn
      (show 0 ≤ D.path.length by omega)
      (show D.path.length ≤ D.path.length by omega)
      (by simpa [hxy] using (show D.path.getVert 0 = D.path.getVert D.path.length by
        simp [hxy]))
    omega
  have hpair : ({x, y} : Set V) ⊆ B := by
    intro v hv
    rcases hv with rfl | hv
    · exact D.path.start_mem_support
    · have : v = y := by simpa using hv
      subst v
      exact D.path.end_mem_support
  have hB : 2 ≤ B.ncard := by
    have hcardPair : ({x, y} : Set V).ncard = 2 := by simp [hxy]
    rw [← hcardPair]
    exact Set.ncard_le_ncard hpair (Set.toFinite B)
  obtain ⟨L⟩ := hG.exists_twoLinkage
    (Structural.LongestOddCycle.two_le_ncard_carrier C) hB
  obtain ⟨a, ha, hale⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp L.b₁_mem
  obtain ⟨b, hb, hble⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp L.b₂_mem
  have hab : a ≠ b := by
    intro hab
    apply L.b_ne
    rw [← ha, ← hb, hab]
  obtain ⟨P⟩ := hpaths hale hble hab
  have ha' : D.path.getVert a = L.b₁ := ha
  have hb' : D.path.getVert b = L.b₂ := hb
  let PF : FanSupportedPathFamily D L.b₁ L.b₂ (j + 1) :=
    { family :=
        { path := fun i ↦ (P.family.path i).copy ha' hb'
          isPath := fun i ↦
            (SimpleGraph.Walk.isPath_copy (P.family.path i) ha' hb').2
              (P.family.isPath i)
          length_injective := by
            simpa only [SimpleGraph.Walk.length_copy] using
              P.family.length_injective
          sameParity := by
            intro i k
            simpa only [SimpleGraph.Walk.length_copy] using
              P.family.sameParity i k }
      support_subset := by
        intro i z hz
        exact P.support_subset i z (by
          simpa only [SimpleGraph.Walk.support_copy] using hz) }
  have hA : ∀ v : V, v ∈ C.carrier ↔ v ∈ C.walk.support := by
    intro v
    exact (Structural.mem_toEndpointLongestOddCycle_support_iff C v).symm
  obtain ⟨F⟩ := Structural.oddCycleFamily_of_pathFamily_linkage
    C.walk C.walk_isCycle (by
      simpa only [Erdos58.LongestOddCycle.walk_length] using C.odd) L hAB hA PF.family
      (fun i z hz ↦ PF.support_subset i z hz)
  exact ncard_oddCycleLengths_ge_of_realizes (by
    simpa using F.realizes)

/-- An endpoint fan of size `2*j+1` supported outside a longest odd cycle
forces `j+1` odd cycle lengths.  The mixed branch is made disjoint from the
longest length by the outside-cycle lemma; the all-odd branch is closed by
Menger through `oddCycleFamily_of_pathFamily_linkage`. -/
theorem endpointFan_force_many_lengths
    (hG : TwoConnected G) {C : Erdos58.LongestOddCycle G}
    (D : EndpointFanData G x y j)
    (houtside : ∀ v ∈ D.path.support, v ∉ C.carrier)
    (hj : 1 ≤ j)
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  rcases D.mixedCyclesBelow_or_allOddSupportedPaths hj hfirst hlast
      (bound := C.length)
      (fun i i' hlt hodd ↦ D.betweenCycle_lt_longest
        hG (C := C) houtside i i' hlt hodd) with hbelow | hpaths
  · obtain ⟨lengths, hcard, hreal⟩ := hbelow
    have hsub : insert C.length (lengths : Set ℕ) ⊆ oddCycleLengths G := by
      intro n hn
      rcases hn with rfl | hn
      · exact C.length_mem_oddCycleLengths
      · obtain ⟨v, c, hc, hodd, hlen⟩ := (hreal n hn).1
        subst n
        exact ⟨hodd, v, c, hc, rfl⟩
    have hnot : C.length ∉ (lengths : Set ℕ) := by
      intro hn
      exact (Nat.lt_irrefl C.length) (hreal C.length hn).2
    have hfinite : (lengths : Set ℕ).Finite := Finset.finite_toSet lengths
    have hle := Set.ncard_le_ncard hsub (oddCycleLengths_finite G)
    rw [Set.ncard_insert_of_notMem hnot hfinite] at hle
    have hle' : lengths.card + 1 ≤ (oddCycleLengths G).ncard := by
      simpa using hle
    omega
  · apply D.allOddSupportedPaths_force_many_lengths hG (C := C) houtside
    · have := D.position_pos iLast
      omega
    · exact hpaths

/-- Exact `j` odd lengths therefore rule out an exterior endpoint carrying
`2*j+1` selected spine neighbours with the two extremal portals present. -/
theorem endpointFan_impossible_of_exact_count
    (hG : TwoConnected G) {C : Erdos58.LongestOddCycle G}
    (D : EndpointFanData G x y j)
    (houtside : ∀ v ∈ D.path.support, v ∉ C.carrier)
    (hj : 1 ≤ j)
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    (hodd : (oddCycleLengths G).ncard = j) : False := by
  have := D.endpointFan_force_many_lengths hG (C := C) houtside hj hfirst hlast
  omega

end EndpointFanData

namespace Structural

/-- If a positive longest exterior path endpoint has no neighbour on the
longest odd cycle, its entire minimum degree lies on the path.  Enumerating
the first `2*j+1` such neighbours and truncating at the last one constructs
the endpoint fan ruled out above. -/
theorem noCycleNeighbors_impossible
    {C : Erdos58.LongestOddCycle G} (hG : TwoConnected G)
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hzero : P.firstCycleNeighbors.card = 0)
    (hodd : (oddCycleLengths G).ncard = j) : False := by
  classical
  let S := CaseAssembly.firstExteriorNeighborPositions P
  have hScard : S.card = P.firstExteriorNeighbors.card := by
    have hinj : Set.InjOn (fun n : ℕ ↦ P.exactAmbientPath.getVert n) S := by
      intro a ha b hb hab
      have ha' := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P a).mp ha
      have hb' := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P b).mp hb
      exact P.exactAmbientPath_isPath.getVert_injOn ha'.2.1 hb'.2.1 hab
    rw [← CaseAssembly.image_firstExteriorNeighborPositions P]
    exact (Finset.card_image_of_injOn hinj).symm
  have hmany : 2 * j + 1 ≤ S.card := by
    have hsplit :=
      P.card_firstCycleNeighbors_add_card_firstExteriorNeighbors
    rw [hzero, zero_add] at hsplit
    rw [hScard, hsplit]
    exact hdegree
  let lift : Fin (2 * j + 1) → Fin S.card := fun i ↦
    ⟨i, i.isLt.trans_le hmany⟩
  let position : Fin (2 * j + 1) → ℕ := fun i ↦
    S.orderEmbOfFin rfl (lift i)
  let iFirst : Fin (2 * j + 1) := ⟨0, by omega⟩
  let iLast : Fin (2 * j + 1) := Fin.last (2 * j)
  let m : ℕ := position iLast
  have hposition_mem (i : Fin (2 * j + 1)) : position i ∈ S := by
    exact Finset.orderEmbOfFin_mem S rfl (lift i)
  have hposition_pos (i : Fin (2 * j + 1)) : 0 < position i := by
    have hi := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (position i)).mp (hposition_mem i)
    omega
  have hposition_le_path (i : Fin (2 * j + 1)) :
      position i ≤ P.exactAmbientPath.length := by
    exact ((CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (position i)).mp (hposition_mem i)).2.1
  have hposition_injective : Function.Injective position := by
    intro a b hab
    apply Fin.ext
    have hlift : lift a = lift b := (S.orderEmbOfFin rfl).injective hab
    change (lift a).val = (lift b).val
    exact congrArg Fin.val hlift
  have hposition_m (i : Fin (2 * j + 1)) : position i ≤ m := by
    by_cases hi : i = iLast
    · simp [hi, m]
    · have hilast : i < iLast := by
        apply Fin.lt_last_iff_ne_last.mpr
        exact hi
      exact ((S.orderEmbOfFin rfl).monotone (show lift i ≤ lift iLast by
        exact_mod_cast hilast.le))
  have hmle : m ≤ P.exactAmbientPath.length := hposition_le_path iLast
  have hmle' : m ≤ P.path.length := by simpa using hmle
  let spine := P.exactAmbientPath.take m
  have hspine_length : spine.length = m := by
    simp [spine, hmle']
  have hfirst : position iFirst = 1 := by
    have hmem := hposition_mem iFirst
    have honeMem : 1 ∈ S := by
      apply (CaseAssembly.mem_firstExteriorNeighborPositions_iff P 1).mpr
      have hambientPos : 0 < P.exactAmbientPath.length := by simpa using hpos
      have hadj := P.exactAmbientPath.adj_getVert_succ (i := 0) hambientPos
      exact ⟨by omega, by omega, by simpa using hadj⟩
    have hmin := Finset.min'_le S 1 honeMem
    have hzeroValue : position iFirst = S.min' ⟨1, honeMem⟩ := by
      simpa [position, lift, iFirst] using
        Finset.orderEmbOfFin_zero (s := S) rfl (by omega)
    rw [hzeroValue]
    have hposMin := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (S.min' ⟨1, honeMem⟩)).mp (Finset.min'_mem S _)
    omega
  let D : EndpointFanData G (P.first : V) (P.exactAmbientPath.getVert m) j :=
    { path := spine.copy rfl (by simp [spine, hmle])
      isPath := (SimpleGraph.Walk.isPath_copy spine rfl
        (by simp [spine, hmle'])).2 (P.exactAmbientPath_isPath.take m)
      position := position
      position_pos := hposition_pos
      position_le := by
        intro i
        simpa [SimpleGraph.Walk.length_copy, hspine_length] using hposition_m i
      position_injective := hposition_injective
      spoke := by
        intro i
        have hadj := ((CaseAssembly.mem_firstExteriorNeighborPositions_iff P
          (position i)).mp (hposition_mem i)).2.2
        simpa [spine, SimpleGraph.Walk.getVert_copy,
          min_eq_right (hposition_m i)] using hadj }
  have houtside : ∀ v ∈ D.path.support, v ∉ C.carrier := by
    intro v hv
    have hv' : v ∈ P.exactAmbientPath.support := by
      have hvspine : v ∈ spine.support := by
        simpa only [D, SimpleGraph.Walk.support_copy] using hv
      change v ∈ (P.exactAmbientPath.take m).support at hvspine
      rw [SimpleGraph.Walk.support_take] at hvspine
      exact (List.take_prefix (m + 1) P.exactAmbientPath.support).subset hvspine
    exact P.exactAmbientPath_avoids_cycle hv'
  apply D.endpointFan_impossible_of_exact_count hG houtside (by omega)
      (iFirst := iFirst) (iLast := iLast)
  · exact hfirst
  · simp [D, position, m, iLast, hspine_length]
  · exact hodd

/-- Both endpoints of the positive longest exterior path meet the longest
cycle.  This is the first geometric consequence of the fan/linkage
argument used by the final endpoint split. -/
theorem endpointCycleNeighbors_nonempty
    {C : Erdos58.LongestOddCycle G} (hG : TwoConnected G)
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    P.firstCycleNeighbors.Nonempty ∧ P.lastCycleNeighbors.Nonempty := by
  constructor
  · apply Finset.card_pos.mp
    by_contra h
    have hzero : P.firstCycleNeighbors.card = 0 := by omega
    exact noCycleNeighbors_impossible hG hj P hpos
      (hdegree (P.first : V)) hzero hodd
  · have hreverse : P.reverse.firstCycleNeighbors.card =
        P.lastCycleNeighbors.card := by
      rfl
    apply Finset.card_pos.mp
    by_contra h
    have hzero : P.reverse.firstCycleNeighbors.card = 0 := by
      rw [hreverse]
      omega
    exact noCycleNeighbors_impossible hG hj P.reverse (by simpa using hpos)
      (hdegree (P.last : V)) hzero hodd

end Structural

end

end Erdos58
