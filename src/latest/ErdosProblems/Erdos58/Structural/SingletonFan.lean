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
import ErdosProblems.Erdos58.Structural.FanLinkage
import ErdosProblems.Erdos58.Structural.K1Boundary

/-!
# The common-singleton endpoint fan

This file joins the endpoint-fan construction to the cleaned escape path
used when the two endpoints of a longest exterior path have one common
neighbour on the longest odd cycle.
-/

open Set SimpleGraph
open scoped SimpleGraph

namespace Erdos58.Structural.K1Boundary

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : EndpointCount.LongestOddCycle G}
variable {S : ExteriorPath C} {x : V}

namespace EscapePath

private lemma odd_replace_of_same_mod {a r s : ℕ}
    (ha : Odd (a + r)) (hrs : r % 2 = s % 2) : Odd (a + s) := by
  rw [Nat.odd_iff] at ha ⊢
  omega

/-- A whole equal-parity, length-injective family of routes through the
exterior path closes, using one fixed complementary arc of the odd cycle,
to the same number of distinct odd cycle lengths. -/
theorem many_odd_lengths_of_pathFamily
    (P : EscapePath C S x) (hxC : x ∈ C.cycle.support) {r : ℕ}
    (F : PathFamily G P.exteriorEnd x (Fin r))
    (hFsupport : ∀ i v, v ∈ (F.path i).support →
      v = x ∨ v ∈ S.walk.support) :
    r ≤ (oddCycleLengths G).ncard := by
  classical
  by_cases hr : r = 0
  · omega
  let i₀ : Fin r := ⟨0, by omega⟩
  let c : G.Walk x x := C.cycle.rotate x hxC
  have hc : c.IsCycle := C.isCycle.rotate hxC
  have hyc : P.cycleEnd ∈ c.support :=
    (C.cycle.mem_support_rotate_iff x hxC).mpr P.cycleEnd_mem
  let Q₁ : G.Walk x P.cycleEnd := c.takeUntil P.cycleEnd hyc
  let Qback : G.Walk P.cycleEnd x := c.dropUntil P.cycleEnd hyc
  let Q₂ : G.Walk x P.cycleEnd := Qback.reverse
  have hQ₁ : Q₁.IsPath := hc.isPath_takeUntil hyc
  have hQ₁nonempty : ¬Q₁.Nil := by
    intro hnil
    exact P.cycleEnd_ne_deleted
      ((c.nil_takeUntil hyc).mp hnil).symm
  have hQback : Qback.IsPath :=
    Walk.IsCycle.isPath_of_append_right hQ₁nonempty (by
      simpa only [Q₁, Qback, c.take_spec hyc] using hc)
  have hQ₂ : Q₂.IsPath := hQback.reverse
  have hQ₁support : ∀ v ∈ Q₁.support, v ∈ C.cycle.support := by
    intro v hv
    exact (C.cycle.mem_support_rotate_iff x hxC).mp
      (c.support_takeUntil_subset_support hyc hv)
  have hQ₂support : ∀ v ∈ Q₂.support, v ∈ C.cycle.support := by
    intro v hv
    apply (C.cycle.mem_support_rotate_iff x hxC).mp
    apply c.support_dropUntil_subset_support hyc
    simpa [Q₂, Qback, Walk.support_reverse] using hv
  have hQsum : Q₁.length + Q₂.length = C.cycle.length := by
    calc
      Q₁.length + Q₂.length = (Q₁.append Qback).length := by
        simp [Q₂, Walk.length_append]
      _ = c.length := congrArg Walk.length (c.take_spec hyc)
      _ = C.cycle.length := by simp [c]
  let a₁ := Q₁.length + P.path.length
  let a₂ := Q₂.length + P.path.length
  have hsame (i : Fin r) :
      (F.path i₀).length % 2 = (F.path i).length % 2 :=
    F.sameParity i₀ i
  rcases Nat.even_or_odd (a₁ + (F.path i₀).length) with heven | hodd
  · have hodd₂ : Odd (a₂ + (F.path i₀).length) := by
      have hCodd := C.odd_length
      dsimp [a₁, a₂] at heven ⊢
      grind
    let f : Fin r → ℕ := fun i ↦ a₂ + (F.path i).length
    apply ncard_oddCycleLengths_ge_of_injective (G := G) f
    · intro i k hik
      apply F.length_injective
      dsimp [f] at hik
      exact Nat.add_left_cancel hik
    · intro i
      exact odd_replace_of_same_mod hodd₂ (hsame i)
    · intro i
      exact P.cycleAtLength_of_route hxC (F.path i) (F.isPath i)
        (hFsupport i) Q₂ hQ₂ hQ₂support
  · let f : Fin r → ℕ := fun i ↦ a₁ + (F.path i).length
    apply ncard_oddCycleLengths_ge_of_injective (G := G) f
    · intro i k hik
      apply F.length_injective
      dsimp [f] at hik
      exact Nat.add_left_cancel hik
    · intro i
      exact odd_replace_of_same_mod hodd (hsame i)
    · intro i
      exact P.cycleAtLength_of_route hxC (F.path i) (F.isPath i)
        (hFsupport i) Q₁ hQ₁ hQ₁support

end EscapePath

end

end Erdos58.Structural.K1Boundary

namespace Erdos58.Structural.SingletonFan

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

open Erdos58 EndpointFanData

/-
/-- The endpoint fan obtained by appending the unique common cycle
neighbour to the longest exterior path.  The `external` portals are exactly
all portals except the appended terminal one. -/
structure SingletonEndpointFan {C₀ : Erdos58.LongestOddCycle G}
    (P : LongestExteriorPath C₀) (z : V) (j : ℕ) where
  data : EndpointFanData G (P.first : V) z j
  external : Finset (Fin (2 * j + 1))
  iFirst : Fin (2 * j + 1)
  iLast : Fin (2 * j + 1)
  external_eq : external = Finset.univ.erase iLast
  first_mem : iFirst ∈ external
  first_position : data.position iFirst = 1
  last_position : data.position iLast = data.path.length
  before_last : ∀ i ∈ external,
    data.position i < data.position iLast
  path_eq : data.path =
    P.exactAmbientPath.concat
      (show G.Adj (P.last : V) z from by assumption)

/-- Select `2*j` exterior neighbours of the first endpoint, retaining the
compulsory position `1`, and append the common cycle neighbour as the last
portal. -/
theorem exists_singletonEndpointFan
    {C₀ : Erdos58.LongestOddCycle G} {j : ℕ} (hj : 1 ≤ j)
    (P : LongestExteriorPath C₀) (hpos : 0 < P.path.length)
    (z : V) (hzC : z ∈ C₀.carrier)
    (hfirstAdj : G.Adj (P.first : V) z)
    (hlastAdj : G.Adj (P.last : V) z)
    (hmany : 2 * j ≤ P.firstExteriorNeighbors.card) :
    Nonempty (SingletonEndpointFan P z j) := by
  classical
  let S₀ := CaseAssembly.firstExteriorNeighborPositions P
  have hS₀card : S₀.card = P.firstExteriorNeighbors.card := by
    have hinj : Set.InjOn (fun n : ℕ ↦ P.exactAmbientPath.getVert n) S₀ := by
      intro a ha b hb hab
      have ha' := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P a).mp ha
      have hb' := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P b).mp hb
      exact P.exactAmbientPath_isPath.getVert_injOn ha'.2.1 hb'.2.1 hab
    rw [← CaseAssembly.image_firstExteriorNeighborPositions P]
    exact (Finset.card_image_of_injOn hinj).symm
  have hS₀many : 2 * j ≤ S₀.card := by omega
  let iLast : Fin (2 * j + 1) := Fin.last (2 * j)
  let iFirst : Fin (2 * j + 1) := ⟨0, by omega⟩
  have hiFirstNe : iFirst ≠ iLast := by
    intro h
    have := congrArg Fin.val h
    simp [iFirst, iLast] at this
    omega
  let extIndex (i : Fin (2 * j + 1)) (hi : i ≠ iLast) : Fin S₀.card :=
    ⟨i, by
      have hil : (i : ℕ) < 2 * j := by
        have hiBound := i.isLt
        have hiNe : (i : ℕ) ≠ 2 * j := by
          intro heq
          apply hi
          apply Fin.ext
          simpa [iLast] using heq
        omega
      exact hil.trans_le hS₀many⟩
  let extPosition (i : Fin (2 * j + 1)) (hi : i ≠ iLast) : ℕ :=
    S₀.orderEmbOfFin rfl (extIndex i hi)
  let path : G.Walk (P.first : V) z := P.exactAmbientPath.concat hlastAdj
  have hpathLength : path.length = P.exactAmbientPath.length + 1 := by
    simp [path]
  have hzNot : z ∉ P.exactAmbientPath.support := by
    intro hz
    exact P.exactAmbientPath_avoids_cycle hz hzC
  have hpathIsPath : path.IsPath :=
    P.exactAmbientPath_isPath.concat hzNot hlastAdj
  let position (i : Fin (2 * j + 1)) : ℕ :=
    if hi : i = iLast then path.length else extPosition i hi
  have hextMem (i : Fin (2 * j + 1)) (hi : i ≠ iLast) :
      extPosition i hi ∈ S₀ :=
    Finset.orderEmbOfFin_mem S₀ rfl (extIndex i hi)
  have hextPos (i : Fin (2 * j + 1)) (hi : i ≠ iLast) :
      0 < extPosition i hi := by
    have hmem := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (extPosition i hi)).mp (hextMem i hi)
    omega
  have hextLe (i : Fin (2 * j + 1)) (hi : i ≠ iLast) :
      extPosition i hi ≤ P.exactAmbientPath.length :=
    ((CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (extPosition i hi)).mp (hextMem i hi)).2.1
  have hpositionLast : position iLast = path.length := by
    simp [position]
  have hpositionPos (i : Fin (2 * j + 1)) : 0 < position i := by
    by_cases hi : i = iLast
    · subst i
      rw [hpositionLast, hpathLength]
      omega
    · simpa [position, hi] using hextPos i hi
  have hpositionLe (i : Fin (2 * j + 1)) : position i ≤ path.length := by
    by_cases hi : i = iLast
    · subst i
      simp [hpositionLast]
    · rw [position, dif_neg hi, hpathLength]
      exact (hextLe i hi).trans (by omega)
  have hpositionInj : Function.Injective position := by
    intro a b hab
    by_cases ha : a = iLast
    · subst a
      by_cases hb : b = iLast
      · exact hb.symm
      · have hbLe := hextLe b hb
        simp [position, hb, hpathLength] at hab
        omega
    · by_cases hb : b = iLast
      · subst b
        have haLe := hextLe a ha
        simp [position, ha, hpathLength] at hab
        omega
      · simp only [position, dif_neg ha, dif_neg hb] at hab
        have heq : extIndex a ha = extIndex b hb :=
          (S₀.orderEmbOfFin rfl).injective hab
        apply Fin.ext
        exact congrArg Fin.val heq
  have honeMem : 1 ∈ S₀ := by
    apply (CaseAssembly.mem_firstExteriorNeighborPositions_iff P 1).mpr
    have hlen : 1 ≤ P.exactAmbientPath.length := by simpa using hpos
    have hadj := P.exactAmbientPath.adj_getVert_succ (i := 0) hlen
    exact ⟨by omega, hlen, by simpa using hadj⟩
  have hfirstPosition : position iFirst = 1 := by
    rw [position, dif_neg hiFirstNe]
    have hzero : extIndex iFirst hiFirstNe = ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [extPosition, hzero]
    have hmin := Finset.min'_le S₀ 1 honeMem
    have hzeroValue := Finset.orderEmbOfFin_zero
      (s := S₀) rfl (by omega)
    rw [hzeroValue]
    have hminPos := (CaseAssembly.mem_firstExteriorNeighborPositions_iff P
      (S₀.min' ⟨1, honeMem⟩)).mp (Finset.min'_mem S₀ _)
    omega
  let D : EndpointFanData G (P.first : V) z j :=
    { path := path
      isPath := hpathIsPath
      position := position
      position_pos := hpositionPos
      position_le := hpositionLe
      position_injective := hpositionInj
      spoke := by
        intro i
        by_cases hi : i = iLast
        · subst i
          simpa [position, path] using hfirstAdj
        · have hadj := ((CaseAssembly.mem_firstExteriorNeighborPositions_iff P
            (extPosition i hi)).mp (hextMem i hi)).2.2
          simpa [position, hi, path, Walk.getVert_append',
            hextLe i hi] using hadj }
  let external : Finset (Fin (2 * j + 1)) := Finset.univ.erase iLast
  have hbefore (i : Fin (2 * j + 1)) (hi : i ∈ external) :
      D.position i < D.position iLast := by
    have hine : i ≠ iLast := (Finset.mem_erase.mp hi).1
    change position i < position iLast
    rw [position, dif_neg hine, hpositionLast, hpathLength]
    have := hextLe i hine
    omega
  refine ⟨{
    data := D
    external := external
    iFirst := iFirst
    iLast := iLast
    external_eq := rfl
    first_mem := by simp [external, hiFirstNe]
    first_position := hfirstPosition
    last_position := by exact hpositionLast
    before_last := hbefore
    path_eq := rfl }⟩
-/

/-- For `j ≥ 2`, a positive longest exterior path cannot have a literal
singleton as the common cycle-neighbour set of its two endpoints.  The
proof appends that neighbour to the exterior path and applies the exact
three-way endpoint-fan split. -/
theorem equalSingletonEndpoint_impossible
    {C₀ : Erdos58.LongestOddCycle G} (hG : TwoConnected G)
    {j : ℕ} (hj : 2 ≤ j)
    (P : LongestExteriorPath C₀) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j)
    (hsame :
      Erdos58.Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C₀) (P.first : V) =
        Erdos58.Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C₀) (P.last : V))
    (hone :
      (Erdos58.Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C₀) (P.first : V)).card = 1) : False := by
  classical
  let N := Erdos58.Structural.cycleNeighborPositions
    (toEndpointLongestOddCycle C₀) (P.first : V)
  have hNcard : N.card = 1 := by simpa [N] using hone
  have hN : N.Nonempty := Finset.card_pos.mp (by omega)
  let base : Fin C₀.walk.length :=
    ⟨hN.choose, by simpa [N, toEndpointLongestOddCycle] using hN.choose.isLt⟩
  have hbaseMem : base ∈ N := by
    change hN.choose ∈ N
    exact hN.choose_spec
  have hbaseFirst : G.Adj (P.first : V) (C₀.walk.getVert base) := by
    exact (Erdos58.Structural.mem_cycleNeighborPositions
      (toEndpointLongestOddCycle C₀) (P.first : V) base).mp hbaseMem
  have hbaseLast : G.Adj (P.last : V) (C₀.walk.getVert base) := by
    apply (Erdos58.Structural.mem_cycleNeighborPositions
      (toEndpointLongestOddCycle C₀) (P.last : V) base).mp
    rw [← hsame]
    exact hbaseMem
  have hfirstCycleCard : P.firstCycleNeighbors.card = 1 := by
    rw [← CaseAssembly.card_boundaryCycleNeighborPositions_first P]
    exact hone
  have hmany : 2 * j ≤
      (CaseAssembly.firstExteriorNeighborPositions P).card :=
    CaseAssembly.two_mul_le_firstExteriorPositions_of_singleton P
      (hdegree (P.first : V)) hfirstCycleCard
  let D : EndpointFanData G (P.first : V) (C₀.walk.getVert base) j :=
    CaseAssembly.commonNeighborAugmentedFan P base hbaseFirst hbaseLast hmany
  let iFirst : Fin (2 * j + 1) := 0
  let iLast : Fin (2 * j + 1) := Fin.last (2 * j)
  let I : Finset (Fin (2 * j + 1)) := Finset.univ.erase iLast
  have hfirstMem : iFirst ∈ I := by
    simp [I, iFirst, iLast]
    omega
  have hfirst : D.position iFirst = 1 := by
    simpa [D, iFirst] using
      CaseAssembly.commonNeighborAugmentedFan_position_zero
        (j := j) (by omega) P hpos base hbaseFirst hbaseLast hmany
  have hlast : D.position iLast = D.path.length := by
    simpa [D, iLast] using
      CaseAssembly.commonNeighborAugmentedFan_position_last
        (j := j) P base hbaseFirst hbaseLast hmany
  have hDlength : D.path.length = P.exactAmbientPath.length + 1 := by
    change (CaseAssembly.commonNeighborAugmentedSpine
      P base hbaseLast).length = P.exactAmbientPath.length + 1
    exact CaseAssembly.commonNeighborAugmentedSpine_length P base hbaseLast
  have hbefore : ∀ i ∈ I, D.position i < D.position iLast := by
    intro i hi
    have hine : i ≠ iLast := (Finset.mem_erase.mp hi).1
    have hle := D.position_le i
    have hnePos : D.position i ≠ D.position iLast := by
      intro heq
      exact hine (D.position_injective heq)
    rw [hlast]
    omega
  let L := toEndpointLongestOddCycle C₀
  let S := P.toBoundaryExteriorPath hpos
  have hbaseC : C₀.walk.getVert base ∈ L.cycle.support := by
    exact C₀.walk.getVert_mem_support base
  obtain ⟨E⟩ := K1Boundary.TwoConnected.exists_escapePath hG L S hbaseC
  have hbetween : ∀ i, i ∈ I → ∀ i', i' ∈ I →
      ∀ (hii' : D.position i < D.position i'),
        Odd (D.betweenCycle i i' hii').length →
          (D.betweenCycle i i' hii').length < C₀.length := by
    intro i hi i' hi' hii' hcycleOdd
    let X : ExteriorOddCycle C₀ :=
      { base := (P.first : V)
        cycle := D.betweenCycle i i' hii'
        isCycle := D.betweenCycle_isCycle i i' hii'
        odd_length := hcycleOdd
        support_outside := by
          intro v hv
          rw [EndpointFanData.betweenCycle,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_concat] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact P.first.property
          · rcases List.mem_append.mp hv with hv | hv
            · obtain ⟨r, hget, hr⟩ :=
                SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
              have hr' : r ≤ D.position i' - D.position i := by
                simpa using hr
              have hindex : D.position i + r ≤ P.exactAmbientPath.length := by
                have hi'Before := hbefore i' hi'
                rw [hlast, hDlength] at hi'Before
                omega
              apply P.exactAmbientPath_avoids_cycle
              apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
              refine ⟨D.position i + r, ?_, hindex⟩
              have hgetD : D.path.getVert (D.position i + r) = v := by
                simpa [EndpointFanData.segment,
                  SimpleGraph.Walk.drop_getVert, min_eq_right hr'] using hget
              change (CaseAssembly.commonNeighborAugmentedSpine
                P base hbaseLast).getVert (D.position i + r) = v at hgetD
              rw [CaseAssembly.commonNeighborAugmentedSpine,
                SimpleGraph.Walk.concat_eq_append,
                SimpleGraph.Walk.getVert_append', if_pos hindex] at hgetD
              exact hgetD
            · simp only [List.mem_singleton] at hv
              subst v
              exact P.first.property }
    exact Structural.outside_odd_cycle_is_shorter_of_twoConnected hG X
  rcases D.externalMixed_or_terminalOpposite_or_allOddSupported
      (by omega) I (iFirst := iFirst) (iLast := iLast) rfl
      hfirstMem hfirst hlast hbefore hbetween with hbelow | hmanyCycles | hpaths
  · obtain ⟨lengths, hcard, hreal⟩ := hbelow
    have hsub : insert C₀.length (lengths : Set ℕ) ⊆ oddCycleLengths G := by
      intro n hn
      rcases hn with rfl | hn
      · exact C₀.length_mem_oddCycleLengths
      · obtain ⟨v, c, hc, hco, rfl⟩ := (hreal n hn).1
        exact ⟨hco, v, c, hc, rfl⟩
    have hnot : C₀.length ∉ (lengths : Set ℕ) := by
      intro hn
      exact (Nat.lt_irrefl C₀.length) (hreal C₀.length hn).2
    have hle := Set.ncard_le_ncard hsub (oddCycleLengths_finite G)
    rw [Set.ncard_insert_of_notMem hnot (Finset.finite_toSet lengths)] at hle
    have hle' : lengths.card + 1 ≤ (oddCycleLengths G).ncard := by
      simpa using hle
    have : j + 1 ≤ (oddCycleLengths G).ncard := by omega
    omega
  · have hmanyN := EndpointFanData.ncard_oddCycleLengths_ge_of_realizes
      hmanyCycles
    omega
  · obtain ⟨a, ha, hale⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp E.exteriorEnd_mem
    have haD : D.path.getVert a = E.exteriorEnd := by
      change (CaseAssembly.commonNeighborAugmentedSpine
        P base hbaseLast).getVert a = E.exteriorEnd
      rw [CaseAssembly.commonNeighborAugmentedSpine,
        SimpleGraph.Walk.concat_eq_append,
        SimpleGraph.Walk.getVert_append', if_pos]
      · exact ha
      · simpa [S, LongestExteriorPath.toBoundaryExteriorPath] using hale
    have haLe : a ≤ D.path.length := by
      have : a ≤ P.exactAmbientPath.length := by
        simpa [S, LongestExteriorPath.toBoundaryExteriorPath] using hale
      rw [hDlength]
      omega
    have haNe : a ≠ D.path.length := by
      intro heq
      have heqv := congrArg D.path.getVert heq
      rw [haD, SimpleGraph.Walk.getVert_length] at heqv
      have hcontra : E.exteriorEnd ∈ L.cycle.support := by
        rw [heqv]
        exact hbaseC
      exact E.exteriorEnd_not_cycle hcontra
    obtain ⟨PF₀⟩ := hpaths haLe (le_refl D.path.length) haNe
    have PF : EndpointFanData.FanSupportedPathFamily D E.exteriorEnd
        (C₀.walk.getVert base) (j + 1) := by
      simpa only [haD, SimpleGraph.Walk.getVert_length] using PF₀
    have hPFsupport : ∀ i v, v ∈ (PF.family.path i).support →
        v = C₀.walk.getVert base ∨ v ∈ S.walk.support := by
      intro i v hv
      have hvD := PF.support_subset i v hv
      change v ∈ (CaseAssembly.commonNeighborAugmentedSpine
        P base hbaseLast).support at hvD
      rw [CaseAssembly.commonNeighborAugmentedSpine,
        SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hvD
      rcases hvD with hvD | rfl
      · right
        simpa [S, LongestExteriorPath.toBoundaryExteriorPath] using hvD
      · exact Or.inl rfl
    have hmanyN := E.many_odd_lengths_of_pathFamily hbaseC
      PF.family hPFsupport
    omega

end

end Erdos58.Structural.SingletonFan
