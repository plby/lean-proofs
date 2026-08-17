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
import ErdosProblems.Erdos58.Structural.IndependentGap
import ErdosProblems.Erdos58.StructuralAlt
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# The one-odd-length structural theorem: independent exterior

This file proves the complete independent-exterior branch of the structural
theorem at `j = 1`.  The only input beyond the original graph hypotheses is
that the vertices outside a designated longest odd cycle are independent.

The proof is the cyclic-gap argument.  An exterior vertex has three distinct
neighbours on the rim.  For every directed gap `d` between two of these
neighbours, the two hub cycles have lengths `d + 2` and `|C| - d + 2`.
Exactly one is odd, hence its length is `|C|`; consequently every gap is
either `2` or `|C| - 2`.  Sorting three neighbours and summing their three
cyclic gaps forces `|C| = 3`.  The already checked cut-path argument then
shows that the exterior consists of one vertex, and the degree hypothesis
forces the graph to be `K4`.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.K1

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma oddCycleLengths_eq_singleton
    (C : LongestOddCycle G)
    (hodd : (oddCycleLengths G).ncard = 1) :
    oddCycleLengths G = {C.length} := by
  obtain ⟨n, hn⟩ := Set.ncard_eq_one.mp hodd
  have hmem := C.length_mem_oddCycleLengths
  rw [hn] at hmem
  have hne : n = C.length := by simpa using hmem.symm
  simpa [hne] using hn

/-- Under a unique-odd-length hypothesis, the directed cyclic gap between
two neighbours of one exterior vertex is either two or two less than the
length of the longest odd cycle. -/
private lemma hub_gap_eq_two_or_length_sub_two
    (C : LongestOddCycle G)
    (hodd : (oddCycleLengths G).ncard = 1)
    {t : V} (ht : t ∈ C.carrierᶜ)
    {x y : Fin C.length} (hxy : y ≠ x)
    (htx : G.Adj t (C.copy x)) (hty : G.Adj t (C.copy y)) :
    (y - x).val = 2 ∨ (y - x).val = C.length - 2 := by
  letI : NeZero C.length := ⟨by omega⟩
  let d : ℕ := (y - x).val
  have hdpos : 0 < d := by
    rw [Nat.pos_iff_ne_zero]
    intro hd
    apply hxy
    have hzero : y - x = 0 := Fin.ext hd
    simpa [sub_eq_zero] using hzero
  have hdlt : d < C.length := (y - x).isLt
  have hsum : d + (x - y).val = C.length := by
    dsimp [d]
    by_cases hle : x ≤ y
    · have hlt : x < y := lt_of_le_of_ne hle hxy.symm
      rw [Fin.sub_val_of_le hle, Fin.coe_sub_iff_lt.mpr hlt]
      omega
    · have hlt : y < x := lt_of_not_ge hle
      rw [Fin.coe_sub_iff_lt.mpr hlt, Fin.sub_val_of_le hlt.le]
      omega
  have hsingleton : oddCycleLengths G = {C.length} :=
    oddCycleLengths_eq_singleton C hodd
  rcases Nat.even_or_odd d with hdeven | hdodd
  · have hrevodd : Odd (x - y).val := by
      rw [← Nat.not_even_iff_odd]
      intro hrevEven
      have : Even C.length := by
        rw [← hsum]
        exact hdeven.add hrevEven
      exact (Nat.not_even_iff_odd.mpr C.odd) this
    obtain ⟨v, p, hpcycle, hplen⟩ :=
      Erdos58.Structural.IndependentGap.hubArc_cycleAtLength
        C ht hxy.symm hty htx
    have hpodd : Odd p.length := by
      rw [hplen]
      exact hrevodd.add_even (by simp)
    have hpmem : p.length ∈ oddCycleLengths G :=
      ⟨hpodd, v, p, hpcycle, rfl⟩
    rw [hsingleton] at hpmem
    have heq : (x - y).val + 2 = C.length := by
      simpa [hplen] using hpmem
    left
    omega
  · obtain ⟨v, p, hpcycle, hplen⟩ :=
      Erdos58.Structural.IndependentGap.hubArc_cycleAtLength
        C ht hxy htx hty
    have hpodd : Odd p.length := by
      rw [hplen]
      exact hdodd.add_even (by simp)
    have hpmem : p.length ∈ oddCycleLengths G :=
      ⟨hpodd, v, p, hpcycle, rfl⟩
    rw [hsingleton] at hpmem
    have heq : d + 2 = C.length := by
      simpa [hplen, d] using hpmem
    right
    omega

/-- If the exterior of a longest odd cycle is independent, minimum degree
three and a unique odd cycle length force that cycle to be a triangle. -/
theorem length_eq_three_of_independent_exterior
    (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 3 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = 1) :
    C.length = 3 := by
  classical
  have hexterior : C.carrierᶜ.Nonempty := by
    by_contra hnot
    have hcover : ∀ v : V, v ∈ C.carrier := by
      intro v
      by_contra hv
      exact hnot ⟨v, hv⟩
    have hcard : C.length = Fintype.card V := by
      rw [← C.ncard_carrier]
      have hcarrier : C.carrier = Set.univ := Set.eq_univ_of_forall hcover
      simp [hcarrier]
    letI : NeZero C.length := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.three_le)⟩
    let rim := Erdos58.Structural.IndependentGap.rimWalk C (0 : Fin C.length)
    have hham : rim.IsHamiltonianCycle := by
      rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
      exact ⟨Erdos58.Structural.IndependentGap.rimWalk_isCycle C 0,
        by simpa [rim, hcard] using
          Erdos58.Structural.IndependentGap.rimWalk_length C (0 : Fin C.length)⟩
    have hmany : 2 ≤ (oddCycleLengths G).ncard := by
      have hrimodd : Odd rim.length := by
        simpa [rim] using C.odd
      simpa using
        (Erdos58.StructuralAlt.oddCycleLengths_ge_succ_of_hamiltonian_odd_cycle_degree
          hham hrimodd (j := 1) (by omega) (by simpa using hdegree (C.copy 0)))
    omega
  obtain ⟨t, ht⟩ := hexterior
  let N : Finset (Fin C.length) :=
    Finset.univ.filter fun i ↦ G.Adj t (C.copy i)
  have himage : N.image C.copy = G.neighborFinset t := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hiN, rfl⟩ := Finset.mem_image.mp hv
      exact (SimpleGraph.mem_neighborFinset (G := G) (v := t) (w := C.copy i)).mpr
        (Finset.mem_filter.mp hiN).2
    · intro hv
      have hadj : G.Adj t v :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := t) (w := v)).mp hv
      have hvcarrier : v ∈ C.carrier := by
        by_contra hvcarrier
        exact hind ht hvcarrier hadj.ne hadj
      obtain ⟨i, rfl⟩ := hvcarrier
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  have hNcard : N.card = G.degree t := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himage]
    exact (Finset.card_image_of_injective N C.copy.injective).symm
  have hthreeN : 3 ≤ N.card := by simpa [hNcard] using hdegree t
  obtain ⟨S, hSN, hScard⟩ := Finset.exists_subset_card_eq hthreeN
  let e : Fin 3 ↪o Fin C.length := S.orderEmbOfFin hScard
  let x : Fin C.length := e 0
  let y : Fin C.length := e 1
  let z : Fin C.length := e 2
  have hxy : x < y := e.strictMono (by decide)
  have hyz : y < z := e.strictMono (by decide)
  have hxN : x ∈ N := hSN (S.orderEmbOfFin_mem hScard 0)
  have hyN : y ∈ N := hSN (S.orderEmbOfFin_mem hScard 1)
  have hzN : z ∈ N := hSN (S.orderEmbOfFin_mem hScard 2)
  have htx : G.Adj t (C.copy x) := (Finset.mem_filter.mp hxN).2
  have hty : G.Adj t (C.copy y) := (Finset.mem_filter.mp hyN).2
  have htz : G.Adj t (C.copy z) := (Finset.mem_filter.mp hzN).2
  have hgap1 := hub_gap_eq_two_or_length_sub_two C hodd ht hxy.ne' htx hty
  have hgap2 := hub_gap_eq_two_or_length_sub_two C hodd ht hyz.ne' hty htz
  have hzx : x ≠ z := (hxy.trans hyz).ne
  have hgap3 := hub_gap_eq_two_or_length_sub_two C hodd ht hzx htz htx
  have hval1 : (y - x).val = y.val - x.val := by
    exact Fin.sub_val_of_le hxy.le
  have hval2 : (z - y).val = z.val - y.val := by
    exact Fin.sub_val_of_le hyz.le
  have hval3 : (x - z).val = C.length - z.val + x.val := by
    rw [Fin.coe_sub_iff_lt.mpr (hxy.trans hyz)]
    have hzlt := z.isLt
    have hxz := hxy.trans hyz
    omega
  have hsumgaps :
      (y.val - x.val) + (z.val - y.val) +
        (C.length - z.val + x.val) = C.length := by
    have hzlt := z.isLt
    omega
  rw [hval1] at hgap1
  rw [hval2] at hgap2
  rw [hval3] at hgap3
  obtain ⟨k, hk⟩ := C.odd
  rcases hgap1 with h1 | h1 <;>
    rcases hgap2 with h2 | h2 <;>
      rcases hgap3 with h3 | h3 <;> omega

/-- The complete independent-exterior branch of the `j = 1` Gyárfás
structural theorem. -/
theorem independent_exterior_is_K4
    (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 3 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = 1) :
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin 4)) := by
  classical
  have hlength : C.length = 2 * 1 + 1 := by
    simpa using length_eq_three_of_independent_exterior C hind hdegree hodd
  letI : NeZero C.length := ⟨by omega⟩
  let i0 : Fin C.length := ⟨0, by omega⟩
  let i1 : Fin C.length := ⟨1, by omega⟩
  let i2 : Fin C.length := ⟨2, by omega⟩
  have hi12 : (SimpleGraph.cycleGraph C.length).Adj i1 i2 := by
    rw [SimpleGraph.cycleGraph_adj']
    right
    rw [Fin.sub_val_of_le (by simp [i1, i2])]
    simp [i1, i2]
  have hadj12 : G.Adj (C.copy i1) (C.copy i2) := C.copy.toHom.map_rel' hi12
  let cutPath : CycleCutPath C := {
    cut := C.copy i0
    start := C.copy i1
    finish := C.copy i2
    walk := hadj12.toWalk
    isPath := hadj12.isPath_toWalk
    support_subset := by
      intro v hv
      simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons,
        List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨i1, rfl⟩
      · exact ⟨i2, rfl⟩
    cut_mem := ⟨i0, rfl⟩
    cut_notMem_support := by
      intro hmem
      simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons,
        List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h
      ·
        have hi : i0 = i1 := C.copy.injective h
        exact (by simpa [i0, i1] using hi : False)
      ·
        have hi : i0 = i2 := C.copy.injective h
        exact (by simpa [i0, i2] using hi : False)
    length_add_two := by simp [hlength] }
  have hrigid : IndependentExteriorRigidity 1 C :=
    independentExteriorRigidity_of_length_and_cutPath
      hind hlength (by simpa using hdegree) cutPath
  have hcomplete : G = SimpleGraph.completeGraph V :=
    independent_exterior_forces_complete_of_rigidity
      (C := C) (j := 1) (by simpa using hdegree) hrigid
  have hcard : Fintype.card V = 4 := by
    simpa using hrigid.card_vertex_eq
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  subst G
  exact ⟨SimpleGraph.Iso.completeGraph e⟩

end

end Erdos58.K1
