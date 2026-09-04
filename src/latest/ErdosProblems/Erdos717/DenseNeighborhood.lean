/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The numerical heart of the Thomas--Wollan minimal-counterexample argument:
large common neighborhoods and the incident-edge bound force a small closed
neighborhood of minimum degree at least `8k`.
-/

import ErdosProblems.Erdos717.MassedContraction
import ErdosProblems.Erdos717.ThomasWollan

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

open DenseMinor

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The spanning graph obtained by retaining precisely the edges incident
with `S`. -/
def incidentGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ S ∨ v ∈ S)
  symm.symm u v h := ⟨h.1.symm, h.2.symm⟩

instance incidentGraph.instDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (incidentGraph G S).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ (u ∈ S ∨ v ∈ S)))

lemma incidentGraph_edgeFinset_card (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    (incidentGraph G S).edgeFinset.card = incidentEdges G S := by
  classical
  unfold incidentEdges
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_filter]
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [incidentGraph]
      constructor
      · rintro ⟨huv, hu | hv⟩
        · refine ⟨huv, ?_⟩
          intro hsub
          exact (Finset.mem_sdiff.mp (hsub (by simp))).2 hu
        · refine ⟨huv, ?_⟩
          intro hsub
          exact (Finset.mem_sdiff.mp (hsub (by simp))).2 hv
      · rintro ⟨huv, hnot⟩
        refine ⟨huv, ?_⟩
        by_contra hneither
        push Not at hneither
        apply hnot
        intro z hz
        simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hneither.1⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hneither.2⟩

lemma incidentGraph_degree_eq_of_mem (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) {v : V} (hv : v ∈ S) :
    (incidentGraph G S).degree v = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1
  ext w
  rw [(incidentGraph G S).mem_neighborFinset, G.mem_neighborFinset]
  change (G.Adj v w ∧ (v ∈ S ∨ w ∈ S)) ↔ G.Adj v w
  tauto

lemma sum_degrees_on_le_twice_incidentEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    ∑ v ∈ S, G.degree v ≤ 2 * incidentEdges G S := by
  classical
  let H := incidentGraph G S
  calc
    ∑ v ∈ S, G.degree v = ∑ v ∈ S, H.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      symm
      exact incidentGraph_degree_eq_of_mem G S hv
    _ ≤ ∑ v, H.degree v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * incidentEdges G S := by rw [incidentGraph_edgeFinset_card]

namespace MassedCounterexample

variable {k : ℕ}

/-- Every vertex outside the terminal set has a neighbor. -/
def NoIsolatedOutside (C : MassedCounterexample k) : Prop :=
  ∀ v, v ∉ C.X → ∃ u, C.G.Adj u v

lemma outside_nonempty (C : MassedCounterexample k) :
    (Finset.univ \ C.X).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hcard : Fintype.card C.V - C.X.card = 0 := by
    have := congrArg Finset.card h
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C.X),
      Finset.card_univ] at this
    simpa using this
  have hinc : incidentEdges C.G (Finset.univ \ C.X) = 0 := by
    rw [h]
    exact incidentEdges_empty C.G
  have := C.massed.1
  rw [hcard, hinc] at this
  omega

lemma degree_ge_eight_mul_of_outside
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) (hk : 1 ≤ k)
    (hcond : C.ContractConditionTwo)
    (hnoiso : C.NoIsolatedOutside) {v : C.V} (hv : v ∉ C.X) :
    8 * k ≤ C.G.degree v := by
  classical
  obtain ⟨u, huv⟩ := hnoiso v hv
  have hcommon := C.commonNeighbor_card_ge_sub_one_of_contractConditionTwo
    hmin F hk hcond huv hv
  let A := commonNeighborFinset C.G u v
  have huA : u ∉ A := by
    simp [A, commonNeighborFinset, C.G.mem_neighborFinset]
  have hsub : insert u A ⊆ C.G.neighborFinset v := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa [C.G.mem_neighborFinset] using huv.symm
    · have hz' := (Finset.mem_inter.mp hz).2
      exact hz'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem huA] at hcard
  change 8 * k - 1 ≤ A.card at hcommon
  simpa [C.G.card_neighborFinset_eq_degree] using (show 8 * k ≤
    (C.G.neighborFinset v).card by omega)

lemma outside_card_ge_three
    (C : MassedCounterexample k) (hk : 1 ≤ k)
    (hmin : C.IsLexMinimal) (F : FailedPairing C)
    (hcond : C.ContractConditionTwo) (hnoiso : C.NoIsolatedOutside) :
    3 ≤ (Finset.univ \ C.X).card := by
  classical
  obtain ⟨v, hvO⟩ := C.outside_nonempty
  have hvX : v ∉ C.X := (Finset.mem_sdiff.mp hvO).2
  have hdeg := C.degree_ge_eight_mul_of_outside hmin F hk hcond hnoiso hvX
  have hlt := C.G.degree_lt_card_verts v
  have hXcard := C.card_le
  have hOcard : (Finset.univ \ C.X).card =
      Fintype.card C.V - C.X.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C.X),
      Finset.card_univ]
  have hXleV := Finset.card_le_univ C.X
  omega

/-- Some outside vertex has degree at most `16k`. -/
theorem exists_outside_degree_le_sixteen_mul
    (C : MassedCounterexample k) (hk : 1 ≤ k)
    (hmin : C.IsLexMinimal) (F : FailedPairing C)
    (hcond : C.ContractConditionTwo)
    (hnoiso : C.NoIsolatedOutside) :
    ∃ v ∉ C.X, C.G.degree v ≤ 16 * k := by
  classical
  let O := Finset.univ \ C.X
  have hOthree : 3 ≤ O.card :=
    C.outside_card_ge_three hk hmin F hcond hnoiso
  obtain ⟨v₀, hv₀O⟩ := C.outside_nonempty
  have hv₀X : v₀ ∉ C.X := (Finset.mem_sdiff.mp hv₀O).2
  obtain ⟨u₀, hu₀v₀⟩ := hnoiso v₀ hv₀X
  have hsumUpper : ∑ v ∈ O, C.G.degree v ≤
      2 * (8 * k * O.card + 1) := by
    calc
      ∑ v ∈ O, C.G.degree v ≤
          2 * incidentEdges C.G O :=
        sum_degrees_on_le_twice_incidentEdges C.G O
      _ ≤ 2 * (8 * k * O.card + 1) := by
        gcongr
        have hout := C.outsideEdges_le_mass_add_one
          hmin F hk hcond hu₀v₀ (Or.inr hv₀X)
        have hOcard : O.card = Fintype.card C.V - C.X.card := by
          simp only [O, Finset.card_sdiff_of_subset (Finset.subset_univ C.X),
            Finset.card_univ]
        rwa [hOcard]
  by_contra h
  push Not at h
  have hsumLower : (16 * k + 1) * O.card ≤
      ∑ v ∈ O, C.G.degree v := by
    calc
      (16 * k + 1) * O.card = ∑ v ∈ O, (16 * k + 1) := by
        simp [mul_comm]
      _ ≤ ∑ v ∈ O, C.G.degree v :=
        Finset.sum_le_sum fun v hv => h v (Finset.mem_sdiff.mp hv).2
  have hlower' : 2 * (8 * k * O.card) + O.card ≤
      ∑ v ∈ O, C.G.degree v := by
    convert hsumLower using 1 <;> ring
  have hupper' : ∑ v ∈ O, C.G.degree v ≤
      2 * (8 * k * O.card) + 2 := by
    convert hsumUpper using 1 <;> ring
  omega

/-- The closed neighborhood of the minimum-degree outside vertex is a
small induced graph of minimum degree `8k`, hence contains a `k`-linked
subgraph. -/
theorem exists_kLinkedSubgraph_of_contractConditionTwo
    (C : MassedCounterexample k) (hk : 1 ≤ k)
    (hmin : C.IsLexMinimal) (F : FailedPairing C)
    (hcond : C.ContractConditionTwo)
    (hnoiso : C.NoIsolatedOutside) :
    Nonempty (ThomasWollan.KLinkedSubgraph C.G k) := by
  classical
  obtain ⟨v, hvX, hvdeg⟩ :=
    C.exists_outside_degree_le_sixteen_mul hk hmin F hcond hnoiso
  let N := insert v (C.G.neighborFinset v)
  let NS : Set C.V := (N : Set C.V)
  let fintypeNS : Fintype NS := Subtype.fintype fun x => x ∈ NS
  have hvN : v ∈ N := by simp [N]
  have hNcard : N.card ≤ 16 * k + 1 := by
    have hvnot : v ∉ C.G.neighborFinset v := by simp
    rw [show N.card = C.G.degree v + 1 by
      simp [N, Finset.card_insert_of_notMem hvnot,
        C.G.card_neighborFinset_eq_degree]]
    omega
  have hNnonempty : Nonempty NS := ⟨⟨v, hvN⟩⟩
  have hdegree : ∀ z : NS,
      8 * k ≤ (C.G.induce NS).degree z := by
    intro z
    by_cases hzv : (z : C.V) = v
    · have hneighbors : C.G.neighborSet (z : C.V) ⊆ NS := by
        intro w hzw
        have hvw : C.G.Adj v w := by simpa [hzv] using hzw
        exact Finset.mem_insert_of_mem (by simpa [C.G.mem_neighborFinset] using hvw)
      calc
        8 * k ≤ C.G.degree (z : C.V) := by
          have hd :=
            C.degree_ge_eight_mul_of_outside hmin F hk hcond hnoiso hvX
          rw [← hzv] at hd
          exact hd
        _ = (C.G.induce NS).degree z :=
          (C.G.degree_induce_of_neighborSet_subset hneighbors).symm
    · have hzAdj : C.G.Adj (z : C.V) v := by
        have hzN : (z : C.V) ∈ N := z.property
        simp only [N, Finset.mem_insert] at hzN
        have hzmem := hzN.resolve_left hzv
        exact ((C.G.mem_neighborFinset v (z : C.V)).mp hzmem).symm
      have hcommon := C.commonNeighbor_card_ge_sub_one_of_contractConditionTwo
        hmin F hk hcond hzAdj hvX
      let A := commonNeighborFinset C.G (z : C.V) v
      have hvA : v ∉ A := by
        simp [A, commonNeighborFinset, C.G.mem_neighborFinset]
      have hsub : insert v A ⊆ C.G.neighborFinset (z : C.V) ∩ N := by
        intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact Finset.mem_inter.mpr
            ⟨by simpa [C.G.mem_neighborFinset] using hzAdj, hvN⟩
        · have hw' := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr ⟨hw'.1,
            Finset.mem_insert_of_mem hw'.2⟩
      have hcardsub := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hvA] at hcardsub
      have hmap := C.G.map_neighborFinset_induce z
      have hdegEq : (C.G.induce NS).degree z =
          (C.G.neighborFinset (z : C.V) ∩ N).card := by
        rw [← card_neighborFinset_eq_degree]
        have hc := congrArg Finset.card hmap
        have hNS : NS.toFinset = N := by
          ext w
          simp [NS]
        rw [hNS] at hc
        simpa only [Finset.card_map] using hc
      rw [hdegEq]
      change 8 * k - 1 ≤ A.card at hcommon
      omega
  obtain ⟨L⟩ := ThomasWollan.exists_kLinkedSubgraph_of_minDegree_card
    (C.G.induce NS) k hk hNnonempty
    (by simpa [NS] using hNcard) hdegree
  exact ⟨{
    W := L.W
    fintypeW := L.fintypeW
    H := L.H
    inclusion := L.inclusion.trans (SimpleGraph.Embedding.induce NS)
    enough_vertices := L.enough_vertices
    linked := L.linked
  }⟩

end MassedCounterexample
end ThomasWollanMassed
end Erdos717
