/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The finite Thomas--Wollan consequence and topological density theorem. -/

import ErdosProblems.Erdos717.MassedLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

/-- Every `2k`-connected finite graph with at least `8k|V|` edges is
`k`-linked. -/
theorem isKLinked_of_connected_edges
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hconn : Erdos718.IsKConnected G (2 * k))
    (hE : 8 * k * Fintype.card V ≤ G.edgeSet.ncard) :
    Erdos718.IsKLinked G k := by
  classical
  by_cases hk : k = 0
  · subst k
    exact Erdos718.isKLinked_zero G
  have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hE' : 8 * k * Fintype.card V ≤ G.edgeFinset.card := by
    rw [Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
    exact hE
  intro X hXfinite hXcard
  let Xf : Finset V := hXfinite.toFinset
  have hXfcard : Xf.card = X.ncard := by
    exact (Set.ncard_eq_toFinset_card X hXfinite).symm
  obtain ⟨Y, hXfY, _hYuniv, hYcard⟩ := Finset.exists_subsuperset_card_eq
    (s := Xf) (t := (Finset.univ : Finset V)) (Finset.subset_univ Xf)
    (hXfcard.trans_le hXcard) (Nat.le_of_lt hconn.1)
  have hmassed := isEightKMassed_of_connected_edges hkpos hconn hE' Y hYcard
  have hYlinked :=
    MassedCounterexample.isLinkedSet_of_isEightKMassed hkpos
      hYcard.le hmassed
  have hset : (Xf : Set V) = X := hXfinite.coe_toFinset
  have hXY : X ⊆ (Y : Set V) := by
    rw [← hset]
    exact hXfY
  intro I _ terminal hterminal
  obtain ⟨L⟩ := hYlinked I terminal (hterminal.trans hXY)
  exact ⟨{
    path := L.path
    isPath := L.isPath
    avoids := fun i => (L.avoids i).mono_right hXY
    disjoint := L.disjoint
  }⟩

/-- Bollobás--Thomason / Komlós--Szemerédi density theorem with the
explicit constant supplied by the Mader-core and Thomas--Wollan arguments:
`5 r² |V|` edges force a subdivision of `K_r`. -/
theorem containsCliqueSubdivision_of_five_mul_sq_mul_card_le_edges
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (hrV : 0 < Fintype.card V)
    (hE : 5 * (r * r) * Fintype.card V ≤ G.edgeFinset.card) :
    Erdos718.ContainsCliqueSubdivision G r := by
  classical
  rcases lt_trichotomy r 2 with hr | hr | hr
  · have hrsmall : r = 0 ∨ r = 1 := by omega
    rcases hrsmall with rfl | rfl
    · exact Erdos718.containsCliqueSubdivision_zero G
    · letI : Nonempty V := Fintype.card_pos_iff.mp hrV
      exact Erdos718.containsCliqueSubdivision_one_of_nonempty G
  · subst r
    have hr : 1 ≤ (2 : ℕ) := by omega
    obtain ⟨S, hconn, hresidual⟩ :=
      Erdos718.MaderPrototype.exists_induced_dense_core_with_robust_residual
        G 2 (by omega) hrV hE
    let H := G.induce (S : Set V)
    have hsub : Erdos718.ContainsCliqueSubdivision H 2 := by
      apply Erdos718.conditional_core_assembly hr hconn
      · intro branch
        exact (hresidual branch).1
      · intro branch
        exact (hresidual branch).2
      · intro branch hc he
        exact isKLinked_of_connected_edges _ _ hc he
    exact hsub.liftInduce
  · have hr2 : 2 ≤ r := hr.le
    have hr1 : 1 ≤ r := hr2.trans' (by omega)
    obtain ⟨S, hconn, hresidual⟩ :=
      Erdos718.MaderPrototype.exists_induced_dense_core_with_robust_residual
        G r hr2 hrV hE
    let H := G.induce (S : Set V)
    have hsub : Erdos718.ContainsCliqueSubdivision H r := by
      apply Erdos718.conditional_core_assembly hr1 hconn
      · intro branch
        exact (hresidual branch).1
      · intro branch
        exact (hresidual branch).2
      · intro branch hc he
        exact isKLinked_of_connected_edges _ _ hc he
    exact hsub.liftInduce

end ThomasWollanMassed
end Erdos717
