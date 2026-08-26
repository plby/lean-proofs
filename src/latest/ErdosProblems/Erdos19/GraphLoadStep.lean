import ErdosProblems.Erdos19.ReservoirLoads
import ErdosProblems.Erdos19.GraphDegreeAccounting

/-! # Updating reservoir loads after adding a matching -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def reservoirLoad (U R : _root_.SimpleGraph V) (v : V) : ℕ :=
  ((U ⊓ R).neighborSet v).ncard

theorem reservoir_inter_support_subset {G : _root_.SimpleGraph V}
    (R : _root_.SimpleGraph V) (M N : G.Subgraph) (T : Finset V)
    (hdis : Disjoint M.edgeSet R.edgeSet)
    (hnew : ∀ e ∈ N.edgeSet \ M.edgeSet, ∀ x ∈ e, x ∈ T) :
    (N.spanningCoe ⊓ R).support ⊆ (T : Set V) := by
  intro v hv
  obtain ⟨w, hvw⟩ := hv
  have heN : s(v, w) ∈ N.edgeSet := Subgraph.mem_edgeSet.mpr hvw.1
  have heR : s(v, w) ∈ R.edgeSet := by simpa only [mem_edgeSet] using hvw.2
  have heM : s(v, w) ∉ M.edgeSet := fun h ↦ Set.disjoint_left.mp hdis h heR
  exact hnew _ ⟨heN, heM⟩ v (by simp)

theorem reservoirLoad_step {G : _root_.SimpleGraph V}
    (U R : _root_.SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (hdis : Disjoint U M.spanningCoe) (T : Finset V)
    (hsupport : (M.spanningCoe ⊓ R).support ⊆ (T : Set V)) (K : ℕ)
    (hbal : IsLoadBalanced K (reservoirLoad U R))
    (havoid : Disjoint T (overloadedVertices K (reservoirLoad U R))) :
    IsLoadBalanced K (reservoirLoad (U ⊔ M.spanningCoe) R) ∧
      totalLoad (reservoirLoad (U ⊔ M.spanningCoe) R) ≤ totalLoad (reservoirLoad U R) + T.card := by
  classical
  let load := reservoirLoad U R
  let next := reservoirLoad (U ⊔ M.spanningCoe) R
  have heq : ∀ v, next v = load v + ((M.spanningCoe ⊓ R).neighborSet v).ncard :=
    reservoir_load_sup_matching U R M hdis
  have hmono : ∀ v, load v ≤ next v := by
    intro v
    rw [heq]
    exact Nat.le_add_right _ _
  have hone : ∀ v, next v ≤ load v + 1 := by
    intro v
    rw [heq]
    exact Nat.add_le_add_left (matching_reservoir_increment_le_one R M hM v) _
  have hfixed : ∀ v ∉ T, next v = load v := by
    intro v hv
    have hempty : (M.spanningCoe ⊓ R).neighborSet v = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hv (hsupport ⟨w, hw⟩)
    rw [heq, hempty, Set.ncard_empty, Nat.add_zero]
  have hnew : ∀ v, load v < next v → v ∉ overloadedVertices K load := by
    intro v hv hvbad
    have hvT : v ∈ T := by
      by_contra hvT
      rw [hfixed v hvT] at hv
      exact (Nat.lt_irrefl _ hv)
    exact Finset.disjoint_left.mp havoid hvT hvbad
  exact ⟨hbal.step hmono hone hnew, totalLoad_step_le_add_card T hone hfixed⟩

#print axioms reservoirLoad_step

end Erdos19
