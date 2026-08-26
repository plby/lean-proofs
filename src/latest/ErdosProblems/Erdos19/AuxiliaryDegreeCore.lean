import ErdosProblems.Erdos19.MatchingFamilyDegrees
import ErdosProblems.Erdos19.MatchingCoreColoring
import ErdosProblems.Erdos19.AuxiliaryTargets

/-! # An independent residual degree core from auxiliary parity defects -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem residual_matching_core_of_auxiliary_targets {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (m : ℕ) (hm : m < Fintype.card V)
    (C : Fin m → Set V) (f : Fin m ↪ V) (M : Fin m → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching ∧ (M i).verts = auxiliaryTarget (C i) (f i))
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hbudget : ∀ v, (G.neighborSet v).ncard +
      (∑ i : Fin m, if v ∈ C i then 1 else 0) ≤ Fintype.card V - 1)
    (hcover : ∀ x ∈ Set.range f, ∀ y ∈ Set.range f, x ≠ y →
      (⨆ i, (M i).spanningCoe).Adj x y) :
    (∀ v, (G \ ⨆ i, (M i).spanningCoe).degree v ≤ Fintype.card V - m) ∧
    Vizing.HasMatchingDegreeCore (G \ ⨆ i, (M i).spanningCoe) (Fintype.card V - m) := by
  let U := ⨆ i, (M i).spanningCoe
  let R := G \ U
  have hUG : U ≤ G := iSup_le (fun i ↦ (M i).spanningCoe_le)
  have hpointwise : ∀ v, (R.neighborSet v).ncard + m ≤
      Fintype.card V - 1 + if v ∈ Set.range f then 1 else 0 := by
    intro v
    have hmiss := auxiliaryTarget_omission_bound C f f.injective v
    have hmiss' : (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤
        (∑ i : Fin m, if v ∈ C i then 1 else 0) + if v ∈ Set.range f then 1 else 0 := by
      simpa only [fun i ↦ (hM i).2] using hmiss
    have hcount := matching_family_degree_add_absences G M (fun i ↦ (hM i).1) hdis v
    simp only [Fintype.card_fin] at hcount
    have hsplit : (R.neighborSet v).ncard + (U.neighborSet v).ncard = (G.neighborSet v).ncard := by
      rw [neighborSet_sdiff]
      exact Set.ncard_sdiff_add_ncard_of_subset (fun _ h ↦ hUG h)
    have hb := hbudget v
    change (U.neighborSet v).ncard + _ = m at hcount
    omega
  have hdegree : ∀ v, (R.neighborSet v).ncard ≤ Fintype.card V - m := by
    intro v
    have h := hpointwise v
    split_ifs at h <;> omega
  have hhigh : ∀ v, (R.neighborSet v).ncard = Fintype.card V - m → v ∈ Set.range f := by
    intro v hv
    by_contra hnot
    have h := hpointwise v
    rw [if_neg hnot] at h
    omega
  constructor
  · intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdegree v
  · intro x y z hx hxy _ hy _
    have hx' : (R.neighborSet x).ncard = Fintype.card V - m := by
      simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hx
    have hy' : (R.neighborSet y).ncard = Fintype.card V - m := by
      simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hy
    exact (hxy.2 (hcover x (hhigh x hx') y (hhigh y hy') hxy.1.ne)).elim

#print axioms residual_matching_core_of_auxiliary_targets

end Erdos19
