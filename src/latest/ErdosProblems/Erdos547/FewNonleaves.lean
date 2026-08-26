import ErdosProblems.Erdos547.SmallCoreEscape
import ErdosProblems.Erdos547.ParentBunch
import ErdosProblems.Erdos547.EscapeRamsey
import ErdosProblems.Erdos547.NumericalParameters

/-!
# The leaf-rich near-core case, including large leaf bunches
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem ramsey_of_near_core_few_nonleaves {m : ℕ} (hm : coreDeficitDivisor ≤ m)
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree)
    (R : SimpleGraph (Fin (2 * m))) (A : Finset (Fin (2 * m))) (hA : A.Nonempty)
    (hnear : ∀ v ∈ A, (1 - 1 / coreDeficitDivisor : ℝ) * m ≤ degreeIn R A v)
    (hcore : Fintype.card (treeCore T) < m / (4 * corePairDivisor)) : T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  let d := m / coreDeficitDivisor + 1
  let k := m / corePairDivisor
  let t := m / coreCleaningDivisor
  have hmpos : 0 < m := by norm_num [coreDeficitDivisor] at hm; omega
  have hTcard : 3 ≤ Fintype.card (Fin (m + 1)) := by
    simp only [Fintype.card_fin]
    norm_num [coreDeficitDivisor] at hm
    omega
  obtain ⟨hk, _, hroom, hbudget, _, _, hkd, _⟩ := near_core_integer_bounds m hm
  obtain ⟨hsize, hdk, hsmall, hd128⟩ :=
    small_core_integer_bounds m (Fintype.card (treeCore T)) hm hcore
  have hdegreeA : ∀ v ∈ A, m ≤ degreeIn R A v + d := by
    intro v hv
    exact deficit_rounding m (degreeIn R A v) (hnear v hv)
  obtain ⟨parent, hp⟩ := exists_treeCore_parent T hT hTcard
  by_cases hbig : ∃ p : treeCore T, m ≤ 4 * parentWeight parent p
  · obtain ⟨p, hpbig⟩ := hbig
    obtain ⟨Q, r, _, hparent, hcount⟩ := exists_parent_bunch_complement T (treeCore T) parent hp p
    refine ramsey_of_near_core_of_leaf_bunch hmpos hd128 T hT Q r hparent ?_ R A hA hdegreeA
    rw [hcount]
    exact hpbig
  · let : Fintype (A : Set (Fin (2 * m))) := FinsetCoe.fintype A
    let : Nonempty (A : Set (Fin (2 * m))) := (Finset.coe_nonempty.mpr hA).to_subtype
    let : DecidableEq (A : Set (Fin (2 * m))) := fun a b ↦ Classical.propDecidable (a = b)
    have hlocal : ∀ z : (A : Set (Fin (2 * m))), m ≤ (R.induce (A : Set _)).degree z + d := by
      intro z
      rw [← degreeIn_eq_induce_degree R A z]
      exact hdegreeA z.val z.property
    rcases ramsey_or_induced_escape T hT R (A : Set _) d k t hk hroom hbudget hlocal with
      hmono | hescape
    · exact hmono
    have hweights : ∀ p : treeCore T, parentWeight parent p ≤ m / 4 := by
      intro p
      have hp' : ¬ m ≤ 4 * parentWeight parent p := fun h ↦ hbig ⟨p, h⟩
      omega
    have hcopy : T ⊑ R.induce (A : Set _) := by
      refine isContained_of_small_core_and_escape T (R.induce (A : Set _)) (treeCore T)
        (isTree_treeCore T hT hTcard) parent hp m d k (m / 4)
        (Fintype.card_fin (m + 1)) ?_ ?_ ?_ ?_ ?_ hweights hlocal hescape
      · exact hsize
      · exact hdk
      · exact hkd
      · exact hsmall
      · omega
    obtain ⟨f⟩ := hcopy
    exact Or.inl ⟨(SimpleGraph.Copy.induce R (A : Set _)).comp f⟩

end Erdos547

#print axioms Erdos547.ramsey_of_near_core_few_nonleaves
