import ErdosProblems.Erdos745.TreeComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite size-window and disjoint-set sums -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

/-- All vertex sets whose cardinality belongs to a prescribed finite window. -/
def vertexWindow (n : ℕ) (I : Finset ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter fun S ↦ S.card ∈ I

theorem sum_vertexWindow (n : ℕ) (I : Finset ℕ) (f : Finset (Fin n) → ℝ) :
    ∑ S ∈ vertexWindow n I, f S =
      ∑ k ∈ I, ∑ S ∈ Finset.univ.powersetCard k, f S := by
  simpa only [vertexWindow, Finset.powersetCard_eq_filter] using
    (Finset.sum_fiberwise_eq_sum_filter Finset.univ.powerset I Finset.card f).symm

theorem treeComponentCount_eq_window {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset ℕ) :
    treeComponentCount G I = ((vertexWindow n I).filter (IsTreeComponentSet G)).card := by
  rw [treeComponentCount_eq_vertexSet_count]
  congr 1
  ext S
  simp only [vertexWindow, Finset.mem_filter]
  tauto

theorem filter_powersetCard_disjoint {n : ℕ} (S : Finset (Fin n)) (l : ℕ) :
    (Finset.univ.powersetCard l).filter (Disjoint S) = Sᶜ.powersetCard l := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  have hsub : U ⊆ Sᶜ ↔ Disjoint S U := by
    rw [Finset.disjoint_left]
    simp only [Finset.subset_iff, Finset.mem_compl]
    aesop
  rw [hsub, and_comm]

theorem card_powersetCard_disjoint {n : ℕ} (S : Finset (Fin n)) (l : ℕ) :
    ((Finset.univ.powersetCard l).filter (Disjoint S)).card = (n - S.card).choose l := by
  rw [filter_powersetCard_disjoint, Finset.card_powersetCard, Finset.card_compl,
    Fintype.card_fin]

theorem sum_offDiag_eq {α : Type*} [DecidableEq α] (s : Finset α) (f : α × α → ℝ) :
    ∑ x ∈ s.offDiag, f x = ∑ u ∈ s, ∑ v ∈ s, if u ≠ v then f (u, v) else 0 := by
  have heq : s.offDiag = (s ×ˢ s).filter (fun x ↦ x.1 ≠ x.2) := by
    ext x
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [heq, Finset.sum_filter, Finset.sum_product]

end

end Erdos745
