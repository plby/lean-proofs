import ErdosProblems.Erdos1148.PartitionStableCores
import ErdosProblems.Erdos1148.InvariantVisitCount
import ErdosProblems.Erdos1148.HammingWordBound
import ErdosProblems.Erdos1148.ModularTimeOne

/-! # Names in one coherent piece differ only at visits outside stable atom cores -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem coherent_word_mismatch_le_bad_visits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι) (C : ι → Set ModularOrbitSpace)
    (hCsub : ∀ i, C i ⊆ P.atom i) {η S : ℝ}
    (hstable : ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ), EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i)
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E) {n : ℕ} (hnS : (n : ℝ) ≤ S)
    {g h : SL(2, ℝ)} (hg : g ∈ E) (hh : h ∈ E) {v w : Fin n → ι}
    (hv : modularMk g ∈ P.orbitAtom modularTimeOne n v)
    (hw : modularMk h ∈ P.orbitAtom modularTimeOne n w) :
    (wordMismatchCount v w : ℝ) ≤ orbitVisitCount modularTimeOne (⋃ i, C i)ᶜ n (modularMk g) := by
  classical
  have hsub : Finset.univ.filter (fun j : Fin n => w j ≠ v j) ⊆
      orbitVisitPattern modularTimeOne (⋃ i, C i)ᶜ n (modularMk g) := by
    intro j hj
    simp only [orbitVisitPattern, Finset.mem_filter, Finset.mem_univ, true_and]
    change modularTimeOne^[j.val] (modularMk g) ∉ ⋃ i, C i
    intro hcore
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcore
    have hvi : v j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (P.disjoint_atom hne) (hv j) (hCsub i hi)
    let u := (g * diagonalFlow (j.val : ℝ))⁻¹ * (h * diagonalFlow (j.val : ℝ))
    have hu : EntryCloseOne η u := hE g hg h hh j.val
      ⟨Nat.cast_nonneg _, (by exact_mod_cast j.isLt.le : (j.val : ℝ) ≤ n).trans hnS⟩
    have heq : modularRightTranslate u (modularTimeOne^[j.val] (modularMk g)) =
        modularTimeOne^[j.val] (modularMk h) := by
      rw [modularTimeOne_iterate_mk, modularTimeOne_iterate_mk, modularRightTranslate_mk]
      simp only [u, mul_inv_cancel_left]
    have hwi : w j = i := by
      have hmem := hstable i _ hi u hu
      rw [heq] at hmem
      by_contra hne
      exact Set.disjoint_left.mp (P.disjoint_atom hne) (hw j) hmem
    exact (Finset.mem_filter.mp hj).2 (hwi.trans hvi.symm)
  have hcard := Finset.card_le_card hsub
  change (wordMismatchCount v w : ℝ) ≤ ((orbitVisitPattern modularTimeOne (⋃ i, C i)ᶜ n (modularMk g)).card : ℝ)
  exact_mod_cast hcard

end Erdos1148.DukeArithmetic
