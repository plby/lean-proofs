import ErdosProblems.Erdos1148.CoherentWordMismatch
import ErdosProblems.Erdos1148.RegularOrbitWords

/-! # Counting regular partition words in coherent orbit covers -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem regularOrbitWords_card_le_coherent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι) (C : ι → Set ModularOrbitSpace)
    (hCsub : ∀ i, C i ⊆ P.atom i) {η S ε τ : ℝ} {n : ℕ}
    (hstable : ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ), EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i)
    (hwords : ∀ (v : Fin n → ι) (F : Finset (Fin n → ι)),
      (∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) → (F.card : ℝ) ≤ Real.exp (ε * n))
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E) (hnS : (n : ℝ) ≤ S) :
    ((regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (modularMk '' E)).card : ℝ) ≤
      Real.exp (ε * n) := by
  classical
  let F := regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (modularMk '' E)
  by_cases hne : F.Nonempty
  · obtain ⟨v, hvF⟩ := hne
    obtain ⟨_, ⟨g, hg, rfl⟩, hcount, hv⟩ := (mem_regularOrbitWords P modularTimeOne
      (⋃ i, C i)ᶜ τ n (modularMk '' E) v).mp hvF
    apply hwords v F
    intro w hwF
    obtain ⟨_, ⟨h, hh, rfl⟩, _, hw⟩ := (mem_regularOrbitWords P modularTimeOne
      (⋃ i, C i)ᶜ τ n (modularMk '' E) w).mp hwF
    exact (coherent_word_mismatch_le_bad_visits P C hCsub hstable hE hnS hg hh hv hw).trans hcount
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (F.card : ℝ) ≤ _
    simp only [hzero, Finset.card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le

theorem regularOrbitWords_iUnion {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : FiniteMeasurablePartition X ι) (f : X → X) (Q : Set X) (τ : ℝ) (n : ℕ) (A : κ → Set X) :
    regularOrbitWords P f Q τ n (⋃ j, A j) =
      Finset.univ.biUnion (fun j : κ => regularOrbitWords P f Q τ n (A j)) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, hc, hword⟩ := (mem_regularOrbitWords P f Q τ n _ w).mp hw
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      (mem_regularOrbitWords P f Q τ n (A j) w).mpr ⟨x, hj, hc, hword⟩⟩
  · intro hw
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨x, hx, hc, hword⟩ := (mem_regularOrbitWords P f Q τ n (A j) w).mp hj
    exact (mem_regularOrbitWords P f Q τ n _ w).mpr ⟨x, Set.mem_iUnion.mpr ⟨j, hx⟩, hc, hword⟩

theorem regularOrbitWords_card_le_coherent_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι) (C : ι → Set ModularOrbitSpace)
    (hCsub : ∀ i, C i ⊆ P.atom i) {η S ε τ : ℝ} {n N : ℕ}
    (hstable : ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ), EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i)
    (hwords : ∀ (v : Fin n → ι) (F : Finset (Fin n → ι)),
      (∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) → (F.card : ℝ) ≤ Real.exp (ε * n))
    (B : Fin N → Set SL(2, ℝ)) (hB : ∀ i, LiftForwardClose η S (B i)) (hnS : (n : ℝ) ≤ S) :
    ((regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (⋃ j, modularMk '' B j)).card : ℝ) ≤
      (N : ℝ) * Real.exp (ε * n) := by
  classical
  rw [regularOrbitWords_iUnion]
  calc
    ((Finset.univ.biUnion (fun j : Fin N => regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n
        (modularMk '' B j))).card : ℝ) ≤
        ∑ j : Fin N, ((regularOrbitWords P modularTimeOne (⋃ i, C i)ᶜ τ n (modularMk '' B j)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin N, Real.exp (ε * n) := Finset.sum_le_sum (fun j _ =>
      regularOrbitWords_card_le_coherent P C hCsub hstable hwords (hB j) hnS)
    _ = _ := by simp

end Erdos1148.DukeArithmetic
