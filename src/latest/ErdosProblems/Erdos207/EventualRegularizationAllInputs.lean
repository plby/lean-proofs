/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualRegularizationOrderInput

/-! # One threshold supplies all forbidden-order inputs simultaneously -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_sourceRegularizationAllInputs
    (q K Y D A v w L R : ℕ) (C : ℝ≥0) (hC : 0 < C)
    (hD : K + 1 ≤ D) (hA : D + 1 ≤ A) (hv : K + 1 ≤ v)
    (hLmass : w + 2 ≤ L) (hLdensity : w * (q - 3) + 1 ≤ L)
    (hLsquare : 2 * D ≤ L) (hLy : D + Y ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I] {ell : ℕ},
      ∀ (W : Vortex V ell) (e : I ↪ TripleOn V),
      (∀ i, (e i).1 ⊆ W.U (Fin.last ell)) →
      ∀ (localFamily : ℕ → Finset (Finset I)) (F : ℕ → ForbiddenFamilyOn V)
        (y z B : ℕ → ℝ≥0) (sigma : ℝ≥0),
      (∀ j ∈ Icc 4 q, ∀ E ∈ localFamily j, E.card = j - 2) →
      (∀ j ∈ Icc 4 q, SourceVortexWellSpread W j (F j) (y j) (z j)) →
      t ^ L ≤ W.terminalSize → Fintype.card V ≤ t ^ R →
      1 / (t : ℝ≥0) ^ w ≤ sigma → sigma ≤ 1 / (t : ℝ≥0) ^ v →
      (∀ j ∈ Icc 4 q, B j ≤ (t : ℝ≥0) ^ K) →
      (∀ j ∈ Icc 4 q, y j ≤ (t : ℝ≥0) ^ Y) →
      sigma * (W.terminalSize : ℝ≥0) ^ 3 / C ≤ Fintype.card I →
      (∀ j ∈ Icc 4 q, (finiteHypergraphMaxDegree (localFamily j) : ℝ≥0) ≤
        B j * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3)) →
      q ≤ W.terminalSize ∧
      ∀ j ∈ Icc 4 q, SourceRegularizationOrderInput W j (localFamily j) (F j) (8192 * t) t (y j) (z j)
        ((t : ℝ≥0) ^ A) ((t : ℝ≥0) ^ D) sigma C (B j) := by
  classical
  let Orders := {j : ℕ // j ∈ Icc 4 q}
  letI : Fintype Orders := by
    dsimp only [Orders]
    infer_instance
  have hsingle (j : Orders) := eventually_sourceRegularizationOrderInput j.val K Y D A v w L R C
    (mem_Icc.mp j.property).1 hC hD hA hv hLmass
    ((Nat.add_le_add_right (Nat.mul_le_mul_left w (Nat.sub_le_sub_right (mem_Icc.mp j.property).2 3)) 1).trans hLdensity)
    hLsquare hLy
  let threshold : Orders → ℕ := fun j ↦ (hsingle j).choose
  let T := max (q + 1) (univ.sup threshold)
  refine ⟨T, by dsimp [T]; omega, ?_⟩
  intro t ht V I _ _ _ _ _ ell W e hsupport localFamily F y z B sigma huniform hspread hn hN
    hsigmaLo hsigmaHi hB hy hmass hdegree
  have htq : q + 1 ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := by omega
  have htPower : t ≤ t ^ L := by
    simpa only [pow_one] using Nat.pow_le_pow_right ht1 (show 1 ≤ L by omega)
  refine ⟨(show q ≤ t by omega).trans (htPower.trans hn), ?_⟩
  intro j hj
  let jj : Orders := ⟨j, hj⟩
  have hthreshold : threshold jj ≤ t :=
    (le_sup (f := threshold) (mem_univ jj)).trans ((le_max_right _ _).trans ht)
  exact (hsingle jj).choose_spec.2 t hthreshold W e hsupport (localFamily j) (F j) (y j) (z j) (B j) sigma
    (huniform j hj) (hspread j hj) hn hN hsigmaLo hsigmaHi (hB j hj) (hy j hj) hmass (hdegree j hj)

end

end Erdos207
