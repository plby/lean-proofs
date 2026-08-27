/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SeparatedCardinalVortex

/-!
# A padded absorber inside an absorber-separated gradual vortex

This is the quantitatively useful initial package.  The absorber's nonroot
support is omitted from every positive vortex level.  Consequently the
ambient level alone pays the polynomial absorber loss, while every inner
level uses the sharp root constants.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- Construct the padded absorber and an explicit separated vortex, together
with exact positive-level cardinalities and the complete initial typicality
certificate. -/
theorem exists_paddedAbsorber_with_initial_separated_typicality
    {q h m n ell : ℕ} {xi : ℝ≥0}
    (hell : 0 < ell) (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n)
    (freeSize : Fin (ell + 1) → ℕ)
    (hanti : Antitone freeSize)
    (hlast : freeSize (Fin.last ell) = 0)
    (hfreeFit : ∀ i, i ≠ 0 →
      freeSize i + 2 *
        (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156) ≤ n)
    (hxi : xi ≤ 1)
    (hDegreeAmbient :
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156 + 1 : ℕ) : ℝ≥0) ≤ xi * (n : ℝ≥0))
    (hDegreeInner : (15 : ℝ≥0) ≤ xi * (m : ℝ≥0))
    (hExtensionAmbient :
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * m) ^ 156)) : ℕ) : ℝ≥0) ≤ xi * (n : ℝ≥0))
    (hExtensionInner :
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * (m : ℝ≥0)) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n), ∃ W : Vortex (Fin n) ell,
        X.card = m ∧
        W = separatedCardinalVortex H X B freeSize hanti ∧
        W.U (Fin.last ell) = X ∧
        (∀ i, i ≠ 0 → (W.U i).card = m + freeSize i) ∧
        (∀ i, (W.U i).Nonempty) ∧
        HasHighGirthAbsorptionBank q H X B ∧
        HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
        (verticesOn B).card ≤
          highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
        (graphSupportFinset H).card ≤
          highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
        (∀ v, H.degree v ≤
          highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
        B.card ≤
          (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * m) ^ 156) ^ 3 ∧
        HasPaddedAbsorberRootBounds q H X B ∧
        HasPaddedAbsorberRootLocalization q X B ∧
        IsIterationTypical W 0
          (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)).available
          1 1 xi h := by
  let C := highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156
  obtain ⟨H, X, B, hXcard, hA, hlocal, hBsupport, hdegree,
      hBcard, hroot, hrootLocal⟩ :=
    exists_paddedEfficientAbsorber_with_rootBounds_and_rootLocalization hm hfit
  have hcoefPos : 0 < highGirthAbsorberCardCoefficient (q + 2) := by
    unfold highGirthAbsorberCardCoefficient cycleCoverCardConstant
    positivity
  have hcoef : 1 ≤ highGirthAbsorberCardCoefficient (q + 2) := hcoefPos
  have hmC : m ≤ C := by
    have hmTwo : m ≤ 2 * m := by omega
    have htwoPos : 1 ≤ 2 * m := by omega
    have hpower : 2 * m ≤ (2 * m) ^ 156 := by
      simpa only [pow_one] using
        (pow_le_pow_right' htwoPos (by omega : 1 ≤ 156))
    calc
      m ≤ 2 * m := hmTwo
      _ ≤ (2 * m) ^ 156 := hpower
      _ = 1 * (2 * m) ^ 156 := by simp
      _ ≤ highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156 := Nat.mul_le_mul_right _ hcoef
      _ = C := rfl
  have hHsupport : (graphSupportFinset H).card ≤ C := by
    exact (card_le_card
      (graphSupportFinset_subset_verticesOn_of_absorptionBank hA)).trans
        hBsupport
  let W : Vortex (Fin n) ell :=
    separatedCardinalVortex H X B freeSize hanti
  have hcapacity : ∀ i, i ≠ 0 →
      freeSize i ≤ (absorberFreeVertices H X B).card := by
    intro i hi
    apply freeSize_le_card_absorberFreeVertices hA
      (by simpa only [hXcard, C] using hmC)
      (by simpa only [C] using hBsupport)
    simpa only [C] using hfreeFit i hi
  have hlevelCard : ∀ i, i ≠ 0 → (W.U i).card = m + freeSize i := by
    intro i hi
    rw [← hXcard]
    simpa only [W] using
      card_separatedCardinalVortex_of_capacity H X B freeSize hanti hi
        (hcapacity i hi)
  have hterminal : W.U (Fin.last ell) = X := by
    simpa only [W] using
      separatedCardinalVortex_U_last hell H X B freeSize hanti hlast
  have hXnonempty : X.Nonempty := card_pos.mp (by omega)
  have hnonempty : ∀ i, (W.U i).Nonempty := by
    simpa only [W] using
      separatedCardinalVortex_nonempty H X B freeSize hanti hXnonempty
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have htyp : IsIterationTypical W 0
      (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
    apply initial_separated_vortex_isIterationTypical
      (X := X) (B := B)
      (fun j hj ↦ by
        simpa only [W] using
          separatedCardinalVortex_separated H X B freeSize hanti hj)
      hroot hdegree hBsupport hxi
    · simpa only [C, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        using hDegreeAmbient
    · intro j hj
      have hmul : xi * (m : ℝ≥0) ≤ xi * ((W.U j).card : ℝ≥0) := by
        gcongr
        rw [hlevelCard j hj]
        omega
      exact hDegreeInner.trans hmul
    · simpa only [C, Fintype.card_fin, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat] using hExtensionAmbient
    · intro j hj
      have hmul : xi * (m : ℝ≥0) ≤ xi * ((W.U j).card : ℝ≥0) := by
        gcongr
        rw [hlevelCard j hj]
        omega
      exact hExtensionInner.trans hmul
  exact ⟨H, X, B, W, hXcard, rfl, hterminal, hlevelCard, hnonempty,
    hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hroot,
    hrootLocal, htyp⟩

end

end Erdos207
