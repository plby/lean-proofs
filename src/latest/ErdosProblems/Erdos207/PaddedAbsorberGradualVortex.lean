/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CardinalVortex
import ErdosProblems.Erdos207.PaddedAbsorberRootBounds

/-!
# A padded absorber at the end of an explicit gradual vortex

The coarse ambient initial loss estimates are used only on nonterminal
vortex levels.  The sharp padded-absorber root estimates control the terminal
level itself.  This separation is essential because the global absorber can
be polynomially larger than its flexible root set.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Package the padded absorber, its localization and root bounds, an
arbitrary explicit prefix-sized vortex ending at its flexible set, and the
complete initial iteration-typicality certificate. -/
theorem exists_paddedAbsorber_with_initial_gradual_typicality
    {q h m n ell : ℕ} {xi : ℝ≥0}
    (hell : 0 < ell) (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n)
    (sizes : Fin (ell + 1) → ℕ)
    (hzero : sizes 0 = n)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes)
    (hlast : sizes (Fin.last ell) = 0)
    (hxi : xi ≤ 1)
    (hDegreeOuter : ∀ j : Fin (ell + 1), j ≠ Fin.last ell →
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156 + 1 : ℕ) : ℝ≥0) ≤ xi * (sizes j : ℝ≥0))
    (hDegreeRoot : (15 : ℝ≥0) ≤ xi * (m : ℝ≥0))
    (hExtensionOuter : ∀ j : Fin (ell + 1), j ≠ Fin.last ell →
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * m) ^ 156)) : ℕ) : ℝ≥0) ≤ xi * (sizes j : ℝ≥0))
    (hExtensionRoot :
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * (m : ℝ≥0)) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n), ∃ W : Vortex (Fin n) ell,
        X.card = m ∧
        W = cardinalVortex X sizes hsmall hanti ∧
        W.U (Fin.last ell) = X ∧
        (∀ i, (W.U i).Nonempty) ∧
        HasHighGirthAbsorptionBank q H X B ∧
        HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
        (verticesOn B).card ≤
          highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
        B.card ≤
          (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * m) ^ 156) ^ 3 ∧
        HasPaddedAbsorberRootBounds q H X B ∧
        IsIterationTypical W 0
          (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)).available
          1 1 xi h := by
  obtain ⟨H, X, B, hXcard, hA, hlocal, hBsupport, hdegree,
      hBcard, hroot⟩ :=
    exists_paddedEfficientAbsorber_with_rootBounds hm hfit
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let W : Vortex (Fin n) ell := cardinalVortex X sizes hsmall hanti
  have hXnonempty : X.Nonempty := card_pos.mp (by omega)
  have hnonempty : ∀ i, (W.U i).Nonempty := by
    simpa only [W] using
      cardinalVortex_nonempty X sizes hsmall hanti hXnonempty
  have hterminal : W.U (Fin.last ell) = X := by
    simpa only [W] using
      cardinalVortex_U_last hell X sizes hsmall hanti hlast
  have htyp : IsIterationTypical W 0
      (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
    apply initial_gradual_vortex_isIterationTypical hell hterminal hroot
      hdegree hBsupport hxi
    · intro j hj
      have hsize := hDegreeOuter j hj
      have hlevel : sizes j ≤ (W.U j).card := by
        by_cases hj0 : j = 0
        · subst j
          simp only [hzero, W, cardinalVortex_U_zero, card_univ,
            Fintype.card_fin, le_refl]
        · simpa only [W] using
            sizes_le_card_cardinalVortex_U X sizes hsmall hanti hj0
      have hmul : xi * (sizes j : ℝ≥0) ≤
          xi * ((W.U j).card : ℝ≥0) := by
        gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hsize.trans hmul
    · simpa only [hXcard] using hDegreeRoot
    · intro j hj
      have hsize := hExtensionOuter j hj
      have hlevel : sizes j ≤ (W.U j).card := by
        by_cases hj0 : j = 0
        · subst j
          simp only [hzero, W, cardinalVortex_U_zero, card_univ,
            Fintype.card_fin, le_refl]
        · simpa only [W] using
            sizes_le_card_cardinalVortex_U X sizes hsmall hanti hj0
      have hmul : xi * (sizes j : ℝ≥0) ≤
          xi * ((W.U j).card : ℝ≥0) := by
        gcongr
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat] using hsize.trans hmul
    · simpa only [hXcard] using hExtensionRoot
  refine ⟨H, X, B, W, hXcard, rfl, ?_, hnonempty, hA, hlocal,
    hBsupport, hBcard, hroot, htyp⟩
  exact hterminal

end

end Erdos207
