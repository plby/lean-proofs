/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HybridVortexSchedule
import ErdosProblems.Erdos207.InitialDyadicHierarchy

/-!
# The packaged two-step hybrid vortex

The terminal flexible set remains a small common-base power, while the first
positive vortex level contains one half of the ambient vertices.  The
absorber and typicality certificates are the same as for the power package.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure InitialHybridVortexPackage
    (q h n t rootPower : ℕ) where
  base_ge_eight : 8 ≤ t
  H : SimpleGraph (Fin n)
  X : Finset (Fin n)
  B : TripleSystemOn (Fin n)
  W : Vortex (Fin n) 2
  rootCard : X.card = t ^ rootPower
  vortex_eq : W = separatedCardinalVortex H X B (hybridFreeSize n)
    (hybridFreeSize_antitone n)
  terminal : W.U (Fin.last 2) = X
  levelCard : ∀ i, i ≠ 0 →
    (W.U i).card = t ^ rootPower + hybridFreeSize n i
  nonempty : ∀ i, (W.U i).Nonempty
  absorption : HasHighGirthAbsorptionBank q H X B
  localization : HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B
  bankSupport : (verticesOn B).card ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  graphSupport : (graphSupportFinset H).card ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  graphDegree : ∀ v, H.degree v ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  bankCard : B.card ≤
    (highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156) ^ 3
  absorberEight :
    8 * (highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156) ≤ n
  rootBounds : HasPaddedAbsorberRootBounds q H X B
  rootLocalization : HasPaddedAbsorberRootLocalization q X B
  typical : IsIterationTypical W 0
    (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
    (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available
    1 1 (t : ℝ≥0)⁻¹ h

/-- Fixed coefficients eventually fit below the dyadic common base. -/
def hybridPackageBaseThreshold (q h : ℕ) : ℕ :=
  max 8 <| max (1 + 2 * powerAbsorberCoefficient q) <|
    max (1 + powerAbsorberCoefficient q) <|
      max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q) <|
        max 15 (h + h ^ 2 * 36)

lemma hybridPackageBaseThreshold_bounds (q h t : ℕ)
    (ht : hybridPackageBaseThreshold q h ≤ t) :
    8 ≤ t ∧
      1 + 2 * powerAbsorberCoefficient q ≤ t ∧
      1 + powerAbsorberCoefficient q ≤ t ∧
      (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤ t ∧
      15 ≤ t ∧ h + h ^ 2 * 36 ≤ t := by
  unfold hybridPackageBaseThreshold at ht
  omega

/-- Every large order admits the two-step hybrid package. -/
theorem eventually_exists_initialHybridVortexPackage
    (q h rootPower E : ℕ)
    (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Nonempty (InitialHybridVortexPackage q h n
        (dyadicPowerScale E n) rootPower) := by
  have hE : 0 < E := by omega
  obtain ⟨Nbase, hNbase⟩ := eventually_le_dyadicPowerScale hE
    (hybridPackageBaseThreshold q h)
  let N₀ := max Nbase 1
  refine ⟨N₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  let t := dyadicPowerScale E n
  have htBounds := hybridPackageBaseThreshold_bounds q h t
    (hNbase n (le_trans (le_max_left _ _) hn))
  have ht : 1 ≤ t := htBounds.1.trans' (by norm_num)
  have hnPower : t ^ E ≤ n :=
    dyadicPowerScale_pow_le (by omega : n ≠ 0)
  have hscalars := initial_power_hierarchy_scalars
    (q := q) (h := h) (t := t) (rootPower := rootPower)
    (step := 0) (ell := 2) (E := E) (n := n)
    ht hroot habsorberExp (by simp; omega)
    htBounds.2.1 htBounds.2.2.1 htBounds.2.2.2.1
    htBounds.2.2.2.2.1 htBounds.2.2.2.2.2 hnPower
  let C := highGirthAbsorberCardCoefficient (q + 2) *
    (2 * t ^ rootPower) ^ 156
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast (by omega : 0 < t)
  have hmulNN : (t : ℝ≥0) * (C + 1 : ℕ) ≤ (n : ℝ≥0) := by
    calc
      (t : ℝ≥0) * (C + 1 : ℕ) ≤
          (t : ℝ≥0) * ((t : ℝ≥0)⁻¹ * (n : ℝ≥0)) := by
        gcongr
        simpa only [C] using hscalars.2.2.2.1
      _ = (n : ℝ≥0) := by
        rw [← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul]
  have hmul : t * (C + 1) ≤ n := by exact_mod_cast hmulNN
  have hC8 : 8 * C ≤ n := by
    calc
      8 * C ≤ t * (C + 1) := by nlinarith [htBounds.1]
      _ ≤ n := hmul
  have htwoC : 2 * C ≤ n / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    nlinarith
  have hfreeFit : ∀ i : Fin 3, i ≠ 0 →
      hybridFreeSize n i + 2 * C ≤ n := by
    intro i hi
    have hfree : hybridFreeSize n i ≤ n / 2 := by
      unfold hybridFreeSize
      simp only [if_neg hi]
      split_ifs
      · exact Nat.le_refl _
      · exact Nat.zero_le _
    calc
      hybridFreeSize n i + 2 * C ≤ n / 2 + n / 4 :=
        Nat.add_le_add hfree htwoC
      _ ≤ n := by omega
  obtain ⟨H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
      hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
      hrootLocalization, htyp⟩ :=
    exists_paddedAbsorber_with_initial_separated_typicality
      (q := q) (h := h) (m := t ^ rootPower) (n := n) (ell := 2)
      (xi := (t : ℝ≥0)⁻¹) (by omega)
      (Nat.one_le_pow _ _ (by omega : 0 < t))
      hscalars.1 (hybridFreeSize n) (hybridFreeSize_antitone n)
      (hybridFreeSize_last n) (by simpa only [C] using hfreeFit)
      hscalars.2.2.1 hscalars.2.2.2.1 hscalars.2.2.2.2.1
      hscalars.2.2.2.2.2.1 hscalars.2.2.2.2.2.2
  exact ⟨⟨htBounds.1, H, X, B, W, hX, hW, hterminal, hlevel,
    hnonempty, hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hC8,
    hrootBounds, hrootLocalization, htyp⟩⟩

end

end Erdos207
