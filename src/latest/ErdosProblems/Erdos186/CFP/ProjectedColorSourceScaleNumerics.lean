/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ScaledCertificateNumerics
import ErdosProblems.Erdos186.CFP.BlockedCertificateNumerics
import ErdosProblems.Erdos186.CFP.ProjectedProperizationScale

/-!
# Per-colour scale bounds for projected properization

After the finite number of colours and every fixed geometric constant have
been chosen, one cutoff makes the rounded per-colour scale large enough for
all of them.  The same cutoff also supplies the reserve bounds and the final
projected-properization scale inequality.
-/

namespace Erdos186.CFP

/-- A concrete cutoff absorbing both the two-units-per-colour rounding loss
and a fixed per-colour lower bound `K`. -/
def projectedColorSourceScaleCutoff (q K : ℕ) : ℕ :=
  max (2 * (q + 1)) ((q + 1) * K)

/-- All scalar bounds needed by the projected physical-density certificate
hold above `projectedColorSourceScaleCutoff`. -/
theorem projectedColorSourceScale_bounds
    {q denseConstant D K s : ℕ}
    (hdense : 0 < denseConstant)
    (hdenseColors : denseConstant ≤ q + 1)
    (hprojection : ProjectedProperization.projectionFactor D ≤ K)
    (hs : projectedColorSourceScaleCutoff q K ≤ s) :
    0 < colorSourceScale s q ∧
      K ≤ colorSourceScale s q ∧
      (q + 1) * colorSourceScale s q ≤ s ∧
      s ≤ 2 * (q + 1) * colorSourceScale s q ∧
      colorSourceScale s q * ((q + 1) / denseConstant) ≤ s ∧
      ProjectedProperization.projectionFactor D ≤
        colorSourceScale s q * ((q + 1) / denseConstant) := by
  have hcolors : 0 < q + 1 := by omega
  have hroom : 2 * (q + 1) ≤ s :=
    (le_max_left _ _).trans hs
  have hmulK : (q + 1) * K ≤ s :=
    (le_max_right _ _).trans hs
  have hKscale : K ≤ colorSourceScale s q := by
    dsimp only [colorSourceScale]
    exact (Nat.le_div_iff_mul_le hcolors).2 (by
      simpa only [Nat.mul_comm] using hmulK)
  have hscalePos : 0 < colorSourceScale s q := by
    have hKpos : 0 < K :=
      lt_of_lt_of_le (ProjectedProperization.projectionFactor_pos D)
        hprojection
    omega
  have hquotient : 1 ≤ (q + 1) / denseConstant := by
    exact (Nat.le_div_iff_mul_le hdense).2 (by
      simpa only [Nat.one_mul] using hdenseColors)
  have hcertificate :=
    colorSourceScale_certificate_bounds hroom hdense
  refine ⟨hscalePos, hKscale, hcertificate.1, hcertificate.2.1,
    hcertificate.2.2, ?_⟩
  calc
    ProjectedProperization.projectionFactor D ≤ K := hprojection
    _ ≤ colorSourceScale s q := hKscale
    _ = colorSourceScale s q * 1 := by rw [Nat.mul_one]
    _ ≤ colorSourceScale s q * ((q + 1) / denseConstant) := by
      exact Nat.mul_le_mul_left _ hquotient

/-- Existential cutoff form used when all finite parameters have already
been fixed uniformly. -/
theorem exists_cutoff_projectedColorSourceScale_bounds
    (q denseConstant D K : ℕ)
    (hdense : 0 < denseConstant)
    (hdenseColors : denseConstant ≤ q + 1)
    (hprojection : ProjectedProperization.projectionFactor D ≤ K) :
    ∃ cutoff : ℕ, 0 < cutoff ∧ ∀ {s : ℕ}, cutoff ≤ s →
      0 < colorSourceScale s q ∧
        K ≤ colorSourceScale s q ∧
        (q + 1) * colorSourceScale s q ≤ s ∧
        s ≤ 2 * (q + 1) * colorSourceScale s q ∧
        colorSourceScale s q * ((q + 1) / denseConstant) ≤ s ∧
        ProjectedProperization.projectionFactor D ≤
          colorSourceScale s q * ((q + 1) / denseConstant) := by
  refine ⟨projectedColorSourceScaleCutoff q K, ?_, ?_⟩
  · unfold projectedColorSourceScaleCutoff
    have : 0 < 2 * (q + 1) := by omega
    exact this.trans_le (le_max_left _ _)
  · intro s hs
    exact projectedColorSourceScale_bounds hdense hdenseColors hprojection hs

/-- Blocked counterpart of `projectedColorSourceScaleCutoff`.  The extra
factor is fixed before the source set and is paid in the final scale
denominator. -/
def projectedBlockedColorSourceScaleCutoff (q block K : ℕ) : ℕ :=
  max (2 * block * (q + 1)) ((block * (q + 1)) * K)

/-- Above one fixed cutoff, the blocked per-colour scale absorbs every fixed
geometric constant and still supports projected properization. -/
theorem projectedBlockedColorSourceScale_bounds
    {q block denseConstant D K s : ℕ}
    (hblock : 0 < block)
    (hdense : 0 < denseConstant)
    (hdenseColors : denseConstant ≤ q + 1)
    (hprojection : ProjectedProperization.projectionFactor D ≤ K)
    (hs : projectedBlockedColorSourceScaleCutoff q block K ≤ s) :
    0 < RandomPartition.blockedColorSourceScale s q block ∧
      K ≤ RandomPartition.blockedColorSourceScale s q block ∧
      block * (q + 1) *
          RandomPartition.blockedColorSourceScale s q block ≤ s ∧
      s ≤ 2 * block * (q + 1) *
          RandomPartition.blockedColorSourceScale s q block ∧
      (q + 1) * RandomPartition.blockedColorSourceScale s q block ≤ s ∧
      RandomPartition.blockedColorSourceScale s q block *
          ((q + 1) / denseConstant) ≤ s ∧
      ProjectedProperization.projectionFactor D ≤
        RandomPartition.blockedColorSourceScale s q block *
          ((q + 1) / denseConstant) := by
  have hden : 0 < block * (q + 1) := Nat.mul_pos hblock (by omega)
  have hroom : 2 * block * (q + 1) ≤ s :=
    (le_max_left _ _).trans hs
  have hmulK : block * (q + 1) * K ≤ s :=
    (le_max_right _ _).trans hs
  have hKscale : K ≤
      RandomPartition.blockedColorSourceScale s q block := by
    dsimp only [RandomPartition.blockedColorSourceScale]
    exact (Nat.le_div_iff_mul_le hden).2 (by
      simpa only [Nat.mul_comm, Nat.mul_assoc] using hmulK)
  have hquotient : 1 ≤ (q + 1) / denseConstant := by
    exact (Nat.le_div_iff_mul_le hdense).2 (by
      simpa only [Nat.one_mul] using hdenseColors)
  have hquotientLe : (q + 1) / denseConstant ≤ q + 1 :=
    Nat.div_le_self _ _
  have hb := RandomPartition.blockedColorSourceScale_bounds hblock hroom
  refine ⟨hb.1, hKscale, hb.2.1, hb.2.2.1, hb.2.2.2, ?_, ?_⟩
  · calc
      RandomPartition.blockedColorSourceScale s q block *
            ((q + 1) / denseConstant) ≤
          RandomPartition.blockedColorSourceScale s q block * (q + 1) := by
        exact Nat.mul_le_mul_left _ hquotientLe
      _ = (q + 1) *
          RandomPartition.blockedColorSourceScale s q block := by
        rw [Nat.mul_comm]
      _ ≤ s := hb.2.2.2
  · calc
      ProjectedProperization.projectionFactor D ≤ K := hprojection
      _ ≤ RandomPartition.blockedColorSourceScale s q block := hKscale
      _ = RandomPartition.blockedColorSourceScale s q block * 1 := by
        rw [Nat.mul_one]
      _ ≤ RandomPartition.blockedColorSourceScale s q block *
          ((q + 1) / denseConstant) := by
        exact Nat.mul_le_mul_left _ hquotient

/-- Existential cutoff form of the blocked projected scale bounds. -/
theorem exists_cutoff_projectedBlockedColorSourceScale_bounds
    (q block denseConstant D K : ℕ)
    (hblock : 0 < block)
    (hdense : 0 < denseConstant)
    (hdenseColors : denseConstant ≤ q + 1)
    (hprojection : ProjectedProperization.projectionFactor D ≤ K) :
    ∃ cutoff : ℕ, 0 < cutoff ∧ ∀ {s : ℕ}, cutoff ≤ s →
      0 < RandomPartition.blockedColorSourceScale s q block ∧
        K ≤ RandomPartition.blockedColorSourceScale s q block ∧
        block * (q + 1) *
            RandomPartition.blockedColorSourceScale s q block ≤ s ∧
        s ≤ 2 * block * (q + 1) *
            RandomPartition.blockedColorSourceScale s q block ∧
        (q + 1) * RandomPartition.blockedColorSourceScale s q block ≤ s ∧
        RandomPartition.blockedColorSourceScale s q block *
            ((q + 1) / denseConstant) ≤ s ∧
        ProjectedProperization.projectionFactor D ≤
          RandomPartition.blockedColorSourceScale s q block *
            ((q + 1) / denseConstant) := by
  refine ⟨projectedBlockedColorSourceScaleCutoff q block K, ?_, ?_⟩
  · unfold projectedBlockedColorSourceScaleCutoff
    have : 0 < 2 * block * (q + 1) := by positivity
    exact this.trans_le (le_max_left _ _)
  · intro s hs
    exact projectedBlockedColorSourceScale_bounds hblock hdense
      hdenseColors hprojection hs

end Erdos186.CFP

#print axioms Erdos186.CFP.projectedColorSourceScale_bounds
#print axioms Erdos186.CFP.exists_cutoff_projectedColorSourceScale_bounds
#print axioms Erdos186.CFP.projectedBlockedColorSourceScale_bounds
#print axioms
  Erdos186.CFP.exists_cutoff_projectedBlockedColorSourceScale_bounds
