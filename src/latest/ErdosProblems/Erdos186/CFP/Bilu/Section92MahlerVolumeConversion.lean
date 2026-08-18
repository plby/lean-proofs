/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92UniformRankRepair

/-!
# Uniform conversion from body volume to Mahler progression volume

The upper half of the Section 3 Mahler comparison contains a simplex
factor.  This file clears that factor and takes a finite maximum over all
ranks below the Section 9 ceiling.  The resulting natural number is the
last fixed constant needed to turn a stopped body into the displayed GAP
volume bound.
-/

namespace Erdos186.CFP.Bilu.Section92MahlerVolumeConversion

open MeasureTheory
open Mahler MahlerOuterContainer MinkowskiUpper
open Section9ContainerIntegration
open Section92PresentationDescent
open Section92UniformRankRepair Section92WeightedRankRepair
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

/-- A convenient real upper coefficient for the Section 3 outer box in
rank `n`.  The omitted factor `2^n` is at least one. -/
def mahlerOuterVolumeCoefficient (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (5 * outerConstant n) ^ n

theorem mahlerOuterVolumeCoefficient_nonneg (n : ℕ) :
    0 ≤ mahlerOuterVolumeCoefficient n := by
  unfold mahlerOuterVolumeCoefficient
  exact mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (mul_nonneg (by norm_num) (outerConstant_nonneg n)) _)

/-- The displayed Mahler box has volume at most a dimension-only multiple
of the real volume of the seminorm unit ball. -/
theorem MappedOuterContainer.source_volume_cast_le_bodyVolume
    {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : IntegralPoint n →+ ℤ}
    (D : MappedOuterContainer p phi) (hp : IsDefinite p) :
    (D.source.volume : ℝ) ≤
      mahlerOuterVolumeCoefficient n *
        volume.real {y : Fin n → ℝ | p y ≤ 1} := by
  have htop : volume {y : Fin n → ℝ | p y ≤ 1} ≠ ⊤ :=
    (isBounded_unitBall p hp).measure_lt_top.ne
  have hrhs :
      ENNReal.ofReal ((5 * outerConstant n) ^ n) *
          volume {y : Fin n → ℝ | p y ≤ 1} ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) htop
  have hreal := ENNReal.toReal_mono hrhs D.volume_mul_simplex_le
  have hsimplex : 0 ≤ (2 : ℝ) ^ n / (n.factorial : ℝ) := by positivity
  have hconstant : 0 ≤ (5 * outerConstant n) ^ n :=
    pow_nonneg (mul_nonneg (by norm_num) (outerConstant_nonneg n)) _
  have hbasic :
      (D.source.volume : ℝ) *
          ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        (5 * outerConstant n) ^ n *
          volume.real {y : Fin n → ℝ | p y ≤ 1} := by
    simpa only [MappedOuterContainer.source, ENNReal.toReal_mul,
      ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hsimplex,
      ENNReal.toReal_ofReal hconstant, Measure.real] using hreal
  have hfactorial : (0 : ℝ) < n.factorial := by positivity
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hgap : (0 : ℝ) ≤ D.source.volume := by positivity
  have hcleared := mul_le_mul_of_nonneg_right hbasic hfactorial.le
  have hleft :
      (D.source.volume : ℝ) * (2 : ℝ) ^ n ≤
        ((n.factorial : ℝ) * (5 * outerConstant n) ^ n) *
          volume.real {y : Fin n → ℝ | p y ≤ 1} := by
    calc
      (D.source.volume : ℝ) * (2 : ℝ) ^ n =
          ((D.source.volume : ℝ) *
              ((2 : ℝ) ^ n / (n.factorial : ℝ))) *
            (n.factorial : ℝ) := by field_simp
      _ ≤ ((5 * outerConstant n) ^ n *
          volume.real {y : Fin n → ℝ | p y ≤ 1}) *
            (n.factorial : ℝ) := hcleared
      _ = ((n.factorial : ℝ) * (5 * outerConstant n) ^ n) *
          volume.real {y : Fin n → ℝ | p y ≤ 1} := by ring
  calc
    (D.source.volume : ℝ) ≤
        (D.source.volume : ℝ) * (2 : ℝ) ^ n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hgap
    _ ≤ mahlerOuterVolumeCoefficient n *
        volume.real {y : Fin n → ℝ | p y ≤ 1} := by
      simpa only [mahlerOuterVolumeCoefficient] using hleft

/-- One natural constant dominating every Mahler conversion coefficient
up to `rankBound`. -/
def uniformMahlerOuterVolumeConstant (rankBound : ℕ) : ℕ :=
  Nat.ceil (1 + ∑ n ∈ Finset.range (rankBound + 1),
    mahlerOuterVolumeCoefficient n)

theorem uniformMahlerOuterVolumeConstant_pos (rankBound : ℕ) :
    0 < uniformMahlerOuterVolumeConstant rankBound := by
  rw [uniformMahlerOuterVolumeConstant, Nat.ceil_pos]
  have hsum : 0 ≤ ∑ n ∈ Finset.range (rankBound + 1),
      mahlerOuterVolumeCoefficient n := by
    exact Finset.sum_nonneg fun n _ ↦
      mahlerOuterVolumeCoefficient_nonneg n
  linarith

theorem mahlerOuterVolumeCoefficient_le_uniform
    {n rankBound : ℕ} (hn : n ≤ rankBound) :
    mahlerOuterVolumeCoefficient n ≤
      (uniformMahlerOuterVolumeConstant rankBound : ℝ) := by
  have hterm : mahlerOuterVolumeCoefficient n ≤
      ∑ i ∈ Finset.range (rankBound + 1),
        mahlerOuterVolumeCoefficient i := by
    exact Finset.single_le_sum
      (fun i _ ↦ mahlerOuterVolumeCoefficient_nonneg i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have hceil :
      1 + ∑ i ∈ Finset.range (rankBound + 1),
          mahlerOuterVolumeCoefficient i ≤
        (uniformMahlerOuterVolumeConstant rankBound : ℝ) := by
    exact Nat.le_ceil _
  exact hterm.trans ((le_add_of_nonneg_left zero_le_one).trans hceil)

/-- Rank-uniform form of the Mahler outer-volume estimate. -/
theorem MappedOuterContainer.source_volume_cast_le_uniform_mul_bodyVolume
    {A : Finset ℤ} (X : RankedBodyPresentation A)
    {rankBound : ℕ} (hrank : X.1 ≤ rankBound)
    (D : MappedOuterContainer X.2.seminorm X.2.map) :
    (D.source.volume : ℝ) ≤
      (uniformMahlerOuterVolumeConstant rankBound : ℝ) * bodyVolume X := by
  calc
    (D.source.volume : ℝ) ≤
        mahlerOuterVolumeCoefficient X.1 * bodyVolume X :=
      MappedOuterContainer.source_volume_cast_le_bodyVolume
        D X.2.definite
    _ ≤ (uniformMahlerOuterVolumeConstant rankBound : ℝ) * bodyVolume X :=
      mul_le_mul_of_nonneg_right
        (mahlerOuterVolumeCoefficient_le_uniform hrank)
        (bodyVolume_pos X).le

/-- The scalar minimized by Section 4 after incorporating both the
rank-repair weight and the final Mahler conversion factor. -/
def terminalScaledBodyVolume {A : Finset ℤ}
    (s rankBound : ℕ) (X : RankedBodyPresentation A) : ℝ :=
  (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
    rankWeightedBodyVolume (canonicalRankRepairFactor s rankBound) X

theorem terminalScaledBodyVolume_pos {A : Finset ℤ}
    (s rankBound : ℕ) (X : RankedBodyPresentation A) :
    0 < terminalScaledBodyVolume s rankBound X := by
  apply mul_pos
  · exact_mod_cast uniformMahlerOuterVolumeConstant_pos rankBound
  · exact rankWeightedBodyVolume_pos
      (lt_of_lt_of_le zero_lt_one
        (one_le_canonicalRankRepairFactor s rankBound)) X

/-- A selected presentation with small scaled weighted volume produces the
complete reduced outer realization.  Kernel collisions are repaired
internally before the Mahler container is selected. -/
theorem exists_reducedOuterRealization_of_terminalScaledBodyVolume
    {A : Finset ℤ} (s volumeConstant rankBound : ℕ)
    (hcard : 1 < A.card)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (hvolume : terminalScaledBodyVolume s rankBound initial ≤
      ((volumeConstant * A.card : ℕ) : ℝ)) :
    Nonempty (ReducedOuterRealization
      s volumeConstant rankBound A) := by
  obtain ⟨X, hgood, hrank, hweighted⟩ :=
    exists_enlargedInjective_of_canonicalQuotient
      s rankBound hcard initial hinitialRank
  apply exists_reducedOuterRealization_of_presentation X hgood
  · intro D
    have hD :=
      MappedOuterContainer.source_volume_cast_le_uniform_mul_bodyVolume
        X hrank D
    have hbody := bodyVolume_le_rankWeightedBodyVolume
      (one_le_canonicalRankRepairFactor s rankBound) X
    have hM :
        (0 : ℝ) ≤ uniformMahlerOuterVolumeConstant rankBound := by
      positivity
    have hscaledX :
        (uniformMahlerOuterVolumeConstant rankBound : ℝ) * bodyVolume X ≤
          terminalScaledBodyVolume s rankBound initial := by
      calc
        (uniformMahlerOuterVolumeConstant rankBound : ℝ) * bodyVolume X ≤
            (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
              rankWeightedBodyVolume
                (canonicalRankRepairFactor s rankBound) X :=
          mul_le_mul_of_nonneg_left hbody hM
        _ ≤ (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
              rankWeightedBodyVolume
                (canonicalRankRepairFactor s rankBound) initial :=
          mul_le_mul_of_nonneg_left hweighted hM
        _ = terminalScaledBodyVolume s rankBound initial := rfl
    have hreal : (D.source.volume : ℝ) ≤
        ((volumeConstant * A.card : ℕ) : ℝ) :=
      hD.trans (hscaledX.trans hvolume)
    exact_mod_cast hreal
  · exact hrank

end

end Erdos186.CFP.Bilu.Section92MahlerVolumeConversion

#print axioms
  Erdos186.CFP.Bilu.Section92MahlerVolumeConversion.MappedOuterContainer.source_volume_cast_le_uniform_mul_bodyVolume
#print axioms
  Erdos186.CFP.Bilu.Section92MahlerVolumeConversion.exists_reducedOuterRealization_of_terminalScaledBodyVolume
