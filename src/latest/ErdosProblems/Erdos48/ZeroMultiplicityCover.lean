/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroSelection

/-!
# Recovering zero multiplicity from an ordinate cover

A maximal separated family is selected only at the level of ordinates.
Every zero whose ordinate it covers nevertheless lies in the radius-`4*eta`
disk centered over that selected ordinate.  The checked local divisor bound
therefore controls the complete analytic multiplicity in the rectangle.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

/-- Horizontal location in the high-zero strip, together with a nearby
ordinate, places a zero in the local disk used by the multiplicity theorem. -/
theorem highZero_mem_smallDisk_of_ordinate_near
    {rho : ℂ} {y eta delta : ℝ}
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (heta : 0 < eta) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hord : dist rho.im y ≤ 2 * delta * eta) :
    dist rho (((1 + eta : ℝ) : ℂ) + y * I) ≤ 4 * eta := by
  rw [Complex.dist_eq]
  have hre :
      |(rho - (((1 + eta : ℝ) : ℂ) + y * I)).re| ≤ 2 * eta := by
    simp only [Complex.sub_re, Complex.add_re, ofReal_re, mul_re,
      ofReal_re, I_re, ofReal_im, I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have him :
      |(rho - (((1 + eta : ℝ) : ℂ) + y * I)).im| ≤
        2 * delta * eta := by
    simp only [Complex.sub_im, Complex.add_im, ofReal_im, mul_im,
      ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul, zero_add]
    simpa only [Real.dist_eq, add_zero] using hord
  calc
    ‖rho - (((1 + eta : ℝ) : ℂ) + y * I)‖ ≤
        |(rho - (((1 + eta : ℝ) : ℂ) + y * I)).re| +
          |(rho - (((1 + eta : ℝ) : ℂ) + y * I)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * eta + 2 * delta * eta := add_le_add hre him
    _ ≤ 4 * eta := by nlinarith

private theorem finset_sum_finsupp_apply_le_sum
    {α : Type*} (F : α →₀ ℕ) (s : Finset α) :
    ∑ x ∈ s, (F x : ℝ) ≤ F.sum (fun _ m ↦ (m : ℝ)) := by
  classical
  have heq :
      F.sum (fun _ m ↦ (m : ℝ)) =
        ∑ x ∈ F.support ∪ s, (F x : ℝ) := by
    exact Finsupp.sum_of_support_subset F Finset.subset_union_left
      (fun _ m ↦ (m : ℝ)) (by simp)
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun _ _ _ ↦ by positivity)

/-- A covering family of ordinates bounds the total multiplicity in the
high-zero rectangle by the sum of the corresponding local disk masses. -/
theorem highZeroRectangleMass_le_sum_smallDiskMass
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {eta T delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hT : 0 ≤ T)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (S : Finset ℝ)
    (hcover : ∀ x ∈ highZeroOrdinates hq chi hchi eta T,
      ∃ y ∈ S, dist x y ≤ 2 * delta * eta) :
    (highZeroRectangleMass hq chi hchi eta T : ℝ) ≤
      ∑ y ∈ S,
        (smallDiskZeroFinsupp hq chi hchi y eta).sum
          (fun _ m ↦ (m : ℝ)) := by
  classical
  let Z := highZeroRectangle hq chi hchi eta T
  let F : ℝ → ℂ →₀ ℕ := fun y ↦
    smallDiskZeroFinsupp hq chi hchi y eta
  have hpoint (rho : ℂ) (hrho : rho ∈ Z) :
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℝ) ≤
        ∑ y ∈ S, (F y rho : ℝ) := by
    have hrhoData :=
      (mem_highZeroRectangle_iff hq chi hchi heta1 hT rho).mp hrho
    have hrhoOrd : rho.im ∈ highZeroOrdinates hq chi hchi eta T := by
      rw [highZeroOrdinates, Finset.mem_image]
      exact ⟨rho, hrho, rfl⟩
    obtain ⟨y, hyS, hy⟩ := hcover rho.im hrhoOrd
    have hdisk := highZero_mem_smallDisk_of_ordinate_near
      hrhoData.2.1 hrhoData.2.2.1 heta hdelta0 hdelta1 hy
    have hFy : F y rho =
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho := by
      rw [show F y rho = smallDiskZeroMultiplicity chi y eta rho by
        exact smallDiskZeroFinsupp_apply hq chi hchi y eta rho]
      unfold smallDiskZeroMultiplicity
      rw [if_pos hdisk]
    rw [← hFy]
    exact_mod_cast Finset.single_le_sum
      (fun z _ ↦ Nat.zero_le (F z rho)) hyS
  calc
    (highZeroRectangleMass hq chi hchi eta T : ℝ) =
        ∑ rho ∈ Z,
          (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℝ) := by
      simp only [highZeroRectangleMass, Z, Nat.cast_sum]
    _ ≤ ∑ rho ∈ Z, ∑ y ∈ S, (F y rho : ℝ) :=
      Finset.sum_le_sum fun rho hrho ↦ hpoint rho hrho
    _ = ∑ y ∈ S, ∑ rho ∈ Z, (F y rho : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ y ∈ S, (F y).sum (fun _ m ↦ (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact finset_sum_finsupp_apply_le_sum (F y) Z
    _ = _ := by rfl

/-- There is an absolute local-multiplicity constant such that any ordinate
cover satisfying the common logarithmic-height hypothesis controls the whole
rectangle mass by its cardinality times that constant. -/
theorem exists_highZeroRectangleMass_cover_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (eta T lambda delta : ℝ),
            0 < eta → eta ≤ 1 → 0 ≤ T →
            0 ≤ delta → delta ≤ 1 →
            eta * Real.log ((q : ℝ) * (T + 2)) ≤ lambda →
            ∀ S : Finset ℝ,
              S ⊆ highZeroOrdinates hq chi hchi eta T →
              (∀ x ∈ highZeroOrdinates hq chi hchi eta T,
                ∃ y ∈ S, dist x y ≤ 2 * delta * eta) →
              (highZeroRectangleMass hq chi hchi eta T : ℝ) ≤
                (S.card : ℝ) *
                  (32 * (Real.log 4 + 4) + (256 * (A : ℝ) / 3) * lambda) := by
  obtain ⟨A, hA, hlocal⟩ := exists_smallDiskZeroMultiplicity_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi eta T lambda delta heta heta1 hT
    hdelta0 hdelta1 hglobal S hSsub hcover
  have hmass := highZeroRectangleMass_le_sum_smallDiskMass
    hq chi hchi heta heta1 hT hdelta0 hdelta1 S hcover
  let K : ℝ :=
    32 * (Real.log 4 + 4) + (256 * (A : ℝ) / 3) * lambda
  have hterm : ∀ y ∈ S,
      (smallDiskZeroFinsupp hq chi hchi y eta).sum
          (fun _ m ↦ (m : ℝ)) ≤ K := by
    intro y hy
    have hyOrd := hSsub hy
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, hy0, hyT⟩ :=
      (mem_highZeroOrdinates_iff hq chi hchi heta1 hT y).mp hyOrd
    have hlog : eta * Real.log ((q : ℝ) * (|y| + 2)) ≤ lambda :=
      (mul_le_mul_of_nonneg_left (log_height_mono hy0 hyT) heta.le).trans hglobal
    have hb := hlocal q hq chi hchi y eta heta heta1
    dsimp [K]
    calc
      (smallDiskZeroFinsupp hq chi hchi y eta).sum
          (fun _ m ↦ (m : ℝ)) ≤
        16 * (Real.log 4 + 4) * (1 + eta) +
          (256 * (A : ℝ) / 3) * eta *
            Real.log ((q : ℝ) * (|y| + 2)) := hb
      _ ≤ 32 * (Real.log 4 + 4) +
          (256 * (A : ℝ) / 3) * lambda := by
        have hC : 0 ≤ Real.log 4 + 4 := by positivity
        have hA0 : 0 ≤ (256 * (A : ℝ) / 3) := by positivity
        nlinarith
  calc
    (highZeroRectangleMass hq chi hchi eta T : ℝ) ≤
        ∑ y ∈ S,
          (smallDiskZeroFinsupp hq chi hchi y eta).sum
            (fun _ m ↦ (m : ℝ)) := hmass
    _ ≤ ∑ y ∈ S, K := Finset.sum_le_sum fun y hy ↦ hterm y hy
    _ = (S.card : ℝ) * K := by simp

end

end Erdos48
