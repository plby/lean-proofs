/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RetainedPowerVortex

/-! # Actual current-size and next-size powers on the retained vortex -/

namespace Erdos207

open Finset

noncomputable section

def retainedStageExponent (Rfixed step ell i : ℕ) : ℕ :=
  if i = 0 then Rfixed + step * ell else step * (ell - i)

def retainedRatioExponent (Rfixed step i : ℕ) : ℕ :=
  if i = 0 then Rfixed + step + 1 else 2 * step + 1

theorem InitialPowerVortexPackage.retainedVortex_first_scale_bounds
    {q h n ell t rootPower step length m Rfixed : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hsplit : length + m = ell) (hlength : 2 ≤ length)
    (hroot : rootPower ≤ step * m)
    (hnlo : t ^ (Rfixed + step * ell) ≤ n) (hnhi : n ≤ t ^ (Rfixed + step * ell + 1)) :
    let W := P.retainedVortex length (by omega) (by omega)
    let i : Fin length := ⟨0, by omega⟩
    t ^ step * (W.U i.succ).card ≤ 2 * n ∧
      n ≤ t ^ (Rfixed + step + 1) * (W.U i.succ).card := by
  dsimp only
  let j : Fin (ell + 1) := ⟨1, by omega⟩
  have hfirst : (P.retainedVortex length (by omega) (by omega)).U
      (Fin.succ (⟨0, by omega⟩ : Fin length)) = P.W.U j := by
    simp [InitialPowerVortexPackage.retainedVortex, Vortex.reindex,
      terminalJumpStage, show 1 < length by omega, j]
  rw [hfirst]
  have hj0 : j ≠ 0 := by intro hz; have hv := congrArg Fin.val hz; change 1 = 0 at hv; omega
  have hjlast : j ≠ Fin.last ell := by
    intro hz
    have hv := congrArg Fin.val hz
    change 1 = ell at hv
    omega
  have hrootj : rootPower ≤ step * (ell - j.val) :=
    hroot.trans (Nat.mul_le_mul_left step (by dsimp only [j]; omega))
  obtain ⟨hlo, hhi⟩ := P.positiveLevel_card_power_bounds j hj0 hjlast hrootj
  have hpow : step * ell = step * (ell - j.val) + step := by
    have heq : ell = (ell - j.val) + 1 := by dsimp only [j]; omega
    conv_lhs => rw [heq]
    rw [Nat.mul_add, Nat.mul_one]
  have ht := Nat.zero_lt_one.trans_le P.base_ge_one
  constructor
  · calc
      _ ≤ t ^ step * (2 * t ^ (step * (ell - j.val))) := Nat.mul_le_mul_left _ hhi
      _ = 2 * t ^ (step * ell) := by rw [hpow, pow_add]; ring
      _ ≤ 2 * t ^ (Rfixed + step * ell) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right ht (by omega))
      _ ≤ _ := Nat.mul_le_mul_left 2 hnlo
  · calc
      _ ≤ t ^ (Rfixed + step * ell + 1) := hnhi
      _ = t ^ (Rfixed + step + 1) * t ^ (step * (ell - j.val)) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ hlo

theorem InitialPowerVortexPackage.retainedVortex_stage_power_geometry
    {q h n ell t rootPower step length m Rfixed K : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hsplit : length + m = ell) (hlength : 2 ≤ length) (ht : 2 ≤ t)
    (hroot : rootPower ≤ step * m) (hrootUpper : step * m ≤ rootPower + step)
    (hrootGap : K * (2 * step + 1) ≤ rootPower)
    (hfirstGap : K * (Rfixed + step + 1) ≤ Rfixed + step * ell)
    (hnlo : t ^ (Rfixed + step * ell) ≤ n) (hnhi : n ≤ t ^ (Rfixed + step * ell + 1))
    (i : Fin length) :
    let W := P.retainedVortex length (by omega) (by omega)
    let D := retainedStageExponent Rfixed step ell i.val
    let v := retainedRatioExponent Rfixed step i.val
    t ^ D ≤ (W.U i.castSucc).card ∧ (W.U i.castSucc).card ≤ t ^ (D + 1) ∧
      t ^ step * (W.U i.succ).card ≤ 2 * (W.U i.castSucc).card ∧
      (W.U i.castSucc).card ≤ t ^ v * (W.U i.succ).card ∧ K * v ≤ D := by
  dsimp only
  let W := P.retainedVortex length (by omega) (by omega)
  by_cases hi : i.val = 0
  · have hiEq : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hiEq]
    have hcard : (W.U ((⟨0, by omega⟩ : Fin length).castSucc)).card = n := by
      change (W.U 0).card = n
      rw [W.root, card_univ, Fintype.card_fin]
    obtain ⟨hlo, hhi⟩ := P.retainedVortex_first_scale_bounds (Rfixed := Rfixed) hsplit hlength hroot hnlo hnhi
    change t ^ (retainedStageExponent Rfixed step ell 0) ≤ (W.U _).card ∧ _
    simp only [retainedStageExponent, retainedRatioExponent]
    rw [show ((P.retainedVortex length (by omega) (by omega)).U
      ((⟨0, by omega⟩ : Fin length).castSucc)).card = n from hcard]
    exact ⟨hnlo, hnhi, hlo, hhi, hfirstGap⟩
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
    let current : Fin (ell + 1) := ⟨i.val, by have := i.isLt; omega⟩
    have hcurrent : W.U i.castSucc = P.W.U current := by
      change P.W.U (terminalJumpStage ell length (by omega) i.castSucc) = P.W.U current
      rw [terminalJumpStage_castSucc]
    have hcur0 : current ≠ 0 := by
      intro hz
      have hv : current.val = 0 := by rw [hz]; rfl
      exact hi hv
    have hcurLast : current ≠ Fin.last ell := by
      intro hz
      have hv := congrArg Fin.val hz
      change i.val = ell at hv
      have := i.isLt
      omega
    have hrootCur : rootPower ≤ step * (ell - i.val) :=
      hroot.trans (Nat.mul_le_mul_left step (by have := i.isLt; omega))
    obtain ⟨hlower, hupper⟩ := P.positiveLevel_card_power_bounds current hcur0 hcurLast hrootCur
    have hcardUpper : (P.W.U current).card ≤ t ^ (step * (ell - i.val) + 1) := by
      calc
        _ ≤ 2 * t ^ (step * (ell - i.val)) := hupper
        _ ≤ t * t ^ (step * (ell - i.val)) := Nat.mul_le_mul_right _ ht
        _ = _ := (pow_succ' _ _).symm
    obtain ⟨hratioLo, hratioHi⟩ := P.retainedVortex_positive_scale_bounds hsplit
      (by omega) hroot hrootUpper i hiPos
    have hratio : (W.U i.castSucc).card ≤ t ^ (2 * step + 1) * (W.U i.succ).card := by
      calc
        _ ≤ 2 * t ^ (2 * step) * (W.U i.succ).card := hratioHi
        _ ≤ t * t ^ (2 * step) * (W.U i.succ).card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ht)
        _ = _ := by rw [pow_succ']
    simp only [retainedStageExponent, retainedRatioExponent, if_neg hi]
    exact ⟨hcurrent.symm ▸ hlower, hcurrent.symm ▸ hcardUpper, hratioLo, hratio, hrootGap.trans hrootCur⟩

theorem InitialPowerVortexPackage.dyadic_retained_stage_power_geometry
    {q h n ell rootPower step length m Rfixed K : ℕ}
    (P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed + step * ell) n) rootPower step)
    (hsplit : length + m = ell) (hlength : 2 ≤ length)
    (ht : 2 ≤ dyadicPowerScale (Rfixed + step * ell) n)
    (hround : 2 ^ (Rfixed + step * ell) ≤ dyadicPowerScale (Rfixed + step * ell) n)
    (hR : 0 < Rfixed + step * ell)
    (hroot : rootPower ≤ step * m) (hrootUpper : step * m ≤ rootPower + step)
    (hrootGap : K * (2 * step + 1) ≤ rootPower)
    (hfirstGap : K * (Rfixed + step + 1) ≤ Rfixed + step * ell) (i : Fin length) :
    let t := dyadicPowerScale (Rfixed + step * ell) n
    let W := P.retainedVortex length (by omega) (by omega)
    let D := retainedStageExponent Rfixed step ell i.val
    let v := retainedRatioExponent Rfixed step i.val
    t ^ D ≤ (W.U i.castSucc).card ∧ (W.U i.castSucc).card ≤ t ^ (D + 1) ∧
      t ^ step * (W.U i.succ).card ≤ 2 * (W.U i.castSucc).card ∧
      (W.U i.castSucc).card ≤ t ^ v * (W.U i.succ).card ∧ K * v ≤ D := by
  have hnpos : n ≠ 0 := by
    have hp := card_pos.mpr (P.nonempty 0)
    rw [P.rootLevel_card] at hp
    omega
  have hupper : n ≤ (dyadicPowerScale (Rfixed + step * ell) n) ^ (Rfixed + step * ell + 1) := by
    calc
      n ≤ 2 ^ (Rfixed + step * ell) * (dyadicPowerScale (Rfixed + step * ell) n) ^ (Rfixed + step * ell) :=
        le_two_pow_mul_dyadicPowerScale_pow hR
      _ ≤ dyadicPowerScale (Rfixed + step * ell) n *
          (dyadicPowerScale (Rfixed + step * ell) n) ^ (Rfixed + step * ell) :=
        Nat.mul_le_mul_right _ hround
      _ = _ := (pow_succ' _ _).symm
  exact P.retainedVortex_stage_power_geometry hsplit hlength ht hroot hrootUpper hrootGap hfirstGap
    (dyadicPowerScale_pow_le hnpos) hupper i

end

end Erdos207
