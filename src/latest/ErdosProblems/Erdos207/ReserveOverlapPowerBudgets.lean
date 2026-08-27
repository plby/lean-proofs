/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveCommonCenterTail
import ErdosProblems.Erdos207.FutureTypicalityPowerBudgets

/-! # A rounded, slowly enlarged overlap cutoff gives polynomial simultaneous tails -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem finite_moment_error_power_decay_with_coefficient
    (t error factor A B0 : ℝ≥0) (B d s decay : ℕ) (ht : 1 ≤ t)
    (herror : error ≤ B0/t^B) (hfactor : factor ≤ A*t^d) (hgap : d*s+decay ≤ B) :
    error * factor^s ≤ B0*A^s/t^decay := by
  have hb := finite_moment_error_power_decay t (1/t^B) factor A B d s decay ht le_rfl hfactor hgap
  calc
    _ ≤ (B0/t^B)*factor^s := mul_le_mul_of_nonneg_right herror zero_le
    _ = B0*((1/t^B)*factor^s) := by ring
    _ ≤ B0*(A^s/t^decay) := mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by ring

theorem rounded_reserve_overlap_bounds (t r n : ℝ≥0) (hscale : 1 ≤ t*r^2*n) :
    (⌈t*r^2*n⌉₊ : ℝ≥0) ≤ 2*t*r^2*n ∧
      (⌈t*r^2*n⌉₊ + 1 : ℝ≥0) ≤ 3*t*r^2*n := by
  have hc := (Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ t*r^2*n from zero_le)).le
  have htwo : (⌈t*r^2*n⌉₊ : ℝ≥0) ≤ 2*t*r^2*n := by
    calc
      _ ≤ t*r^2*n+1 := hc
      _ ≤ t*r^2*n+t*r^2*n := add_le_add le_rfl hscale
      _ = _ := by ring
  refine ⟨htwo, ?_⟩
  calc
    _ ≤ 2*t*r^2*n+t*r^2*n := add_le_add htwo hscale
    _ = _ := by ring

theorem FiniteLaw.reserveOverlap_failure_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (reserve : Omega → Finset (Sym2 V)) (r C beta : ℝ≥0)
    (hreserve : ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C^E.card*(r^E.card+beta))
    (current U : Finset V) (s M : ℕ) (hs : 2*s ≤ M+1) :
    L.probability (fun omega ↦ ¬ ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      (reserveCommonCenters (current \ U) (reserve omega) u v).card ≤ M) ≤
      (Fintype.card V : ℝ≥0)^2 *
        ((2*(current.card : ℝ≥0)*C^2*r^2/(M+1))^s+
          (2*(current.card : ℝ≥0)*C^2/(M+1))^s*beta) := by
  have ht := L.reserveCommonCenters_simultaneous_tail reserve r C beta hreserve
    (current \ U) U sdiff_disjoint s (M+1) (by omega) hs
  have hevent := L.probability_mono (Q := fun omega ↦ ∃ uv ∈ U.offDiag,
      M+1 ≤ (reserveCommonCenters (current \ U) (reserve omega) uv.1 uv.2).card)
    (fun omega (h : ¬ ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      (reserveCommonCenters (current \ U) (reserve omega) u v).card ≤ M) ↦ by
      simp only [not_forall, exists_prop, not_le] at h
      obtain ⟨u, hu, v, hv, huv, hM⟩ := h
      exact ⟨(u,v), mem_offDiag.mpr ⟨hu,hv,huv⟩,
        by change M+1 ≤ (reserveCommonCenters (current \ U) (reserve omega) u v).card; omega⟩)
  have hcard : (U.offDiag.card : ℝ≥0) ≤ (Fintype.card V : ℝ≥0)^2 := by
    have hh : U.offDiag.card ≤ Fintype.card V * Fintype.card V := by
      simpa only [Fintype.card_prod] using card_le_univ U.offDiag
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hn : ((current \ U).card : ℝ≥0) ≤ current.card := by
    exact_mod_cast card_le_card (sdiff_subset : current \ U ⊆ current)
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact (hevent.trans ht).trans (by gcongr)

theorem reserveOverlap_failure_power_bound
    (N n R s B decay : ℕ) (t r C beta B0 : ℝ≥0)
    (ht : 1 ≤ t) (hr : 0 < r) (hn : 0 < n)
    (hN : (N : ℝ≥0) ≤ t^R) (hsize : (n : ℝ≥0) ≤ t^R)
    (hbeta : beta ≤ B0/t^B) (hmainGap : 2*R+decay ≤ s)
    (herrorGap : R*s+2*R+decay ≤ B) :
    (N : ℝ≥0)^2 *
      ((2*(n : ℝ≥0)*C^2*r^2/(⌈t*r^2*n⌉₊+1))^s+
        (2*(n : ℝ≥0)*C^2/(⌈t*r^2*n⌉₊+1))^s*beta) ≤
      ((1+B0)*(2*C^2)^s)/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn0 : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hceil : t*r^2*n ≤ (⌈t*r^2*n⌉₊+1 : ℝ≥0) :=
    (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le)
  have hmain : 2*(n : ℝ≥0)*C^2*r^2/(⌈t*r^2*n⌉₊+1) ≤ (2*C^2)/t := by
    calc
      _ ≤ 2*(n : ℝ≥0)*C^2*r^2/(t*r^2*n) :=
        div_le_div_of_nonneg_left zero_le (by positivity) hceil
      _ = _ := by field_simp
  have hfactor : 2*(n : ℝ≥0)*C^2/(⌈t*r^2*n⌉₊+1) ≤ (2*C^2)*t^R := by
    calc
      _ ≤ 2*(n : ℝ≥0)*C^2/1 := div_le_div_of_nonneg_left zero_le zero_lt_one
        (le_add_of_nonneg_left zero_le)
      _ ≤ 2*t^R*C^2 := by rw [div_one]; gcongr
      _ = _ := by ring
  have hmainTerm : (2*(n : ℝ≥0)*C^2*r^2/(⌈t*r^2*n⌉₊+1))^s ≤
      (2*C^2)^s/t^(2*R+decay) := by
    calc
      _ ≤ ((2*C^2)/t)^s := pow_le_pow_left' hmain s
      _ = (2*C^2)^s/t^s := div_pow _ _ _
      _ ≤ _ := div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) (pow_le_pow_right₀ ht hmainGap)
  have herrorTerm := finite_moment_error_power_decay_with_coefficient t beta
    (2*(n : ℝ≥0)*C^2/(⌈t*r^2*n⌉₊+1)) (2*C^2) B0 B R s (2*R+decay)
    ht hbeta hfactor (by omega)
  have hsingle : (2*(n : ℝ≥0)*C^2*r^2/(⌈t*r^2*n⌉₊+1))^s+
      (2*(n : ℝ≥0)*C^2/(⌈t*r^2*n⌉₊+1))^s*beta ≤
        ((1+B0)*(2*C^2)^s)/t^(2*R+decay) := by
    calc
      _ ≤ (2*C^2)^s/t^(2*R+decay)+B0*(2*C^2)^s/t^(2*R+decay) :=
        add_le_add hmainTerm (by simpa only [mul_comm] using herrorTerm)
      _ = _ := by ring
  have htests : (N : ℝ≥0)^2 ≤ 1*t^(2*R) := by
    simpa only [one_mul, pow_mul, Nat.mul_comm 2 R] using pow_le_pow_left' hN 2
  simpa only [one_mul] using finite_polynomial_union_power_decay t ((N : ℝ≥0)^2) _ 1
    ((1+B0)*(2*C^2)^s) (2*R) (2*R+decay) decay ht htests hsingle le_rfl

end

end Erdos207
