/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualReserveDistribution
import ErdosProblems.Erdos207.ReserveWedgeSampling
import ErdosProblems.Erdos207.JointInclusionFactorialTail

/-! # Two-spoke overlap tails under the actual augmented-reserve law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def reserveCommonCenters
    {V : Type*} [DecidableEq V] (S : Finset V) (reserve : Finset (Sym2 V)) (u v : V) : Finset V :=
  S.filter fun w ↦ reserveWedgeBlock u v w ⊆ reserve

theorem IsResidualReserveStronglyWellDistributed.reserve_prescription_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (E : Finset (Sym2 V)) :
    L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C ^ E.card * (r ^ E.card + b) := by
  have ht := h ∅ ∅ ∅ E (disjoint_empty_left _) (empty_subset _)
  have hevent : ResidualReserveDistributionEvent initial later reserve ∅ ∅ ∅ E =
      (fun omega ↦ E ⊆ reserve omega) := by
    funext omega
    simp [ResidualReserveDistributionEvent, ResidualDistributionEvent]
  rw [hevent] at ht
  simpa using ht

theorem FiniteLaw.reserveCommonCenters_subset_le
    {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (reserve : Ω → Finset (Sym2 V)) (r C b : ℝ≥0)
    (hreserve : ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C ^ E.card * (r ^ E.card + b))
    (S H : Finset V) (hHS : H ⊆ S) (u v : V) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S) :
    L.probability (fun omega ↦ H ⊆ reserveCommonCenters S (reserve omega) u v) ≤
      C ^ (2 * H.card) * (r ^ (2 * H.card) + b) := by
  have hpair : (H : Set V).PairwiseDisjoint (reserveWedgeBlock u v) := by
    intro w _ x hx hwx
    exact reserveWedgeBlock_disjoint huv (fun heq ↦ hu (heq ▸ hHS hx))
      (fun heq ↦ hv (heq ▸ hHS hx)) hwx
  have hcard : (H.biUnion (reserveWedgeBlock u v)).card = 2 * H.card := by
    rw [card_biUnion hpair]
    simp only [card_reserveWedgeBlock huv, sum_const, smul_eq_mul]
    omega
  calc
    _ ≤ L.probability (fun omega ↦ H.biUnion (reserveWedgeBlock u v) ⊆ reserve omega) := by
      apply L.probability_mono
      intro omega hH e he
      obtain ⟨w, hw, hew⟩ := mem_biUnion.mp he
      exact (mem_filter.mp (hH hw)).2 hew
    _ ≤ C ^ (2 * H.card) * (r ^ (2 * H.card) + b) := by
      simpa only [hcard] using hreserve (H.biUnion (reserveWedgeBlock u v))

theorem FiniteLaw.reserveCommonCenters_tail
    {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (reserve : Ω → Finset (Sym2 V)) (r C b : ℝ≥0)
    (hreserve : ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C ^ E.card * (r ^ E.card + b))
    (S : Finset V) (u v : V) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (s M : ℕ) (hM : 0 < M) (hs : 2 * s ≤ M) :
    L.probability (fun omega ↦ M ≤ (reserveCommonCenters S (reserve omega) u v).card) ≤
      (2 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2 / M) ^ s +
        (2 * (S.card : ℝ≥0) * C ^ 2 / M) ^ s * b := by
  let selected := fun omega ↦ reserveCommonCenters S (reserve omega) u v
  have ht := L.probability_card_inter_ge_le_powerMoment selected S s M
    (C ^ (2*s) * (r ^ (2*s) + b)) hM hs (fun H hH ↦ by
      have hm := mem_powersetCard.mp hH
      simpa only [hm.2] using L.reserveCommonCenters_subset_le reserve r C b hreserve S H hm.1 u v huv hu hv)
  have hsub (omega : Ω) : selected omega ⊆ S := filter_subset _ _
  simp_rw [inter_eq_right.mpr (hsub _)] at ht
  convert ht using 1
  rw [pow_mul, pow_mul]
  simp only [div_pow, mul_pow]
  ring

theorem FiniteLaw.reserveCommonCenters_tail_dyadic
    {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (reserve : Ω → Finset (Sym2 V)) (r C b : ℝ≥0)
    (hreserve : ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C ^ E.card * (r ^ E.card + b))
    (S : Finset V) (u v : V) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (s M : ℕ) (hM : 0 < M) (hs : 2 * s ≤ M)
    (hmean : 4 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2 ≤ M) :
    L.probability (fun omega ↦ M ≤ (reserveCommonCenters S (reserve omega) u v).card) ≤
      ((2 : ℝ≥0) ^ s)⁻¹ + (2 * (S.card : ℝ≥0) * C ^ 2 / M) ^ s * b := by
  apply (L.reserveCommonCenters_tail reserve r C b hreserve S u v huv hu hv s M hM hs).trans
  apply add_le_add _ le_rfl
  have hMreal : (0 : ℝ≥0) < M := by exact_mod_cast hM
  have hbase : 2 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2 / M ≤ (1 / 2 : ℝ≥0) := by
    apply (div_le_iff₀ hMreal).mpr
    calc
      _ = (4 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2) / 2 := by ring
      _ ≤ (M : ℝ≥0) / 2 := div_le_div_of_nonneg_right hmean zero_le
      _ = _ := by ring
  simpa only [one_div, inv_pow] using pow_le_pow_left' hbase s

theorem FiniteLaw.reserveCommonCenters_simultaneous_tail
    {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (reserve : Ω → Finset (Sym2 V)) (r C b : ℝ≥0)
    (hreserve : ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ E ⊆ reserve omega) ≤ C ^ E.card * (r ^ E.card + b))
    (S U : Finset V) (hSU : Disjoint S U)
    (s M : ℕ) (hM : 0 < M) (hs : 2 * s ≤ M) :
    L.probability (fun omega ↦ ∃ uv ∈ U.offDiag,
      M ≤ (reserveCommonCenters S (reserve omega) uv.1 uv.2).card) ≤
      (U.offDiag.card : ℝ≥0) * ((2 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2 / M) ^ s +
        (2 * (S.card : ℝ≥0) * C ^ 2 / M) ^ s * b) := by
  apply (L.probability_exists_le U.offDiag
    (fun uv omega ↦ M ≤ (reserveCommonCenters S (reserve omega) uv.1 uv.2).card)).trans
  calc
    _ ≤ ∑ _uv ∈ U.offDiag, ((2 * (S.card : ℝ≥0) * C ^ 2 * r ^ 2 / M) ^ s +
        (2 * (S.card : ℝ≥0) * C ^ 2 / M) ^ s * b) := by
      apply sum_le_sum
      intro uv huv
      have hm := mem_offDiag.mp huv
      exact L.reserveCommonCenters_tail reserve r C b hreserve S uv.1 uv.2 hm.2.2
        (fun hu ↦ disjoint_left.mp hSU hu hm.1)
        (fun hv ↦ disjoint_left.mp hSU hv hm.2.1) s M hM hs
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

end

end Erdos207
