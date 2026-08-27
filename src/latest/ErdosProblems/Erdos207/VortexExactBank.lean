/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexPrefix

/-! # Exact-bank profile bounds in a vortex -/

namespace Erdos207

open Finset

noncomputable section

lemma exactBank_decomposition
    {V : Type*} [DecidableEq V]
    {B S K E : TripleSystemOn V}
    (hEout : E \ B = S) (hEin : E ∩ B = K) :
    E = S ∪ K := by
  calc
    E = (E \ B) ∪ (E ∩ B) := (sdiff_union_inter E B).symm
    _ = S ∪ K := by rw [hEout, hEin]

lemma exactBank_sdiff_root_union
    {V : Type*} [DecidableEq V]
    {B R S K E : TripleSystemOn V}
    (hRS : R ⊆ S) (hEout : E \ B = S) (hEin : E ∩ B = K) :
    E \ (R ∪ K) = S \ R := by
  have hdecomp := exactBank_decomposition hEout hEin
  have hSK : Disjoint S K := by
    rw [Finset.disjoint_left]
    intro T hTS hTK
    have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
    have hTinter : T ∈ E ∩ B := by simpa only [hEin] using hTK
    exact (mem_sdiff.mp hTdiff).2 (mem_inter.mp hTinter).2
  ext T
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hTE, hTnot⟩
    rw [hdecomp] at hTE
    rcases mem_union.mp hTE with hTS | hTK
    · exact ⟨hTS, fun hTR ↦ hTnot (Or.inl hTR)⟩
    · exact (hTnot (Or.inr hTK)).elim
  · rintro ⟨hTS, hTnotR⟩
    refine ⟨by rw [hdecomp]; exact mem_union_left K hTS, ?_⟩
    rintro (hTR | hTK)
    · exact hTnotR hTR
    · exact (Finset.disjoint_left.mp hSK hTS hTK).elim

/-- For an exact bank class, minimality leaves at most the KSSS root
exponent's complement many vertices outside the fixed root and bank. -/
theorem exactBank_extraVertices_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 3 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K) :
    (verticesOn E \ verticesOn (R ∪ K)).card ≤
      j - vortexRootExponent j R.card := by
  let hS : S ∈ exactBankOutsideExtensions rho j B R K :=
    mem_exactBankOutsideExtensions_iff.mpr
      ⟨hScard, hRS, E, hE, hEout, hEin⟩
  have hKcard : K.card = rho - j :=
    exactBankOutsideExtensions_bank_card (by omega) (by omega) hjrho hS
  have hQcard : (R ∪ K).card = R.card + K.card :=
    exactBankOutsideExtensions_root_union_card hS
  have hQsubE : R ∪ K ⊆ E := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTK
    · have hTS := hRS hTR
      have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
      exact (mem_sdiff.mp hTdiff).1
    · have hTinter : T ∈ E ∩ B := by rw [hEin]; exact hTK
      exact (mem_inter.mp hTinter).1
  have hspanE : (verticesOn E).card = rho :=
    IsErdosConfig.vertices_card_eq hE hrho
  have hextra : (verticesOn E \ verticesOn (R ∪ K)).card =
      rho - (verticesOn (R ∪ K)).card := by
    rw [card_sdiff_of_subset (verticesOn_mono hQsubE), hspanE]
  by_cases hRone : R.card = 1
  · have hspan := exactBankOutsideExtensions_root_span_weak
      hrho (by rw [hQcard, hRone]; omega) hS
    rw [hextra, hRone, vortexRootExponent_one]
    omega
  · by_cases hRfull : R.card = j - 2
    · have hRS_eq : R = S :=
        Finset.eq_of_subset_of_card_le hRS (by rw [hScard, hRfull])
      have hEQ : E = R ∪ K := by
        rw [exactBank_decomposition hEout hEin, hRS_eq]
      rw [hEQ]
      have hempty : verticesOn (R ∪ K) \ verticesOn (R ∪ K) = ∅ :=
        sdiff_self
      rw [hempty]
      exact Nat.zero_le _
    · have hRtwo : 2 ≤ R.card := by
        have hRpos : 0 < R.card := card_pos.mpr hR
        omega
      have hRsmall : R.card ≤ j - 3 := by omega
      have hspan := exactBankOutsideExtensions_root_span
        (by rw [hQcard]; omega) (by rw [hQcard, hKcard]; omega) hS
      rw [hextra, vortexRootExponent_middle hRone hRfull]
      omega

/-- Exact-bank configurations satisfy the cumulative vertex/triangle profile
domination that drives KSSS Lemma 7.2. -/
theorem exactBank_vertexProfile_prefix
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    (W : Vortex V ell) {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 3 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K)
    (t : VortexProfile ell) (ht : W.outerProfile (S \ R) = t) :
    let extra := verticesOn E \ verticesOn (R ∪ K)
    let bound := j - vortexRootExponent j R.card
    (∑ i, W.vertexProfile extra i) ≤ bound ∧
      FinPrefixLe
        (padTerminalExponent (W.vertexProfile extra) (max bound t.mass))
        (profileExponentVector bound t) := by
  dsimp only
  let extra := verticesOn E \ verticesOn (R ∪ K)
  let bound := j - vortexRootExponent j R.card
  have hextraBound : extra.card ≤ bound :=
    exactBank_extraVertices_card_le hrho hj hjrho hR hRcard
      hScard hRS hE hEout hEin
  have hvsum : (∑ i, W.vertexProfile extra i) = extra.card := by
    exact W.sum_vertexProfile extra
  refine ⟨by rw [hvsum]; exact hextraBound, ?_⟩
  intro k
  by_cases hk : k ≤ ell
  · rw [finPrefixSum_padTerminalExponent_of_le _ hk,
      finPrefixSum_profileExponentVector_of_le _ hk,
      W.finPrefixSum_vertexProfile extra k,
      ← ht, W.finPrefixSum_outerProfile (S \ R) hk]
    let A := W.verticesBefore extra k
    have hAE : A ⊆ verticesOn E := by
      intro x hx
      exact (mem_sdiff.mp ((W.mem_verticesBefore_iff extra x).mp hx).1).1
    have hAcard : A.card ≤ rho - 2 := by
      have hAextra : A ⊆ extra := fun x hx ↦
        (W.mem_verticesBefore_iff extra x).mp hx |>.1
      have := (card_le_card hAextra).trans hextraBound
      have hexp := add_two_le_vortexRootExponent j R.card
      dsimp only [bound] at this
      omega
    have hlower := IsErdosConfig.card_le_trianglesTouching
      hE hrho A hAE hAcard
    have htouch := W.trianglesTouching_verticesBefore_subset
      (k := k) E (R ∪ K)
    have hdiff : E \ (R ∪ K) = S \ R :=
      exactBank_sdiff_root_union hRS hEout hEin
    calc
      A.card ≤ (trianglesTouching E A).card := hlower
      _ ≤ (W.trianglesBefore (E \ (R ∪ K)) k).card :=
        card_le_card htouch
      _ = (W.trianglesBefore (S \ R) k).card := by rw [hdiff]
  · have hkfull : ell + 1 ≤ k := by omega
    rw [finPrefixSum_eq_sum_of_length_le _ hkfull,
      finPrefixSum_eq_sum_of_length_le _ hkfull,
      sum_padTerminalExponent (by
        rw [hvsum]
        exact hextraBound.trans (le_max_left _ _)),
      sum_profileExponentVector]

end

end Erdos207
