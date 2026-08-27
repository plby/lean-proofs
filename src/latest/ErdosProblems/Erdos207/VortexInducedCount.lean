/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankCount

/-! # Profiled counting for the absorber-induced forbidden family -/

namespace Erdos207

open Finset

noncomputable section

/-- A deliberately explicit finite coefficient: sum over every possible
minimal-configuration order and every possible exact bank part of size at
most the forbidden cutoff.  The cardinality restriction is essential: an
Erdős configuration of order at most `q` cannot meet the absorber bank in
more than `q` triangles. -/
def inducedVortexCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q ell : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ rho ∈ Icc 5 q, ∑ _K ∈ B.powerset.filter (fun K ↦ K.card ≤ q),
    exactBankVortexCoefficient rho ell

def profiledExactBankCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q j : ℕ) (B R : TripleSystemOn V)
  (t : VortexProfile ell) : ForbiddenFamilyOn V :=
  (Icc 5 q).biUnion fun rho ↦
    (B.powerset.filter (fun K ↦ K.card ≤ q)).biUnion fun K ↦
      exactBankProfiledExtensions W rho j B R K t

lemma profiledExtensions_absorberInduced_subset_exactBankCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V)
    (t : VortexProfile ell) :
    W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t ⊆
      profiledExactBankCover W q j B R t := by
  intro S hS
  have hm := W.mem_profiledExtensions_iff
    (absorberInducedConfigurationsOn q j B) R t S |>.mp hS
  obtain ⟨hScard, rho, hrho5, hrhoq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hm.1
  let K := E ∩ B
  have hKB : K ⊆ B := inter_subset_right
  have hSexact : S ∈ exactBankOutsideExtensions rho j B R K :=
    mem_exactBankOutsideExtensions_iff.mpr
      ⟨hScard, hm.2.1, E, hE, hEout, rfl⟩
  apply mem_biUnion.mpr
  refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨K, mem_filter.mpr ⟨mem_powerset.mpr hKB, ?_⟩, ?_⟩
  · have hKE : K ⊆ E := inter_subset_left
    exact (card_le_card hKE).trans (by rw [hE.1.1]; omega)
  exact mem_exactBankProfiledExtensions_iff.mpr ⟨hSexact, hm.2.2⟩

lemma exactBank_index_order_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R K S : TripleSystemOn V}
    (hj : 3 ≤ j)
    (hS : S ∈ exactBankOutsideExtensions rho j B R K) : j ≤ rho := by
  obtain ⟨hScard, _hRS, E, hE, hEout, _hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hSE : S ⊆ E := by
    intro T hTS
    have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
    exact (mem_sdiff.mp hTdiff).1
  have hc := card_le_card hSE
  rw [hScard, hE.1.1] at hc
  omega

/-- W1's profiled extension bound, before the coefficient is renamed `z`. -/
theorem card_profiledExtensions_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V)
    (t : VortexProfile ell)
    (hj : 3 ≤ j) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) :
    (W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card ≤
      inducedVortexCoefficient q ell B *
        W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) *
        W.profileScale t := by
  let target := W.terminalSize ^
      (j - t.mass - vortexRootExponent j R.card) * W.profileScale t
  calc
    (W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card ≤
        (profiledExactBankCover W q j B R t).card :=
      card_le_card
        (profiledExtensions_absorberInduced_subset_exactBankCover W B R t)
    _ ≤ ∑ rho ∈ Icc 5 q,
        ∑ K ∈ B.powerset.filter (fun K ↦ K.card ≤ q),
        (exactBankProfiledExtensions W rho j B R K t).card := by
      unfold profiledExactBankCover
      exact (card_biUnion_le.trans (sum_le_sum fun rho _hrho ↦
        card_biUnion_le))
    _ ≤ ∑ rho ∈ Icc 5 q,
        ∑ _K ∈ B.powerset.filter (fun K ↦ K.card ≤ q),
        exactBankVortexCoefficient rho ell * target := by
      apply sum_le_sum
      intro rho hrho
      apply sum_le_sum
      intro K _hK
      have hr := mem_Icc.mp hrho
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hSF⟩ := hF
        have hSexact := (mem_exactBankProfiledExtensions_iff.mp hSF).1
        have hjrho := exactBank_index_order_le hj hSexact
        simpa only [target, mul_assoc] using
          (card_exactBankProfiledExtensions_le
            (B := B) (R := R) (K := K)
            W t hr.1 hj hjrho hR hRcard hterminal)
      · rw [not_nonempty_iff_eq_empty.mp hF]
        simp
    _ = inducedVortexCoefficient q ell B *
        W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) *
        W.profileScale t := by
      simp only [inducedVortexCoefficient, target, Finset.sum_mul,
        mul_assoc]

end

end Erdos207
