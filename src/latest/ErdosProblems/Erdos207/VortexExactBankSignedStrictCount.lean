/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankSignedCount
import ErdosProblems.Erdos207.VortexExactBankStrictCount

/-! # Strict exact-bank counts with the full terminal denominator -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_exactBankProfiledExtensions_mul_terminal_pow_le_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j d : ℕ}
    (W : Vortex V ell) {B R K : TripleSystemOn V}
    (t u : VortexProfile ell) (hrho : 5 ≤ rho) (hterminal : 0 < W.terminalSize)
    (hbound : ∀ S ∈ exactBankProfiledExtensions W rho j B R K t,
      (∑ i, exactBankVertexProfile W R K S i) ≤ d ∧
        ∀ k ≤ ell, finPrefixSum (exactBankVertexProfile W R K S) k ≤ finPrefixSum u k) :
    (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ u.mass ≤
      exactBankVortexCoefficient rho ell * W.terminalSize ^ d * W.profileScale u := by
  let F := exactBankProfiledExtensions W rho j B R K t
  let code : TripleSystemOn V → VortexVertexProfile ell := exactBankVertexProfile W R K
  let target := W.terminalSize ^ d * W.profileScale u
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun S ↦ code S = v).card * W.terminalSize ^ u.mass ≤ 2 ^ (rho ^ 3) * target := by
    intro v hv
    obtain ⟨S, hSF, hcode⟩ := mem_image.mp hv
    have hp := hbound S hSF
    have hmono := W.vertexProfileMonomial_mul_terminal_pow_le
      (exactBankVertexProfile W R K S) u hp.1 hterminal hp.2
    change exactBankVertexProfile W R K S = v at hcode
    rw [hcode] at hmono
    calc
      _ ≤ (2 ^ (rho ^ 3) * (∏ i : Fin (ell + 1), (W.U i).card ^ v i)) * W.terminalSize ^ u.mass :=
        Nat.mul_le_mul_right _ (card_exactBank_profile_fiber_le W hrho v)
      _ = 2 ^ (rho ^ 3) * ((∏ i : Fin (ell + 1), (W.U i).card ^ v i) * W.terminalSize ^ u.mass) := by ring
      _ ≤ 2 ^ (rho ^ 3) * target := Nat.mul_le_mul_left _ hmono
  have hprofiles : F.image code ⊆ vortexProfileBox (ell + 1) rho := by
    intro v hv
    obtain ⟨S, hSF, rfl⟩ := mem_image.mp hv
    rw [mem_vortexProfileBox_iff]
    intro i
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hE := (exactBank_completion_data hmem.1).1
    calc
      exactBankVertexProfile W R K S i ≤ (exactBankExtraVertices R K S).card := card_le_card inter_subset_left
      _ ≤ (verticesOn (S ∪ K)).card := card_le_card sdiff_subset
      _ = rho := IsErdosConfig.vertices_card_eq hE hrho
  calc
    F.card * W.terminalSize ^ u.mass =
        ∑ v ∈ F.image code, (F.filter fun S ↦ code S = v).card * W.terminalSize ^ u.mass := by
      rw [card_eq_sum_card_image code F, sum_mul]
    _ ≤ ∑ _v ∈ F.image code, 2 ^ (rho ^ 3) * target := sum_le_sum hprofile
    _ = (2 ^ (rho ^ 3) * target) * (F.image code).card := by simp [Nat.mul_comm]
    _ ≤ (2 ^ (rho ^ 3) * target) * (rho + 1) ^ (ell + 1) :=
      Nat.mul_le_mul_left _ ((card_le_card hprofiles).trans_eq (card_vortexProfileBox _ _))
    _ = _ := by dsimp only [target, exactBankVortexCoefficient]; ring

theorem card_exactBankProfiledExtensions_mul_root_terminal_pow_le_of_strict_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j d : ℕ}
    (W : Vortex V (m + 1)) {B R K : TripleSystemOn V}
    (t : VortexProfile (m + 1)) (hrho : 5 ≤ rho)
    (hterminal : 0 < W.terminalSize) (ht0 : 0 < t 0)
    (hbound : ∀ S ∈ exactBankProfiledExtensions W rho j B R K t,
      (∑ i, exactBankVertexProfile W R K S i) ≤ d ∧
        ∀ k ≤ m + 1, finPrefixSum (exactBankVertexProfile W R K S) k ≤ finPrefixSum t.dropFirst k) :
    (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.mass ≤
      exactBankVortexCoefficient rho (m + 1) * W.terminalSize ^ (d + 1) * W.profileScale t := by
  have h := card_exactBankProfiledExtensions_mul_terminal_pow_le_of_bounds
    W t t.dropFirst hrho hterminal hbound
  calc
    _ = ((W.U 0).card * W.terminalSize) *
        ((exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.dropFirst.mass) := by
      rw [← t.dropFirst_mass_add_one ht0, pow_succ]
      ring
    _ ≤ ((W.U 0).card * W.terminalSize) *
        (exactBankVortexCoefficient rho (m + 1) * W.terminalSize ^ d * W.profileScale t.dropFirst) :=
      Nat.mul_le_mul_left _ h
    _ = _ := by
      rw [pow_succ, ← W.profileScale_dropFirst t ht0]
      ring

theorem card_exactBankProfiledExtensions_mul_root_terminal_pow_le_nonempty_bank
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R K : TripleSystemOn V}
    (t : VortexProfile (m + 1))
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) (hK : K.Nonempty)
    (ht0 : 0 < t 0) (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.mass ≤
      exactBankVortexCoefficient rho (m + 1) * W.terminalSize ^ (j - vortexRootExponent j R.card + 1) * W.profileScale t := by
  apply card_exactBankProfiledExtensions_mul_root_terminal_pow_le_of_strict_bounds W t hrho hterminal ht0
  intro S hS
  have hm := mem_exactBankProfiledExtensions_iff.mp hS
  have hd := mem_exactBankOutsideExtensions_iff.mp hm.1
  have hc := exactBank_completion_data hm.1
  have hp := exactBank_vertexProfile_prefix_nonempty_bank W hrho hj hjrho hR hRcard hK
    hd.1 hd.2.1 hc.1 hc.2.1 hc.2.2 t hm.2 ht0
  refine ⟨hp.1, ?_⟩
  intro k hk
  have h := hp.2 k
  rw [finPrefixSum_padTerminalExponent_of_le _ hk, finPrefixSum_profileExponentVector_of_le _ hk] at h
  exact h

theorem card_exactBankProfiledExtensions_mul_root_terminal_pow_le_singleton_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R K : TripleSystemOn V}
    (t : VortexProfile (m + 1))
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hRcard : R.card = 1) (hK : K.Nonempty)
    (ht0 : 0 < t 0) (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.mass ≤
      exactBankVortexCoefficient rho (m + 1) * W.terminalSize ^ (j - 3) * W.profileScale t := by
  rw [show j - 3 = (j - 4) + 1 by omega]
  apply card_exactBankProfiledExtensions_mul_root_terminal_pow_le_of_strict_bounds W t hrho hterminal ht0
  intro S hS
  have hm := mem_exactBankProfiledExtensions_iff.mp hS
  have hd := mem_exactBankOutsideExtensions_iff.mp hm.1
  have hc := exactBank_completion_data hm.1
  have hp := exactBank_vertexProfile_prefix_singleton_nonempty W hrho hj hjrho hRcard hK
    hd.1 hd.2.1 hc.1 hc.2.1 hc.2.2 t hm.2 ht0
  refine ⟨hp.1, ?_⟩
  intro k hk
  have h := hp.2 k
  rw [finPrefixSum_padTerminalExponent_of_le _ hk, finPrefixSum_profileExponentVector_of_le _ hk] at h
  exact h

theorem card_exactBankProfiledExtensions_mul_terminal_pow_le_singleton_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    (W : Vortex V ell) {B R K : TripleSystemOn V}
    (t : VortexProfile ell)
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hRcard : R.card = 1) (hK : K.Nonempty) (hterminal : 0 < W.terminalSize) :
    (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.mass ≤
      exactBankVortexCoefficient rho ell * W.terminalSize ^ (j - 4) * W.profileScale t := by
  apply card_exactBankProfiledExtensions_mul_terminal_pow_le_of_bounds W t t hrho hterminal
  intro S hS
  have hm := mem_exactBankProfiledExtensions_iff.mp hS
  have hd := mem_exactBankOutsideExtensions_iff.mp hm.1
  have hc := exactBank_completion_data hm.1
  have hsum := exactBank_extraVertices_card_le_singleton_nonempty hrho hj hjrho hRcard hK
    hd.1 hd.2.1 hc.1 hc.2.1 hc.2.2
  have hR : R.Nonempty := card_pos.mp (by omega)
  have hRle : R.card ≤ j - 2 := by omega
  have hp := exactBank_vertexProfile_prefix W hrho (by omega) hjrho hR hRle
    hd.1 hd.2.1 hc.1 hc.2.1 hc.2.2 t hm.2
  refine ⟨?_, ?_⟩
  · simpa only [exactBankVertexProfile, W.sum_vertexProfile, exactBankExtraVertices] using hsum
  · intro k hk
    have h := hp.2 k
    rw [finPrefixSum_padTerminalExponent_of_le _ hk, finPrefixSum_profileExponentVector_of_le _ hk] at h
    exact h

end

end Erdos207
