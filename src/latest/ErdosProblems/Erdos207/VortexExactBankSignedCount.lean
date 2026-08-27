/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankCount
import ErdosProblems.Erdos207.VortexSignedMonomial

/-! # The exact-bank profile count with the source's full terminal denominator -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_exactBankProfiledExtensions_mul_terminal_pow_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    (W : Vortex V ell) {B R K : TripleSystemOn V} (t : VortexProfile ell)
    (hrho : 5 ≤ rho) (hj : 3 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) (hterminal : 0 < W.terminalSize) :
    (exactBankProfiledExtensions W rho j B R K t).card * W.terminalSize ^ t.mass ≤
      exactBankVortexCoefficient rho ell * W.terminalSize ^ (j - vortexRootExponent j R.card) * W.profileScale t := by
  let F := exactBankProfiledExtensions W rho j B R K t
  let code : TripleSystemOn V → VortexVertexProfile ell := exactBankVertexProfile W R K
  let target := W.terminalSize ^ (j - vortexRootExponent j R.card) * W.profileScale t
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun S ↦ code S = v).card * W.terminalSize ^ t.mass ≤ 2 ^ (rho ^ 3) * target := by
    intro v hv
    obtain ⟨S, hSF, hcode⟩ := mem_image.mp hv
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hdata := mem_exactBankOutsideExtensions_iff.mp hmem.1
    have hc := exactBank_completion_data hmem.1
    have hp := exactBank_vertexProfile_prefix W hrho hj hjrho hR hRcard
      hdata.1 hdata.2.1 hc.1 hc.2.1 hc.2.2 t hmem.2
    have hmono := W.vertexProfileMonomial_mul_terminal_pow_le
      (exactBankVertexProfile W R K S) t hp.1 hterminal (by
        intro k hk
        have h := hp.2 k
        rw [finPrefixSum_padTerminalExponent_of_le _ hk, finPrefixSum_profileExponentVector_of_le _ hk] at h
        exact h)
    change exactBankVertexProfile W R K S = v at hcode
    rw [hcode] at hmono
    calc
      _ ≤ (2 ^ (rho ^ 3) * (∏ i : Fin (ell + 1), (W.U i).card ^ v i)) * W.terminalSize ^ t.mass :=
        Nat.mul_le_mul_right _ (card_exactBank_profile_fiber_le W hrho v)
      _ = 2 ^ (rho ^ 3) * ((∏ i : Fin (ell + 1), (W.U i).card ^ v i) * W.terminalSize ^ t.mass) := by ring
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
    F.card * W.terminalSize ^ t.mass =
        ∑ v ∈ F.image code, (F.filter fun S ↦ code S = v).card * W.terminalSize ^ t.mass := by
      rw [card_eq_sum_card_image code F, sum_mul]
    _ ≤ ∑ _v ∈ F.image code, 2 ^ (rho ^ 3) * target := sum_le_sum hprofile
    _ = (2 ^ (rho ^ 3) * target) * (F.image code).card := by simp [Nat.mul_comm]
    _ ≤ (2 ^ (rho ^ 3) * target) * (rho + 1) ^ (ell + 1) :=
      Nat.mul_le_mul_left _ ((card_le_card hprofiles).trans_eq (card_vortexProfileBox _ _))
    _ = _ := by dsimp only [target, exactBankVortexCoefficient]; ring

theorem card_exactBankProfiledExtensions_signed_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    (W : Vortex V ell) {B R K : TripleSystemOn V} (t : VortexProfile ell)
    (hrho : 5 ≤ rho) (hj : 3 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) (hterminal : 0 < W.terminalSize) :
    ((exactBankProfiledExtensions W rho j B R K t).card : ℝ≥0) ≤
      (exactBankVortexCoefficient rho ell : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) *
        W.profileScale t / (W.terminalSize : ℝ≥0) ^ t.mass := by
  apply (le_div_iff₀ (pow_pos (by exact_mod_cast hterminal : (0 : ℝ≥0) < W.terminalSize) _)).mpr
  exact_mod_cast card_exactBankProfiledExtensions_mul_terminal_pow_le W t hrho hj hjrho hR hRcard hterminal

end

end Erdos207
