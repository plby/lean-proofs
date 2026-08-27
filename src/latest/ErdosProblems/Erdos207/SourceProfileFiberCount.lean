/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexSignedMonomial
import ErdosProblems.Erdos207.VortexExactBankCount

/-! # Signed profile counting from a bounded finite vertex encoding -/

namespace Erdos207

open Finset

noncomputable section

theorem card_vertex_encoding_profile_fiber_le
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    {ell c : ℕ} (W : Vortex V ell) (F : Finset α) (extra : α → Finset V)
    (hfiber : ∀ A : Finset V, (F.filter fun x ↦ extra x = A).card ≤ c)
    (v : VortexVertexProfile ell) :
    (F.filter fun x ↦ W.vertexProfile (extra x) = v).card ≤
      c * ∏ i : Fin (ell + 1), (W.U i).card ^ v i := by
  let G := F.filter fun x ↦ W.vertexProfile (extra x) = v
  have hGfiber : ∀ A ∈ G.image extra, (G.filter fun x ↦ extra x = A).card ≤ c := by
    intro A _hA
    apply (card_le_card (show (G.filter fun x ↦ extra x = A) ⊆ F.filter (fun x ↦ extra x = A) from ?_)).trans (hfiber A)
    intro x hx
    have h := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp h.1).1, h.2⟩
  have himage : G.image extra ⊆ W.vertexSetsWithProfile v := by
    intro A hA
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hA
    exact (W.mem_vertexSetsWithProfile_iff v _).mpr (mem_filter.mp hx).2
  calc
    G.card ≤ c * (G.image extra).card := card_le_mul_card_image G c hGfiber
    _ ≤ c * (W.vertexSetsWithProfile v).card := Nat.mul_le_mul_left _ (card_le_card himage)
    _ ≤ _ := Nat.mul_le_mul_left _ (W.card_vertexSetsWithProfile_le v)

theorem card_mul_terminal_pow_le_of_vertex_encoding
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    {ell r d c : ℕ} (W : Vortex V ell) (F : Finset α) (extra : α → Finset V)
    (t : VortexProfile ell) (hterminal : 0 < W.terminalSize)
    (hfiber : ∀ A : Finset V, (F.filter fun x ↦ extra x = A).card ≤ c)
    (hsize : ∀ x ∈ F, (extra x).card ≤ r)
    (hbound : ∀ x ∈ F, (extra x).card ≤ d ∧
      ∀ k ≤ ell, finPrefixSum (W.vertexProfile (extra x)) k ≤ finPrefixSum t k) :
    F.card * W.terminalSize ^ t.mass ≤
      ((r + 1) ^ (ell + 1) * c) * W.terminalSize ^ d * W.profileScale t := by
  let code := fun x ↦ W.vertexProfile (extra x)
  let target := W.terminalSize ^ d * W.profileScale t
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun x ↦ code x = v).card * W.terminalSize ^ t.mass ≤ c * target := by
    intro v hv
    obtain ⟨x, hxF, hcode⟩ := mem_image.mp hv
    have hb := hbound x hxF
    have hsum : (∑ i, W.vertexProfile (extra x) i) ≤ d := by
      rw [W.sum_vertexProfile]
      exact hb.1
    have hmono := W.vertexProfileMonomial_mul_terminal_pow_le (W.vertexProfile (extra x)) t
      hsum hterminal hb.2
    change W.vertexProfile (extra x) = v at hcode
    rw [hcode] at hmono
    calc
      _ ≤ (c * (∏ i : Fin (ell + 1), (W.U i).card ^ v i)) * W.terminalSize ^ t.mass :=
        Nat.mul_le_mul_right _ (card_vertex_encoding_profile_fiber_le W F extra hfiber v)
      _ = c * ((∏ i : Fin (ell + 1), (W.U i).card ^ v i) * W.terminalSize ^ t.mass) := by ring
      _ ≤ c * target := Nat.mul_le_mul_left _ hmono
  have hprofiles : F.image code ⊆ vortexProfileBox (ell + 1) r := by
    intro v hv
    obtain ⟨x, hxF, rfl⟩ := mem_image.mp hv
    rw [mem_vortexProfileBox_iff]
    intro i
    exact (card_le_card (inter_subset_left : extra x ∩ W.verticesAtLevel i ⊆ extra x)).trans (hsize x hxF)
  calc
    F.card * W.terminalSize ^ t.mass =
        ∑ v ∈ F.image code, (F.filter fun x ↦ code x = v).card * W.terminalSize ^ t.mass := by
      rw [card_eq_sum_card_image code F, sum_mul]
    _ ≤ ∑ _v ∈ F.image code, c * target := sum_le_sum hprofile
    _ = (c * target) * (F.image code).card := by simp [Nat.mul_comm]
    _ ≤ (c * target) * (r + 1) ^ (ell + 1) :=
      Nat.mul_le_mul_left _ ((card_le_card hprofiles).trans_eq (card_vortexProfileBox _ _))
    _ = _ := by dsimp only [target]; ring

end

end Erdos207
