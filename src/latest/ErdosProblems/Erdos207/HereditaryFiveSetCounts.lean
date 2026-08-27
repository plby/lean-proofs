/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedHereditaryLayers

/-! # The exact factors six and two in five-clique extension counts -/

namespace Erdos207

open Finset

noncomputable section

theorem hereditary_fiveSet_pair_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (hQ : Q.card = 2) (hgQ : good Q)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S)
    (lo : ℕ → ℝ) (hlo3 : 0 ≤ lo 3) (hlo4 : 0 ≤ lo 4)
    (hext : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → good S →
      lo S.card ≤ ((hereditaryExtensionVertices good S).card : ℝ)) :
    lo 2 * lo 3 * lo 4 / 6 ≤ ((rootedHereditaryLayer good Q 5).card : ℝ) := by
  have hstep (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
      ((rootedHereditaryLayer good Q k).card : ℝ) * lo k ≤
        (k + 1 - 2 : ℕ) * ((rootedHereditaryLayer good Q (k + 1)).card : ℝ) := by
    have h := rootedHereditaryLayer_card_lower good Q k (by omega) hdown (lo k)
      (fun S hS ↦ by
        have hm := (mem_rootedHereditaryLayer_iff good Q S k).mp hS
        simpa only [hm.1] using hext S (by omega) (by omega) hm.2.2)
    simpa only [hQ] using h
  have hbase : (rootedHereditaryLayer good Q 2).card = 1 := by
    rw [← hQ, rootedHereditaryLayer_base good Q hgQ, card_singleton]
  have h3 := hstep 2 (by omega) (by omega)
  have h4 := hstep 3 (by omega) (by omega)
  have h5 := hstep 4 (by omega) (by omega)
  norm_num only [hbase, Nat.reduceAdd, Nat.reduceSub, Nat.cast_one, Nat.cast_ofNat,
    one_mul] at h3 h4 h5
  have hfour : lo 2 * lo 3 ≤ 2 * ((rootedHereditaryLayer good Q 4).card : ℝ) :=
    (mul_le_mul_of_nonneg_right h3 hlo3).trans h4
  have hprod := mul_le_mul_of_nonneg_right hfour hlo4
  linarith

theorem hereditary_fiveSet_triple_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (T : Finset V) (hT : T.card = 3) (hgT : good T)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S)
    (hi : ℕ → ℝ) (hhi4 : 0 ≤ hi 4)
    (hext : ∀ S : Finset V, 3 ≤ S.card → S.card ≤ 4 → good S →
      ((hereditaryExtensionVertices good S).card : ℝ) ≤ hi S.card) :
    ((rootedHereditaryLayer good T 5).card : ℝ) ≤ hi 3 * hi 4 / 2 := by
  have hstep (k : ℕ) (hk3 : 3 ≤ k) (hk4 : k ≤ 4) :
      (k + 1 - 3 : ℕ) * ((rootedHereditaryLayer good T (k + 1)).card : ℝ) ≤
        ((rootedHereditaryLayer good T k).card : ℝ) * hi k := by
    have h := rootedHereditaryLayer_card_upper good T k (by omega) hdown (hi k)
      (fun S hS ↦ by
        have hm := (mem_rootedHereditaryLayer_iff good T S k).mp hS
        simpa only [hm.1] using hext S (by omega) (by omega) hm.2.2)
    simpa only [hT] using h
  have hbase : (rootedHereditaryLayer good T 3).card = 1 := by
    rw [← hT, rootedHereditaryLayer_base good T hgT, card_singleton]
  have h4 := hstep 3 (by omega) (by omega)
  have h5 := hstep 4 (by omega) (by omega)
  norm_num only [hbase, Nat.reduceAdd, Nat.reduceSub, Nat.cast_one, Nat.cast_ofNat,
    one_mul] at h4 h5
  have hprod := mul_le_mul_of_nonneg_right h4 hhi4
  linarith

end

end Erdos207
