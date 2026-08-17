/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Util.Density

/-!
# Density squeeze lemmas for Erdős Problem 144

This file records the elementary final density argument used in the proof of
Erdős Problem 144.  A set of natural numbers has density one if it contains
sets of existing natural density arbitrarily close to one.
-/

namespace Erdos144

open Filter
open scoped Topology

/-- Partial natural density is monotone under inclusion. -/
lemma partialDensity_mono_of_subset {S T : Set ℕ} (hST : S ⊆ T) (n : ℕ) :
    S.partialDensity Set.univ n ≤ T.partialDensity Set.univ n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (by
    rintro x ⟨⟨hxS, hxU⟩, hxn⟩
    exact ⟨⟨hST hxS, hxU⟩, hxn⟩)

/-- If, below every threshold `a < 1`, a set `S` contains a set of an
existing density strictly larger than `a`, then `S` has natural density one.

This formulation does not assume in advance that `S` itself has a density.
-/
theorem hasDensity_one_of_arbitrarily_high_density_subsets {S : Set ℕ}
    (happrox : ∀ a : ℝ, a < 1 →
      ∃ A : Set ℕ, ∃ d : ℝ, A ⊆ S ∧ A.HasDensity d ∧ a < d) :
    S.HasDensity 1 := by
  rw [Set.HasDensity]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨A, d, hAS, hA, had⟩ := happrox a ha
    filter_upwards [(tendsto_order.1 hA).1 a had] with n hn
    exact hn.trans_le (partialDensity_mono_of_subset hAS n)
  · intro b hb
    exact Filter.Eventually.of_forall fun n ↦
      (Set.partialDensity_le_one S Set.univ n).trans_lt hb

/-- Epsilon version of
`hasDensity_one_of_arbitrarily_high_density_subsets`: it is enough to have,
for every positive `ε`, a subset whose existing density is at least
`1 - ε`. -/
theorem hasDensity_one_of_approximate_subsets {S : Set ℕ}
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ A : Set ℕ, ∃ d : ℝ, A ⊆ S ∧ A.HasDensity d ∧ 1 - ε ≤ d) :
    S.HasDensity 1 := by
  apply hasDensity_one_of_arbitrarily_high_density_subsets
  intro a ha
  obtain ⟨A, d, hAS, hA, hd⟩ := happrox ((1 - a) / 2) (by linarith)
  exact ⟨A, d, hAS, hA, by linarith⟩

/-- Sequence version of the density squeeze: if `A k ⊆ S`, every `A k` has
density `d k`, and these densities tend to one, then `S` has density one. -/
theorem hasDensity_one_of_tendsto_subsets {S : Set ℕ} (A : ℕ → Set ℕ)
    (d : ℕ → ℝ) (hAS : ∀ k, A k ⊆ S)
    (hA : ∀ k, (A k).HasDensity (d k))
    (hd : Tendsto d atTop (nhds 1)) :
    S.HasDensity 1 := by
  apply hasDensity_one_of_arbitrarily_high_density_subsets
  intro a ha
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hd).1 a ha).exists
  exact ⟨A k, d k, hAS k, hA k, hk⟩

/-- Error-bound version of the density squeeze.  The exact densities need
not themselves be exhibited as converging: a lower bound `1 - e k`, with
`e k → 0`, suffices. -/
theorem hasDensity_one_of_subsets_with_vanishing_error {S : Set ℕ}
    (A : ℕ → Set ℕ) (d e : ℕ → ℝ) (hAS : ∀ k, A k ⊆ S)
    (hA : ∀ k, (A k).HasDensity (d k)) (hde : ∀ k, 1 - e k ≤ d k)
    (he : Tendsto e atTop (nhds 0)) :
    S.HasDensity 1 := by
  apply hasDensity_one_of_arbitrarily_high_density_subsets
  intro a ha
  have hevent := (tendsto_order.1 he).2 (1 - a) (by linarith)
  obtain ⟨k, hk⟩ := hevent.exists
  exact ⟨A k, d k, hAS k, hA k, lt_of_lt_of_le (by linarith) (hde k)⟩

end Erdos144
