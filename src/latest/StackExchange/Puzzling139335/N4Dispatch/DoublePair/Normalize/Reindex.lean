import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.N4OuterPair.Defs

/-!
# Relabeling a reflected outer pair

This module only changes piece indices.  The horizontal reflection and
the bottom corner memberships are hypotheses; no geometric normalization
is concealed in the relabeling step.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair.Normalize

/-- Two distinct pieces can be placed first in the indexing. -/
theorem exists_perm_zero_one {i j : Fin 4} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  let τ := Equiv.swap (0 : Fin 4) i
  have hτ0 : τ 0 = i := Equiv.swap_apply_left _ _
  have hiτ1 : i ≠ τ 1 := by
    rw [← hτ0]
    exact τ.injective.ne (by decide)
  refine ⟨τ.trans (Equiv.swap (τ 1) j), ?_, ?_⟩
  · change Equiv.swap (τ 1) j (τ 0) = i
    rw [hτ0, Equiv.swap_apply_of_ne_of_ne hiτ1 hij]
  · change Equiv.swap (τ 1) j (τ 1) = j
    exact Equiv.swap_apply_left _ _

/-- A prescribed relabeling carries an already horizontal outer pair to
the standard configuration, preserving all four actual pieces. -/
theorem configuration_reindex_of_horizontal_pair
    (d : SquareDissection) {i j : Fin 4} (σ : Equiv.Perm (Fin 4))
    (hσ0 : σ 0 = i) (hσ1 : σ 1 = j)
    (hbottom_left : corner 0 ∈ d.piece i)
    (hbottom_right : corner 1 ∈ d.piece i)
    (hreflected : ReflectionSeparation.horizontal '' d.piece i = d.piece j)
    (hcornerless : ∀ k : Fin 4, k ≠ i → k ≠ j →
      ∀ c : Fin 4, corner c ∉ d.piece k) :
    N4OuterPair.Configuration (d.reindex σ) := by
  constructor
  · change corner 0 ∈ d.piece (σ 0)
    simpa only [hσ0] using hbottom_left
  · change corner 1 ∈ d.piece (σ 0)
    simpa only [hσ0] using hbottom_right
  · change ReflectionSeparation.horizontal '' d.piece (σ 0) = d.piece (σ 1)
    simpa only [hσ0, hσ1] using hreflected
  · intro k hk c
    have hk0 : k ≠ 0 := by
      rcases hk with rfl | rfl <;> decide
    have hk1 : k ≠ 1 := by
      rcases hk with rfl | rfl <;> decide
    have hki : σ k ≠ i := by
      intro heq
      exact hk0 (σ.injective (heq.trans hσ0.symm))
    have hkj : σ k ≠ j := by
      intro heq
      exact hk1 (σ.injective (heq.trans hσ1.symm))
    exact hcornerless (σ k) hki hkj c

/-- Relabel an already horizontal reflected pair, retaining a protected
center and recording the permutation used. -/
theorem exists_reindex_configuration_of_horizontal_pair
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hij : i ≠ j)
    (hbottom_left : corner 0 ∈ d.piece i)
    (hbottom_right : corner 1 ∈ d.piece i)
    (hreflected : ReflectionSeparation.horizontal '' d.piece i = d.piece j)
    (hcornerless : ∀ k : Fin 4, k ≠ i → k ≠ j →
      ∀ c : Fin 4, corner c ∉ d.piece k) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j ∧
      (d.reindex σ).HasProtectedCenter ∧ N4OuterPair.Configuration (d.reindex σ) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one hij
  refine ⟨σ, hσ0, hσ1, (d.reindex_hasProtectedCenter σ).mpr hc, ?_⟩
  exact configuration_reindex_of_horizontal_pair d σ hσ0 hσ1
    hbottom_left hbottom_right hreflected hcornerless

/-- An already horizontal reflected pair yields a standard outer-pair
configuration by relabeling alone. -/
theorem exists_configuration_of_horizontal_pair
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hij : i ≠ j)
    (hbottom_left : corner 0 ∈ d.piece i)
    (hbottom_right : corner 1 ∈ d.piece i)
    (hreflected : ReflectionSeparation.horizontal '' d.piece i = d.piece j)
    (hcornerless : ∀ k : Fin 4, k ≠ i → k ≠ j →
      ∀ c : Fin 4, corner c ∉ d.piece k) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' := by
  obtain ⟨σ, _, _, hc', hconfig⟩ :=
    exists_reindex_configuration_of_horizontal_pair d hc hij
      hbottom_left hbottom_right hreflected hcornerless
  exact ⟨d.reindex σ, hc', hconfig⟩

end Puzzling139335.N4Dispatch.DoublePair.Normalize
