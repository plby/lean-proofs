import StackExchange.Puzzling139335.CentralTwoPiece
import StackExchange.Puzzling139335.HalfTurnRemainder

/-!
# The actual half-turn-pair obstruction

If the half-turn about the square center exchanges any two pieces of a
four-piece dissection, the center cannot lie in the interior of any piece.
For either exchanged piece this is the fixed-point obstruction. For a
remaining piece, the actual remainder is a centrally symmetric Jordan
region with a proper common cut, so the central two-piece theorem applies.
-/

open Set Schoenflies

namespace Puzzling139335.SquareDissection

/-- The normalized half-turn-pair contradiction, with piece 0 containing
the center and pieces 2 and 3 actually exchanged. -/
theorem center_not_mem_of_halfTurn_pair_two_three (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3) :
    squareCenter ∉ interior (d.piece 0) := by
  intro hc
  obtain ⟨_, p, q, M, N, hcut, houter, hM, hN⟩ := d.pair_remainder_jordan hpair hc
  have hcongr : Congruent
      (closure (inside (M ∪ (d.piece 0 ∩ d.piece 1))))
      (closure (inside (N ∪ (d.piece 0 ∩ d.piece 1)))) := by
    rw [← hM, ← hN]
    exact d.congruent 0 1
  exact d.pair_remainder_center_not_mem_inter hc
    (hcut.center_mem_of_congruent_sides houter hcongr
      (d.pair_remainder_frontier_pointReflection hpair))

private theorem exists_halfTurn_reindex {k i j : Fin 4}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = k ∧ σ 2 = i ∧ σ 3 = j := by
  let τ₀ := Equiv.swap (0 : Fin 4) k
  have hτ₀ : τ₀ 0 = k := Equiv.swap_apply_left _ _
  have hkτ₂ : k ≠ τ₀ 2 := by
    rw [← hτ₀]
    exact τ₀.injective.ne (by decide)
  let τ := τ₀.trans (Equiv.swap (τ₀ 2) i)
  have hτ0 : τ 0 = k := by
    change Equiv.swap (τ₀ 2) i (τ₀ 0) = k
    rw [hτ₀, Equiv.swap_apply_of_ne_of_ne hkτ₂ hki]
  have hτ2 : τ 2 = i := Equiv.swap_apply_left _ _
  have hkτ₃ : k ≠ τ 3 := by
    rw [← hτ0]
    exact τ.injective.ne (by decide)
  have hiτ₃ : i ≠ τ 3 := by
    rw [← hτ2]
    exact τ.injective.ne (by decide)
  refine ⟨τ.trans (Equiv.swap (τ 3) j), ?_, ?_, ?_⟩
  · change Equiv.swap (τ 3) j (τ 0) = k
    rw [hτ0, Equiv.swap_apply_of_ne_of_ne hkτ₃ hkj]
  · change Equiv.swap (τ 3) j (τ 2) = i
    rw [hτ2, Equiv.swap_apply_of_ne_of_ne hiτ₃ hij]
  · change Equiv.swap (τ 3) j (τ 3) = j
    exact Equiv.swap_apply_left _ _

/-- An actual centered half-turn pair rules out a protected center,
regardless of the labels of the pair or of the center-containing piece. -/
theorem not_hasProtectedCenter_of_halfTurn_pair (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i = d.piece j) :
    ¬d.HasProtectedCenter := by
  rintro ⟨k, hk⟩
  have hfixed := d.center_not_mem_fixed_pair hij
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) hpair (by simp)
  have hki : k ≠ i := by
    intro heq
    exact hfixed.1 (heq ▸ hk)
  have hkj : k ≠ j := by
    intro heq
    exact hfixed.2 (heq ▸ hk)
  obtain ⟨σ, hσ0, hσ2, hσ3⟩ := exists_halfTurn_reindex hki hkj hij
  apply (d.reindex σ).center_not_mem_of_halfTurn_pair_two_three
  · change AffineIsometryEquiv.pointReflection ℝ squareCenter ''
      d.piece (σ 2) = d.piece (σ 3)
    simpa only [hσ2, hσ3] using hpair
  · change squareCenter ∈ interior (d.piece (σ 0))
    simpa only [hσ0] using hk

end Puzzling139335.SquareDissection
