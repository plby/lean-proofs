import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.LowerConstruction
import ErdosProblems.Erdos336.FiniteTwoPointExponent
import ErdosProblems.Erdos336.PeriodicLift

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Actual periodic asymptotic bases attaining the 1/3 lower coefficient
-/

namespace Erdos336.Problem336

open Erdos336

private lemma lower_modulus_pos' (u : ℕ) : 0 < lowerModulus u := by
  simp [lowerModulus]

/-- The finite two-residue set has positive diameter at most `3u`. -/
theorem lowerResidues_groupRepAtMost
    (u : ℕ) (hu : 1 ≤ u) (y : ZMod (lowerModulus u)) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 3 * u ∧
      GroupRepExactly (lowerResidues u) k y := by
  let g := lowerModulus u
  let x := lowerStep u
  let n := y.val
  haveI : NeZero g := ⟨by dsimp [g]; exact Nat.ne_of_gt (lower_modulus_pos' u)⟩
  have hn : n < lowerModulus u := by
    dsimp [n, g] at *
    exact ZMod.val_lt y
  obtain ⟨Q, R, hpos, hle, heq⟩ :=
    lower_cyclic_cover_multiple_three u n hu hn
  let k := Q + R
  let xs : List (ZMod g) :=
    List.replicate Q (x : ZMod g) ++ List.replicate R 1
  refine ⟨k, hpos, hle, xs, ?_, ?_, ?_⟩
  · simp [xs, k]
  · intro a ha
    simp only [xs, List.mem_append, List.mem_replicate] at ha
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hny : (n : ZMod g) = y := by
      dsimp [n]
      exact ZMod.natCast_zmod_val y
    simp only [xs, List.sum_append, List.sum_replicate, nsmul_eq_mul]
    have hcast : ((Q * lowerStep u + R : ℕ) : ZMod g) = y := by
      rcases heq with heq | heq
      · rw [heq]
        exact hny
      · rw [heq, Nat.cast_add]
        dsimp [g] at *
        rw [ZMod.natCast_self, add_zero]
        exact hny
    rw [show (Q : ZMod g) * (x : ZMod g) + (R : ZMod g) * 1 =
      ((Q * lowerStep u + R : ℕ) : ZMod g) by
        dsimp [x]
        push_cast
        ring]
    exact hcast

/-- The periodic lift of the two residues is an at-most-`3u` basis. -/
theorem lowerPeriodic_eventuallyAtMost
    (u : ℕ) (hu : 1 ≤ u) :
    EventuallyAtMost (PeriodicLift (lowerResidues u)) (3 * u) := by
  apply eventuallyAtMost_periodic_of_groupRepAtMost (lower_modulus_pos' u)
  exact lowerResidues_groupRepAtMost u hu

/-- The same periodic lift has exact asymptotic order exactly
`3u²+4u = lowerModulus u - 1`. -/
theorem lowerPeriodic_hasExactOrder
    (u : ℕ) (hu : 1 ≤ u) :
    HasExactOrder (PeriodicLift (lowerResidues u)) (lowerModulus u - 1) := by
  constructor
  · apply eventuallyExactly_periodic_of_all_groupRep
      (lower_modulus_pos' u)
    · simp [lowerModulus]
      exact Or.inr (by omega)
    · exact lowerResidues_all_exact u hu
  · intro l hl
    apply not_eventuallyExactly_periodic_of_missing (lower_modulus_pos' u)
    have hnotall := lowerResidues_not_all_exact_before u l hu hl
    push_neg at hnotall
    exact hnotall

/-- For every positive `u`, exact order `3u²+4u` is admissible at variable
order `3u`. -/
theorem lowerPeriodic_admissible
    (u : ℕ) (hu : 1 ≤ u) :
    Admissible (3 * u) (3 * u ^ 2 + 4 * u) := by
  refine ⟨PeriodicLift (lowerResidues u),
    lowerPeriodic_eventuallyAtMost u hu, ?_⟩
  simpa [lowerModulus] using lowerPeriodic_hasExactOrder u hu

end Erdos336.Problem336
