import Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixingBound
import Wikipedia.HomotopyGroupsOfSpheres.BalancedSpectralGap

/-!
# Constrained commutator families for balanced signed spectra

The selected spectral block gives an injective real-linear family of
symmetric trace-zero matrices. Orthogonal conjugation transports this
family and its square-norm estimates to the original eigenbasis.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace RealSymmetricMixing

open RealMatrixSquareNorm

variable {N : Type*} [Fintype N] [DecidableEq N] {r : ℕ}

def conjugateDirection (U : unitary (Matrix N N ℝ)) : DirectionSpace N →ₗ[ℝ] DirectionSpace N where
  toFun A := ⟨conjugate U A.val, by
    constructor
    · rw [conjugate_transpose, A.property.1]
    · rw [trace_conjugate, A.property.2]⟩
  map_add' A B := Subtype.ext ((conjugate U).map_add A.val B.val)
  map_smul' c A := Subtype.ext ((conjugate U).map_smul c A.val)

theorem conjugateDirection_injective (U : unitary (Matrix N N ℝ)) :
    Function.Injective (conjugateDirection U) := by
  intro A B h
  apply Subtype.ext
  exact conjugate_injective U (congrArg Subtype.val h)

def transportedMixing (U : unitary (Matrix N N ℝ)) (b : N) (e : Fin r ↪ N)
    (he : ∀ j, b ≠ e j) : (Fin r → ℝ) →ₗ[ℝ] DirectionSpace N :=
  (conjugateDirection U).comp (mixingDirection b e he)

theorem transportedMixing_injective (U : unitary (Matrix N N ℝ)) (b : N) (e : Fin r ↪ N)
    (he : ∀ j, b ≠ e j) : Function.Injective (transportedMixing U b e he) :=
  (conjugateDirection_injective U).comp (mixingDirection_injective b e he)

theorem transportedMixing_bound (U : unitary (Matrix N N ℝ)) (b : N) (e : Fin r ↪ N)
    (he : ∀ j, b ≠ e j) (α : N → ℝ) (hgap : ∀ j, 4 * Real.pi ≤ |α b - α (e j)|)
    (c : Fin r → ℝ) :
    16 * Real.pi ^ 2 * squareNorm (transportedMixing U b e he c).val ≤
      squareNorm (commutator (conjugate U (Matrix.diagonal α))
        (transportedMixing U b e he c).val) := by
  change 16 * Real.pi ^ 2 * squareNorm (conjugate U (mixingLinear b e c)) ≤
    squareNorm (commutator (conjugate U (Matrix.diagonal α))
      (conjugate U (mixingLinear b e c)))
  rw [commutator_conjugate, squareNorm_conjugate, squareNorm_conjugate]
  exact mixing_commutator_bound b e α hgap c

theorem transportedMixing_strict (U : unitary (Matrix N N ℝ)) (b : N) (e : Fin r ↪ N)
    (he : ∀ j, b ≠ e j) (α : N → ℝ) (hgap : ∀ j, 4 * Real.pi ≤ |α b - α (e j)|)
    (c : Fin r → ℝ) (hc : c ≠ 0) :
    4 * Real.pi ^ 2 * squareNorm (transportedMixing U b e he c).val <
      squareNorm (commutator (conjugate U (Matrix.diagonal α))
        (transportedMixing U b e he c).val) := by
  change 4 * Real.pi ^ 2 * squareNorm (conjugate U (mixingLinear b e c)) <
    squareNorm (commutator (conjugate U (Matrix.diagonal α))
      (conjugate U (mixingLinear b e c)))
  rw [commutator_conjugate, squareNorm_conjugate, squareNorm_conjugate]
  exact mixing_commutator_strict b e he α hgap c hc

end RealSymmetricMixing

namespace BalancedRealInvolutions

open RealMatrixSquareNorm RealSymmetricMixing

theorem exists_balanced_commutator_family (n : ℕ) (m : Index n → ℤ)
    (hsum : ∑ a, (2 * (m a : ℝ) + 1) = 0) (hfast : ∃ a, m a ≠ 0 ∧ m a ≠ -1)
    (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] DirectionSpace (Index n), Function.Injective L ∧
      (∀ c, 16 * Real.pi ^ 2 * squareNorm (L c).val ≤
        squareNorm (commutator (conjugate U (Matrix.diagonal
          (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1)))) (L c).val)) ∧
      ∀ c, c ≠ 0 → 4 * Real.pi ^ 2 * squareNorm (L c).val <
        squareNorm (commutator (conjugate U (Matrix.diagonal
          (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1)))) (L c).val) := by
  obtain ⟨b, e, he⟩ := exists_odd_speed_separated_embedding n m hsum hfast
  let L := transportedMixing U b e (fun j ↦ (he j).1)
  refine ⟨L, transportedMixing_injective U b e _, ?_, ?_⟩
  · intro c
    exact transportedMixing_bound U b e _ _ (fun j ↦ (he j).2) c
  · intro c hc
    exact transportedMixing_strict U b e _ _ (fun j ↦ (he j).2) c hc

end BalancedRealInvolutions

end Wikipedia.HomotopyGroupsOfSpheres
