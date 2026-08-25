import StackExchange.Puzzling139335.InterfacePairing.Involution

/-!
# Exact signed balance for finite interface weights

An interface is represented once on each of its two incident boundaries.
For weights preserved by the actual mate involution, the total from either
boundary agrees.  The signed sum for the two pairs of square pieces therefore
contains the exterior contributions and twice the difference of the two
interfaces internal to those pairs.  No sign condition on the weights is needed.
-/

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

noncomputable section

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- The weight of all arc occurrences on one boundary. -/
def rowSum (w : F.Occurrence → ℝ) (i : ExtendedPieceIndex) : ℝ :=
  ∑ k : Fin (F.n i), w ⟨i, k⟩

/-- The interface weight counted from boundary `i`.  Each physical interface
arc between distinct boundaries occurs once in this sum. -/
def interfaceWeight (w : F.Occurrence → ℝ) (i j : ExtendedPieceIndex) : ℝ :=
  ∑ k : Fin (F.n i), if F.partner i k = j then w ⟨i, k⟩ else 0

/-- The part of a square piece's boundary weight incident to the exterior. -/
def outerWeight (w : F.Occurrence → ℝ) (i : Fin 4) : ℝ :=
  interfaceWeight F w (Sum.inl i) (Sum.inr ())

/-- A directed interface sum is the corresponding restricted sum over all
occurrences.  This form exposes the actual mate permutation. -/
theorem interfaceWeight_eq_occurrenceSum (w : F.Occurrence → ℝ)
    (i j : ExtendedPieceIndex) :
    interfaceWeight F w i j =
      ∑ a : F.Occurrence,
        if a.1 = i ∧ F.partner a.1 a.2 = j then w a else 0 := by
  classical
  symm
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp [interfaceWeight]
  · intro b _ hbi
    simp [hbi]
  · simp

/-- The mate involution gives an exact equality of the weights measured from
the two sides of an interface. -/
theorem interfaceWeight_symm (w : F.Occurrence → ℝ)
    (hmate : ∀ a, w (F.mate a) = w a) (i j : ExtendedPieceIndex) :
    interfaceWeight F w i j = interfaceWeight F w j i := by
  classical
  rw [interfaceWeight_eq_occurrenceSum, interfaceWeight_eq_occurrenceSum]
  apply Fintype.sum_equiv (F.mate_involutive.toPerm F.mate)
  intro a
  change (if a.1 = i ∧ F.partner a.1 a.2 = j then w a else 0) =
    (if (F.mate a).1 = j ∧ F.partner (F.mate a).1 (F.mate a).2 = i then
      w (F.mate a) else 0)
  rw [F.partner_mate, F.mate_fst, hmate a]
  simp only [and_comm]

/-- An arc's partner boundary is distinct from its own boundary. -/
@[simp] theorem interfaceWeight_self (w : F.Occurrence → ℝ)
    (i : ExtendedPieceIndex) : interfaceWeight F w i i = 0 := by
  classical
  simp [interfaceWeight, F.partner_ne]

/-- Partition a boundary's total weight by its partner boundary. -/
theorem rowSum_eq_sum_interfaceWeight (w : F.Occurrence → ℝ)
    (i : ExtendedPieceIndex) :
    rowSum F w i = ∑ j : ExtendedPieceIndex, interfaceWeight F w i j := by
  classical
  unfold rowSum interfaceWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

/-- The partner labels consist of the four pieces and the exterior. -/
theorem rowSum_eq_five (w : F.Occurrence → ℝ) (i : ExtendedPieceIndex) :
    rowSum F w i =
      interfaceWeight F w i (Sum.inl 0) + interfaceWeight F w i (Sum.inl 1) +
      interfaceWeight F w i (Sum.inl 2) + interfaceWeight F w i (Sum.inl 3) +
      interfaceWeight F w i (Sum.inr ()) := by
  rw [rowSum_eq_sum_interfaceWeight]
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, add_assoc]

/-- Exact balance for the two pairs of pieces.  Each interior interface on the
right is counted from only one of its incident boundaries. -/
theorem signed_rowSum_balance (w : F.Occurrence → ℝ)
    (hmate : ∀ a, w (F.mate a) = w a) :
    rowSum F w (Sum.inl 0) + rowSum F w (Sum.inl 1) -
        rowSum F w (Sum.inl 2) - rowSum F w (Sum.inl 3) =
      outerWeight F w 0 + outerWeight F w 1 - outerWeight F w 2 - outerWeight F w 3 +
        2 * (interfaceWeight F w (Sum.inl 0) (Sum.inl 1) -
          interfaceWeight F w (Sum.inl 2) (Sum.inl 3)) := by
  simp only [rowSum_eq_five, outerWeight, interfaceWeight_self,
    interfaceWeight_symm F w hmate (Sum.inl 1) (Sum.inl 0),
    interfaceWeight_symm F w hmate (Sum.inl 2) (Sum.inl 0),
    interfaceWeight_symm F w hmate (Sum.inl 3) (Sum.inl 0),
    interfaceWeight_symm F w hmate (Sum.inl 2) (Sum.inl 1),
    interfaceWeight_symm F w hmate (Sum.inl 3) (Sum.inl 1),
    interfaceWeight_symm F w hmate (Sum.inl 3) (Sum.inl 2)]
  ring

/-- The equivalent balance identity expressed using addition only. -/
theorem rowSum_balance (w : F.Occurrence → ℝ)
    (hmate : ∀ a, w (F.mate a) = w a) :
    rowSum F w (Sum.inl 0) + rowSum F w (Sum.inl 1) +
        outerWeight F w 2 + outerWeight F w 3 +
        2 * interfaceWeight F w (Sum.inl 2) (Sum.inl 3) =
      rowSum F w (Sum.inl 2) + rowSum F w (Sum.inl 3) +
        outerWeight F w 0 + outerWeight F w 1 +
        2 * interfaceWeight F w (Sum.inl 0) (Sum.inl 1) := by
  linarith [signed_rowSum_balance F w hmate]

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
