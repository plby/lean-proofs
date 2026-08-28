import Wikipedia.HopfProblem.SingularCohomologyCupFacesDifferential

/-!
# The middle-face cancellation in the Alexander–Whitney formula
-/

namespace Wikipedia.HopfProblem.SingularCohomologyCup

theorem sum_faces_split {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q + 2) → M) :
    ∑ i, f i =
      (∑ i : Fin (p + 1), f ⟨i.val, by omega⟩) +
        ∑ j : Fin (q + 1), f ⟨p + 1 + j.val, by omega⟩ := by
  have h : (p + 1) + (q + 1) = p + q + 2 := by omega
  calc
    ∑ i, f i = ∑ i : Fin ((p + 1) + (q + 1)), f (i.cast h) :=
      (Fin.sum_congr' f h).symm
    _ = _ := by
      rw [Fin.sum_univ_add]
      rfl

theorem alexanderWhitney_sign_sum (p q : ℕ)
    (a : Fin (p + 2) → ℤ) (b : Fin (q + 2) → ℤ) :
    (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val * a i.castSucc * b 0) +
        (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) *
          a (Fin.last (p + 1)) * b j.succ) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val * a i) * b 0 +
        (-1 : ℤ) ^ p * a (Fin.last (p + 1)) *
          (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val * b j) := by
  have hs :
      (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) *
        a (Fin.last (p + 1)) * b j.succ) =
      (-1 : ℤ) ^ p * a (Fin.last (p + 1)) *
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (j.val + 1) * b j.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show p + 1 + j.val = p + (j.val + 1) by omega, pow_add]
    ring
  rw [hs, Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val * a i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val * b j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
    pow_zero, one_mul, pow_succ]
  rw [← Finset.sum_mul]
  ring

end Wikipedia.HopfProblem.SingularCohomologyCup
