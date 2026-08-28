import Wikipedia.HopfProblem.SingularCohomologyCupCochains
import Wikipedia.HopfProblem.SingularCohomologyCupFacesSigns

/-!
# The Leibniz identity for the actual singular cup product

The proof splits the native alternating face sum at the common vertex
of the front and back faces. The two extra middle faces cancel.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

theorem coboundary_cup_simplex {p q : ℕ} (α : Cochain X p) (β : Cochain X q)
    (σ : SingularSimplex X (p + q + 1)) :
    coboundary (cup α β) (simplexChain X (p + q + 1) σ) =
      cupInDegree (by omega) (coboundary α) β (simplexChain X (p + q + 1) σ) +
        (-1 : ℤ) ^ p * cup α (coboundary β) (simplexChain X (p + q + 1) σ) := by
  let a : Fin (p + 2) → ℤ := fun i =>
    α (simplexChain X p
      ((σ.comp (windowFace 0 (p + 1) (p + q + 1) (by omega))).comp (simplexFace p i)))
  let b : Fin (q + 2) → ℤ := fun j =>
    β (simplexChain X q
      ((σ.comp (windowFace p (q + 1) (p + q + 1) (by omega))).comp (simplexFace q j)))
  have ha : a (Fin.last (p + 1)) =
      α (simplexChain X p (σ.comp (windowFace 0 p (p + q + 1) (by omega)))) := by
    dsimp only [a]
    rw [ContinuousMap.comp_assoc, window_face_last]
  have hb : b 0 =
      β (simplexChain X q (σ.comp (windowFace (p + 1) q (p + q + 1) (by omega)))) := by
    dsimp only [b]
    rw [ContinuousMap.comp_assoc, window_face_zero]
  have hd : coboundary (cup α β) (simplexChain X (p + q + 1) σ) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val * a i.castSucc * b 0) +
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) *
          a (Fin.last (p + 1)) * b j.succ := by
    rw [coboundary_simplex, sum_faces_split p q]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      rw [cup_simplex, hb]
      dsimp only [a]
      simp only [frontFace, backFace, ContinuousMap.comp_assoc]
      rw [face_window_middle 0 p (p + q) (by omega)
        ⟨i.val, by omega⟩ i.castSucc (by simp),
        face_window_before p q (p + q) (by omega) ⟨i.val, by omega⟩
          (by change i.val ≤ p; omega)]
      ring
    · apply Finset.sum_congr rfl
      intro j _
      rw [cup_simplex, ha]
      dsimp only [b]
      simp only [frontFace, backFace, ContinuousMap.comp_assoc]
      rw [face_window_after 0 p (p + q) (by omega) ⟨p + 1 + j.val, by omega⟩
          (by change 0 + p < p + 1 + j.val; omega),
        face_window_middle p q (p + q) (by omega)
          ⟨p + 1 + j.val, by omega⟩ j.succ (by simp; omega)]
      ring
  have hcb : cup α (coboundary β) (simplexChain X (p + q + 1) σ) =
      α (simplexChain X p (σ.comp (windowFace 0 p (p + q + 1) (by omega)))) *
        coboundary β (simplexChain X (q + 1)
          (σ.comp (windowFace p (q + 1) (p + q + 1) (by omega)))) :=
    cup_simplex α (coboundary β) σ
  have hr :
      cupInDegree (by omega) (coboundary α) β (simplexChain X (p + q + 1) σ) +
        (-1 : ℤ) ^ p * cup α (coboundary β) (simplexChain X (p + q + 1) σ) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val * a i) * b 0 +
        (-1 : ℤ) ^ p * a (Fin.last (p + 1)) *
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val * b j := by
    rw [cupInDegree_simplex, hcb,
      coboundary_simplex, coboundary_simplex, ha, hb]
    simp only [a, b, mul_assoc]
  exact hd.trans ((alexanderWhitney_sign_sum p q a b).trans hr.symm)

/-- The Leibniz identity in every pair of degrees, with the total degree explicit. -/
theorem coboundary_cup {p q : ℕ} (α : Cochain X p) (β : Cochain X q) :
    coboundary (cup α β) = cupInDegree (by omega) (coboundary α) β +
      (-1 : ℤ) ^ p • cup α (coboundary β) := by
  apply chainMap_ext X (p + q + 1)
  intro σ
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using
    coboundary_cup_simplex α β σ

/-- The usual Leibniz identity, displaying its only degree cast. -/
theorem coboundary_cup_cast {p q : ℕ} (α : Cochain X p) (β : Cochain X q) :
    coboundary (cup α β) = castCochain (by omega) (cup (coboundary α) β) +
      (-1 : ℤ) ^ p • cup α (coboundary β) := by
  rw [coboundary_cup, cupInDegree_eq_cast]

theorem cup_cocycle {p q : ℕ} (α : Cochain X p) (β : Cochain X q)
    (hα : coboundary α = 0) (hβ : coboundary β = 0) :
    coboundary (cup α β) = 0 := by
  rw [coboundary_cup_cast, hα, hβ, cup_zero_left, cup_zero_right,
    castCochain_zero, smul_zero, add_zero]

end Wikipedia.HopfProblem.SingularCohomologyCup
