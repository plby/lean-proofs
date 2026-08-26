import ErdosProblems.Erdos421.RepeatedIntegerCount

/-! # Moving an arbitrary coordinate collision to a fixed repeated pair -/

namespace Erdos421

theorem exists_perm_two_points {X : Type*} (a b c d : X)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm X, e a = c ∧ e b = d := by
  classical
  let e₀ := Equiv.swap a c
  let t := e₀ b
  have hct : c ≠ t := by
    intro h
    apply hab
    apply e₀.injective
    simpa only [e₀, Equiv.swap_apply_left] using h
  refine ⟨e₀.trans (Equiv.swap t d), ?_, ?_⟩
  · rw [Equiv.trans_apply]
    change Equiv.swap t d (Equiv.swap a c a) = c
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hct hcd
  · exact Equiv.swap_apply_left t d

theorem vinogradovSums_comp_perm {s k N : ℕ} (x : Fin s → Fin N) (e : Equiv.Perm (Fin s)) :
    vinogradovSums k (fun i ↦ x (e i)) = vinogradovSums k x := by
  funext j
  exact Equiv.sum_comp e (fun i ↦ ((x i : ℤ) + 1) ^ ((j : ℕ) + 1))

def collisionData {n : ℕ} {X : Type*} (x : Fin (n + 2) → X)
    (e : Equiv.Perm (Fin (n + 2))) : (Fin n → X) × X :=
  (fun i ↦ x (e (Fin.castAdd 2 i)), x (e (Fin.natAdd n 0)))

theorem repeatTuple_collisionData {n : ℕ} {X : Type*} (x : Fin (n + 2) → X)
    (e : Equiv.Perm (Fin (n + 2)))
    (he : x (e (Fin.natAdd n 0)) = x (e (Fin.natAdd n 1))) :
    repeatTuple (collisionData x e) = fun i ↦ x (e i) := by
  apply (Fin.appendEquiv n 2).symm.injective
  apply Prod.ext
  · funext i
    simp only [Fin.appendEquiv_symm_apply, repeatTuple, Fin.append_left, collisionData]
  · funext i
    have hi : i = (0 : Fin 2) ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp only [Fin.appendEquiv_symm_apply, repeatTuple, Fin.append_right, collisionData]
    · simpa only [Fin.appendEquiv_symm_apply, repeatTuple, Fin.append_right, collisionData] using he

theorem collisionData_injective_on {n : ℕ} {X : Type*} (e : Equiv.Perm (Fin (n + 2))) :
    Set.InjOn (fun x : Fin (n + 2) → X ↦ collisionData x e)
      {x | x (e (Fin.natAdd n 0)) = x (e (Fin.natAdd n 1))} := by
  intro x hx y hy h
  have he := congrArg repeatTuple h
  rw [repeatTuple_collisionData x e hx, repeatTuple_collisionData y e hy] at he
  funext i
  simpa only [Equiv.apply_symm_apply] using congrFun he (e.symm i)

end Erdos421
