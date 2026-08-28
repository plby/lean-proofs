import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationSort
import Mathlib.Logic.Equiv.Basic

/-!
# Equal-coordinate swaps from adjacent swaps

In a sorted tuple, equal endpoint values force every intervening value to
be equal.  Conjugating a shorter swap by the last adjacent swap therefore
reduces an arbitrary tie swap to adjacent tie swaps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

variable {n : ℕ} {α : Type*} [LinearOrder α]

omit [LinearOrder α] in
/-- Exchanging equal coordinates does not change the ordered value tuple. -/
theorem coordinate_swap_of_tie {u : Fin n → α} {e : Equiv.Perm (Fin n)}
    {a b : Fin n} (hab : u (e a) = u (e b)) (i : Fin n) :
    u (((Equiv.swap a b).trans e) i) = u (e i) :=
  Equiv.apply_swap_eq_self (v := fun j => u (e j)) hab i

/-- Every swap of equal coordinates preserves the sorted condition. -/
theorem sortedCoordinates_swap_of_tie {u : Fin n → α}
    {e : Equiv.Perm (Fin n)} (he : SortedCoordinates u e)
    {a b : Fin n} (hab : u (e a) = u (e b)) :
    SortedCoordinates u ((Equiv.swap a b).trans e) := by
  intro i j hij
  simpa only [coordinate_swap_of_tie hab] using he hij

private theorem swap_trans_swap_trans_swap {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) :
    ((Equiv.swap b c).trans (Equiv.swap a b)).trans (Equiv.swap b c) =
      Equiv.swap a c := by
  simpa only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hab hac,
    Equiv.swap_apply_left] using
      Equiv.symm_trans_swap_trans a b (Equiv.swap b c)

private theorem eq_swap_of_sorted_tie_of_lt (u : Fin (n + 1) → α) {A : Type*}
    (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap : ∀ e, SortedCoordinates u e → ∀ i : Fin n,
      u (e i.castSucc) = u (e i.succ) →
        F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    (b : Fin (n + 1)) :
    ∀ (a : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1))),
      a < b → SortedCoordinates u e → u (e a) = u (e b) →
        F e = F ((Equiv.swap a b).trans e) := by
  induction b using Fin.induction with
  | zero =>
      intro a e hab
      exact (Fin.not_lt_zero a hab).elim
  | succ b ih =>
      intro a e hab he ht
      obtain rfl | hlt := (Fin.le_castSucc_iff.mpr hab).eq_or_lt
      · exact hswap e he b ht
      have hmid : u (e b.castSucc) = u (e b.succ) :=
        le_antisymm ((he hlt.le).trans ht.le) (he Fin.castSucc_lt_succ.le)
      have hleft : u (e a) = u (e b.castSucc) := ht.trans hmid.symm
      let e₁ := (Equiv.swap b.castSucc b.succ).trans e
      have h₁ : SortedCoordinates u e₁ := sortedCoordinates_swap_of_tie he hmid
      have hv₁ (i : Fin (n + 1)) : u (e₁ i) = u (e i) :=
        coordinate_swap_of_tie hmid i
      have ht₁ : u (e₁ a) = u (e₁ b.castSucc) := by
        rw [hv₁, hv₁]
        exact hleft
      let e₂ := (Equiv.swap a b.castSucc).trans e₁
      have h₂ : SortedCoordinates u e₂ := sortedCoordinates_swap_of_tie h₁ ht₁
      have hv₂ (i : Fin (n + 1)) : u (e₂ i) = u (e₁ i) :=
        coordinate_swap_of_tie ht₁ i
      have ht₂ : u (e₂ b.castSucc) = u (e₂ b.succ) := by
        rw [hv₂, hv₂, hv₁, hv₁]
        exact hmid
      calc
        F e = F e₁ := hswap e he b hmid
        _ = F e₂ := ih a e₁ hlt h₁ ht₁
        _ = F ((Equiv.swap b.castSucc b.succ).trans e₂) := hswap e₂ h₂ b ht₂
        _ = F ((Equiv.swap a b.succ).trans e) := by
          apply congrArg F
          dsimp only [e₂, e₁]
          rw [← Equiv.trans_assoc, ← Equiv.trans_assoc,
            swap_trans_swap_trans_swap hlt.ne hab.ne]

/-- Invariance under adjacent sorted tie swaps implies invariance under every
equal-coordinate swap, in any finite dimension. -/
theorem eq_swap_of_sorted_tie (u : Fin (n + 1) → α) {A : Type*}
    (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap : ∀ e, SortedCoordinates u e → ∀ i : Fin n,
      u (e i.castSucc) = u (e i.succ) →
        F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e)
    (a b : Fin (n + 1)) (hab : u (e a) = u (e b)) :
    F e = F ((Equiv.swap a b).trans e) := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact eq_swap_of_sorted_tie_of_lt u F hswap b a e hlt he hab
  · simp
  · simpa only [Equiv.swap_comm b a] using
      eq_swap_of_sorted_tie_of_lt u F hswap a b e hgt he hab.symm

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
