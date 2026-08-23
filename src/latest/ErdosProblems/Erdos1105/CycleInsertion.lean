import ErdosProblems.Erdos1105.CycleEdges

namespace Erdos1105

open SimpleGraph

/-- Insert an external vertex before the first vertex of a cyclic sequence.
Only the two new edges can collide with each other or with retained edges. -/
theorem cycle_cons_collision {V C : Type*} {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (v : Fin (n + 3) ↪ V)
    (hb : Function.Injective (fun i : Fin (n + 3) ↦ extendColor c s(v i, v (i + 1))))
    (u : V) (hu : u ∉ Set.range v) :
    extendColor c s(u, v 0) = extendColor c s(v (Fin.last (n + 2)), u) ∨
      (∃ i : Fin (n + 2), extendColor c s(u, v 0) =
        extendColor c s(v i.castSucc, v i.succ)) ∨
      (∃ i : Fin (n + 2), extendColor c s(v (Fin.last (n + 2)), u) =
        extendColor c s(v i.castSucc, v i.succ)) := by
  by_contra h
  let a₀ := extendColor c s(u, v 0)
  let a₁ := extendColor c s(v (Fin.last (n + 2)), u)
  let b : Fin (n + 3) → Option C := fun i ↦ extendColor c s(v i, v (i + 1))
  have hstep (i : Fin (n + 2)) : (i.castSucc : Fin (n + 3)) + 1 = i.succ := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_castSucc, Fin.val_succ, Fin.val_one]
    exact Nat.mod_eq_of_lt (by omega)
  have hne : a₀ ≠ a₁ := fun he ↦ h (.inl he)
  have ha₀ (i : Fin (n + 2)) : a₀ ≠ b i.castSucc := by
    intro he
    apply h
    refine .inr (.inl ⟨i, ?_⟩)
    simpa only [b, hstep] using he
  have ha₁ (i : Fin (n + 2)) : a₁ ≠ b i.castSucc := by
    intro he
    apply h
    refine .inr (.inr ⟨i, ?_⟩)
    simpa only [b, hstep] using he
  let w := Fin.Embedding.cons v hu
  let d : Fin (n + 4) → Option C := fun i ↦ extendColor c s(w i, w (i + 1))
  have hd₀ : d 0 = a₀ := by
    have h01 : (0 + 1 : Fin (n + 4)) = (0 : Fin (n + 3)).succ := by
      apply Fin.ext
      simp
    simp only [d, w, Fin.Embedding.coe_cons, h01, Fin.cons_zero, Fin.cons_succ, a₀]
  have hd₁ : d (Fin.last (n + 3)) = a₁ := by
    have hlast : (Fin.last (n + 3) : Fin (n + 4)) + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_last, Fin.val_one, Fin.val_zero]
      exact Nat.mod_self (n + 4)
    have hlast' : (Fin.last (n + 3) : Fin (n + 4)) = (Fin.last (n + 2)).succ := by rfl
    dsimp only [d]
    rw [hlast, hlast']
    rfl
  have hdmid (i : Fin (n + 2)) : d i.castSucc.succ = b i.castSucc := by
    have hnext : (i.castSucc.succ : Fin (n + 4)) + 1 = i.succ.succ := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_castSucc, Fin.val_succ, Fin.val_one]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [d, hnext, w, Fin.Embedding.coe_cons, Fin.cons_succ, b, hstep]
  have hclass (i : Fin (n + 4)) : i = 0 ∨ i = Fin.last (n + 3) ∨
      ∃ j : Fin (n + 2), i = j.castSucc.succ := by
    refine Fin.cases (.inl rfl) (fun j ↦ ?_) i
    exact Fin.lastCases (.inr (.inl rfl)) (fun j ↦ .inr (.inr ⟨j, rfl⟩)) j
  have hd : Function.Injective d := by
    intro i j hij
    rcases hclass i with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases hclass j with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [hd₀, hd₁, hdmid] at hij
    · rfl
    · exact (hne hij).elim
    · exact (ha₀ j hij).elim
    · exact (hne hij.symm).elim
    · rfl
    · exact (ha₁ j hij).elim
    · exact (ha₀ i hij.symm).elim
    · exact (ha₁ i hij.symm).elim
    · exact congrArg Fin.succ (hb hij)
  apply hH (completeCopy (cycleGraph (n + 4)) w)
  exact (isRainbow_cycle_iff_pairColors _ c).mpr hd

end Erdos1105
