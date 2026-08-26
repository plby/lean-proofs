import ErdosProblems.Erdos73.NoncrossingPortBlocks

/-! Inserting one convex block with a fresh label preserves a noncrossing port word. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {M N : ℕ} {U : Type*}

theorem NoncrossingPortWord.map_partialIndex {label : Fin N → U}
    (hNC : NoncrossingPortWord label) (p : Fin M → Option (Fin N))
    (hconvex : ∀ i j k, i < j → j < k → p i = none → p k = none → p j = none)
    (hmono : ∀ i j a b, i < j → p i = some a → p j = some b → a < b) :
    NoncrossingPortWord (fun i => (p i).map label) := by
  intro a b c d hab hbc hcd hac hbd
  cases ha : p a with
  | none =>
    have hc : p c = none := by
      cases hc : p c
      · rfl
      · simp only [ha, hc, Option.map_none, Option.map_some, reduceCtorEq] at hac
    have hb := hconvex a b c hab hbc ha hc
    simp only [ha, hb]
  | some x =>
    cases hc : p c with
    | none => simp only [ha, hc, Option.map_none, Option.map_some, reduceCtorEq] at hac
    | some z =>
      cases hb : p b with
      | none =>
        have hd : p d = none := by
          cases hd : p d
          · rfl
          · simp only [hb, hd, Option.map_none, Option.map_some, reduceCtorEq] at hbd
        have hn := hconvex b c d hbc hcd hb hd
        simp only [hc, reduceCtorEq] at hn
      | some y =>
        cases hd : p d with
        | none => simp only [hb, hd, Option.map_none, Option.map_some, reduceCtorEq] at hbd
        | some w =>
          simp only [ha, hb, hc, hd, Option.map_some, Option.some.injEq] at hac hbd ⊢
          exact hNC x y z w (hmono a b x y hab ha hb) (hmono b c y z hbc hb hc)
            (hmono c d z w hcd hc hd) hac hbd

def insertPortIndex (p m : ℕ) (hp : p ≤ N) (i : Fin (N + m)) : Option (Fin N) :=
  if hi : i.val < p then some ⟨i.val, hi.trans_le hp⟩
  else if him : i.val < p + m then none
  else some ⟨i.val - m, by have hi := i.isLt; omega⟩

theorem insertPortIndex_none_iff (p m : ℕ) (hp : p ≤ N) (i : Fin (N + m)) :
    insertPortIndex p m hp i = none ↔ p ≤ i.val ∧ i.val < p + m := by
  dsimp only [insertPortIndex]
  split_ifs <;> simp only [reduceCtorEq, true_iff, false_iff] <;> omega

theorem insertPortIndex_some_bounds (p m : ℕ) (hp : p ≤ N)
    (i : Fin (N + m)) (a : Fin N) (hi : insertPortIndex p m hp i = some a) :
    (i.val < p ∧ a.val = i.val) ∨ (p + m ≤ i.val ∧ a.val = i.val - m) := by
  by_cases hip : i.val < p
  · rw [insertPortIndex, dif_pos hip] at hi
    exact Or.inl ⟨hip, congrArg Fin.val (Option.some.inj hi).symm⟩
  · by_cases him : i.val < p + m
    · simp only [insertPortIndex, dif_neg hip, dif_pos him, reduceCtorEq] at hi
    · rw [insertPortIndex, dif_neg hip, dif_neg him] at hi
      exact Or.inr ⟨by omega, congrArg Fin.val (Option.some.inj hi).symm⟩

theorem insertPortIndex_strictMono (p m : ℕ) (hp : p ≤ N)
    (i j : Fin (N + m)) (a b : Fin N) (hij : i < j)
    (hi : insertPortIndex p m hp i = some a) (hj : insertPortIndex p m hp j = some b) : a < b := by
  have ha := insertPortIndex_some_bounds p m hp i a hi
  have hb := insertPortIndex_some_bounds p m hp j b hj
  exact Fin.mk_lt_mk.mpr (by omega)

theorem NoncrossingPortWord.insert_fresh_block {label : Fin N → U}
    (hNC : NoncrossingPortWord label) (p m : ℕ) (hp : p ≤ N) :
    NoncrossingPortWord (fun i => (insertPortIndex p m hp i).map label) := by
  apply hNC.map_partialIndex (insertPortIndex p m hp)
  · intro i j k hij hjk hi hk
    rw [insertPortIndex_none_iff] at hi hk ⊢
    omega
  · exact insertPortIndex_strictMono p m hp

end
end Erdos73
