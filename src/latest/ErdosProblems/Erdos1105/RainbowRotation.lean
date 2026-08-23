import ErdosProblems.Erdos1105.PathRotation
import ErdosProblems.Erdos1105.SwapRepresentative

namespace Erdos1105

open SimpleGraph

/-- When the closing edge repeats the first path color, a pair of
crossing chords provides a rainbow cycle by deleting that first edge. -/
theorem rainbow_cycle_of_rotating_chords {V C : Type*} {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet) (v : Fin (n + 3) ↪ V)
    (hpath : ∀ i j : Fin (n + 3), j.val = i.val + 1 → R.Adj (v i) (v j))
    (q : Fin (n + 3)) (hq : 2 ≤ q.val) (hqend : q.val < n + 2)
    (hfirst : R.Adj (v 0) (v q)) (hjoin : R.Adj (v 1) (v (q + 1)))
    (hclosing : extendColor c s(v (Fin.last (n + 2)), v 0) = extendColor c s(v 0, v 1)) :
    ∃ f : (cycleGraph (n + 3)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  have h01 : R.Adj (v 0) (v 1) := hpath 0 1 (by simp)
  let e : R.edgeSet := ⟨s(v 0, v 1), h01⟩
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(v (Fin.last (n + 2)), v 0), by
    apply v.injective.ne
    intro h
    have hv := congrArg Fin.val h
    simp at hv⟩
  let R' := swapRepresentative R e.val d.val
  have hR' : Set.InjOn (extendColor c) R'.edgeSet :=
    swapRepresentative_rainbow c R hR e d hclosing
  have hkeep (i j : Fin (n + 3)) (hij : R.Adj (v i) (v j))
      (hne : s(i, j) ≠ s(0, 1)) : R'.Adj (v i) (v j) := by
    apply (mem_swapRepresentative R e.val d s(v i, v j)).mpr
    refine Or.inl ⟨hij, ?_⟩
    intro heq
    apply hne
    rcases Sym2.eq_iff.mp heq with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [v.injective hi, v.injective hj]
    · rw [v.injective hi, v.injective hj, Sym2.eq_swap]
  let G := R'.comap v
  have hGfirst : G.Adj 0 q := by
    apply hkeep 0 q hfirst
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨_, heq⟩ | ⟨heq, _⟩
    · have hv := congrArg Fin.val heq
      simp at hv
      omega
    · have hv := congrArg Fin.val heq
      simp at hv
  have hGjoin : G.Adj 1 (q + 1) := by
    apply hkeep 1 (q + 1) hjoin
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨heq, _⟩ | ⟨_, heq⟩
    · have hv := congrArg Fin.val heq
      simp at hv
    · have hv := congrArg Fin.val heq
      have hqval : (q + 1).val = q.val + 1 := by
        rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
      rw [hqval, Fin.val_zero] at hv
      omega
  have hGpath (i j : Fin (n + 3)) (hi : 1 ≤ i.val) (hj : j.val = i.val + 1) : G.Adj i j := by
    apply hkeep i j (hpath i j hj)
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨heq, _⟩ | ⟨_, heq⟩
    · have hv := congrArg Fin.val heq
      rw [Fin.val_zero] at hv
      omega
    · have hv := congrArg Fin.val heq
      rw [Fin.val_zero] at hv
      omega
  have hGlast : G.Adj (Fin.last (n + 2)) 0 :=
    (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)
  let f := (Embedding.comap v R').toCopy.comp
    (rotatedCycleCopy G q hq hqend hGfirst hGjoin hGpath hGlast)
  exact ⟨(Copy.ofLE R' ⊤ le_top).comp f, isRainbow_comp_of_color_injOn le_top c hR' f⟩

end Erdos1105
