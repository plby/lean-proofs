/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.PathSeparator

/-! # Paths versus finitely colorable targets -/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- A path-versus-target bound from an explicit proper coloring.  This is the
iterated form of Häggkvist's bipartite bound used in the CFMPP proof. -/
theorem pathGraph_isContained_or_compl_of_coloring
    {W V : Type*} [Fintype W] [Fintype V]
    {k t : ℕ} (hk : 2 ≤ k) (H : SimpleGraph W)
    (c : H.Coloring (Fin t)) (C : SimpleGraph V)
    (hcard : Fintype.card W + k * (t - 1) ≤ Fintype.card V) :
    SimpleGraph.pathGraph k ⊑ C ∨ H ⊑ Cᶜ := by
  classical
  cases t with
  | zero =>
      right
      let : IsEmpty W := ⟨fun w ↦ Fin.elim0 (c w)⟩
      exact SimpleGraph.IsContained.of_isEmpty
  | succ t =>
      cases t with
      | zero =>
          right
          have hH : H = ⊥ := by
            ext x y
            constructor
            · intro hxy
              have hcx : c x = 0 := Fin.eq_zero _
              have hcy : c y = 0 := Fin.eq_zero _
              exact (c.valid hxy (hcx.trans hcy.symm)).elim
            · simp
          rw [hH]
          apply SimpleGraph.IsContained.bot.mpr
          simpa using hcard
      | succ r =>
          by_cases hpath : SimpleGraph.pathGraph k ⊑ C
          · exact .inl hpath
          let S : Finset W := Finset.univ.filter fun w ↦ c w = 0
          let T : Finset W := Sᶜ
          have hSTcard : S.card + T.card = Fintype.card W := by
            simpa [T] using Finset.card_add_card_compl S
          let bsize := T.card + k * r
          have hcard' : Fintype.card W + k * (r + 1) ≤ Fintype.card V := by
            simpa using hcard
          have hsepCard : S.card + bsize + k - 2 ≤ Fintype.card V := by
            calc
              S.card + bsize + k - 2 ≤ S.card + bsize + k := Nat.sub_le _ _
              _ = Fintype.card W + k * (r + 1) := by
                simp only [bsize, Nat.mul_add, Nat.mul_one]
                omega
              _ ≤ Fintype.card V := hcard'
          obtain ⟨A, B, hA, hB, hAB, hno⟩ :=
            exists_anticomplete_finsets_of_pathGraph_not_isContained C hk
              (n := S.card) (m := bsize) hsepCard hpath
          have hcT_ne_zero (w : T) : c w.1 ≠ 0 := by
            intro hw
            have hwS : w.1 ∈ S := by simp [S, hw]
            have hwT : w.1 ∈ Sᶜ := by
              change w.1 ∈ Sᶜ
              exact w.2
            exact (Finset.mem_compl.mp hwT) hwS
          let cT : (H.induce (T : Set W)).Coloring (Fin (r + 1)) :=
            SimpleGraph.Coloring.mk
              (fun w ↦ ⟨(c w.1).val - 1, by
                have hcpos : 0 < (c w.1).val := Nat.pos_of_ne_zero
                  (fun h ↦ hcT_ne_zero w (Fin.ext h))
                have hclt := (c w.1).isLt
                omega⟩)
              (by
                intro x y hxy heq
                apply c.valid hxy
                apply Fin.ext
                have hxpos : 0 < (c x.1).val := Nat.pos_of_ne_zero
                  (fun h ↦ hcT_ne_zero x (Fin.ext h))
                have hypos : 0 < (c y.1).val := Nat.pos_of_ne_zero
                  (fun h ↦ hcT_ne_zero y (Fin.ext h))
                have hval := congrArg Fin.val heq
                change (c x.1).val - 1 = (c y.1).val - 1 at hval
                exact (Nat.sub_add_cancel hxpos).symm.trans
                  ((congrArg (fun n ↦ n + 1) hval).trans (Nat.sub_add_cancel hypos)))
          have hrecCard : Fintype.card T + k * ((r + 1) - 1) ≤ Fintype.card B := by
            simp only [Fintype.card_coe, hB, bsize, Nat.add_sub_cancel]
            exact le_rfl
          have hrec := pathGraph_isContained_or_compl_of_coloring
            (W := T) (V := B) (t := r + 1) hk
            (H.induce (T : Set W)) cT (C.induce (B : Set V)) hrecCard
          have hblueT : H.induce (T : Set W) ⊑ Cᶜ.induce (B : Set V) := by
            rcases hrec with hred | hblue
            · exact (hpath (hred.trans
                (SimpleGraph.Embedding.induce (B : Set V)).isContained)).elim
            · have hcomp : (C.induce (B : Set V))ᶜ = Cᶜ.induce (B : Set V) := by
                ext x y
                simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj]
                rw [Subtype.val_injective.ne_iff]
              rw [hcomp] at hblue
              exact hblue
          obtain ⟨copyT⟩ := hblueT
          let eS : S ≃ A := Finset.equivOfCardEq hA.symm
          let f : W → V := fun w ↦
            if hw : w ∈ S then (eS ⟨w, hw⟩).1
            else (copyT ⟨w, by simpa [T] using hw⟩).1
          have hcross : ∀ a ∈ A, ∀ b ∈ B, Cᶜ.Adj a b := by
            intro a ha b hb
            rw [SimpleGraph.compl_adj]
            refine ⟨?_, hno a ha b hb⟩
            intro hab
            exact Finset.disjoint_left.mp hAB ha (hab ▸ hb)
          let hom : H →g Cᶜ :=
            { toFun := f
              map_rel' := by
                intro x y hxy
                by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
                · have hcx : c x = 0 := by simpa [S] using hx
                  have hcy : c y = 0 := by simpa [S] using hy
                  exact (c.valid hxy (hcx.trans hcy.symm)).elim
                · dsimp only [f]
                  rw [dif_pos hx, dif_neg hy]
                  exact hcross _ (eS ⟨x, hx⟩).2 _ (copyT ⟨y, by simpa [T] using hy⟩).2
                · dsimp only [f]
                  rw [dif_neg hx, dif_pos hy]
                  exact (hcross _ (eS ⟨y, hy⟩).2 _
                    (copyT ⟨x, by simpa [T] using hx⟩).2).symm
                · dsimp only [f]
                  rw [dif_neg hx, dif_neg hy]
                  apply copyT.toHom.map_adj
                  exact hxy }
          have hf : Function.Injective hom := by
            intro x y hxy
            by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
            · change f x = f y at hxy
              dsimp only [f] at hxy
              rw [dif_pos hx, dif_pos hy] at hxy
              exact congrArg Subtype.val (eS.injective (Subtype.ext hxy))
            · change f x = f y at hxy
              dsimp only [f] at hxy
              rw [dif_pos hx, dif_neg hy] at hxy
              exfalso
              exact Finset.disjoint_left.mp hAB (eS ⟨x, hx⟩).2
                (hxy ▸ (copyT ⟨y, by simpa [T] using hy⟩).2)
            · change f x = f y at hxy
              dsimp only [f] at hxy
              rw [dif_neg hx, dif_pos hy] at hxy
              exfalso
              exact Finset.disjoint_left.mp hAB (eS ⟨y, hy⟩).2
                (hxy.symm ▸ (copyT ⟨x, by simpa [T] using hx⟩).2)
            · change f x = f y at hxy
              dsimp only [f] at hxy
              rw [dif_neg hx, dif_neg hy] at hxy
              exact congrArg Subtype.val
                (copyT.injective (Subtype.ext hxy))
          exact .inr ⟨hom.toCopy hf⟩
termination_by t
decreasing_by omega

end Erdos570
