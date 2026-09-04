/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleExtension

/-!
# Extending a clique embedding across an independent target set

This is the graph-theoretic half of the Goddard--Kleitman extension step.
The non-minimum-degree core is already embedded in a blue clique.  Some
vertices of the independent minimum-degree set receive distinct compatible
representatives outside the clique; all remaining target vertices are then
placed in its unused positions.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- Extend an embedding of the complement of an independent target set.
The cardinal identity says precisely that after putting `P` outside `T`,
all other target vertices fit in `T`. -/
theorem isContained_of_independent_core_extension
    {W V : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {B : SimpleGraph V} [DecidableEq V]
    (S : Finset W) (hSind : H.IsIndepSet (S : Set W))
    (T Y : Finset V) (hTY : Disjoint T Y)
    (hT : B.IsClique (T : Set V))
    (hTcard : T.card ≤ Fintype.card W)
    (P : Finset W) (hPS : P ⊆ S)
    (hPcard : P.card = Fintype.card W - T.card)
    (core : {w : W // w ∉ S} ↪ T)
    (outside : P ↪ Y)
    (hattach : ∀ x : P, ∀ w : W, ∀ hw : w ∉ S,
      H.Adj x.1 w → B.Adj (outside x).1 (core ⟨w, hw⟩).1) :
    H ⊑ B := by
  classical
  let D := {w : W // w ∉ S}
  let used : Finset T := Finset.univ.image core
  have hused : used.card = Fintype.card D := by
    change (Finset.univ.image core).card =
      Fintype.card {w : W // w ∉ S}
    rw [Finset.card_image_of_injective _ core.injective]
    simp
  have hDcard : Fintype.card D = Fintype.card W - S.card := by
    let : Fintype {w : W // w ∈ S} := Fintype.ofFinite _
    calc
      Fintype.card D =
          Fintype.card W - Fintype.card {w : W // w ∈ S} := by
        simpa [D] using Fintype.card_subtype_compl (fun w : W ↦ w ∈ S)
      _ = Fintype.card W - S.card := by simp
  let R := {w : W // w ∈ S ∧ w ∉ P}
  let A := {z : T // z ∉ used}
  have hRcard : Fintype.card R = S.card - P.card := by
    let e : R ≃ ↑(S \ P) :=
      { toFun := fun w ↦ ⟨w.1, Finset.mem_sdiff.mpr
          (show w.1 ∈ S ∧ w.1 ∉ P from w.2)⟩
        invFun := fun w ↦ ⟨w.1, Finset.mem_sdiff.mp w.2⟩
        left_inv := fun w ↦ by simp
        right_inv := fun w ↦ by simp }
    calc
      Fintype.card R = Fintype.card ↑(S \ P) := Fintype.card_congr e
      _ = (S \ P).card := Fintype.card_coe _
      _ = S.card - P.card := Finset.card_sdiff_of_subset hPS
  have hAcard : Fintype.card A = T.card - Fintype.card D := by
    change Fintype.card {z : T // ¬z ∈ used} = _
    rw [Fintype.card_subtype_compl]
    simp [hused]
  have hScard : S.card ≤ Fintype.card W := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hcorecard : Fintype.card D ≤ T.card := by
    simpa [D] using Fintype.card_le_of_injective core core.injective
  have hcards : Fintype.card R = Fintype.card A := by
    rw [hRcard, hAcard, hDcard, hPcard]
    omega
  let fill : R ≃ A := Fintype.equivOfCardEq hcards
  let inside : {w : W // w ∉ P} → T := fun w ↦
    if hw : w.1 ∈ S then (fill ⟨w.1, hw, w.2⟩).1
    else core ⟨w.1, hw⟩
  have hinside : Function.Injective inside := by
    intro x y hxy
    by_cases hx : x.1 ∈ S <;> by_cases hy : y.1 ∈ S
    · dsimp only [inside] at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      have hf := fill.injective (Subtype.ext hxy)
      exact Subtype.ext (congrArg (fun z : R ↦ z.1) hf)
    · dsimp only [inside] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exfalso
      exact (fill ⟨x.1, hx, x.2⟩).2 (by
        rw [Finset.mem_image]
        exact ⟨⟨y.1, hy⟩, by simp, hxy.symm⟩)
    · dsimp only [inside] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exfalso
      exact (fill ⟨y.1, hy, y.2⟩).2 (by
        rw [Finset.mem_image]
        exact ⟨⟨x.1, hx⟩, by simp, hxy⟩)
    · dsimp only [inside] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      have hd : (⟨x.1, hx⟩ : D) = ⟨y.1, hy⟩ := core.injective hxy
      exact Subtype.ext (congrArg (fun z : D ↦ z.1) hd)
  let emb : W → V := fun w ↦
    if hw : w ∈ P then (outside ⟨w, hw⟩).1
    else (inside ⟨w, hw⟩).1
  have hemb : Function.Injective emb := by
    intro x y hxy
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    · dsimp only [emb] at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (outside.injective (Subtype.ext hxy))
    · dsimp only [emb] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exfalso
      exact Finset.disjoint_left.mp hTY (inside ⟨y, hy⟩).2
        (by rw [← hxy]; exact (outside ⟨x, hx⟩).2)
    · dsimp only [emb] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exfalso
      exact Finset.disjoint_left.mp hTY (inside ⟨x, hx⟩).2
        (by rw [hxy]; exact (outside ⟨y, hy⟩).2)
    · dsimp only [emb] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (hinside (Subtype.ext hxy))
  let hom : H →g B :=
    { toFun := emb
      map_rel' := by
        intro x y hxy
        by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
        · exact (hSind (hPS hx) (hPS hy) (H.ne_of_adj hxy) hxy).elim
        · have hyS : y ∉ S := by
            intro hyS
            exact hSind (hPS hx) hyS (H.ne_of_adj hxy) hxy
          dsimp only [emb, inside]
          rw [dif_pos hx, dif_neg hy, dif_neg hyS]
          exact hattach ⟨x, hx⟩ y hyS hxy
        · have hxS : x ∉ S := by
            intro hxS
            exact hSind hxS (hPS hy) (H.ne_of_adj hxy) hxy
          dsimp only [emb, inside]
          rw [dif_neg hx, dif_pos hy, dif_neg hxS]
          exact (hattach ⟨y, hy⟩ x hxS hxy.symm).symm
        · dsimp only [emb]
          rw [dif_neg hx, dif_neg hy]
          apply hT (inside ⟨x, hx⟩).2 (inside ⟨y, hy⟩).2
          intro heq
          exact hxy.ne (congrArg Subtype.val
            (hinside (Subtype.ext heq))) }
  exact ⟨hom.toCopy hemb⟩

end Erdos570
