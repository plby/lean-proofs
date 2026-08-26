import ErdosProblems.Erdos747.ThinningPairs

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## An abstract two-level thinning amplifier

The joint law "choose an `M`-set and then delete a `t`-set" is the same
as "choose an `(M-t)`-set and then extend it by a `t`-set".  The lemma
below packages the standard consequence used in Kahn's thinning argument:
a bad top object is rare if, conditional on every bad top object, a
diagnostic usually occurs, while conditional on every bottom object the
same diagnostic is rare.
-/

lemma thinning_bad_probability_le
    {α : Type*} (K : Finset α) (M t : ℕ)
    (htM : t ≤ M) (hMK : M ≤ K.card)
    (Bad : Finset α → Prop)
    (Diagnostic : (Sigma fun _H : Finset α ↦ Finset α) → Prop)
    (topError bottomError : ℝ)
    (htop0 : 0 ≤ topError) (hbottom0 : 0 ≤ bottomError)
    (htop : ∀ H ∈ K.powersetCard M,
      finsetProbability (H.powersetCard t)
          (fun T ↦ Bad H ∧ ¬ Diagnostic ⟨H, T⟩) ≤ topError)
    (hbottom : ∀ F ∈ K.powersetCard (M - t),
      finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ Diagnostic ⟨F ∪ T, T⟩) ≤ bottomError) :
    finsetProbability (K.powersetCard M) Bad ≤
      topError + bottomError := by
  let D := thinningDeletionPairs K M t
  let E := thinningExtensionPairs K M t
  let TopMiss : (Sigma fun _H : Finset α ↦ Finset α) → Prop :=
    fun p ↦ Bad p.1 ∧ ¬ Diagnostic p
  let BottomDiagnostic :
      (Sigma fun _F : Finset α ↦ Finset α) → Prop :=
    fun p ↦ Diagnostic (thinningExtendToDelete p)
  letI topMissDecidable : DecidablePred TopMiss :=
    fun p ↦ Classical.propDecidable (TopMiss p)
  letI bottomDiagnosticDecidable : DecidablePred BottomDiagnostic :=
    fun p ↦ Classical.propDecidable (BottomDiagnostic p)
  have hbad :
      finsetProbability (K.powersetCard M) Bad =
        finsetProbability D (fun p ↦ Bad p.1) := by
    symm
    exact thinningDeletionPairs_probability_fst K M t htM hMK Bad
  have hsplit :
      finsetProbability D (fun p ↦ Bad p.1) ≤
        finsetProbability D TopMiss +
          finsetProbability D Diagnostic := by
    calc
      finsetProbability D (fun p ↦ Bad p.1) ≤
          finsetProbability D
            (fun p ↦ TopMiss p ∨ Diagnostic p) := by
        apply finsetProbability_mono_event
        intro p hp hBad
        by_cases hQ : Diagnostic p
        · exact Or.inr hQ
        · exact Or.inl ⟨hBad, hQ⟩
      _ ≤ finsetProbability D TopMiss +
          finsetProbability D Diagnostic :=
        finsetProbability_or_le_add D TopMiss Diagnostic
  have htopBound : finsetProbability D TopMiss ≤ topError := by
    apply thinningDeletionPairs_probability_le_of_fiber
      K M t htM hMK TopMiss topError htop0
    intro H hH
    calc
      finsetProbability (H.powersetCard t)
          (fun T ↦ TopMiss ⟨H, T⟩) =
        finsetProbability (H.powersetCard t)
          (fun T ↦ Bad H ∧ ¬ Diagnostic ⟨H, T⟩) := by
            apply finsetProbability_congr_event
            intro T hT
            rfl
      _ ≤ topError := htop H hH
  have hequiv :
      finsetProbability D Diagnostic =
        finsetProbability E BottomDiagnostic := by
    apply thinningPair_probability_equiv K M t htM
    intro p hp
    dsimp only [BottomDiagnostic]
    have hinv := thinningDeleteToExtend_leftInverse htM ⟨p, hp⟩
    change Diagnostic p ↔
      Diagnostic (thinningExtendToDelete (thinningDeleteToExtend p))
    rw [hinv]
  have hbottomBound :
      finsetProbability E BottomDiagnostic ≤ bottomError := by
    apply thinningExtensionPairs_probability_le_of_fiber
      K M t htM hMK BottomDiagnostic bottomError hbottom0
    intro F hF
    calc
      finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ BottomDiagnostic ⟨F, T⟩) =
        finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ Diagnostic ⟨F ∪ T, T⟩) := by
            apply finsetProbability_congr_event
            intro T hT
            rfl
      _ ≤ bottomError := hbottom F hF
  rw [hbad]
  calc
    finsetProbability D (fun p ↦ Bad p.1) ≤
        finsetProbability D TopMiss +
          finsetProbability D Diagnostic := hsplit
    _ = finsetProbability D TopMiss +
          finsetProbability E BottomDiagnostic := by rw [hequiv]
    _ ≤ topError + bottomError := add_le_add htopBound hbottomBound

/-- Sharp multiplicative form of the two-level thinning amplifier.  If the
diagnostic misses a bad top object with conditional probability at most
`topError`, then the bad-object probability times `1 - topError` is bounded
by the bottom-fibre diagnostic probability.  This is the form that preserves
the superpolynomial bottom tail in Kahn's argument. -/
lemma thinning_bad_probability_mul_one_sub_le
    {α : Type*} (K : Finset α) (M t : ℕ)
    (htM : t ≤ M) (hMK : M ≤ K.card)
    (Bad : Finset α → Prop)
    (Diagnostic : (Sigma fun _H : Finset α ↦ Finset α) → Prop)
    (topError bottomError : ℝ)
    (htop0 : 0 ≤ topError) (htop1 : topError ≤ 1)
    (hbottom0 : 0 ≤ bottomError)
    (htop : ∀ H ∈ K.powersetCard M, Bad H →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ Diagnostic ⟨H, T⟩) ≤ topError)
    (hbottom : ∀ F ∈ K.powersetCard (M - t),
      finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ Diagnostic ⟨F ∪ T, T⟩) ≤ bottomError) :
    finsetProbability (K.powersetCard M) Bad * (1 - topError) ≤
      bottomError := by
  let D := thinningDeletionPairs K M t
  let E := thinningExtensionPairs K M t
  let Joint : (Sigma fun _H : Finset α ↦ Finset α) → Prop :=
    fun p ↦ Bad p.1 ∧ Diagnostic p
  let BottomDiagnostic :
      (Sigma fun _F : Finset α ↦ Finset α) → Prop :=
    fun p ↦ Diagnostic (thinningExtendToDelete p)
  have hsuccess : ∀ H ∈ K.powersetCard M, Bad H →
      1 - topError ≤ finsetProbability (H.powersetCard t)
        (fun T ↦ Diagnostic ⟨H, T⟩) := by
    intro H hH hBad
    have hHcard : H.card = M := (Finset.mem_powersetCard.mp hH).2
    have hs : (H.powersetCard t).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_powersetCard, hHcard]
      exact Nat.choose_pos htM
    have hcomp := finsetProbability_not_eq_one_sub
      (H.powersetCard t) (fun T ↦ Diagnostic ⟨H, T⟩) hs
    have hmiss := htop H hH hBad
    rw [hcomp] at hmiss
    linarith
  have hjoint :
      finsetProbability (K.powersetCard M) Bad * (1 - topError) ≤
        finsetProbability D Joint := by
    simpa only [D, Joint] using
      thinningDeletionPairs_probability_mul_le_of_fiber
        K M t htM hMK Bad Diagnostic (1 - topError)
          (sub_nonneg.mpr htop1) hsuccess
  have hmono : finsetProbability D Joint ≤
      finsetProbability D Diagnostic := by
    apply finsetProbability_mono_event
    intro p hp hJoint
    exact hJoint.2
  have hequiv : finsetProbability D Diagnostic =
      finsetProbability E BottomDiagnostic := by
    apply thinningPair_probability_equiv K M t htM
    intro p hp
    dsimp only [BottomDiagnostic]
    have hinv := thinningDeleteToExtend_leftInverse htM ⟨p, hp⟩
    change Diagnostic p ↔
      Diagnostic (thinningExtendToDelete (thinningDeleteToExtend p))
    rw [hinv]
  have hbottomBound :
      finsetProbability E BottomDiagnostic ≤ bottomError := by
    apply thinningExtensionPairs_probability_le_of_fiber
      K M t htM hMK BottomDiagnostic bottomError hbottom0
    intro F hF
    calc
      finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ BottomDiagnostic ⟨F, T⟩) =
        finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ Diagnostic ⟨F ∪ T, T⟩) := by
            apply finsetProbability_congr_event
            intro T hT
            rfl
      _ ≤ bottomError := hbottom F hF
  exact hjoint.trans (hmono.trans (hequiv.le.trans hbottomBound))

/-- Convenient corollary of the sharp amplifier when the top-fibre miss
probability is at most one half. -/
lemma thinning_bad_probability_le_two_mul
    {α : Type*} (K : Finset α) (M t : ℕ)
    (htM : t ≤ M) (hMK : M ≤ K.card)
    (Bad : Finset α → Prop)
    (Diagnostic : (Sigma fun _H : Finset α ↦ Finset α) → Prop)
    (topError bottomError : ℝ)
    (htop0 : 0 ≤ topError) (htopHalf : topError ≤ 1 / 2)
    (hbottom0 : 0 ≤ bottomError)
    (htop : ∀ H ∈ K.powersetCard M, Bad H →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ Diagnostic ⟨H, T⟩) ≤ topError)
    (hbottom : ∀ F ∈ K.powersetCard (M - t),
      finsetProbability ((K \ F).powersetCard t)
          (fun T ↦ Diagnostic ⟨F ∪ T, T⟩) ≤ bottomError) :
    finsetProbability (K.powersetCard M) Bad ≤ 2 * bottomError := by
  have hmul := thinning_bad_probability_mul_one_sub_le
    K M t htM hMK Bad Diagnostic topError bottomError htop0
      (htopHalf.trans (by norm_num)) hbottom0 htop hbottom
  have hprob0 : 0 ≤ finsetProbability (K.powersetCard M) Bad :=
    finsetProbability_nonneg _ _
  nlinarith

lemma card_filter_historyEdges_eq_embeddingHitCount
    {n t : ℕ} {s : Finset (Edge n)}
    (e : DeletionHistory s t) (Y : Finset (Edge n)) :
    ((historyEdges e).filter fun A ↦ A ∈ Y).card =
      embeddingHitCount Y e := by
  let I : Finset (Fin t) :=
    (Finset.univ : Finset (Fin t)).filter fun i ↦ (e i).1 ∈ Y
  let J : Finset (Edge n) :=
    (historyEdges e).filter fun A ↦ A ∈ Y
  have hleft :
      ((historyEdges e).filter fun A ↦ A ∈ Y).card = J.card := by
    apply congrArg Finset.card
    ext A
    simp only [J, Finset.mem_filter]
  have hright : embeddingHitCount Y e = I.card := by
    unfold embeddingHitCount
    apply congrArg Finset.card
    ext i
    simp only [I, Finset.mem_filter]
  have hJI : J = I.image fun i ↦ (e i).1 := by
    ext A
    simp only [J, I, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hAhist, hAY⟩
      rcases Finset.mem_image.mp hAhist with ⟨i, hi, hAi⟩
      exact ⟨i, hAi ▸ hAY, hAi⟩
    · rintro ⟨i, hiY, rfl⟩
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hiY⟩
  have hinj : Function.Injective (fun i : Fin t ↦ (e i).1) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  calc
    ((historyEdges e).filter fun A ↦ A ∈ Y).card = J.card := hleft
    _ = (I.image fun i ↦ (e i).1).card := congrArg Finset.card hJI
    _ = I.card := Finset.card_image_of_injective _ hinj
    _ = embeddingHitCount Y e := hright.symm

/-- Constant-fraction hypergeometric under-hit bound directly on an
unordered `powersetCard` sample. -/
lemma powersetCard_hitCount_three_quarters_le_mean
    {n t : ℕ} (s Y : Finset (Edge n))
    (hYs : Y ⊆ s) (hts : t ≤ s.card)
    (hs : s.Nonempty) (hcollision : 2 * t * t ≤ s.card) :
    finsetProbability (s.powersetCard t)
        (fun T ↦ (((T.filter fun A ↦ A ∈ Y).card : ℕ) : ℝ) ≤
          (3 / 4 : ℝ) * (t : ℝ) * ((Y.card : ℝ) / s.card)) ≤
      2 * Real.exp
        (-((t : ℝ) * ((Y.card : ℝ) / s.card)) / 64) := by
  let P : Finset (Edge n) → Prop := fun T ↦
    (((T.filter fun A ↦ A ∈ Y).card : ℕ) : ℝ) ≤
      (3 / 4 : ℝ) * (t : ℝ) * ((Y.card : ℝ) / s.card)
  rw [← historyEdges_probability_eq_sample s hts P]
  calc
    finsetProbability
          (Finset.univ : Finset (DeletionHistory s t))
          (fun e ↦ P (historyEdges e)) =
        finsetProbability
          (Finset.univ : Finset (Fin t ↪ ↥s))
          (fun e ↦ (embeddingHitCount Y e : ℝ) ≤
            (3 / 4 : ℝ) * (t : ℝ) *
              ((Y.card : ℝ) / s.card)) := by
      apply finsetProbability_congr_event
      intro e he
      dsimp only [P]
      rw [card_filter_historyEdges_eq_embeddingHitCount e Y]
    _ ≤ _ := embeddingHitCount_three_quarters_le_mean
      s Y hYs t hs hcollision

/-- Matching constant-fraction hypergeometric over-hit bound directly on
an unordered `powersetCard` sample. -/
lemma powersetCard_hitCount_five_quarters_le_mean
    {n t : ℕ} (s Y : Finset (Edge n))
    (hYs : Y ⊆ s) (hts : t ≤ s.card)
    (hs : s.Nonempty) (hcollision : 2 * t * t ≤ s.card) :
    finsetProbability (s.powersetCard t)
        (fun T ↦ (5 / 4 : ℝ) * (t : ℝ) *
            ((Y.card : ℝ) / s.card) ≤
          (((T.filter fun A ↦ A ∈ Y).card : ℕ) : ℝ)) ≤
      2 * Real.exp
        (-((t : ℝ) * ((Y.card : ℝ) / s.card)) / 64) := by
  let P : Finset (Edge n) → Prop := fun T ↦
    (5 / 4 : ℝ) * (t : ℝ) * ((Y.card : ℝ) / s.card) ≤
      (((T.filter fun A ↦ A ∈ Y).card : ℕ) : ℝ)
  rw [← historyEdges_probability_eq_sample s hts P]
  calc
    finsetProbability
          (Finset.univ : Finset (DeletionHistory s t))
          (fun e ↦ P (historyEdges e)) =
        finsetProbability
          (Finset.univ : Finset (Fin t ↪ ↥s))
          (fun e ↦ (5 / 4 : ℝ) * (t : ℝ) *
              ((Y.card : ℝ) / s.card) ≤
            (embeddingHitCount Y e : ℝ)) := by
      apply finsetProbability_congr_event
      intro e he
      dsimp only [P]
      rw [card_filter_historyEdges_eq_embeddingHitCount e Y]
    _ ≤ _ := embeddingHitCount_five_quarters_le_mean
      s Y hYs t hs hcollision

end

end Erdos747
