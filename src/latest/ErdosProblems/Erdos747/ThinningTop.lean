import ErdosProblems.Erdos747.ResidualSurvival

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Conditional top-fibre bounds for the weight-block amplifier -/

lemma finsetProbability_decidable_irrel {α : Type*}
    (s : Finset α) (P : α → Prop) (d₁ d₂ : DecidablePred P) :
    @finsetProbability α s P d₁ = @finsetProbability α s P d₂ := by
  unfold finsetProbability
  rw [@Finset.filter_congr_decidable α s P d₁ d₂]

lemma upperWeightBlockDiagnostic_top_miss_probability_le
    {n t d e : ℕ} {H X : Finset (Edge n)} {a p pExc : ℝ}
    (hXd : X ⊆ allEdges n \ H) (hdX : d < X.card)
    (hambient : ∀ T ∈ H.powersetCard t,
      d ≤ (allEdges n \ (H \ T)).card)
    (hbudget : ∀ T ∈ H.powersetCard t,
      (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hpoint : ∀ Z ∈ X,
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ a < (completionWeight (H \ T) Z : ℝ)) ≤ p)
    (hExc : finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤
          (T.filter fun Z ↦ a <
            (completionWeight (H \ T) Z : ℝ)).card) ≤ pExc) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      ((X.card : ℝ) * p) / ((X.card - d : ℕ) : ℝ) + pExc := by
  let Good : Finset (Edge n) → Edge n → Prop := fun T Z ↦
    a < (completionWeight (H \ T) Z : ℝ)
  let Fail : Edge n → Finset (Edge n) → Prop := fun Z T ↦ ¬ Good T Z
  letI : ∀ Z, DecidablePred (Fail Z) := fun _ ↦ Classical.decPred _
  have hk : 0 < X.card - d := Nat.sub_pos_of_lt hdX
  have hpoint' : ∀ Z ∈ X,
      finsetProbability (H.powersetCard t) (Fail Z) ≤ p := by
    intro Z hZX
    exact (finsetProbability_decidable_irrel
      (H.powersetCard t) (Fail Z) _ _).le.trans (hpoint Z hZX)
  have hmany := finsetProbability_many_finite_events_le
    (H.powersetCard t) X Fail (X.card - d) p hk hpoint'
  have hmany' :
      finsetProbability (H.powersetCard t)
          (fun T ↦ ((X.card - d : ℕ) : ℝ) ≤
            (X.filter fun Z ↦ Fail Z T).card) ≤
        ((X.card : ℝ) * p) / ((X.card - d : ℕ) : ℝ) := by
    refine (finsetProbability_congr_event (H.powersetCard t) _ _ ?_).le.trans
      hmany
    intro T hT
    exact Iff.rfl
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦
          ((X.card - d : ℕ) : ℝ) ≤
              (X.filter fun Z ↦ Fail Z T).card ∨
            e + 1 ≤
              (T.filter fun Z ↦ Good T Z).card) := by
        apply finsetProbability_mono_event
        intro T hT hnot
        by_cases hsurv : d < (X.filter fun Z ↦ Good T Z).card
        · by_cases hexc :
              (T.filter fun Z ↦ Good T Z).card ≤ e
          · exfalso
            apply hnot
            apply upperWeightBlockDiagnostic_of_certificate
              H T (X.filter fun Z ↦ Good T Z) a
                (hambient T hT)
            · intro Z hZ
              have hZX := (Finset.mem_filter.mp hZ).1
              have hXall := (Finset.mem_sdiff.mp (hXd hZX)).1
              have hXnotH := (Finset.mem_sdiff.mp (hXd hZX)).2
              exact Finset.mem_sdiff.mpr ⟨hXall, fun hZHT ↦
                hXnotH (Finset.mem_sdiff.mp hZHT).1⟩
            · exact hsurv
            · intro Z hZ
              exact (Finset.mem_filter.mp hZ).2
            · simpa only [Good] using hexc
            · exact hbudget T hT
          · exact Or.inr (by omega)
        · apply Or.inl
          have hpartition :
              (X.filter (Good T)).card +
                  (X.filter fun Z ↦ ¬ Good T Z).card = X.card :=
            Finset.card_filter_add_card_filter_not
            (s := X) (p := Good T)
          have hfailCard : X.card - d ≤
              (X.filter fun Z ↦ Fail Z T).card := by
            have hfailEq :
                (X.filter fun Z ↦ Fail Z T).card =
                  (X.filter fun Z ↦ ¬ Good T Z).card := by
              apply congrArg Finset.card
              apply Finset.filter_congr
              intro Z hZX
              rfl
            rw [hfailEq]
            have hsurv' : (X.filter (Good T)).card ≤ d :=
              Nat.le_of_not_gt hsurv
            omega
          exact_mod_cast hfailCard
    _ ≤ finsetProbability (H.powersetCard t)
          (fun T ↦ ((X.card - d : ℕ) : ℝ) ≤
            (X.filter fun Z ↦ Fail Z T).card) +
        finsetProbability (H.powersetCard t)
          (fun T ↦ e + 1 ≤ (T.filter fun Z ↦ Good T Z).card) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ ((X.card : ℝ) * p) / ((X.card - d : ℕ) : ℝ) + pExc := by
      exact add_le_add hmany' (by simpa only [Good] using hExc)

lemma lowerWeightBlockDiagnostic_top_miss_probability_le
    {n t d e : ℕ} {H X : Finset (Edge n)} {a pExc : ℝ}
    (hXd : X ⊆ allEdges n \ H) (hdX : d < X.card)
    (hambient : ∀ T ∈ H.powersetCard t,
      d ≤ (allEdges n \ (H \ T)).card)
    (hbudget : ∀ T ∈ H.powersetCard t,
      (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hlow : ∀ T ∈ H.powersetCard t, ∀ Z ∈ X,
      (completionWeight (H \ T) Z : ℝ) < a)
    (hExc : finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤
          (T.filter fun Z ↦
            (completionWeight (H \ T) Z : ℝ) < a).card) ≤ pExc) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤ pExc := by
  apply le_trans (finsetProbability_mono_event
    (s := H.powersetCard t)
    (P := fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩)
    (Q := fun T ↦ e + 1 ≤
      (T.filter fun Z ↦
        (completionWeight (H \ T) Z : ℝ) < a).card) ?_) hExc
  intro T hT hnot
  by_contra hnotExc
  have hexc :
      (T.filter fun Z ↦
        (completionWeight (H \ T) Z : ℝ) < a).card ≤ e := by omega
  apply hnot
  apply lowerWeightBlockDiagnostic_of_certificate H T X a
    (hambient T hT)
  · intro Z hZX
    have hXall := (Finset.mem_sdiff.mp (hXd hZX)).1
    have hXnotH := (Finset.mem_sdiff.mp (hXd hZX)).2
    exact Finset.mem_sdiff.mpr ⟨hXall, fun hZHT ↦
      hXnotH (Finset.mem_sdiff.mp hZHT).1⟩
  · exact hdX
  · exact hlow T hT
  · exact hexc
  · exact hbudget T hT

end

end Erdos747
