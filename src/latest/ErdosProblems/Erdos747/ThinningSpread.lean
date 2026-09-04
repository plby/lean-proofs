import ErdosProblems.Erdos747.ThinningConsequences

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Global one-sided spreading from the two-level thinning amplifier -/

lemma finsetSdiff_decidable_irrel {α : Type*}
    (s t : Finset α) (d₁ d₂ : DecidableEq α) :
    @sdiff (Finset α) (@Finset.instSDiff α d₁) s t =
      @sdiff (Finset α) (@Finset.instSDiff α d₂) s t := by
  ext x
  simp

lemma finsetUnion_decidable_irrel {α : Type*}
    (s t : Finset α) (d₁ d₂ : DecidableEq α) :
    @Union.union (Finset α) (@Finset.instUnion α d₁) s t =
      @Union.union (Finset α) (@Finset.instUnion α d₂) s t := by
  ext x
  simp

lemma upperWeightBlockDiagnostic_top_of_global_failure
    {n M t d e : ℕ} {H : Finset (Edge n)} {L delta p pExc topError : ℝ}
    (hH : H ∈ (allEdges n).powersetCard M)
    (hAll : (allEdges n).Nonempty)
    (hfail : ¬ GlobalUpperWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card))
    (htH : t ≤ H.card) (hHne : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hdiagnostic : ∀ T ∈ H.powersetCard t,
      (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hpoint : ∀ Z ∈ coarseUpperBadNonedges n H L,
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ (1 + delta) * matchingWeightTarget n H <
            (completionWeight (H \ T) Z : ℝ)) ≤ p)
    (hexceptionThreshold : (5 / 4 : ℝ) * (t : ℝ) *
      (((presentUpperWeightExceptions H delta).card : ℝ) / H.card) ≤
        (e + 1 : ℕ))
    (htopError :
      (((coarseUpperBadNonedges n H L).card : ℝ) * p) /
          (((coarseUpperBadNonedges n H L).card - d : ℕ) : ℝ) +
        2 * Real.exp
          (-((t : ℝ) *
            (((presentUpperWeightExceptions H delta).card : ℝ) / H.card)) /
              64) ≤ topError) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      topError := by
  let X := coarseUpperBadNonedges n H L
  have hHcard : H.card = M := (Finset.mem_powersetCard.mp hH).2
  have hbudget : (((2 * d + H.card : ℕ) : ℝ)) ≤
      ((((2 * d + M : ℕ) : ℝ) / (allEdges n).card) *
        (allEdges n).card) := by
    rw [hHcard]
    have hne : ((allEdges n).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hAll
    field_simp [hne]
    exact le_rfl
  have h2dX : 2 * d < X.card :=
    coarseUpperBadNonedges_card_gt_of_not_global hbudget hfail
  have hdX : d < X.card := by omega
  have hXd : X ⊆ allEdges n \ H := Finset.filter_subset _ _
  have hambient : ∀ T ∈ H.powersetCard t,
      d ≤ (allEdges n \ (H \ T)).card := by
    intro T hT
    apply le_trans (show d ≤ X.card by omega)
    apply Finset.card_le_card
    intro Z hZX
    rcases Finset.mem_sdiff.mp (hXd hZX) with ⟨hZall, hZnotH⟩
    exact Finset.mem_sdiff.mpr ⟨hZall, fun hZHT ↦
      hZnotH (Finset.mem_sdiff.mp hZHT).1⟩
  have hExc := presentUpperWeightException_probability_le
    H delta htH hHne hcollision hexceptionThreshold
  exact (upperWeightBlockDiagnostic_top_miss_probability_le
    hXd hdX hambient hdiagnostic
      (by simpa only [X] using hpoint) hExc).trans (by
        simpa only [X] using htopError)

lemma globalUpperWeightSpread_failure_probability_le_of_thinning
    {n M t d e : ℕ} {L delta p pExc topError : ℝ}
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      ¬ GlobalUpperWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card) →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ ¬ GlobalUpperWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) ≤
      topError +
        2 * Real.exp
          (-((t : ℝ) *
            ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    ¬ GlobalUpperWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ ¬ GlobalUpperWeightSpread n H L
            (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hbound :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        topError +
          2 * Real.exp
            (-((t : ℝ) *
              ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
    let : DecidablePred Bad := badDecidable
    apply thinning_bad_probability_le (allEdges n) M t htM hMtop
      Bad (UpperWeightBlockDiagnostic n d t) topError
      (2 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64))
      htop0 (by positivity)
    · intro H hH
      by_cases hbad : Bad H
      · calc
          finsetProbability (H.powersetCard t)
              (fun T ↦ Bad H ∧
                ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) =
            finsetProbability (H.powersetCard t)
              (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) := by
                apply finsetProbability_congr_event
                intro T hT
                simp [hbad]
          _ ≤ topError := htop H hH (by simpa only [Bad] using hbad)
      · have hempty : (H.powersetCard t).filter
            (fun T ↦ Bad H ∧
              ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) = ∅ := by
          simp [hbad]
        unfold finsetProbability
        rw [hempty]
        simp only [Finset.card_empty, CharP.cast_eq_zero, Finset.card_powersetCard, zero_div, ge_iff_le]
        exact htop0
    · intro F hF
      let dClassical : DecidableEq (Edge n) :=
        fun A B ↦ Classical.propDecidable (A = B)
      let dFin : DecidableEq (Edge n) := Finset.decidableEq
      have hsdiff := finsetSdiff_decidable_irrel
        (allEdges n) F dClassical dFin
      change finsetProbability
          ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dClassical)
            (allEdges n) F).powersetCard t)
          (fun T ↦ UpperWeightBlockDiagnostic n d t
            ⟨@Union.union (Finset (Edge n))
              (@Finset.instUnion (Edge n) dClassical) F T, T⟩) ≤ _
      rw [hsdiff]
      have htail := upperWeightBlockDiagnostic_bottom_probability_le
        (n := n) (M := M) (t := t) (d := d)
        htM hMtop hdBottom htBottom hbottomPos hbottomCollision F hF
      calc
        finsetProbability
            ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dFin)
              (allEdges n) F).powersetCard t)
            (fun T ↦ UpperWeightBlockDiagnostic n d t
              ⟨@Union.union (Finset (Edge n)) (@Finset.instUnion (Edge n) dClassical)
                F T, T⟩) =
          finsetProbability
            ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dFin)
              (allEdges n) F).powersetCard t)
            (fun T ↦ UpperWeightBlockDiagnostic n d t
              ⟨@Union.union (Finset (Edge n)) (@Finset.instUnion (Edge n) dFin)
                F T, T⟩) := by
                  apply finsetProbability_congr_event
                  intro T hT
                  rw [finsetUnion_decidable_irrel F T dClassical dFin]
        _ ≤ _ := htail
  exact hnormalize.le.trans hbound

lemma lowerWeightBlockDiagnostic_top_of_global_failure
    {n M t d e : ℕ} {H : Finset (Edge n)} {L pExc topError : ℝ}
    (hH : H ∈ (allEdges n).powersetCard M)
    (hAll : (allEdges n).Nonempty)
    (hfail : ¬ GlobalLowerWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card))
    (hdiagnostic : ∀ T ∈ H.powersetCard t,
      (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hExc : finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤
          (T.filter fun Z ↦
            (completionWeight (H \ T) Z : ℝ) <
              L * matchingWeightTarget n H).card) ≤ pExc)
    (herror : pExc ≤ topError) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
      topError := by
  let X := predicateLowerBadNonedges H L
  have hHcard : H.card = M := (Finset.mem_powersetCard.mp hH).2
  have hbudget : (((2 * d + H.card : ℕ) : ℝ)) ≤
      ((((2 * d + M : ℕ) : ℝ) / (allEdges n).card) *
        (allEdges n).card) := by
    rw [hHcard]
    have hne : ((allEdges n).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hAll
    field_simp [hne]
    exact le_rfl
  have h2dX : 2 * d < X.card :=
    predicateLowerBadNonedges_card_gt_of_not_global hbudget hfail
  have hdX : d < X.card := by omega
  have hXd : X ⊆ allEdges n \ H := Finset.filter_subset _ _
  have hambient : ∀ T ∈ H.powersetCard t,
      d ≤ (allEdges n \ (H \ T)).card := by
    intro T hT
    apply le_trans (show d ≤ X.card by omega)
    apply Finset.card_le_card
    intro Z hZX
    rcases Finset.mem_sdiff.mp (hXd hZX) with ⟨hZall, hZnotH⟩
    exact Finset.mem_sdiff.mpr ⟨hZall, fun hZHT ↦
      hZnotH (Finset.mem_sdiff.mp hZHT).1⟩
  have hlow : ∀ T ∈ H.powersetCard t, ∀ Z ∈ X,
      (completionWeight (H \ T) Z : ℝ) <
        L * matchingWeightTarget n H := by
    intro T hT Z hZX
    have hbad := (Finset.mem_filter.mp hZX).2
    unfold CompletionWeightLowerBound at hbad
    push Not at hbad
    have hmono : (completionWeight (H \ T) Z : ℝ) ≤
        completionWeight H Z := by
      exact_mod_cast completionWeight_mono
        (Finset.sdiff_subset : H \ T ⊆ H) Z
    exact hmono.trans_lt hbad
  exact (lowerWeightBlockDiagnostic_top_miss_probability_le
    hXd hdX hambient hdiagnostic hlow hExc).trans herror

lemma globalLowerWeightSpread_failure_probability_le_of_thinning
    {n M t d e : ℕ} {L topError : ℝ}
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      ¬ GlobalLowerWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card) →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ ¬ GlobalLowerWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) ≤
      topError +
        2 * Real.exp
          (-((t : ℝ) *
            ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    ¬ GlobalLowerWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ ¬ GlobalLowerWeightSpread n H L
            (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hbound :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        topError +
          2 * Real.exp
            (-((t : ℝ) *
              ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
    let : DecidablePred Bad := badDecidable
    apply thinning_bad_probability_le (allEdges n) M t htM hMtop
      Bad (LowerWeightBlockDiagnostic n d t) topError
      (2 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64))
      htop0 (by positivity)
    · intro H hH
      by_cases hbad : Bad H
      · calc
          finsetProbability (H.powersetCard t)
              (fun T ↦ Bad H ∧
                ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) =
            finsetProbability (H.powersetCard t)
              (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) := by
                apply finsetProbability_congr_event
                intro T hT
                simp [hbad]
          _ ≤ topError := htop H hH (by simpa only [Bad] using hbad)
      · have hempty : (H.powersetCard t).filter
            (fun T ↦ Bad H ∧
              ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) = ∅ := by
          simp [hbad]
        unfold finsetProbability
        rw [hempty]
        simp only [Finset.card_empty, CharP.cast_eq_zero, Finset.card_powersetCard, zero_div, ge_iff_le]
        exact htop0
    · intro F hF
      let dClassical : DecidableEq (Edge n) :=
        fun A B ↦ Classical.propDecidable (A = B)
      let dFin : DecidableEq (Edge n) := Finset.decidableEq
      have hsdiff := finsetSdiff_decidable_irrel
        (allEdges n) F dClassical dFin
      change finsetProbability
          ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dClassical)
            (allEdges n) F).powersetCard t)
          (fun T ↦ LowerWeightBlockDiagnostic n d t
            ⟨@Union.union (Finset (Edge n))
              (@Finset.instUnion (Edge n) dClassical) F T, T⟩) ≤ _
      rw [hsdiff]
      have htail := lowerWeightBlockDiagnostic_bottom_probability_le
        (n := n) (M := M) (t := t) (d := d)
        htM hMtop hdBottom htBottom hbottomPos hbottomCollision F hF
      calc
        finsetProbability
            ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dFin)
              (allEdges n) F).powersetCard t)
            (fun T ↦ LowerWeightBlockDiagnostic n d t
              ⟨@Union.union (Finset (Edge n)) (@Finset.instUnion (Edge n) dClassical)
                F T, T⟩) =
          finsetProbability
            ((@sdiff (Finset (Edge n)) (@Finset.instSDiff (Edge n) dFin)
              (allEdges n) F).powersetCard t)
            (fun T ↦ LowerWeightBlockDiagnostic n d t
              ⟨@Union.union (Finset (Edge n)) (@Finset.instUnion (Edge n) dFin)
                F T, T⟩) := by
                  apply finsetProbability_congr_event
                  intro T hT
                  rw [finsetUnion_decidable_irrel F T dClassical dFin]
        _ ≤ _ := htail
  exact hnormalize.le.trans hbound

/-! The multiplicative versions below are the quantitative forms used in
the final deletion-level union.  A top-fibre miss bound of at most one half
does not appear additively; it only costs a factor two. -/

lemma globalUpperWeightSpread_failure_probability_le_of_thinning_sharp
    {n M t d e : ℕ} {L topError : ℝ}
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError) (htopHalf : topError ≤ 1 / 2)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      ¬ GlobalUpperWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card) →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ ¬ GlobalUpperWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) ≤
      4 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    ¬ GlobalUpperWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)
  let Diagnostic := UpperWeightBlockDiagnostic n d t
  let bottomError := 2 * Real.exp
    (-((t : ℝ) *
      ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ ¬ GlobalUpperWeightSpread n H L
            (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hraw :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        2 * bottomError := by
    let : DecidablePred Bad := badDecidable
    exact thinning_bad_probability_le_two_mul
      (allEdges n) M t htM hMtop Bad Diagnostic topError bottomError
        htop0 htopHalf (by positivity)
        (by
          intro H hH hbad
          exact htop H hH (by simpa only [Bad] using hbad))
        (by
          intro F hF
          let dClassical : DecidableEq (Edge n) :=
            fun A B ↦ Classical.propDecidable (A = B)
          let dFin : DecidableEq (Edge n) := Finset.decidableEq
          have hsdiff := finsetSdiff_decidable_irrel
            (allEdges n) F dClassical dFin
          change finsetProbability
              ((@sdiff (Finset (Edge n))
                (@Finset.instSDiff (Edge n) dClassical)
                (allEdges n) F).powersetCard t)
              (fun T ↦ UpperWeightBlockDiagnostic n d t
                ⟨@Union.union (Finset (Edge n))
                  (@Finset.instUnion (Edge n) dClassical) F T, T⟩) ≤ _
          rw [hsdiff]
          have htail := upperWeightBlockDiagnostic_bottom_probability_le
            (n := n) (M := M) (t := t) (d := d)
            htM hMtop hdBottom htBottom hbottomPos hbottomCollision F hF
          calc
            finsetProbability
                ((@sdiff (Finset (Edge n))
                  (@Finset.instSDiff (Edge n) dFin)
                  (allEdges n) F).powersetCard t)
                (fun T ↦ UpperWeightBlockDiagnostic n d t
                  ⟨@Union.union (Finset (Edge n))
                    (@Finset.instUnion (Edge n) dClassical) F T, T⟩) =
              finsetProbability
                ((@sdiff (Finset (Edge n))
                  (@Finset.instSDiff (Edge n) dFin)
                  (allEdges n) F).powersetCard t)
                (fun T ↦ UpperWeightBlockDiagnostic n d t
                  ⟨@Union.union (Finset (Edge n))
                    (@Finset.instUnion (Edge n) dFin) F T, T⟩) := by
                      apply finsetProbability_congr_event
                      intro T hT
                      rw [finsetUnion_decidable_irrel F T dClassical dFin]
            _ ≤ _ := htail)
  have hfinal : 2 * bottomError = 4 * Real.exp
      (-((t : ℝ) *
        ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
    dsimp only [bottomError]
    ring
  exact (hnormalize.le.trans
    ((finsetProbability_decidable_irrel
      ((allEdges n).powersetCard M) Bad _ badDecidable).le.trans hraw)).trans_eq
        hfinal

lemma globalLowerWeightSpread_failure_probability_le_of_thinning_sharp
    {n M t d e : ℕ} {L topError : ℝ}
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError) (htopHalf : topError ≤ 1 / 2)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      ¬ GlobalLowerWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card) →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ ¬ GlobalLowerWeightSpread n H L
          (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) ≤
      4 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    ¬ GlobalLowerWeightSpread n H L
      (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)
  let Diagnostic := LowerWeightBlockDiagnostic n d t
  let bottomError := 2 * Real.exp
    (-((t : ℝ) *
      ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ ¬ GlobalLowerWeightSpread n H L
            (((2 * d + M : ℕ) : ℝ) / (allEdges n).card)) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hraw :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        2 * bottomError := by
    let : DecidablePred Bad := badDecidable
    exact thinning_bad_probability_le_two_mul
      (allEdges n) M t htM hMtop Bad Diagnostic topError bottomError
        htop0 htopHalf (by positivity)
        (by
          intro H hH hbad
          exact htop H hH (by simpa only [Bad] using hbad))
        (by
          intro F hF
          let dClassical : DecidableEq (Edge n) :=
            fun A B ↦ Classical.propDecidable (A = B)
          let dFin : DecidableEq (Edge n) := Finset.decidableEq
          have hsdiff := finsetSdiff_decidable_irrel
            (allEdges n) F dClassical dFin
          change finsetProbability
              ((@sdiff (Finset (Edge n))
                (@Finset.instSDiff (Edge n) dClassical)
                (allEdges n) F).powersetCard t)
              (fun T ↦ LowerWeightBlockDiagnostic n d t
                ⟨@Union.union (Finset (Edge n))
                  (@Finset.instUnion (Edge n) dClassical) F T, T⟩) ≤ _
          rw [hsdiff]
          have htail := lowerWeightBlockDiagnostic_bottom_probability_le
            (n := n) (M := M) (t := t) (d := d)
            htM hMtop hdBottom htBottom hbottomPos hbottomCollision F hF
          calc
            finsetProbability
                ((@sdiff (Finset (Edge n))
                  (@Finset.instSDiff (Edge n) dFin)
                  (allEdges n) F).powersetCard t)
                (fun T ↦ LowerWeightBlockDiagnostic n d t
                  ⟨@Union.union (Finset (Edge n))
                    (@Finset.instUnion (Edge n) dClassical) F T, T⟩) =
              finsetProbability
                ((@sdiff (Finset (Edge n))
                  (@Finset.instSDiff (Edge n) dFin)
                  (allEdges n) F).powersetCard t)
                (fun T ↦ LowerWeightBlockDiagnostic n d t
                  ⟨@Union.union (Finset (Edge n))
                    (@Finset.instUnion (Edge n) dFin) F T, T⟩) := by
                      apply finsetProbability_congr_event
                      intro T hT
                      rw [finsetUnion_decidable_irrel F T dClassical dFin]
            _ ≤ _ := htail)
  have hfinal : 2 * bottomError = 4 * Real.exp
      (-((t : ℝ) *
        ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
    dsimp only [bottomError]
    ring
  exact (hnormalize.le.trans
    ((finsetProbability_decidable_irrel
      ((allEdges n).powersetCard M) Bad _ badDecidable).le.trans hraw)).trans_eq
        hfinal

end

end Erdos747
