import ErdosProblems.Erdos747.AggregateStructuralReduction
import ErdosProblems.Erdos747.ThinningSpread

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Conditional two-level thinning -/

/-- Top-fibre upper diagnostic from an explicit supply of upper-bad missing
triples.  This separates the genuinely useful part of
`upperWeightBlockDiagnostic_top_of_global_failure` from its coarse estimate
that treated every present edge as exceptional. -/
lemma upperWeightBlockDiagnostic_top_of_many_badNonedges
    {n t d e : ℕ} {H : Finset (Edge n)}
    {L delta p topError : ℝ}
    (hlarge : 2 * d < (coarseUpperBadNonedges n H L).card)
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
  have hdX : d < X.card := by dsimp only [X]; omega
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

/-- The analogous lower diagnostic from explicitly many lower-bad missing
triples. -/
lemma lowerWeightBlockDiagnostic_top_of_many_badNonedges
    {n t d e : ℕ} {H : Finset (Edge n)} {L pExc topError : ℝ}
    (hlarge : 2 * d < (predicateLowerBadNonedges H L).card)
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
  have hdX : d < X.card := by dsimp only [X]; omega
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

/-- The sharp two-level thinning amplifier applies unchanged to a bad event
conditioned on an arbitrary predecessor certificate. -/
lemma conditionalGlobalUpper_failure_probability_le_of_thinning_sharp
    {n M t d : ℕ} {L eta topError : ℝ}
    (Good : Finset (Edge n) → Prop)
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError) (htopHalf : topError ≤ 1 / 2)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      Good H → ¬ GlobalUpperWeightSpread n H L eta →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ UpperWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ Good H ∧ ¬ GlobalUpperWeightSpread n H L eta) ≤
      4 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    Good H ∧ ¬ GlobalUpperWeightSpread n H L eta
  let Diagnostic := UpperWeightBlockDiagnostic n d t
  let bottomError := 2 * Real.exp
    (-((t : ℝ) *
      ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ Good H ∧ ¬ GlobalUpperWeightSpread n H L eta) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hraw :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        2 * bottomError := by
    letI : DecidablePred Bad := badDecidable
    exact thinning_bad_probability_le_two_mul
      (allEdges n) M t htM hMtop Bad Diagnostic topError bottomError
        htop0 htopHalf (by positivity)
        (by
          intro H hH hbad
          exact htop H hH hbad.1 hbad.2)
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

/-- Lower-spread conditional thinning. -/
lemma conditionalGlobalLower_failure_probability_le_of_thinning_sharp
    {n M t d : ℕ} {L eta topError : ℝ}
    (Good : Finset (Edge n) → Prop)
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (htop0 : 0 ≤ topError) (htopHalf : topError ≤ 1 / 2)
    (hdBottom : d ≤ (allEdges n).card - (M - t))
    (htBottom : t ≤ (allEdges n).card - (M - t))
    (hbottomPos : 0 < (allEdges n).card - (M - t))
    (hbottomCollision : 2 * t * t ≤
      (allEdges n).card - (M - t))
    (htop : ∀ H ∈ (allEdges n).powersetCard M,
      Good H → ¬ GlobalLowerWeightSpread n H L eta →
      finsetProbability (H.powersetCard t)
          (fun T ↦ ¬ LowerWeightBlockDiagnostic n d t ⟨H, T⟩) ≤
        topError) :
    finsetProbability ((allEdges n).powersetCard M)
        (fun H ↦ Good H ∧ ¬ GlobalLowerWeightSpread n H L eta) ≤
      4 * Real.exp
        (-((t : ℝ) *
          ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  let Bad : Finset (Edge n) → Prop := fun H ↦
    Good H ∧ ¬ GlobalLowerWeightSpread n H L eta
  let Diagnostic := LowerWeightBlockDiagnostic n d t
  let bottomError := 2 * Real.exp
    (-((t : ℝ) *
      ((d : ℝ) / ((allEdges n).card - (M - t) : ℕ))) / 64)
  have hnormalize :
      finsetProbability ((allEdges n).powersetCard M)
          (fun H ↦ Good H ∧ ¬ GlobalLowerWeightSpread n H L eta) =
        @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad
            (fun _ ↦ Classical.propDecidable _) := by
    exact finsetProbability_decidable_irrel _ Bad _ _
  let badDecidable : DecidablePred Bad := fun _ ↦ Classical.propDecidable _
  have hraw :
      @finsetProbability (Finset (Edge n))
          ((allEdges n).powersetCard M) Bad badDecidable ≤
        2 * bottomError := by
    letI : DecidablePred Bad := badDecidable
    exact thinning_bad_probability_le_two_mul
      (allEdges n) M t htM hMtop Bad Diagnostic topError bottomError
        htop0 htopHalf (by positivity)
        (by
          intro H hH hbad
          exact htop H hH hbad.1 hbad.2)
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
