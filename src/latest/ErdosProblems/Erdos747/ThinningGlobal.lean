import ErdosProblems.Erdos747.ResidualWeights

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Bottom-measurable weight-block diagnostics -/

def UpperWeightBlockDiagnostic (n d t : ℕ)
    (p : Sigma fun _H : Finset (Edge n) ↦ Finset (Edge n)) : Prop :=
  let F := p.1 \ p.2
  TopBlockUnderhit (allEdges n \ F) p.2
    (fun Z ↦ (completionWeight F Z : ℝ)) d t

def LowerWeightBlockDiagnostic (n d t : ℕ)
    (p : Sigma fun _H : Finset (Edge n) ↦ Finset (Edge n)) : Prop :=
  let F := p.1 \ p.2
  BottomBlockUnderhit (allEdges n \ F) p.2
    (fun Z ↦ (completionWeight F Z : ℝ)) d t

lemma upperWeightBlockDiagnostic_of_certificate
    {n d t e : ℕ} (H T X : Finset (Edge n)) (a : ℝ)
    (hd : d ≤ (allEdges n \ (H \ T)).card)
    (hXs : X ⊆ allEdges n \ (H \ T)) (hcard : d < X.card)
    (hX : ∀ Z ∈ X, a < (completionWeight (H \ T) Z : ℝ))
    (hexceptions :
      (T.filter fun Z ↦ a < (completionWeight (H \ T) Z : ℝ)).card ≤ e)
    (he : (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
      ((d : ℝ) / (allEdges n \ (H \ T)).card)) :
    UpperWeightBlockDiagnostic n d t ⟨H, T⟩ := by
  exact topBlockUnderhit_of_many_gt
    (allEdges n \ (H \ T)) T X
      (fun Z ↦ (completionWeight (H \ T) Z : ℝ))
      d t e a hd hXs hcard hX hexceptions he

lemma lowerWeightBlockDiagnostic_of_certificate
    {n d t e : ℕ} (H T X : Finset (Edge n)) (a : ℝ)
    (hd : d ≤ (allEdges n \ (H \ T)).card)
    (hXs : X ⊆ allEdges n \ (H \ T)) (hcard : d < X.card)
    (hX : ∀ Z ∈ X, (completionWeight (H \ T) Z : ℝ) < a)
    (hexceptions :
      (T.filter fun Z ↦ (completionWeight (H \ T) Z : ℝ) < a).card ≤ e)
    (he : (e : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) *
      ((d : ℝ) / (allEdges n \ (H \ T)).card)) :
    LowerWeightBlockDiagnostic n d t ⟨H, T⟩ := by
  exact bottomBlockUnderhit_of_many_lt
    (allEdges n \ (H \ T)) T X
      (fun Z ↦ (completionWeight (H \ T) Z : ℝ))
      d t e a hd hXs hcard hX hexceptions he

lemma union_sdiff_eq_left_of_subset_sdiff {α : Type*}
    [DecidableEq α] (K F T : Finset α) (hT : T ⊆ K \ F) :
    (F ∪ T) \ T = F := by
  have hdisj : Disjoint F T := Finset.disjoint_left.mpr fun x hxF hxT ↦
    (Finset.mem_sdiff.mp (hT hxT)).2 hxF
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hxF | hxT, hxnot⟩
    · exact hxF
    · exact False.elim (hxnot hxT)
  · intro hxF
    exact ⟨Or.inl hxF, fun hxT ↦ Finset.disjoint_left.mp hdisj hxF hxT⟩

lemma upperWeightBlockDiagnostic_bottom_probability_le
    {n M t d : ℕ} (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (hd : d ≤ (allEdges n).card - (M - t))
    (ht : t ≤ (allEdges n).card - (M - t))
    (hs : 0 < (allEdges n).card - (M - t))
    (hcollision : 2 * t * t ≤ (allEdges n).card - (M - t)) :
    ∀ F ∈ (allEdges n).powersetCard (M - t),
      finsetProbability ((allEdges n \ F).powersetCard t)
          (fun T ↦ UpperWeightBlockDiagnostic n d t ⟨F ∪ T, T⟩) ≤
        2 * Real.exp
          (-((t : ℝ) *
            ((d : ℝ) /
              ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  intro F hF
  rcases Finset.mem_powersetCard.mp hF with ⟨hFsub, hFcard⟩
  have hcard : (allEdges n \ F).card =
      (allEdges n).card - (M - t) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub, hFcard]
  have hnonempty : (allEdges n \ F).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact hs
  have htail := topBlockUnderhit_powersetCard_probability_le
    (allEdges n \ F)
      (fun Z ↦ (completionWeight F Z : ℝ))
      (by simpa only [hcard] using hd)
      (by simpa only [hcard] using ht) hnonempty
      (by simpa only [hcard] using hcollision)
  calc
    finsetProbability ((allEdges n \ F).powersetCard t)
        (fun T ↦ UpperWeightBlockDiagnostic n d t ⟨F ∪ T, T⟩) =
      finsetProbability ((allEdges n \ F).powersetCard t)
        (fun T ↦ TopBlockUnderhit (allEdges n \ F) T
          (fun Z ↦ (completionWeight F Z : ℝ)) d t) := by
      apply finsetProbability_congr_event
      intro T hT
      have hTsub := (Finset.mem_powersetCard.mp hT).1
      have hdiff := union_sdiff_eq_left_of_subset_sdiff
        (allEdges n) F T hTsub
      simp only [UpperWeightBlockDiagnostic, hdiff]
    _ ≤ 2 * Real.exp
          (-((t : ℝ) * ((d : ℝ) / (allEdges n \ F).card)) / 64) := htail
    _ = _ := by rw [hcard]

lemma lowerWeightBlockDiagnostic_bottom_probability_le
    {n M t d : ℕ} (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card)
    (hd : d ≤ (allEdges n).card - (M - t))
    (ht : t ≤ (allEdges n).card - (M - t))
    (hs : 0 < (allEdges n).card - (M - t))
    (hcollision : 2 * t * t ≤ (allEdges n).card - (M - t)) :
    ∀ F ∈ (allEdges n).powersetCard (M - t),
      finsetProbability ((allEdges n \ F).powersetCard t)
          (fun T ↦ LowerWeightBlockDiagnostic n d t ⟨F ∪ T, T⟩) ≤
        2 * Real.exp
          (-((t : ℝ) *
            ((d : ℝ) /
              ((allEdges n).card - (M - t) : ℕ))) / 64) := by
  intro F hF
  rcases Finset.mem_powersetCard.mp hF with ⟨hFsub, hFcard⟩
  have hcard : (allEdges n \ F).card =
      (allEdges n).card - (M - t) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub, hFcard]
  have hnonempty : (allEdges n \ F).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact hs
  have htail := bottomBlockUnderhit_powersetCard_probability_le
    (allEdges n \ F)
      (fun Z ↦ (completionWeight F Z : ℝ))
      (by simpa only [hcard] using hd)
      (by simpa only [hcard] using ht) hnonempty
      (by simpa only [hcard] using hcollision)
  calc
    finsetProbability ((allEdges n \ F).powersetCard t)
        (fun T ↦ LowerWeightBlockDiagnostic n d t ⟨F ∪ T, T⟩) =
      finsetProbability ((allEdges n \ F).powersetCard t)
        (fun T ↦ BottomBlockUnderhit (allEdges n \ F) T
          (fun Z ↦ (completionWeight F Z : ℝ)) d t) := by
      apply finsetProbability_congr_event
      intro T hT
      have hTsub := (Finset.mem_powersetCard.mp hT).1
      have hdiff := union_sdiff_eq_left_of_subset_sdiff
        (allEdges n) F T hTsub
      simp only [LowerWeightBlockDiagnostic, hdiff]
    _ ≤ 2 * Real.exp
          (-((t : ℝ) * ((d : ℝ) / (allEdges n \ F).card)) / 64) := htail
    _ = _ := by rw [hcard]

end

end Erdos747
