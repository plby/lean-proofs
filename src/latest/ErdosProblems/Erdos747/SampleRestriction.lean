import ErdosProblems.Erdos747.CompletionSurvival

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

/-! ## Restricting an unordered sample away from an exceptional set -/

lemma powersetCard_hit_probability_le_ratio {α : Type*} [DecidableEq α]
    (K B : Finset α) (hBK : B ⊆ K) (t : ℕ)
    (ht : t ≤ K.card) (hK : K.Nonempty) :
    finsetProbability (K.powersetCard t)
        (fun T ↦ ¬ Disjoint T B) ≤
      (t : ℝ) * (B.card : ℝ) / K.card := by
  by_cases ht0 : t = 0
  · subst t
    have hevent : finsetProbability (K.powersetCard 0)
        (fun T ↦ ¬ Disjoint T B) = 0 := by
      simp [finsetProbability]
    rw [hevent]
    norm_num
  have htpos : 0 < t := Nat.pos_of_ne_zero ht0
  let cinter : Finset α → Finset α → Finset α :=
    @Inter.inter (Finset α)
      (@Finset.instInter α (fun a b ↦ Classical.propDecidable (a = b)))
  have hraw := powersetCard_many_hits_probability_le K B hBK t 1
    (by omega)
  have hevent :
      finsetProbability (K.powersetCard t)
          (fun T ↦ ¬ Disjoint T B) =
        finsetProbability (K.powersetCard t)
          (fun T ↦ 1 ≤ (cinter T B).card) := by
    apply finsetProbability_congr_event
    intro T hT
    have hinter : cinter T B = T ∩ B := by
      ext x
      simp [cinter]
    rw [hinter, Finset.not_disjoint_iff_nonempty_inter]
    constructor
    · intro hne
      exact Nat.one_le_iff_ne_zero.mpr
        (Finset.card_ne_zero.mpr hne)
    · intro hcard
      exact Finset.card_pos.mp (by omega)
  rw [hevent]
  have hchoosePos : 0 < K.card.choose t := Nat.choose_pos ht
  have hKcardPos : 0 < K.card := Finset.card_pos.mpr hK
  have hchooseId :
      K.card.choose t * t =
        K.card * (K.card - 1).choose (t - 1) := by
    simpa only [Nat.choose_one_right] using
      (Nat.choose_mul (n := K.card) (k := t) (s := 1) (by omega))
  have hchooseIdR :
      ((K.card.choose t : ℕ) : ℝ) * t =
        (K.card : ℝ) * ((K.card - 1).choose (t - 1) : ℕ) := by
    exact_mod_cast hchooseId
  calc
    finsetProbability (K.powersetCard t)
          (fun T ↦ 1 ≤ (cinter T B).card) ≤
        ((B.card.choose 1 : ℕ) : ℝ) *
            (((K.card - 1).choose (t - 1) : ℕ) : ℝ) /
          ((K.card.choose t : ℕ) : ℝ) := by
      simpa only [cinter] using hraw
    _ = (t : ℝ) * (B.card : ℝ) / K.card := by
      rw [Nat.choose_one_right]
      have hchooseR : (0 : ℝ) < K.card.choose t := by
        exact_mod_cast hchoosePos
      have hKcardR : (0 : ℝ) < K.card := by
        exact_mod_cast hKcardPos
      field_simp [hchooseR.ne', hKcardR.ne']
      nlinarith [hchooseIdR]

lemma powersetCard_probability_disjoint_le_restriction
    {α : Type*} [DecidableEq α]
    (K B : Finset α) (t : ℕ) (P : Finset α → Prop)
    [DecidablePred P]
    (ht : t ≤ (K \ B).card) :
    finsetProbability (K.powersetCard t)
        (fun T ↦ Disjoint T B ∧ P T) ≤
      finsetProbability ((K \ B).powersetCard t) P := by
  have hfilter :
      (K.powersetCard t).filter (fun T ↦ Disjoint T B ∧ P T) =
        ((K \ B).powersetCard t).filter P := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hTK, hTcard⟩, hdisj, hP⟩
      refine ⟨⟨?_, hTcard⟩, hP⟩
      intro x hxT
      exact Finset.mem_sdiff.mpr
        ⟨hTK hxT, fun hxB ↦ Finset.disjoint_left.mp hdisj hxT hxB⟩
    · rintro ⟨⟨hTsub, hTcard⟩, hP⟩
      have hTK : T ⊆ K := fun x hx ↦
        (Finset.mem_sdiff.mp (hTsub hx)).1
      have hdisj : Disjoint T B := Finset.disjoint_left.mpr fun x hxT hxB ↦
        (Finset.mem_sdiff.mp (hTsub hxT)).2 hxB
      exact ⟨⟨hTK, hTcard⟩, hdisj, hP⟩
  have hsmallPos : 0 < (K \ B).card.choose t := Nat.choose_pos ht
  have hcardLe : (K \ B).card.choose t ≤ K.card.choose t :=
    Nat.choose_le_choose t (Finset.card_le_card Finset.sdiff_subset)
  unfold finsetProbability
  rw [hfilter, Finset.card_powersetCard, Finset.card_powersetCard]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast hsmallPos
  · exact_mod_cast hcardLe

lemma powersetCard_probability_le_hit_add_restriction
    {α : Type*} [DecidableEq α]
    (K B : Finset α) (hBK : B ⊆ K) (t : ℕ)
    (P : Finset α → Prop) [DecidablePred P]
    (ht : t ≤ (K \ B).card)
    (hK : K.Nonempty) :
    finsetProbability (K.powersetCard t) P ≤
      (t : ℝ) * (B.card : ℝ) / K.card +
        finsetProbability ((K \ B).powersetCard t) P := by
  have htK : t ≤ K.card :=
    ht.trans (Finset.card_le_card Finset.sdiff_subset)
  calc
    finsetProbability (K.powersetCard t) P ≤
        finsetProbability (K.powersetCard t)
            (fun T ↦ ¬ Disjoint T B) +
          finsetProbability (K.powersetCard t)
            (fun T ↦ Disjoint T B ∧ P T) := by
      calc
        finsetProbability (K.powersetCard t) P ≤
            finsetProbability (K.powersetCard t)
              (fun T ↦ ¬ Disjoint T B ∨ (Disjoint T B ∧ P T)) := by
          apply finsetProbability_mono_event
          intro T hT hP
          by_cases hdisj : Disjoint T B
          · exact Or.inr ⟨hdisj, hP⟩
          · exact Or.inl hdisj
        _ ≤ _ := finsetProbability_or_le_add _ _ _
    _ ≤ (t : ℝ) * (B.card : ℝ) / K.card +
          finsetProbability ((K \ B).powersetCard t) P :=
      add_le_add
        (powersetCard_hit_probability_le_ratio K B hBK t htK hK)
        (powersetCard_probability_disjoint_le_restriction K B t P ht)

end

end Erdos747
