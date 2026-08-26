import ErdosProblems.Erdos747.KahnAggregateLower

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def thinningDeletionPairs {α : Type*} (K : Finset α) (M t : ℕ) :
    Finset (Sigma fun _H : Finset α ↦ Finset α) :=
  (K.powersetCard M).sigma fun H ↦ H.powersetCard t

def thinningExtensionPairs {α : Type*} (K : Finset α) (M t : ℕ) :
    Finset (Sigma fun _F : Finset α ↦ Finset α) :=
  (K.powersetCard (M - t)).sigma fun F ↦ (K \ F).powersetCard t

def thinningDeleteToExtend {α : Type*} :
    (Sigma fun _H : Finset α ↦ Finset α) →
      (Sigma fun _F : Finset α ↦ Finset α)
  | ⟨H, T⟩ => ⟨H \ T, T⟩

def thinningExtendToDelete {α : Type*} :
    (Sigma fun _F : Finset α ↦ Finset α) →
      (Sigma fun _H : Finset α ↦ Finset α)
  | ⟨F, T⟩ => ⟨F ∪ T, T⟩

lemma thinningDeleteToExtend_mem {α : Type*} {K : Finset α} {M t : ℕ}
    (htM : t ≤ M) {p : Sigma fun _H : Finset α ↦ Finset α}
    (hp : p ∈ thinningDeletionPairs K M t) :
    thinningDeleteToExtend p ∈ thinningExtensionPairs K M t := by
  rcases p with ⟨H, T⟩
  rcases Finset.mem_sigma.mp hp with ⟨hHK, hTH⟩
  rcases Finset.mem_powersetCard.mp hHK with ⟨hHK, hHcard⟩
  rcases Finset.mem_powersetCard.mp hTH with ⟨hTH, hTcard⟩
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.Subset.trans Finset.sdiff_subset hHK, ?_⟩
    change (H \ T).card = M - t
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTH,
      hHcard, hTcard]
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hTcard⟩
    intro x hxT
    apply Finset.mem_sdiff.mpr
    refine ⟨hHK (hTH hxT), ?_⟩
    intro hxDiff
    exact (Finset.mem_sdiff.mp hxDiff).2 hxT

lemma thinningExtendToDelete_mem {α : Type*} {K : Finset α} {M t : ℕ}
    (htM : t ≤ M) {p : Sigma fun _F : Finset α ↦ Finset α}
    (hp : p ∈ thinningExtensionPairs K M t) :
    thinningExtendToDelete p ∈ thinningDeletionPairs K M t := by
  rcases p with ⟨F, T⟩
  rcases Finset.mem_sigma.mp hp with ⟨hFK, hTKF⟩
  rcases Finset.mem_powersetCard.mp hFK with ⟨hFK, hFcard⟩
  rcases Finset.mem_powersetCard.mp hTKF with ⟨hTKF, hTcard⟩
  have hTK : T ⊆ K := fun x hx ↦ (Finset.mem_sdiff.mp (hTKF hx)).1
  have hdisj : Disjoint F T := by
    rw [Finset.disjoint_left]
    intro x hxF hxT
    exact (Finset.mem_sdiff.mp (hTKF hxT)).2 hxF
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.union_subset hFK hTK, ?_⟩
    change (F ∪ T).card = M
    rw [Finset.card_union_of_disjoint hdisj, hFcard, hTcard]
    omega
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_union_right, hTcard⟩

lemma thinningDeleteToExtend_leftInverse {α : Type*}
    {K : Finset α} {M t : ℕ} (htM : t ≤ M)
    (p : ↥(thinningDeletionPairs K M t)) :
    thinningExtendToDelete
        (thinningDeleteToExtend p.1) = p.1 := by
  rcases p with ⟨⟨H, T⟩, hp⟩
  rcases Finset.mem_sigma.mp hp with ⟨hHK, hTH⟩
  have hTHsub := (Finset.mem_powersetCard.mp hTH).1
  apply Sigma.ext
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp hx).1
      · exact hTHsub hx
    · intro hx
      by_cases hxT : x ∈ T
      · exact Finset.mem_union_right _ hxT
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
  · rfl

lemma thinningDeleteToExtend_rightInverse {α : Type*}
    {K : Finset α} {M t : ℕ} (htM : t ≤ M)
    (p : ↥(thinningExtensionPairs K M t)) :
    thinningDeleteToExtend
        (thinningExtendToDelete p.1) = p.1 := by
  rcases p with ⟨⟨F, T⟩, hp⟩
  rcases Finset.mem_sigma.mp hp with ⟨hFK, hTKF⟩
  have hTsub := (Finset.mem_powersetCard.mp hTKF).1
  apply Sigma.ext
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxUnion, hxT⟩
      rcases Finset.mem_union.mp hxUnion with hxF | hxT'
      · exact hxF
      · exact False.elim (hxT hxT')
    · intro hxF
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_union_left _ hxF, ?_⟩
      intro hxT
      exact (Finset.mem_sdiff.mp (hTsub hxT)).2 hxF
  · rfl

noncomputable def thinningPairEquiv {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M) :
    ↥(thinningDeletionPairs K M t) ≃
      ↥(thinningExtensionPairs K M t) where
  toFun p := ⟨thinningDeleteToExtend p.1,
    thinningDeleteToExtend_mem htM p.2⟩
  invFun p := ⟨thinningExtendToDelete p.1,
    thinningExtendToDelete_mem htM p.2⟩
  left_inv p := Subtype.ext (thinningDeleteToExtend_leftInverse htM p)
  right_inv p := Subtype.ext (thinningDeleteToExtend_rightInverse htM p)

@[simp] lemma thinningPairEquiv_fst {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M)
    (p : ↥(thinningDeletionPairs K M t)) :
    ((thinningPairEquiv K M t htM p).1).1 = p.1.1 \ p.1.2 := by
  rfl

@[simp] lemma thinningPairEquiv_snd {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M)
    (p : ↥(thinningDeletionPairs K M t)) :
    ((thinningPairEquiv K M t htM p).1).2 = p.1.2 := by
  rfl

lemma thinningPair_probability_equiv {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M)
    (P Q : (Sigma fun _S : Finset α ↦ Finset α) → Prop)
    (hrel : ∀ p ∈ thinningDeletionPairs K M t,
      P p ↔ Q (thinningDeleteToExtend p)) :
    finsetProbability (thinningDeletionPairs K M t) P =
      finsetProbability (thinningExtensionPairs K M t) Q := by
  apply finsetProbability_equiv_subtype _ _
    (thinningPairEquiv K M t htM)
  intro p hp
  exact hrel p hp

lemma card_thinningDeletionPairs {α : Type*}
    (K : Finset α) (M t : ℕ) :
    (thinningDeletionPairs K M t).card =
      (K.powersetCard M).card * M.choose t := by
  rw [thinningDeletionPairs, Finset.card_sigma]
  calc
    ∑ H ∈ K.powersetCard M, (H.powersetCard t).card =
        ∑ _H ∈ K.powersetCard M, M.choose t := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [Finset.card_powersetCard, (Finset.mem_powersetCard.mp hH).2]
    _ = (K.powersetCard M).card * M.choose t := by simp

lemma card_filter_thinningDeletionPairs_fst {α : Type*}
    (K : Finset α) (M t : ℕ) (P : Finset α → Prop) :
    ((thinningDeletionPairs K M t).filter fun p ↦ P p.1).card =
      ((K.powersetCard M).filter P).card * M.choose t := by
  rw [thinningDeletionPairs, Finset.filter_sigma, Finset.card_sigma]
  calc
    ∑ H ∈ K.powersetCard M,
        ((H.powersetCard t).filter fun _T ↦ P H).card =
      ∑ H ∈ (K.powersetCard M).filter P, M.choose t := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases hPH : P H
        · rw [if_pos hPH, Finset.filter_const, if_pos hPH,
            Finset.card_powersetCard,
            (Finset.mem_powersetCard.mp hH).2]
        · rw [if_neg hPH, Finset.filter_const, if_neg hPH]
          simp
    _ = ((K.powersetCard M).filter P).card * M.choose t := by simp

lemma thinningDeletionPairs_probability_fst {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M)
    (hMK : M ≤ K.card) (P : Finset α → Prop) :
    finsetProbability (thinningDeletionPairs K M t) (fun p ↦ P p.1) =
      finsetProbability (K.powersetCard M) P := by
  have hchoose : 0 < M.choose t := Nat.choose_pos htM
  have hchooseR : ((M.choose t : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  unfold finsetProbability
  rw [card_filter_thinningDeletionPairs_fst,
    card_thinningDeletionPairs, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ hchooseR]

lemma thinningDeletionPairs_probability_le_of_fiber {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M) (hMK : M ≤ K.card)
    (P : (Sigma fun _H : Finset α ↦ Finset α) → Prop)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfiber : ∀ H ∈ K.powersetCard M,
      finsetProbability (H.powersetCard t)
        (fun T ↦ P ⟨H, T⟩) ≤ delta) :
    finsetProbability (thinningDeletionPairs K M t) P ≤ delta := by
  let C := M.choose t
  have hbasePos : 0 < (K.powersetCard M).card := by
    rw [Finset.card_powersetCard]
    exact Nat.choose_pos hMK
  have hCpos : 0 < C := Nat.choose_pos htM
  have hnum :
      (((thinningDeletionPairs K M t).filter P).card : ℝ) ≤
        delta * (((K.powersetCard M).card : ℝ) * C) := by
    rw [thinningDeletionPairs, Finset.filter_sigma, Finset.card_sigma]
    rw [Nat.cast_sum (R := ℝ) (K.powersetCard M)
      (fun H ↦ ((H.powersetCard t).filter
        (fun T ↦ P ⟨H, T⟩)).card)]
    calc
      ∑ H ∈ K.powersetCard M,
          ((((H.powersetCard t).filter
            (fun T ↦ P ⟨H, T⟩)).card : ℕ) : ℝ) ≤
        ∑ H ∈ K.powersetCard M,
          delta * ((H.powersetCard t).card : ℝ) := by
            apply Finset.sum_le_sum
            intro H hH
            exact card_filter_le_mul_card_of_finsetProbability_le
              (H.powersetCard t) (fun T ↦ P ⟨H, T⟩)
              delta (hfiber H hH)
      _ = ∑ _H ∈ K.powersetCard M, delta * C := by
        apply Finset.sum_congr rfl
        intro H hH
        rw [Finset.card_powersetCard,
          (Finset.mem_powersetCard.mp hH).2]
      _ = delta * (((K.powersetCard M).card : ℝ) * C) := by
        simp
        ring
  unfold finsetProbability
  rw [card_thinningDeletionPairs]
  norm_num only [Nat.cast_mul]
  have hdenPos : 0 < ((K.powersetCard M).card : ℝ) * (C : ℝ) := by
    positivity
  exact (div_le_iff₀ hdenPos).2 (by simpa only [C] using hnum)

/-- Lower-bound counterpart of `thinningDeletionPairs_probability_le_of_fiber`.
If every top object satisfying `P` has conditional `Q`-probability at
least `delta`, then the joint pair probability is at least the top
probability times `delta`. -/
lemma thinningDeletionPairs_probability_mul_le_of_fiber {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M) (hMK : M ≤ K.card)
    (P : Finset α → Prop)
    (Q : (Sigma fun _H : Finset α ↦ Finset α) → Prop)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfiber : ∀ H ∈ K.powersetCard M, P H →
      delta ≤ finsetProbability (H.powersetCard t)
        (fun T ↦ Q ⟨H, T⟩)) :
    finsetProbability (K.powersetCard M) P * delta ≤
      finsetProbability (thinningDeletionPairs K M t)
        (fun p ↦ P p.1 ∧ Q p) := by
  let C := M.choose t
  have hbasePos : 0 < (K.powersetCard M).card := by
    rw [Finset.card_powersetCard]
    exact Nat.choose_pos hMK
  have hCpos : 0 < C := Nat.choose_pos htM
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hCpos
  have hnum :
      delta * ((((K.powersetCard M).filter P).card : ℝ) * C) ≤
        (((thinningDeletionPairs K M t).filter
          (fun p ↦ P p.1 ∧ Q p)).card : ℝ) := by
    rw [thinningDeletionPairs, Finset.filter_sigma, Finset.card_sigma]
    rw [Nat.cast_sum (R := ℝ) (K.powersetCard M)
      (fun H ↦ ((H.powersetCard t).filter
        (fun T ↦ P H ∧ Q ⟨H, T⟩)).card)]
    rw [show delta * ((((K.powersetCard M).filter P).card : ℝ) * C) =
        ∑ H ∈ K.powersetCard M,
          if P H then delta * C else 0 by
      rw [← Finset.sum_filter]
      simp
      ring]
    apply Finset.sum_le_sum
    intro H hH
    by_cases hPH : P H
    · rw [if_pos hPH]
      have hprob := hfiber H hH hPH
      unfold finsetProbability at hprob
      rw [Finset.filter_congr_decidable
        (p := fun T ↦ Q ⟨H, T⟩),
        Finset.card_powersetCard,
        (Finset.mem_powersetCard.mp hH).2] at hprob
      have hcard :
          delta * (C : ℝ) ≤
            (((H.powersetCard t).filter
              (fun T ↦ Q ⟨H, T⟩)).card : ℝ) := by
        apply (le_div_iff₀ hCposR).mp
        simpa only [C] using hprob
      simpa [hPH, C] using hcard
    · rw [if_neg hPH]
      simp [hPH]
  unfold finsetProbability
  rw [card_thinningDeletionPairs]
  norm_num only [Nat.cast_mul]
  have hdenPos : 0 <
      ((K.powersetCard M).card : ℝ) * (C : ℝ) := by positivity
  have hbasePosR : (0 : ℝ) < (K.powersetCard M).card := by
    exact_mod_cast hbasePos
  have hCneR : (C : ℝ) ≠ 0 := hCposR.ne'
  apply (le_div_iff₀ hdenPos).2
  have hrewrite :
      ((((K.powersetCard M).filter P).card : ℝ) /
          ((K.powersetCard M).card : ℝ)) * delta *
          (((K.powersetCard M).card : ℝ) * C) =
        delta * ((((K.powersetCard M).filter P).card : ℝ) * C) := by
    field_simp [hbasePosR.ne', hCneR]
  rw [hrewrite]
  exact hnum

lemma card_complement_of_mem_powersetCard {α : Type*}
    {K F : Finset α} {m : ℕ} (hF : F ∈ K.powersetCard m) :
    (K \ F).card = K.card - m := by
  rcases Finset.mem_powersetCard.mp hF with ⟨hFK, hFcard⟩
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFK, hFcard]

lemma card_thinningExtensionPairs {α : Type*}
    (K : Finset α) (M t : ℕ) :
    (thinningExtensionPairs K M t).card =
      (K.powersetCard (M - t)).card *
        (K.card - (M - t)).choose t := by
  rw [thinningExtensionPairs, Finset.card_sigma]
  calc
    ∑ F ∈ K.powersetCard (M - t), ((K \ F).powersetCard t).card =
        ∑ _F ∈ K.powersetCard (M - t),
          (K.card - (M - t)).choose t := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [Finset.card_powersetCard,
        card_complement_of_mem_powersetCard hF]
    _ = (K.powersetCard (M - t)).card *
        (K.card - (M - t)).choose t := by simp

lemma thinningExtensionPairs_probability_le_of_fiber {α : Type*}
    (K : Finset α) (M t : ℕ) (htM : t ≤ M) (hMK : M ≤ K.card)
    (P : (Sigma fun _F : Finset α ↦ Finset α) → Prop)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfiber : ∀ F ∈ K.powersetCard (M - t),
      finsetProbability ((K \ F).powersetCard t)
        (fun T ↦ P ⟨F, T⟩) ≤ delta) :
    finsetProbability (thinningExtensionPairs K M t) P ≤ delta := by
  let C := (K.card - (M - t)).choose t
  have hbottom : M - t ≤ K.card := (Nat.sub_le M t).trans hMK
  have hcomp : t ≤ K.card - (M - t) := by omega
  have hbasePos : 0 < (K.powersetCard (M - t)).card := by
    rw [Finset.card_powersetCard]
    exact Nat.choose_pos hbottom
  have hCpos : 0 < C := Nat.choose_pos hcomp
  have hdenPos : (0 : ℝ) <
      ((K.powersetCard (M - t)).card * C : ℕ) := by
    exact_mod_cast Nat.mul_pos hbasePos hCpos
  have hnum :
      (((thinningExtensionPairs K M t).filter P).card : ℝ) ≤
        delta * (((K.powersetCard (M - t)).card : ℝ) * C) := by
    rw [thinningExtensionPairs, Finset.filter_sigma, Finset.card_sigma]
    rw [Nat.cast_sum (R := ℝ) (K.powersetCard (M - t))
      (fun F ↦ (((K \ F).powersetCard t).filter
        (fun T ↦ P ⟨F, T⟩)).card)]
    calc
      ∑ F ∈ K.powersetCard (M - t),
          (((((K \ F).powersetCard t).filter
            (fun T ↦ P ⟨F, T⟩)).card : ℕ) : ℝ) ≤
        ∑ F ∈ K.powersetCard (M - t),
          delta * (((K \ F).powersetCard t).card : ℝ) := by
            apply Finset.sum_le_sum
            intro F hF
            exact card_filter_le_mul_card_of_finsetProbability_le
              ((K \ F).powersetCard t) (fun T ↦ P ⟨F, T⟩)
              delta (hfiber F hF)
      _ = ∑ _F ∈ K.powersetCard (M - t), delta * C := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [Finset.card_powersetCard,
          card_complement_of_mem_powersetCard hF]
      _ = delta * (((K.powersetCard (M - t)).card : ℝ) * C) := by
        simp
        ring
  unfold finsetProbability
  rw [card_thinningExtensionPairs]
  norm_num only [Nat.cast_mul]
  have hdenPos' : 0 <
      ((K.powersetCard (M - t)).card : ℝ) * (C : ℝ) := by
    positivity
  exact (div_le_iff₀ hdenPos').2 (by simpa only [C] using hnum)

end

end Erdos747
