/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import Mathlib

/-!
# The indexed-family selection lemma of Alon--Krivelevich--Sudakov

This file gives a finite double-counting proof of AKS Lemma 2.1.  Families
are functions from a finite index type, rather than finsets of sets, so
distinct indices carrying the same set are counted with their multiplicity.
-/

open scoped BigOperators

namespace Erdos88
namespace AKSFamily

variable {α ι : Type*}

/-- Ordered words of length `t` with letters in `A`. -/
private def words [DecidableEq α] (A : Finset α) (t : ℕ) :
    Finset (∀ j ∈ Finset.range t, α) :=
  (Finset.range t).pi fun _ ↦ A

private lemma card_words [DecidableEq α] (A : Finset α) (t : ℕ) :
    (words A t).card = A.card ^ t := by
  classical
  change ((Multiset.range t).pi fun _ ↦ A.1).card = A.card ^ t
  rw [Multiset.card_pi]
  simp

/-- The points lying in every member of an indexed subfamily. -/
def commonPart [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (A : Finset ι) : Finset α :=
  M.filter fun x ↦ ∀ i ∈ A, x ∈ F i

/-- The points lying outside every member of an indexed subfamily. -/
def commonOutside [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (A : Finset ι) : Finset α :=
  M.filter fun x ↦ ∀ i ∈ A, x ∉ F i

@[simp] lemma mem_commonPart [DecidableEq α] {M : Finset α}
    {F : ι → Finset α} {A : Finset ι} {x : α} :
    x ∈ commonPart M F A ↔ x ∈ M ∧ ∀ i ∈ A, x ∈ F i := by
  classical
  simp [commonPart]

@[simp] lemma mem_commonOutside [DecidableEq α] {M : Finset α}
    {F : ι → Finset α} {A : Finset ι} {x : α} :
    x ∈ commonOutside M F A ↔ x ∈ M ∧ ∀ i ∈ A, x ∉ F i := by
  classical
  simp [commonOutside]

/-- The conclusion required of an AKS-selected indexed subfamily. -/
def GoodSubfamily [DecidableEq α] [DecidableEq ι]
    (M : Finset α) (F : ι → Finset α) (a d : ℕ) (J : Finset ι) : Prop :=
  ∀ A ∈ J.powersetCard a,
    d < (commonPart M F A).card ∧ d < (commonOutside M F A).card

private def samples [DecidableEq α] (M : Finset α) (t : ℕ) :=
  words M t ×ˢ words M t

private lemma card_samples [DecidableEq α] (M : Finset α) (t : ℕ) :
    (samples M t).card = M.card ^ (2 * t) := by
  classical
  rw [samples, Finset.card_product, card_words M t, ← pow_add]
  congr 1
  omega

private def retained [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (F : ι → Finset α) (t : ℕ)
    (w : (∀ j ∈ Finset.range t, α) × (∀ j ∈ Finset.range t, α)) :
    Finset ι :=
  Finset.univ.filter fun i ↦
    (∀ j hj, w.1 j hj ∈ F i) ∧ (∀ j hj, w.2 j hj ∉ F i)

private lemma card_samples_retaining [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (t : ℕ) (i : ι) :
    ((samples M t).filter fun w ↦ i ∈ retained F t w).card =
      (F i).card ^ t * (M \ F i).card ^ t := by
  classical
  have heq :
      (samples M t).filter (fun w ↦ i ∈ retained F t w) =
        words (F i) t ×ˢ words (M \ F i) t := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_product, samples, retained,
      Finset.mem_univ, true_and, Finset.mem_pi, words]
    constructor
    · rintro ⟨⟨hw₁M, hw₂M⟩, hw₁F, hw₂F⟩
      exact ⟨hw₁F, fun j hj ↦ Finset.mem_sdiff.mpr ⟨hw₂M j hj, hw₂F j hj⟩⟩
    · rintro ⟨hw₁F, hw₂out⟩
      refine ⟨⟨fun j hj ↦ hFM i (hw₁F j hj),
        fun j hj ↦ (Finset.mem_sdiff.mp (hw₂out j hj)).1⟩,
        hw₁F, fun j hj ↦ (Finset.mem_sdiff.mp (hw₂out j hj)).2⟩
  rw [heq, Finset.card_product, card_words (F i) t, card_words (M \ F i) t]

private lemma sum_card_retained [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (t : ℕ) :
    ∑ w ∈ samples M t, (retained F t w).card =
      ∑ i : ι, (F i).card ^ t * (M \ F i).card ^ t := by
  classical
  calc
    ∑ w ∈ samples M t, (retained F t w).card =
        ∑ w ∈ samples M t, ∑ i : ι, if i ∈ retained F t w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          symm
          simpa using
            (Finset.sum_boole (R := ℕ) (fun i : ι ↦ i ∈ retained F t w)
              (Finset.univ : Finset ι))
    _ = ∑ i : ι, ∑ w ∈ samples M t,
          if i ∈ retained F t w then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι,
          ((samples M t).filter fun w ↦ i ∈ retained F t w).card := by
          apply Finset.sum_congr rfl
          intro i _
          simpa using
            (Finset.sum_boole (R := ℕ) (fun w ↦ i ∈ retained F t w) (samples M t))
    _ = ∑ i : ι, (F i).card ^ t * (M \ F i).card ^ t := by
          apply Finset.sum_congr rfl
          intro i _
          exact card_samples_retaining M F hFM t i

private lemma lower_sum_card_retained [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (t r q : ℕ)
    (hr : ∀ i, r ≤ (F i).card) (hq : ∀ i, q ≤ (M \ F i).card) :
    Fintype.card ι * (r ^ t * q ^ t) ≤
      ∑ w ∈ samples M t, (retained F t w).card := by
  rw [sum_card_retained M F hFM t]
  calc
    Fintype.card ι * (r ^ t * q ^ t) =
        ∑ _i : ι, r ^ t * q ^ t := by simp
    _ ≤ ∑ i : ι, (F i).card ^ t * (M \ F i).card ^ t := by
      exact Finset.sum_le_sum fun i _ ↦
        Nat.mul_le_mul (Nat.pow_le_pow_left (hr i) t) (Nat.pow_le_pow_left (hq i) t)

private def badTuples [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (M : Finset α) (F : ι → Finset α) (a d : ℕ) : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powersetCard a |>.filter fun A ↦
    (commonPart M F A).card ≤ d ∨ (commonOutside M F A).card ≤ d

private def survivingBad [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (M : Finset α) (F : ι → Finset α) (a d t : ℕ)
    (w : (∀ j ∈ Finset.range t, α) × (∀ j ∈ Finset.range t, α)) :
    Finset (Finset ι) :=
  (badTuples M F a d).filter fun A ↦ A ⊆ retained F t w

private lemma card_samples_surviving_tuple [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (A : Finset ι) (t : ℕ) :
    ((samples M t).filter fun w ↦ A ⊆ retained F t w).card =
      (commonPart M F A).card ^ t * (commonOutside M F A).card ^ t := by
  classical
  have heq :
      (samples M t).filter (fun w ↦ A ⊆ retained F t w) =
        words (commonPart M F A) t ×ˢ words (commonOutside M F A) t := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_filter.mp hw
      have hwSample := Finset.mem_product.mp hw'.1
      have hA := hw'.2
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_pi.mpr
        intro j hj
        rw [mem_commonPart]
        refine ⟨Finset.mem_pi.mp hwSample.1 j hj, ?_⟩
        intro i hi
        exact (Finset.mem_filter.mp (hA hi)).2.1 j hj
      · apply Finset.mem_pi.mpr
        intro j hj
        rw [mem_commonOutside]
        refine ⟨Finset.mem_pi.mp hwSample.2 j hj, ?_⟩
        intro i hi
        exact (Finset.mem_filter.mp (hA hi)).2.2 j hj
    · intro hw
      have hw' := Finset.mem_product.mp hw
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_pi.mpr
          intro j hj
          have hx := Finset.mem_pi.mp hw'.1 j hj
          rw [mem_commonPart] at hx
          exact hx.1
        · apply Finset.mem_pi.mpr
          intro j hj
          have hx := Finset.mem_pi.mp hw'.2 j hj
          rw [mem_commonOutside] at hx
          exact hx.1
      · intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_, ?_⟩
        · intro j hj
          have hx := Finset.mem_pi.mp hw'.1 j hj
          rw [mem_commonPart] at hx
          exact hx.2 i hi
        · intro j hj
          have hx := Finset.mem_pi.mp hw'.2 j hj
          rw [mem_commonOutside] at hx
          exact hx.2 i hi
  rw [heq, Finset.card_product, card_words (commonPart M F A) t,
    card_words (commonOutside M F A) t]

private lemma commonPart_subset [DecidableEq α] (M : Finset α)
    (F : ι → Finset α) (A : Finset ι) : commonPart M F A ⊆ M := by
  intro x hx
  exact (mem_commonPart.mp hx).1

private lemma commonOutside_subset [DecidableEq α] (M : Finset α)
    (F : ι → Finset α) (A : Finset ι) : commonOutside M F A ⊆ M := by
  intro x hx
  exact (mem_commonOutside.mp hx).1

private lemma card_surviving_tuple_le [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (a d t : ℕ) {A : Finset ι} (hA : A ∈ badTuples M F a d) :
    ((samples M t).filter fun w ↦ A ⊆ retained F t w).card ≤
      d ^ t * M.card ^ t := by
  rw [card_samples_surviving_tuple]
  have hbad := (Finset.mem_filter.mp hA).2
  rcases hbad with hpart | hout
  · exact Nat.mul_le_mul (Nat.pow_le_pow_left hpart t)
      (Nat.pow_le_pow_left (Finset.card_le_card (commonOutside_subset M F A)) t)
  · calc
      (commonPart M F A).card ^ t * (commonOutside M F A).card ^ t ≤
          M.card ^ t * d ^ t :=
        Nat.mul_le_mul (Nat.pow_le_pow_left
          (Finset.card_le_card (commonPart_subset M F A)) t)
          (Nat.pow_le_pow_left hout t)
      _ = d ^ t * M.card ^ t := Nat.mul_comm _ _

private lemma card_badTuples_le [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α) (a d : ℕ) :
    (badTuples M F a d).card ≤ (Fintype.card ι).choose a := by
  calc
    (badTuples M F a d).card ≤
        ((Finset.univ : Finset ι).powersetCard a).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (Fintype.card ι).choose a := by
      rw [Finset.card_powersetCard, Finset.card_univ]

private lemma sum_card_survivingBad_le [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (M : Finset α) (F : ι → Finset α)
    (a d t : ℕ) :
    ∑ w ∈ samples M t, (survivingBad M F a d t w).card ≤
      (Fintype.card ι).choose a * (d ^ t * M.card ^ t) := by
  classical
  calc
    ∑ w ∈ samples M t, (survivingBad M F a d t w).card =
        ∑ w ∈ samples M t, ∑ A ∈ badTuples M F a d,
          if A ⊆ retained F t w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      symm
      simpa [survivingBad] using
        (Finset.sum_boole (R := ℕ) (fun A : Finset ι ↦ A ⊆ retained F t w)
          (badTuples M F a d))
    _ = ∑ A ∈ badTuples M F a d, ∑ w ∈ samples M t,
          if A ⊆ retained F t w then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ badTuples M F a d,
          ((samples M t).filter fun w ↦ A ⊆ retained F t w).card := by
      apply Finset.sum_congr rfl
      intro A _
      simpa using
        (Finset.sum_boole (R := ℕ) (fun w ↦ A ⊆ retained F t w) (samples M t))
    _ ≤ ∑ _A ∈ badTuples M F a d, d ^ t * M.card ^ t := by
      exact Finset.sum_le_sum fun A hA ↦ card_surviving_tuple_le M F a d t hA
    _ = (badTuples M F a d).card * (d ^ t * M.card ^ t) := by simp
    _ ≤ (Fintype.card ι).choose a * (d ^ t * M.card ^ t) :=
      Nat.mul_le_mul_right _ (card_badTuples_le M F a d)

/-- **AKS indexed-family selection (Lemma 2.1), in integral counting form.**

`F` is genuinely indexed: two different indices are counted twice even when
they carry equal finsets.  The integers `r` and `q` are lower bounds for the
sizes of a family member and its complement in `M`; `d` is the forbidden
intersection size.  The displayed inequality is the probability inequality
of AKS after multiplication by the `M.card ^ (2*t)` ordered samples. -/
theorem indexedFamilySelection [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (a b t d r q : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ i, r ≤ (F i).card)
    (hq : ∀ i, q ≤ (M \ F i).card)
    (hnumeric :
      (b - 1) * M.card ^ (2 * t) +
          (Fintype.card ι).choose a * (d ^ t * M.card ^ t) <
        Fintype.card ι * (r ^ t * q ^ t)) :
    ∃ J : Finset ι, J.card = b ∧ GoodSubfamily M F a d J := by
  classical
  have hexistsSample :
      ∃ w ∈ samples M t,
        b + (survivingBad M F a d t w).card ≤ (retained F t w).card := by
    by_contra h
    push Not at h
    have hpointwise : ∀ w ∈ samples M t,
        (retained F t w).card ≤
          (b - 1) + (survivingBad M F a d t w).card := by
      intro w hw
      have hwlt := h w hw
      omega
    have hupper :
        ∑ w ∈ samples M t, (retained F t w).card ≤
          (b - 1) * M.card ^ (2 * t) +
            (Fintype.card ι).choose a * (d ^ t * M.card ^ t) := by
      calc
        ∑ w ∈ samples M t, (retained F t w).card ≤
            ∑ w ∈ samples M t,
              ((b - 1) + (survivingBad M F a d t w).card) :=
          Finset.sum_le_sum fun w hw ↦ hpointwise w hw
        _ = (b - 1) * (samples M t).card +
              ∑ w ∈ samples M t, (survivingBad M F a d t w).card := by
          simp [Finset.sum_add_distrib, Nat.mul_comm]
        _ ≤ (b - 1) * M.card ^ (2 * t) +
              (Fintype.card ι).choose a * (d ^ t * M.card ^ t) := by
          rw [card_samples]
          exact Nat.add_le_add_left (sum_card_survivingBad_le M F a d t) _
    have hlower := lower_sum_card_retained M F hFM t r q hr hq
    exact (Nat.not_lt_of_ge (hlower.trans hupper)) hnumeric
  obtain ⟨w, hwSample, hwscore⟩ := hexistsSample
  let R : Finset ι := retained F t w
  let B : Finset (Finset ι) := survivingBad M F a d t w
  have bad_nonempty (A : {A // A ∈ B}) : A.1.Nonempty := by
    have hbad : A.1 ∈ badTuples M F a d :=
      (Finset.mem_filter.mp (show A.1 ∈ B from A.2)).1
    have hpowerset : A.1 ∈ (Finset.univ : Finset ι).powersetCard a :=
      (Finset.mem_filter.mp hbad).1
    have hcard : A.1.card = a := (Finset.mem_powersetCard.mp hpowerset).2
    exact Finset.card_pos.mp (by omega)
  let pick : {A // A ∈ B} → ι := fun A ↦ Classical.choose (bad_nonempty A)
  have pick_mem (A : {A // A ∈ B}) : pick A ∈ A.1 :=
    Classical.choose_spec (bad_nonempty A)
  let D : Finset ι := B.attach.image pick
  let K : Finset ι := R \ D
  have hDcard : D.card ≤ B.card := by
    simpa [D] using (Finset.card_image_le (s := B.attach) (f := pick))
  have hKcard : b ≤ K.card := by
    have hdiff : R.card - D.card ≤ K.card := by
      simpa [K] using Finset.le_card_sdiff D R
    have hscore : b + B.card ≤ R.card := by simpa [R, B] using hwscore
    omega
  have hKsubR : K ⊆ R := Finset.sdiff_subset
  have hKgood : GoodSubfamily M F a d K := by
    intro A hAK
    have hAsubK : A ⊆ K := (Finset.mem_powersetCard.mp hAK).1
    have hAcard : A.card = a := (Finset.mem_powersetCard.mp hAK).2
    have hnotbad : A ∉ badTuples M F a d := by
      intro hAbad
      have hAB : A ∈ B := by
        apply Finset.mem_filter.mpr
        exact ⟨hAbad, hAsubK.trans hKsubR⟩
      let AA : {A // A ∈ B} := ⟨A, hAB⟩
      have hpickD : pick AA ∈ D := by
        exact Finset.mem_image.mpr ⟨AA, by simp, rfl⟩
      have hpickK : pick AA ∈ K := hAsubK (pick_mem AA)
      exact (Finset.mem_sdiff.mp hpickK).2 hpickD
    have hApower : A ∈ (Finset.univ : Finset ι).powersetCard a := by
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hAcard⟩
    have hnot : ¬((commonPart M F A).card ≤ d ∨
        (commonOutside M F A).card ≤ d) := by
      intro hsmall
      exact hnotbad (Finset.mem_filter.mpr ⟨hApower, hsmall⟩)
    omega
  obtain ⟨J, hJK, hJcard⟩ := Finset.exists_subset_card_eq hKcard
  refine ⟨J, hJcard, ?_⟩
  intro A hAJ
  exact hKgood A (Finset.mem_powersetCard.mpr
    ⟨(Finset.mem_powersetCard.mp hAJ).1.trans hJK,
      (Finset.mem_powersetCard.mp hAJ).2⟩)

/-- The first AKS parameter choice: two samples on each side and bad
pairs.  Under the specialized counting inequality one obtains two indexed
sets whose common intersection and common complement both have more than
`d` points. -/
theorem pairSelection [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (d r q : ℕ)
    (hr : ∀ i, r ≤ (F i).card)
    (hq : ∀ i, q ≤ (M \ F i).card)
    (hnumeric :
      M.card ^ 4 + (Fintype.card ι).choose 2 * (d ^ 2 * M.card ^ 2) <
        Fintype.card ι * (r ^ 2 * q ^ 2)) :
    ∃ J : Finset ι, J.card = 2 ∧ GoodSubfamily M F 2 d J := by
  apply indexedFamilySelection M F hFM 2 2 2 d r q (by norm_num) (by norm_num) hr hq
  simpa using hnumeric

/-- The second AKS parameter choice: four samples on each side and bad
triples.  In the application one takes `d = ⌊m^(1/2)⌋` and
`b = ⌊m^(3/5)⌋`; this theorem records the exact integer inequality which is
checked after those substitutions, without hiding any rounding convention. -/
theorem tripleSelection [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (M : Finset α) (F : ι → Finset α)
    (hFM : ∀ i, F i ⊆ M) (b d r q : ℕ) (hb : 0 < b)
    (hr : ∀ i, r ≤ (F i).card)
    (hq : ∀ i, q ≤ (M \ F i).card)
    (hnumeric :
      (b - 1) * M.card ^ 8 +
          (Fintype.card ι).choose 3 * (d ^ 4 * M.card ^ 4) <
        Fintype.card ι * (r ^ 4 * q ^ 4)) :
    ∃ J : Finset ι, J.card = b ∧ GoodSubfamily M F 3 d J := by
  apply indexedFamilySelection M F hFM 3 b 4 d r q (by norm_num) hb hr hq
  simpa using hnumeric

end AKSFamily
end Erdos88
