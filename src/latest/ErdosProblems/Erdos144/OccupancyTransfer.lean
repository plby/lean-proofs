/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos697.Erdos697CRTModel

/-!
# From prime divisibility to occupied logarithmic blocks

This file records the exact finite probability calculation used when prime
divisibility coordinates are grouped into blocks.  A block is occupied when
at least one of its prime coordinates is selected.  The occupied blocks are
independent Bernoulli variables, with parameter

`1 - \prod_p (1 - 1 / p)`.

The formulation with a dependent family `kappa : iota -> Type*` makes the
disjointness of the blocks definitional: the individual prime coordinates
are the elements of `Sigma kappa`.
-/

open scoped BigOperators

namespace Erdos144.OccupancyTransfer

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : ι → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The labels of the blocks meeting a set of prime coordinates. -/
def occupiedLabels (S : Finset (Sigma κ)) : Finset ι :=
  Finset.univ.filter fun i => ∃ j : κ i, Sigma.mk i j ∈ S

@[simp] theorem mem_occupiedLabels (S : Finset (Sigma κ)) (i : ι) :
    i ∈ occupiedLabels κ S ↔ ∃ j : κ i, Sigma.mk i j ∈ S := by
  simp [occupiedLabels]

/-- Compatibility with the ordinary image-of-labels formulation used by
the close-divisor bridge. -/
theorem occupiedLabels_eq_image_fst (S : Finset (Sigma κ)) :
    occupiedLabels κ S = S.image Sigma.fst := by
  ext i
  rw [mem_occupiedLabels]
  constructor
  · rintro ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨⟨i, j⟩, hj, rfl⟩
  · intro hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    obtain ⟨k, j⟩ := z
    dsimp only at hzi
    subst k
    exact ⟨j, hz⟩

/-- The fiber of a finite set of dependent pairs over one block label. -/
def fiber (S : Finset (Sigma κ)) (i : ι) : Finset (κ i) :=
  Finset.univ.filter fun j => Sigma.mk i j ∈ S

@[simp] theorem mem_fiber (S : Finset (Sigma κ)) (i : ι) (j : κ i) :
    j ∈ fiber κ S i ↔ Sigma.mk i j ∈ S := by
  simp [fiber]

/-- Finite subsets of a dependent sum are equivalently finite subsets in
each fiber. -/
def finsetSigmaEquiv : Finset (Sigma κ) ≃ ((i : ι) → Finset (κ i)) where
  toFun S := fiber κ S
  invFun F := Finset.univ.sigma F
  left_inv S := by
    ext z
    obtain ⟨i, j⟩ := z
    simp [fiber]
  right_inv F := by
    funext i
    ext j
    simp [fiber]

@[simp] theorem finsetSigmaEquiv_apply (S : Finset (Sigma κ)) :
    finsetSigmaEquiv κ S = fiber κ S := rfl

@[simp] theorem finsetSigmaEquiv_symm_apply
    (F : (i : ι) → Finset (κ i)) :
    (finsetSigmaEquiv κ).symm F = Finset.univ.sigma F := rfl

@[simp] theorem occupiedLabels_sigma (F : (i : ι) → Finset (κ i)) :
    occupiedLabels κ (Finset.univ.sigma F) =
      Finset.univ.filter fun i => (F i).Nonempty := by
  ext i
  rw [mem_occupiedLabels]
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter]
  change (∃ j, j ∈ F i) ↔ (∃ j, j ∈ F i)
  rfl

/-- The Bernoulli weight on all dependent coordinates factors over the
blocks. -/
theorem weight_sigma_eq_prod_weight
    (p : Sigma κ → ℝ) (F : (i : ι) → Finset (κ i)) :
    Erdos697.Bernoulli.weight (Finset.univ : Finset (Sigma κ)) p
        (Finset.univ.sigma F) =
      ∏ i, Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
        (fun j => p ⟨i, j⟩) (F i) := by
  classical
  unfold Erdos697.Bernoulli.weight
  have hdiff :
      (Finset.univ : Finset (Sigma κ)) \ Finset.univ.sigma F =
        Finset.univ.sigma (fun i => (Finset.univ : Finset (κ i)) \ F i) := by
    ext z
    obtain ⟨i, j⟩ := z
    simp
  rw [hdiff]
  simp only [Finset.prod_sigma]
  rw [Finset.prod_mul_distrib]

/-- Product weight of a family of within-block finite subsets. -/
def blockWeight (p : (i : ι) → κ i → ℝ)
    (F : (i : ι) → Finset (κ i)) : ℝ :=
  ∏ i, Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) (F i)

/-- The occupied-label Bernoulli parameter of a block. -/
def occupancyParam (p : (i : ι) → κ i → ℝ) (i : ι) : ℝ :=
  1 - ∏ j, (1 - p i j)

@[simp] theorem weight_empty (p : (i : ι) → κ i → ℝ) (i : ι) :
    Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) ∅ =
      ∏ j, (1 - p i j) := by
  simp [Erdos697.Bernoulli.weight]

private abbrev LocalChoice (T : Finset ι) (i : ι) :=
  {U : Finset (κ i) // U.Nonempty ↔ i ∈ T}

private theorem sum_localChoice_weight (p : (i : ι) → κ i → ℝ)
    (T : Finset ι) (i : ι) :
    (∑ U : LocalChoice κ T i,
        Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) U.1) =
      if i ∈ T then occupancyParam κ p i else 1 - occupancyParam κ p i := by
  classical
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    have hsum := Erdos697.Bernoulli.sum_weight_powerset
      (Finset.univ : Finset (κ i)) (p i)
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Finset (κ i))))
      (p := fun U : Finset (κ i) => U.Nonempty)
      (f := fun U => Erdos697.Bernoulli.weight
        (Finset.univ : Finset (κ i)) (p i) U)
    have htotal :
        (∑ U : Finset (κ i), Erdos697.Bernoulli.weight
          (Finset.univ : Finset (κ i)) (p i) U) = 1 := by
      simpa using hsum
    have hempty :
        (∑ U ∈ (Finset.univ : Finset (Finset (κ i))).filter
            (fun U => ¬ U.Nonempty),
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) U) =
        ∏ j, (1 - p i j) := by
      rw [Finset.sum_eq_single ∅]
      · exact weight_empty κ p i
      · intro U hU hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
        exact (hU (Finset.nonempty_iff_ne_empty.mpr hne)).elim
      · simp
    have hnonempty :
        (∑ U ∈ (Finset.univ : Finset (Finset (κ i))).filter
            (fun U => U.Nonempty),
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) U) =
        occupancyParam κ p i := by
      rw [occupancyParam]
      linarith [hsplit, htotal, hempty]
    let e : LocalChoice κ T i ≃ {U : Finset (κ i) // U.Nonempty} :=
      { toFun := fun U => ⟨U.1, (U.2.mpr hi)⟩
        invFun := fun U => ⟨U.1, ⟨fun _ => hi, fun _ => U.2⟩⟩
        left_inv := by intro U; apply Subtype.ext; rfl
        right_inv := by intro U; apply Subtype.ext; rfl }
    calc
      (∑ U : LocalChoice κ T i,
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) U.1) =
          ∑ U : {U : Finset (κ i) // U.Nonempty},
            Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
              (p i) U.1 := by
        apply Fintype.sum_equiv e
        intro U
        rfl
      _ = ∑ U ∈ (Finset.univ : Finset (Finset (κ i))).filter
            (fun U => U.Nonempty),
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
            (p i) U := by
        apply (Finset.sum_subtype
          ((Finset.univ : Finset (Finset (κ i))).filter
            (fun U => U.Nonempty)) (by simp)
          (fun U => Erdos697.Bernoulli.weight
            (Finset.univ : Finset (κ i)) (p i) U)).symm
      _ = occupancyParam κ p i := hnonempty
  · rw [if_neg hi]
    have hchoice : ∀ U : LocalChoice κ T i, U.1 = ∅ := by
      intro U
      exact Finset.not_nonempty_iff_eq_empty.mp fun hU =>
        hi (U.2.mp hU)
    calc
      (∑ U : LocalChoice κ T i,
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) U.1) =
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i)) (p i) ∅ := by
            classical
            let e : LocalChoice κ T i ≃ Unit :=
              { toFun := fun _ => Unit.unit
                invFun := fun _ => ⟨∅, by simp [hi]⟩
                left_inv := fun U => Subtype.ext (hchoice U).symm
                right_inv := by intro u; cases u; rfl }
            simpa using Fintype.sum_equiv e
              (fun U : LocalChoice κ T i =>
                Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
                  (p i) U.1)
              (fun _ : Unit =>
                Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
                  (p i) ∅)
              (fun U => by rw [hchoice U])
      _ = 1 - occupancyParam κ p i := by
        simp [occupancyParam, Erdos697.Bernoulli.weight]

private theorem bernoulli_weight_eq_prod_ite
    (q : ι → ℝ) (T : Finset ι) :
    Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T =
      ∏ i, if i ∈ T then q i else 1 - q i := by
  classical
  unfold Erdos697.Bernoulli.weight
  symm
  calc
    (∏ i, if i ∈ T then q i else 1 - q i) =
        ∏ i ∈ T ∪ ((Finset.univ : Finset ι) \ T),
          if i ∈ T then q i else 1 - q i := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ T)]
    _ = (∏ i ∈ T, if i ∈ T then q i else 1 - q i) *
        ∏ i ∈ (Finset.univ : Finset ι) \ T,
          if i ∈ T then q i else 1 - q i :=
      Finset.prod_union Finset.disjoint_sdiff
    _ = (∏ i ∈ T, q i) *
        ∏ i ∈ (Finset.univ : Finset ι) \ T, (1 - q i) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        rw [if_pos hi]
      · apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.mem_sdiff.mp hi).2]

private def choiceFamilyEquiv (T : Finset ι) :
    {F : (i : ι) → Finset (κ i) //
        (Finset.univ.filter fun i => (F i).Nonempty) = T} ≃
      ((i : ι) → LocalChoice κ T i) where
  toFun F i := ⟨F.1 i, by
    have hmem : (F.1 i).Nonempty ↔ i ∈
        (Finset.univ.filter fun j => (F.1 j).Nonempty) := by simp
    rw [F.2] at hmem
    exact hmem⟩
  invFun U := ⟨fun i => (U i).1, by
    ext i
    simp [(U i).2]⟩
  left_inv F := by
    apply Subtype.ext
    funext i
    rfl
  right_inv U := by
    funext i
    apply Subtype.ext
    rfl

/-- Point-mass form of the exact block-occupancy law. -/
theorem sum_blockWeight_fiber_eq_weight
    (p : (i : ι) → κ i → ℝ) (T : Finset ι) :
    (∑ F : {F : (i : ι) → Finset (κ i) //
        (Finset.univ.filter fun i => (F i).Nonempty) = T},
      blockWeight κ p F.1) =
      Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
        (occupancyParam κ p) T := by
  classical
  rw [bernoulli_weight_eq_prod_ite]
  calc
    (∑ F : {F : (i : ι) → Finset (κ i) //
          (Finset.univ.filter fun i => (F i).Nonempty) = T},
        blockWeight κ p F.1) =
        ∑ U : (i : ι) → LocalChoice κ T i,
          blockWeight κ p (fun i => (U i).1) := by
      apply Fintype.sum_equiv (choiceFamilyEquiv κ T)
      intro F
      rfl
    _ = ∑ U : (i : ι) → LocalChoice κ T i,
          ∏ i, Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
            (p i) (U i).1 := by rfl
    _ = ∏ i, ∑ U : LocalChoice κ T i,
          Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
            (p i) U.1 := by
      let w : (i : ι) → LocalChoice κ T i → ℝ := fun i U =>
        Erdos697.Bernoulli.weight (Finset.univ : Finset (κ i))
          (p i) U.1
      change (∑ U : (i : ι) → LocalChoice κ T i, ∏ i, w i (U i)) =
        ∏ i, ∑ U : LocalChoice κ T i, w i U
      exact (Fintype.prod_sum w).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_localChoice_weight κ p T i

/-- Exact pushforward law: independent coordinates grouped by blocks give
independent block-occupancy Bernoulli variables. -/
theorem sum_blockWeight_good_eq_bernoulli
    (p : (i : ι) → κ i → ℝ) (Good : Finset ι → Prop)
    [DecidablePred Good] :
    (∑ F ∈ (Finset.univ : Finset ((i : ι) → Finset (κ i))).filter
        (fun F => Good (Finset.univ.filter fun i => (F i).Nonempty)),
      blockWeight κ p F) =
      ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
          (occupancyParam κ p) T := by
  classical
  simp only [Finset.sum_filter]
  rw [← Fintype.sum_fiberwise
    (fun F : (i : ι) → Finset (κ i) =>
      Finset.univ.filter fun i => (F i).Nonempty)
    (fun F => if Good (Finset.univ.filter fun i => (F i).Nonempty) then
      blockWeight κ p F else 0)]
  apply Fintype.sum_congr
  intro T
  by_cases hT : Good T
  · rw [if_pos hT]
    calc
      (∑ F : {F : (i : ι) → Finset (κ i) //
          (Finset.univ.filter fun i => (F i).Nonempty) = T},
        if Good (Finset.univ.filter fun i => (F.1 i).Nonempty) then
          blockWeight κ p F.1 else 0) =
          ∑ F : {F : (i : ι) → Finset (κ i) //
            (Finset.univ.filter fun i => (F i).Nonempty) = T},
            blockWeight κ p F.1 := by
        apply Fintype.sum_congr
        intro F
        rw [F.2, if_pos hT]
      _ = _ := sum_blockWeight_fiber_eq_weight κ p T
  · rw [if_neg hT]
    apply Fintype.sum_eq_zero
    intro F
    rw [F.2, if_neg hT]

/-- Exact pushforward of the flattened Bernoulli law on `Sigma kappa`. -/
theorem sum_flat_good_eq_bernoulli
    (p : Sigma κ → ℝ) (Good : Finset ι → Prop) [DecidablePred Good] :
    (∑ S ∈ (Finset.univ : Finset (Finset (Sigma κ))).filter
        (fun S => Good (occupiedLabels κ S)),
      Erdos697.Bernoulli.weight (Finset.univ : Finset (Sigma κ)) p S) =
      ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
          (occupancyParam κ (fun i j => p ⟨i, j⟩)) T := by
  classical
  have htransport :
      (∑ S : Finset (Sigma κ),
        if Good (occupiedLabels κ S) then
          Erdos697.Bernoulli.weight (Finset.univ : Finset (Sigma κ)) p S else 0) =
      ∑ F : (i : ι) → Finset (κ i),
        if Good (Finset.univ.filter fun i => (F i).Nonempty) then
          blockWeight κ (fun i j => p ⟨i, j⟩) F else 0 := by
    apply Fintype.sum_equiv (finsetSigmaEquiv κ)
    intro S
    have hS : Finset.univ.sigma (fiber κ S) = S := by
      exact (finsetSigmaEquiv κ).left_inv S
    have hocc : occupiedLabels κ S =
        Finset.univ.filter fun i => (fiber κ S i).Nonempty := by
      calc
        occupiedLabels κ S =
            occupiedLabels κ (Finset.univ.sigma (fiber κ S)) := by rw [hS]
        _ = _ := occupiedLabels_sigma κ (fiber κ S)
    have hw : Erdos697.Bernoulli.weight
        (Finset.univ : Finset (Sigma κ)) p S =
        blockWeight κ (fun i j => p ⟨i, j⟩) (fiber κ S) := by
      calc
        _ = Erdos697.Bernoulli.weight (Finset.univ : Finset (Sigma κ)) p
              (Finset.univ.sigma (fiber κ S)) := by rw [hS]
        _ = _ := weight_sigma_eq_prod_weight κ p (fiber κ S)
    change (if Good (occupiedLabels κ S) then
        Erdos697.Bernoulli.weight (Finset.univ : Finset (Sigma κ)) p S else 0) =
      if Good (Finset.univ.filter fun i => (fiber κ S i).Nonempty) then
        blockWeight κ (fun i j => p ⟨i, j⟩) (fiber κ S) else 0
    rw [hocc, hw]
  simp only [Finset.sum_filter]
  rw [htransport]
  simpa only [Finset.sum_filter] using
    (sum_blockWeight_good_eq_bernoulli κ
      (fun i j => p ⟨i, j⟩) Good)

/-! ## Heterogeneous product comparison -/

/-- Splitting off one unselected Bernoulli coordinate. -/
private theorem weight_insert_not_selected {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) {a : α} (ha : a ∉ s)
    {T : Finset α} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p T =
      (1 - p a) * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT => ha (hT haT)
  simp [Erdos697.Bernoulli.weight, ha, haT,
    Finset.insert_sdiff_of_notMem]
  ring

/-- Splitting off one selected Bernoulli coordinate. -/
private theorem weight_insert_selected {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) {a : α} (ha : a ∉ s)
    {T : Finset α} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p (insert a T) =
      p a * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT => ha (hT haT)
  have hdiff : insert a s \ insert a T = s \ T := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  rw [Erdos697.Bernoulli.weight, Erdos697.Bernoulli.weight, hdiff]
  simp [haT]
  ring

private theorem bernoulli_product_l1_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (q r : α → ℝ)
    (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq1 : ∀ i ∈ s, q i ≤ 1)
    (hr0 : ∀ i ∈ s, 0 ≤ r i) (hr1 : ∀ i ∈ s, r i ≤ 1) :
    (∑ T ∈ s.powerset,
      |Erdos697.Bernoulli.weight s q T -
        Erdos697.Bernoulli.weight s r T|) ≤
      2 * ∑ i ∈ s, |q i - r i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Erdos697.Bernoulli.weight]
  | @insert a s ha ih =>
      have hq0s : ∀ i ∈ s, 0 ≤ q i :=
        fun i hi => hq0 i (Finset.mem_insert_of_mem hi)
      have hq1s : ∀ i ∈ s, q i ≤ 1 :=
        fun i hi => hq1 i (Finset.mem_insert_of_mem hi)
      have hr0s : ∀ i ∈ s, 0 ≤ r i :=
        fun i hi => hr0 i (Finset.mem_insert_of_mem hi)
      have hr1s : ∀ i ∈ s, r i ≤ 1 :=
        fun i hi => hr1 i (Finset.mem_insert_of_mem hi)
      have hi := ih hq0s hq1s hr0s hr1s
      have hqa0 : 0 ≤ q a := hq0 a (Finset.mem_insert_self a s)
      have hqa1 : q a ≤ 1 := hq1 a (Finset.mem_insert_self a s)
      have hra0 : 0 ≤ r a := hr0 a (Finset.mem_insert_self a s)
      have hra1 : r a ≤ 1 := hr1 a (Finset.mem_insert_self a s)
      have hnot : ∀ T ∈ s.powerset,
          |Erdos697.Bernoulli.weight (insert a s) q T -
              Erdos697.Bernoulli.weight (insert a s) r T| ≤
            (1 - q a) *
                |Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T| +
              |q a - r a| * Erdos697.Bernoulli.weight s r T := by
        intro T hT
        have hsub := Finset.mem_powerset.mp hT
        rw [weight_insert_not_selected s q ha hsub,
          weight_insert_not_selected s r ha hsub]
        have hwr := Erdos697.Bernoulli.weight_nonneg s r hr0s hr1s hT
        calc
          |(1 - q a) * Erdos697.Bernoulli.weight s q T -
              (1 - r a) * Erdos697.Bernoulli.weight s r T| =
            |(1 - q a) *
                (Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T) +
              (r a - q a) * Erdos697.Bernoulli.weight s r T| := by
                congr 1
                ring
          _ ≤ |(1 - q a) *
                  (Erdos697.Bernoulli.weight s q T -
                    Erdos697.Bernoulli.weight s r T)| +
                |(r a - q a) * Erdos697.Bernoulli.weight s r T| :=
              abs_add_le _ _
          _ = (1 - q a) *
                  |Erdos697.Bernoulli.weight s q T -
                    Erdos697.Bernoulli.weight s r T| +
                |q a - r a| * Erdos697.Bernoulli.weight s r T := by
              rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqa1), abs_mul,
                abs_of_nonneg hwr, abs_sub_comm (r a) (q a)]
      have hsel : ∀ T ∈ s.powerset,
          |Erdos697.Bernoulli.weight (insert a s) q (insert a T) -
              Erdos697.Bernoulli.weight (insert a s) r (insert a T)| ≤
            q a *
                |Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T| +
              |q a - r a| * Erdos697.Bernoulli.weight s r T := by
        intro T hT
        have hsub := Finset.mem_powerset.mp hT
        rw [weight_insert_selected s q ha hsub,
          weight_insert_selected s r ha hsub]
        have hwr := Erdos697.Bernoulli.weight_nonneg s r hr0s hr1s hT
        calc
          |q a * Erdos697.Bernoulli.weight s q T -
              r a * Erdos697.Bernoulli.weight s r T| =
            |q a *
                (Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T) +
              (q a - r a) * Erdos697.Bernoulli.weight s r T| := by
                congr 1
                ring
          _ ≤ |q a *
                  (Erdos697.Bernoulli.weight s q T -
                    Erdos697.Bernoulli.weight s r T)| +
                |(q a - r a) * Erdos697.Bernoulli.weight s r T| :=
              abs_add_le _ _
          _ = q a *
                  |Erdos697.Bernoulli.weight s q T -
                    Erdos697.Bernoulli.weight s r T| +
                |q a - r a| * Erdos697.Bernoulli.weight s r T := by
              rw [abs_mul, abs_of_nonneg hqa0, abs_mul,
                abs_of_nonneg hwr]
      have hsumr :
          (∑ T ∈ s.powerset, Erdos697.Bernoulli.weight s r T) = 1 :=
        Erdos697.Bernoulli.sum_weight_powerset s r
      rw [Finset.sum_powerset_insert ha, Finset.sum_insert ha]
      calc
        (∑ T ∈ s.powerset,
            |Erdos697.Bernoulli.weight (insert a s) q T -
              Erdos697.Bernoulli.weight (insert a s) r T|) +
            ∑ T ∈ s.powerset,
              |Erdos697.Bernoulli.weight (insert a s) q (insert a T) -
                Erdos697.Bernoulli.weight (insert a s) r (insert a T)| ≤
          (∑ T ∈ s.powerset,
            ((1 - q a) *
                |Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T| +
              |q a - r a| * Erdos697.Bernoulli.weight s r T)) +
          ∑ T ∈ s.powerset,
            (q a *
                |Erdos697.Bernoulli.weight s q T -
                  Erdos697.Bernoulli.weight s r T| +
              |q a - r a| * Erdos697.Bernoulli.weight s r T) :=
            add_le_add (Finset.sum_le_sum hnot) (Finset.sum_le_sum hsel)
        _ = (∑ T ∈ s.powerset,
              |Erdos697.Bernoulli.weight s q T -
                Erdos697.Bernoulli.weight s r T|) +
            2 * |q a - r a| := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum]
          rw [hsumr]
          ring
        _ ≤ 2 * (∑ i ∈ s, |q i - r i|) + 2 * |q a - r a| :=
          add_le_add hi (le_refl _)
        _ = 2 * (|q a - r a| + ∑ i ∈ s, |q i - r i|) := by ring

/-- The `L^1` distance of two Bernoulli product laws is at most twice the
sum of the coordinate parameter errors. -/
theorem bernoulli_product_l1_le
    (q r : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    (∑ T : Finset ι,
      |Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T -
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T|) ≤
      2 * ∑ i, |q i - r i| := by
  classical
  simpa using bernoulli_product_l1_finset
    (Finset.univ : Finset ι) q r
    (fun i _ => hq0 i) (fun i _ => hq1 i)
    (fun i _ => hr0 i) (fun i _ => hr1 i)

/-- Event probabilities differ by at most the full `L^1` distance. -/
theorem bernoulli_good_mass_sub_le
    (q r : ι → ℝ) (Good : Finset ι → Prop) [DecidablePred Good]
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    |(∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T) -
      (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T)| ≤
      2 * ∑ i, |q i - r i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        (Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T -
          Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T)| ≤
      ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        |Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T -
          Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T : Finset ι,
        |Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T -
          Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro T _ _
        exact abs_nonneg _
    _ ≤ 2 * ∑ i, |q i - r i| :=
      bernoulli_product_l1_le q r hq0 hq1 hr0 hr1

/-! ## CRT package -/

/-- The prime-divisibility CRT set whose occupied labels satisfy `Good` has
exactly the Bernoulli block-occupancy density. -/
theorem crt_occupiedLabels_good_hasDensity
    (a : Sigma κ → ℕ) [(z : Sigma κ) → NeZero (a z)]
    [NeZero (∏ z, a z)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (Good : Finset ι → Prop) [DecidablePred Good] :
    {n : ℕ | Good
      (occupiedLabels κ
        (Erdos697.CRTModel.zeroSet a
          (ZMod.prodEquivPi a hcoprime (n : ZMod (∏ z, a z)))))}.HasDensity
      (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
          (occupancyParam κ (fun i j => 1 / (a ⟨i, j⟩ : ℝ))) T) := by
  have hcrt := Erdos697.CRTModel.crt_zeroSet_good_hasDensity a hcoprime
    (fun S => Good (occupiedLabels κ S))
  rw [sum_flat_good_eq_bernoulli] at hcrt
  exact hcrt

/-- Quantitative CRT transfer from an arbitrary comparison product law. -/
theorem comparison_good_mass_sub_le_crt_density
    (a : Sigma κ → ℕ) [(z : Sigma κ) → NeZero (a z)]
    [NeZero (∏ z, a z)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (Good : Finset ι → Prop) [DecidablePred Good]
    (r : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ occupancyParam κ
      (fun i j => 1 / (a ⟨i, j⟩ : ℝ)) i)
    (hq1 : ∀ i, occupancyParam κ
      (fun i j => 1 / (a ⟨i, j⟩ : ℝ)) i ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    let q := occupancyParam κ (fun i j => 1 / (a ⟨i, j⟩ : ℝ))
    let d := ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
      Erdos697.Bernoulli.weight (Finset.univ : Finset ι) q T
    let harmonicMass := ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
      Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T
    ({n : ℕ | Good
      (occupiedLabels κ
        (Erdos697.CRTModel.zeroSet a
          (ZMod.prodEquivPi a hcoprime (n : ZMod (∏ z, a z)))))}.HasDensity d) ∧
      harmonicMass - 2 * ∑ i, |q i - r i| ≤ d := by
  dsimp only
  constructor
  · exact crt_occupiedLabels_good_hasDensity κ a hcoprime Good
  · have h := bernoulli_good_mass_sub_le
      (occupancyParam κ (fun i j => 1 / (a ⟨i, j⟩ : ℝ))) r Good
      hq0 hq1 hr0 hr1
    have hlow :
        (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
            Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T) -
          (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
            Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
              (occupancyParam κ (fun i j => 1 / (a ⟨i, j⟩ : ℝ))) T) ≤
          2 * ∑ i, |occupancyParam κ
            (fun i j => 1 / (a ⟨i, j⟩ : ℝ)) i - r i| := by
      calc
        _ ≤ |(∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
                Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
                  (occupancyParam κ (fun i j => 1 / (a ⟨i, j⟩ : ℝ))) T) -
              (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
                Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T)| := by
          simpa only [neg_sub] using neg_le_abs
            ((∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
                Erdos697.Bernoulli.weight (Finset.univ : Finset ι)
                  (occupancyParam κ
                    (fun i j => 1 / (a ⟨i, j⟩ : ℝ))) T) -
              (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter Good,
                Erdos697.Bernoulli.weight (Finset.univ : Finset ι) r T))
        _ ≤ _ := h
    linarith

end

end Erdos144.OccupancyTransfer
