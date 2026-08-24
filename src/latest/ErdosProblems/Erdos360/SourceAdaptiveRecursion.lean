/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.NormalizedFiberSelector

/-!
# The source-faithful adaptive modular recursion

The original recursion in `Core` chooses a large *global* translation in
every non-growth phase.  The inverse-theorem part of the Conlon--Fox--Pham
argument needs a different choice: after selecting an occupied fibre, the
next element must maximize translation growth in the normalized copy of
that fibre.  This file defines that recursion without changing the earlier
one.

The fibre is chosen canonically, as a fibre of minimum cardinality.  Thus
the choice depends only on the source threshold `Q`: if no fibre has size at
most `Q`, but some fibre is below a later saturation threshold, the chosen
fibre is automatically strictly between those two thresholds.  In a source
growth phase for which `4 * Q <= |R|`, the recursion retains the internal
`3/2` growth witness already proved in `Core`.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

section LocalSelector

variable {b : ℕ} [NeZero b]

/-- The subset-sum set visible at a phase whose unused set is `R`. -/
noncomputable def sourceAdaptivePhaseSet
    (R₀ E R : Finset (ZMod b)) : Finset (ZMod b) :=
  E + (R₀ \ R).subsetSum

/-- The normalized fibre over `u` at a phase whose unused set is `R`. -/
noncomputable def sourceAdaptiveFiber
    (R₀ E R : Finset (ZMod b)) (u : ZMod b) :=
  normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
    (sourceAdaptivePhaseSet R₀ E R) u

/-- A canonical fibre of minimum cardinality.  Choosing the smallest fibre
is what makes the selector independent of the later saturation target. -/
noncomputable def sourceAdaptiveMinFiberCenter
    (R₀ E R : Finset (ZMod b)) : ZMod b :=
  Classical.choose (Finset.exists_min_image (Finset.univ : Finset (ZMod b))
    (fun u => (sourceAdaptiveFiber R₀ E R u).card)
    Finset.univ_nonempty)

lemma sourceAdaptiveMinFiberCenter_mem_univ
    (R₀ E R : Finset (ZMod b)) :
    sourceAdaptiveMinFiberCenter R₀ E R ∈
      (Finset.univ : Finset (ZMod b)) := by
  exact (Classical.choose_spec (Finset.exists_min_image
    (Finset.univ : Finset (ZMod b))
    (fun u => (sourceAdaptiveFiber R₀ E R u).card)
    Finset.univ_nonempty)).1

lemma sourceAdaptiveMinFiberCenter_minimal
    (R₀ E R : Finset (ZMod b)) (u : ZMod b) :
    (sourceAdaptiveFiber R₀ E R
        (sourceAdaptiveMinFiberCenter R₀ E R)).card ≤
      (sourceAdaptiveFiber R₀ E R u).card := by
  exact (Classical.choose_spec (Finset.exists_min_image
    (Finset.univ : Finset (ZMod b))
    (fun v => (sourceAdaptiveFiber R₀ E R v).card)
    Finset.univ_nonempty)).2 u (Finset.mem_univ u)

/-- The source growth test, phrased for an arbitrary current remainder. -/
def IsSourceAdaptiveGrowthPhase
    (R₀ E R : Finset (ZMod b)) (Q : ℕ) : Prop :=
  ∃ u : ZMod b,
    (sourceAdaptiveFiber R₀ E R u).Nonempty ∧
      (sourceAdaptiveFiber R₀ E R u).card ≤ Q

/-- The exact guard under which the internal-growth witness can be used.
The first two conjuncts are the hypotheses needed by divisor diversity and
the last inequality converts the source threshold into the quarter-size
condition of `IsModularGrowthPhase`. -/
def SourceAdaptiveGrowthReady
    (R₀ E R : Finset (ZMod b)) (Q : ℕ) : Prop :=
  R.Nonempty ∧ R ⊆ R₀ ∧ R₀.card ≤ 2 * R.card ∧
    4 * Q ≤ R.card ∧ IsSourceAdaptiveGrowthPhase R₀ E R Q

lemma isModularGrowthPhase_of_sourceAdaptive
    (hb : 0 < b) (R₀ E R : Finset (ZMod b)) (Q : ℕ)
    (hQ : 4 * Q ≤ R.card)
    (hg : IsSourceAdaptiveGrowthPhase R₀ E R Q) :
    IsModularGrowthPhase hb R₀ R E := by
  obtain ⟨u, _, huQ⟩ := hg
  refine ⟨u, ?_⟩
  change 4 * (sourceAdaptiveFiber R₀ E R u).card ≤ R.card
  exact (Nat.mul_le_mul_left 4 huQ).trans hQ

lemma sourceAdaptiveFiber_nonempty
    (hb : 0 < b) (R₀ E R : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (hsub : R ⊆ R₀) (hwide : R₀.card ≤ 2 * R.card) (u : ZMod b) :
    (sourceAdaptiveFiber R₀ E R u).Nonempty := by
  simpa [sourceAdaptiveFiber, sourceAdaptivePhaseSet] using
    normalizedCosetFiber_nonempty_of_diverse_used
      hb R₀ R E hE (hdiverse R hsub hwide) u

lemma sourceAdaptiveMinFiber_nonempty
    (hb : 0 < b) (R₀ E R : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (hsub : R ⊆ R₀) (hwide : R₀.card ≤ 2 * R.card) :
    (sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)).Nonempty :=
  sourceAdaptiveFiber_nonempty hb R₀ E R hE hdiverse hsub hwide _

lemma sourceAdaptiveMinFiber_gt_of_not_growth
    (hb : 0 < b) (R₀ E R : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (hsub : R ⊆ R₀) (hwide : R₀.card ≤ 2 * R.card) (Q : ℕ)
    (hg : ¬ IsSourceAdaptiveGrowthPhase R₀ E R Q) :
    Q < (sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)).card := by
  have hne := sourceAdaptiveMinFiber_nonempty
    hb R₀ E R hE hdiverse hsub hwide
  by_contra hnot
  apply hg
  exact ⟨sourceAdaptiveMinFiberCenter R₀ E R, hne, by omega⟩

lemma sourceAdaptiveMinFiber_lt_of_exists
    (R₀ E R : Finset (ZMod b)) {s : ℕ}
    (h : ∃ u : ZMod b,
      (sourceAdaptiveFiber R₀ E R u).card < s) :
    (sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)).card < s := by
  obtain ⟨u, hu⟩ := h
  exact (sourceAdaptiveMinFiberCenter_minimal R₀ E R u).trans_lt hu

/-- The maximum-translation element of the canonical normalized fibre,
viewed back in the original cyclic group. -/
noncomputable def normalizedFiberMaxPick
    (R₀ E R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · let H := AddSubgroup.closure (R : Set (ZMod b))
    let U := sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)
    let X := liftFinsetToClosure R
    have hX : X.Nonempty := by
      apply Finset.card_pos.mp
      rw [show X.card = R.card by exact card_liftFinsetToClosure R]
      exact Finset.card_pos.mpr hR
    exact (subgroupFiberMaxPick U X hX).1
  · exact 0

lemma normalizedFiberMaxPick_mem
    (R₀ E R : Finset (ZMod b)) (hR : R.Nonempty) :
    normalizedFiberMaxPick R₀ E R ∈ R := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := sourceAdaptiveFiber R₀ E R
    (sourceAdaptiveMinFiberCenter R₀ E R)
  let X := liftFinsetToClosure R
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hR
  have hpick : subgroupFiberMaxPick U X hX ∈ X :=
    subgroupFiberMaxPick_mem U X hX
  unfold normalizedFiberMaxPick
  rw [dif_pos hR]
  exact mem_liftFinsetToClosure.mp hpick

/-- The chosen element really is maximal for translation of the canonical
normalized fibre by the lifted remainder. -/
lemma normalizedFiberMaxPick_maximal
    (R₀ E R : Finset (ZMod b)) (hR : R.Nonempty) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let U := sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)
    let X := liftFinsetToClosure R
    TranslationNewMaximal U X
      (⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩ : H) := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := sourceAdaptiveFiber R₀ E R
    (sourceAdaptiveMinFiberCenter R₀ E R)
  let X := liftFinsetToClosure R
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hR
  have heq :
      (⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩ : H) =
        subgroupFiberMaxPick U X hX := by
    apply Subtype.ext
    change normalizedFiberMaxPick R₀ E R =
      (subgroupFiberMaxPick U X hX).1
    simp only [normalizedFiberMaxPick, dif_pos hR]
    congr 1
  rw [heq]
  exact subgroupFiberMaxPick_maximal U X hX

/-- The same maximality after passage to standard cyclic coordinates. -/
lemma normalizedFiberMaxPick_coordinates_maximal
    (R₀ E R : Finset (ZMod b)) (hR : R.Nonempty) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let U := sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)
    let X := liftFinsetToClosure R
    let pick : H :=
      ⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩
    TranslationNewMaximal (subgroupCoordinates U) (subgroupCoordinates X)
      ((subgroupZModEquiv H).symm pick) := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := sourceAdaptiveFiber R₀ E R
    (sourceAdaptiveMinFiberCenter R₀ E R)
  let X := liftFinsetToClosure R
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hR
  have heq :
      (⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩ : H) =
        subgroupFiberMaxPick U X hX := by
    apply Subtype.ext
    change normalizedFiberMaxPick R₀ E R =
      (subgroupFiberMaxPick U X hX).1
    simp only [normalizedFiberMaxPick, dif_pos hR]
    congr 1
  rw [heq]
  exact subgroupCoordinates_maxPick_maximal U X hX

/-- Fibre growth is bounded by the global increment produced by the same
selected shift. -/
lemma normalizedFiberMaxPick_translation_le_global
    (R₀ E R : Finset (ZMod b)) (hR : R.Nonempty) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let U := sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)
    let pick : H :=
      ⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩
    (translationNew U pick).card ≤
      (translationNew (sourceAdaptivePhaseSet R₀ E R) pick.1).card := by
  dsimp only
  exact card_translationNew_normalizedCosetFiber_le
    (AddSubgroup.closure (R : Set (ZMod b)))
    (sourceAdaptivePhaseSet R₀ E R)
    (sourceAdaptiveMinFiberCenter R₀ E R) _

/-- Any lower bound proved for the normalized-fibre translation is an
actual increment of the ambient phase set. -/
lemma normalizedFiberMaxPick_global_increment_of_fiber
    (R₀ E R : Finset (ZMod b)) (hR : R.Nonempty) {D : ℕ}
    (hD : let H := AddSubgroup.closure (R : Set (ZMod b))
      let U := sourceAdaptiveFiber R₀ E R
        (sourceAdaptiveMinFiberCenter R₀ E R)
      let pick : H :=
        ⟨normalizedFiberMaxPick R₀ E R,
          AddSubgroup.subset_closure
            (normalizedFiberMaxPick_mem R₀ E R hR)⟩
      D ≤ (translationNew U pick).card) :
    D + (sourceAdaptivePhaseSet R₀ E R).card ≤
      ((sourceAdaptivePhaseSet R₀ E R) ∪
        Erdos587.addTranslate (normalizedFiberMaxPick R₀ E R)
          (sourceAdaptivePhaseSet R₀ E R)).card := by
  have hglobal : D ≤ (translationNew
      (sourceAdaptivePhaseSet R₀ E R)
      (normalizedFiberMaxPick R₀ E R)).card :=
    hD.trans (normalizedFiberMaxPick_translation_le_global R₀ E R hR)
  rw [card_union_addTranslate_eq]
  omega

/-- In a growth phase, choose a remaining element which maximizes the
translation boundary of the internal subset-sum set in the subgroup
generated by the current remainder.  This is the choice made in CFP's
proof of Claim 1 in Lemma 5.6. -/
noncomputable def sourceAdaptiveInternalMaxPick
    (R₀ R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    let X : Finset H := liftFinsetToClosure R
    have hX : X.Nonempty := liftFinsetToClosure_nonempty_of_nonempty hR
    exact (Classical.choose
      (Finset.exists_max_image X (fun x ↦ (translationNew T x).card) hX)).1
  · exact 0

lemma sourceAdaptiveInternalMaxPick_mem
    (R₀ R : Finset (ZMod b)) (hR : R.Nonempty) :
    sourceAdaptiveInternalMaxPick R₀ R ∈ R := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X : Finset H := liftFinsetToClosure R
  have hX : X.Nonempty := liftFinsetToClosure_nonempty_of_nonempty hR
  have hmem := (Classical.choose_spec
    (Finset.exists_max_image X (fun x ↦ (translationNew T x).card) hX)).1
  rw [sourceAdaptiveInternalMaxPick]
  simp only [dif_pos hR]
  exact mem_liftFinsetToClosure.mp hmem

lemma sourceAdaptiveInternalMaxPick_maximal
    (R₀ R : Finset (ZMod b)) (hR : R.Nonempty) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    ∀ x : H, x.1 ∈ R →
      (translationNew T x).card ≤
        (translationNew T
          (⟨sourceAdaptiveInternalMaxPick R₀ R,
            AddSubgroup.subset_closure
              (sourceAdaptiveInternalMaxPick_mem R₀ R hR)⟩ : H)).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X : Finset H := liftFinsetToClosure R
  have hX : X.Nonempty := liftFinsetToClosure_nonempty_of_nonempty hR
  intro x hx
  have hxX : x ∈ X := mem_liftFinsetToClosure.mpr hx
  have hmax := (Classical.choose_spec
    (Finset.exists_max_image X (fun z ↦ (translationNew T z).card) hX)).2 x hxX
  have hpick :
      (⟨sourceAdaptiveInternalMaxPick R₀ R,
        AddSubgroup.subset_closure
          (sourceAdaptiveInternalMaxPick_mem R₀ R hR)⟩ : H) =
        Classical.choose
          (Finset.exists_max_image X (fun z ↦ (translationNew T z).card) hX) := by
    apply Subtype.ext
    simp [sourceAdaptiveInternalMaxPick, hR, H, T, X]
  simpa [hpick] using hmax

/-- The Q-dependent next-element choice.  Every growth phase uses the
internal maximum above; every nongrowth phase uses the maximum translation
of the canonical normalized fibre. -/
noncomputable def sourceAdaptivePhasePick
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    (R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hgrowth : IsSourceAdaptiveGrowthPhase R₀ E R Q
  · exact sourceAdaptiveInternalMaxPick R₀ R
  · exact normalizedFiberMaxPick R₀ E R

lemma sourceAdaptivePhasePick_eq_normalized_of_not_growth
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    (R : Finset (ZMod b))
    (hgrowth : ¬ IsSourceAdaptiveGrowthPhase R₀ E R Q) :
    sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R =
      normalizedFiberMaxPick R₀ E R := by
  unfold sourceAdaptivePhasePick
  rw [dif_neg hgrowth]

lemma sourceAdaptivePhasePick_mem
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    (R : Finset (ZMod b)) (hR : R.Nonempty) :
    sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R ∈ R := by
  classical
  unfold sourceAdaptivePhasePick
  by_cases hgrowth : IsSourceAdaptiveGrowthPhase R₀ E R Q
  · rw [dif_pos hgrowth]
    exact sourceAdaptiveInternalMaxPick_mem R₀ R hR
  · rw [dif_neg hgrowth]
    exact normalizedFiberMaxPick_mem R₀ E R hR

lemma sourceAdaptivePhasePick_internal_maximal
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    (R : Finset (ZMod b))
    (hR : R.Nonempty)
    (hgrowth : IsSourceAdaptiveGrowthPhase R₀ E R Q) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    ∀ x : H, x.1 ∈ R →
      (translationNew T x).card ≤
        (translationNew T
          (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
            AddSubgroup.subset_closure
              (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hR)⟩ : H)).card := by
  classical
  dsimp only
  have hmax := sourceAdaptiveInternalMaxPick_maximal R₀ R hR
  have hpick : sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R =
      sourceAdaptiveInternalMaxPick R₀ R := by
    simp [sourceAdaptivePhasePick, hgrowth]
  simpa [hpick] using hmax

/-- Compatibility form: whenever the old quarter-fibre growth criterion is
available, the internal maximum realizes the same `3/2` growth witness. -/
lemma sourceAdaptivePhasePick_internal_growth
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    (R : Finset (ZMod b))
    (hready : SourceAdaptiveGrowthReady R₀ E R Q) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    3 * T.card ≤ 2 *
      (T ∪ Erdos587.addTranslate
        (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
          AddSubgroup.subset_closure
            (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hready.1)⟩ : H)
        T).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  obtain ⟨x, hxR, hxgrowth⟩ :=
    exists_internal_growth_of_modularGrowthPhase hb R₀ R E
      hready.1 hE (hdiverse R hready.2.1 hready.2.2.1)
      (isModularGrowthPhase_of_sourceAdaptive hb R₀ E R Q
        hready.2.2.2.1 hready.2.2.2.2)
  have hmax := sourceAdaptivePhasePick_internal_maximal
    hb R₀ E hE hdiverse Q R hready.1 hready.2.2.2.2 x hxR
  rw [card_union_addTranslate_eq] at hxgrowth ⊢
  omega

end LocalSelector

section Recursion

variable {b : ℕ} [NeZero b]

/-- The unused residues in the source-faithful Q-dependent recursion. -/
noncomputable def sourceAdaptiveRemainder
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) :
    ℕ → Finset (ZMod b)
  | 0 => R₀
  | i + 1 =>
      let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
      if R.Nonempty then
        R.erase (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R)
      else R

/-- The subset-sum set exposed after `i` source-adaptive steps. -/
noncomputable def sourceAdaptivePhaseSums
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) :
    Finset (ZMod b) :=
  sourceAdaptivePhaseSet R₀ E
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i)

@[simp] lemma sourceAdaptiveRemainder_zero
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) :
    sourceAdaptiveRemainder hb R₀ E hE hdiverse Q 0 = R₀ := rfl

lemma sourceAdaptiveRemainder_succ_of_nonempty
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ)
    (hne : (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).Nonempty) :
    sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (i + 1) =
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).erase
        (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q
          (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i)) := by
  change (if (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).Nonempty then
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).erase
        (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q
          (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i))
    else sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) = _
  rw [if_pos hne]

lemma sourceAdaptiveRemainder_succ_subset
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) :
    sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (i + 1) ⊆
      sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i := by
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  change (if R.Nonempty then
      R.erase (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R) else R) ⊆ R
  split_ifs
  · exact Finset.erase_subset _ _
  · exact fun _ hx => hx

lemma sourceAdaptiveRemainder_subset_initial
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) :
    ∀ i : ℕ, sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i ⊆ R₀ := by
  intro i
  induction i with
  | zero => exact fun _ hx => hx
  | succ i ih =>
      exact (sourceAdaptiveRemainder_succ_subset
        hb R₀ E hE hdiverse Q i).trans ih

lemma sourceAdaptiveRemainder_antitone
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    sourceAdaptiveRemainder hb R₀ E hE hdiverse Q j ⊆
      sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      exact (sourceAdaptiveRemainder_succ_subset
        hb R₀ E hE hdiverse Q (i + k)).trans (ih (by omega))

lemma card_sourceAdaptiveRemainder
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card =
      R₀.card - i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ R₀.card := by omega
      have hcard := ih hi'
      have hne :
          (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcard]
        omega
      rw [sourceAdaptiveRemainder_succ_of_nonempty
        hb R₀ E hE hdiverse Q i hne]
      rw [Finset.card_erase_of_mem
        (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q _ hne)]
      omega

lemma card_used_sourceAdaptiveRemainder
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (R₀ \ sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card = i := by
  rw [Finset.card_sdiff_of_subset
    (sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i)]
  rw [card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q hi]
  omega

lemma sourceAdaptiveRemainder_at_card
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) :
    sourceAdaptiveRemainder hb R₀ E hE hdiverse Q R₀.card = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (le_refl _)]
  omega

lemma sourceAdaptivePhaseSums_at_card
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) :
    sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q R₀.card =
      E + R₀.subsetSum := by
  rw [sourceAdaptivePhaseSums, sourceAdaptivePhaseSet,
    sourceAdaptiveRemainder_at_card hb R₀ E hE hdiverse Q]
  simp

lemma sourceAdaptivePhaseSums_succ
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card) :
    sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1) =
      sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i ∪
        Erdos587.addTranslate
          (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q
            (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i))
          (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i) := by
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  have hcard : R.card = R₀.card - i :=
    card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hRsub : R ⊆ R₀ :=
    sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i
  have hxR := sourceAdaptivePhasePick_mem
    hb R₀ E hE hdiverse Q R hRne
  have hxNot :
      sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R ∉ R₀ \ R := by
    simp only [Finset.mem_sdiff]
    exact fun h => h.2 hxR
  rw [sourceAdaptivePhaseSums, sourceAdaptivePhaseSums,
    sourceAdaptivePhaseSet, sourceAdaptivePhaseSet]
  rw [sourceAdaptiveRemainder_succ_of_nonempty
    hb R₀ E hE hdiverse Q i hRne]
  rw [sdiff_erase_eq_insert_sdiff hxR hRsub]
  exact seededSubsetSum_insert_eq E (R₀ \ R)
    (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R) hxNot

lemma card_sourceAdaptivePhaseSums_succ
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card) :
    (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1)).card =
      (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i).card +
        (translationNew
          (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i)
          (sourceAdaptivePhasePick hb R₀ E hE hdiverse Q
            (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i))).card := by
  rw [sourceAdaptivePhaseSums_succ hb R₀ E hE hdiverse Q hi]
  exact card_union_addTranslate_eq _ _

lemma sourceAdaptivePhaseSums_mono
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card) :
    sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i ⊆
      sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1) := by
  rw [sourceAdaptivePhaseSums_succ hb R₀ E hE hdiverse Q hi]
  exact Finset.subset_union_left

/-! ## Indexed source phases

These abbreviations are the Q-dependent counterparts of the phase notions
in `CFPModularPhases`.  In particular, an unsaturated phase records only
the existence of a fibre below `sat`; the minimum-fibre construction then
turns that existential statement into facts about the fibre actually used
by the recursion. -/

/-- The current subgroup index in the source-adaptive recursion. -/
noncomputable abbrev sourceAdaptiveModulus
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : ℕ :=
  closureModulus hb
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i)

/-- Internal subset sums made from already-used elements that lie in the
subgroup generated by the current remainder. -/
noncomputable abbrev sourceAdaptiveInternalCard
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : ℕ :=
  modularInternalCard R₀
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i)

/-- Source growth at step `i` of the Q-dependent recursion. -/
noncomputable def IsSourceAdaptiveGrowthStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  IsSourceAdaptiveGrowthPhase R₀ E
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) Q

lemma sourceAdaptiveModulus_dvd_of_le
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ∣
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q j := by
  exact closureModulus_dvd_of_subset hb
    (sourceAdaptiveRemainder_antitone hb R₀ E hE hdiverse Q hij)

lemma sourceAdaptiveModulus_le_ambient
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) :
    sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ b := by
  exact Nat.le_of_dvd hb (closureModulus_dvd hb _)

lemma sourceAdaptiveInternalCard_mono_of_modulus_eq
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i j : ℕ} (hij : i ≤ j)
    (hmod : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q j) :
    sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
      sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j := by
  apply modularInternalCard_mono_of_subset_of_closure_eq R₀
    (sourceAdaptiveRemainder_antitone hb R₀ E hE hdiverse Q hij)
  exact (closure_eq_of_closureModulus_eq hb hmod).symm

/-- The internal `3/2` step for the new recursion.  This is the direct
replacement for `modularInternalCard_growth_step` used by
`AdaptiveSelector`. -/
lemma sourceAdaptiveInternalCard_growth_step
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card)
    (hwide : R₀.card ≤ 2 *
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hQ : 4 * Q ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hg : IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i)
    (hmod : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1)) :
    3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
      2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
  classical
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  let T := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (i + 1)
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := R₀ \ R
  let x := sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R
  have hRcard : R.card = R₀.card - i :=
    card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hRsub : R ⊆ R₀ :=
    sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i
  have hgLocal : IsSourceAdaptiveGrowthPhase R₀ E R Q := by
    simpa [IsSourceAdaptiveGrowthStep, R] using hg
  have hready : SourceAdaptiveGrowthReady R₀ E R Q :=
    ⟨hRne, hRsub, hwide, hQ, hgLocal⟩
  have hxR : x ∈ R :=
    sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne
  have hxU : x ∉ U := by
    simp only [U, Finset.mem_sdiff]
    exact fun h => h.2 hxR
  have hT : T = R.erase x := by
    exact sourceAdaptiveRemainder_succ_of_nonempty
      hb R₀ E hE hdiverse Q i hRne
  have hused : R₀ \ T = insert x U := by
    rw [hT]
    exact sdiff_erase_eq_insert_sdiff hxR
      (sourceAdaptiveRemainder_subset_initial
        hb R₀ E hE hdiverse Q i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hgrowth := sourceAdaptivePhasePick_internal_growth
    hb R₀ E hE hdiverse Q R hready
  have hclosure : AddSubgroup.closure (T : Set (ZMod b)) = H := by
    exact (closure_eq_of_closureModulus_eq hb hmod).symm
  have hnext : elementsInSubgroup H (R₀ \ T) =
      insert xH (elementsInSubgroup H U) := by
    rw [hused]
    exact elementsInSubgroup_insert H U xH hxU
  have hsumNext : (elementsInSubgroup H (R₀ \ T)).subsetSum =
      (elementsInSubgroup H U).subsetSum ∪
        Erdos587.addTranslate xH (elementsInSubgroup H U).subsetSum := by
    rw [hnext]
    exact subsetSum_insert_eq _ _ (by
      rw [mem_elementsInSubgroup]
      exact hxU)
  dsimp only [sourceAdaptiveInternalCard, modularInternalCard]
  rw [show AddSubgroup.closure (T : Set (ZMod b)) = H by exact hclosure]
  rw [hsumNext]
  exact hgrowth

/-- Exact one-step formula for the internal subset-sum cardinality when the
closure modulus does not change.  It isolates the only selector-dependent
quantity as a translation boundary. -/
lemma sourceAdaptiveInternalCard_succ_eq_add_translationNew
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card)
    (hmod : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1)) :
    let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    let x : H :=
      ⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
        AddSubgroup.subset_closure
          (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R
            (Finset.card_pos.mp (by
              rw [card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q
                (by omega)]
              omega)))⟩
    sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) =
      sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i +
        (translationNew T x).card := by
  classical
  dsimp only
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  let R' := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (i + 1)
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := R₀ \ R
  let x := sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R
  have hRcard : R.card = R₀.card - i :=
    card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hxR : x ∈ R :=
    sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne
  have hxU : x ∉ U := by
    simp only [U, Finset.mem_sdiff]
    exact fun h ↦ h.2 hxR
  have hR' : R' = R.erase x :=
    sourceAdaptiveRemainder_succ_of_nonempty
      hb R₀ E hE hdiverse Q i hRne
  have hused : R₀ \ R' = insert x U := by
    rw [hR']
    exact sdiff_erase_eq_insert_sdiff hxR
      (sourceAdaptiveRemainder_subset_initial
        hb R₀ E hE hdiverse Q i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hclosure : AddSubgroup.closure (R' : Set (ZMod b)) = H :=
    (closure_eq_of_closureModulus_eq hb hmod).symm
  have hnext : elementsInSubgroup H (R₀ \ R') =
      insert xH (elementsInSubgroup H U) := by
    rw [hused]
    exact elementsInSubgroup_insert H U xH hxU
  have hsumNext : (elementsInSubgroup H (R₀ \ R')).subsetSum =
      (elementsInSubgroup H U).subsetSum ∪
        Erdos587.addTranslate xH (elementsInSubgroup H U).subsetSum := by
    rw [hnext]
    exact subsetSum_insert_eq _ _ (by
      rw [mem_elementsInSubgroup]
      exact hxU)
  dsimp only [sourceAdaptiveInternalCard, modularInternalCard]
  rw [show AddSubgroup.closure (R' : Set (ZMod b)) = H from hclosure]
  rw [hsumNext, card_union_addTranslate_eq]

/-- The small-growth estimate from CFP Claim 1.  It needs no comparison
between the external threshold `Q` and the remainder cardinality. -/
lemma sourceAdaptiveInternalCard_small_growth_step
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i : ℕ} (hi : i < R₀.card)
    (hg : IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i)
    (hsmall : 2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i <
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hmod : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1)) :
    3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
      2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
  classical
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X : Finset H := liftFinsetToClosure R
  have hRcard : R.card = R₀.card - i :=
    card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hTne : T.Nonempty := by
    refine ⟨0, ?_⟩
    simp [T]
  have hXne : X.Nonempty := liftFinsetToClosure_nonempty_of_nonempty hRne
  have hXcard : X.card = R.card := card_liftFinsetToClosure R
  have hsmall' : 2 * T.card < X.card := by
    simpa [T, R, sourceAdaptiveInternalCard, modularInternalCard, H, hXcard]
      using hsmall
  obtain ⟨x, hxX, hxgrowth⟩ :=
    exists_three_halves_growth hTne hXne hsmall'
  have hgLocal : IsSourceAdaptiveGrowthPhase R₀ E R Q := by
    simpa [IsSourceAdaptiveGrowthStep, R] using hg
  have hmax := sourceAdaptivePhasePick_internal_maximal
    hb R₀ E hE hdiverse Q R hRne hgLocal x
      (mem_liftFinsetToClosure.mp hxX)
  have hmax' : (translationNew T x).card ≤
      (translationNew T
        (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
          AddSubgroup.subset_closure
            (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne)⟩ : H)).card := by
    simpa [T, H, R] using hmax
  have heq := sourceAdaptiveInternalCard_succ_eq_add_translationNew
    hb R₀ E hE hdiverse Q hi hmod
  rw [card_union_addTranslate_eq] at hxgrowth
  dsimp only at heq
  rw [heq]
  dsimp only [sourceAdaptiveInternalCard, modularInternalCard]
  change 3 * T.card ≤ 2 * (T.card +
    (translationNew T
      (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
        AddSubgroup.subset_closure
          (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne)⟩ : H)).card)
  omega

/-- The large-growth estimate from CFP Claim 1.  Once the internal set has
at least half as many points as the remainder, generation plus an ambient
quarter-density bound forces a translation boundary of size `|R|/16`. -/
lemma sourceAdaptiveInternalCard_large_growth_step
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q L : ℕ)
    {i : ℕ} (hi : i < R₀.card)
    (hwide : R₀.card ≤ 2 *
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hg : IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i)
    (hlarge : (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card ≤
      2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i)
    (hambient :
      4 * Q < Nat.card (AddSubgroup.closure
        ((sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i :
          Finset (ZMod b)) : Set (ZMod b))))
    (hLroom : 16 * L ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hmod : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1)) :
    L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
      sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
  classical
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X : Finset H := liftFinsetToClosure R
  have hRcard : R.card = R₀.card - i :=
    card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hTne : T.Nonempty := by
    refine ⟨0, ?_⟩
    simp [T]
  have hXne : X.Nonempty := liftFinsetToClosure_nonempty_of_nonempty hRne
  have hXcard : X.card = R.card := card_liftFinsetToClosure R
  have hTQ : T.card ≤ Q := by
    let u := Classical.choose hg
    have hu := Classical.choose_spec hg
    have hRsub : R ⊆ R₀ :=
      sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i
    have huNe := hu.1
    have hle := seededSubsetSum_fiber_lower H E (R₀ \ R) u huNe
    exact hle.trans hu.2
  have hXU : X.card < 4 * T.card := by
    rw [hXcard]
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    have : R.card ≤ 2 * T.card := by
      simpa [R, T, H, sourceAdaptiveInternalCard, modularInternalCard]
        using hlarge
    omega
  have hUG : 4 * T.card < Fintype.card H := by
    have hcard : Fintype.card H = Nat.card H := by
      rw [Nat.card_eq_fintype_card]
    rw [hcard]
    exact (Nat.mul_le_mul_left 4 hTQ).trans_lt (by simpa [H, R] using hambient)
  obtain ⟨x, hxX, hxlarge⟩ :=
    exists_translationNew_large_of_closure_eq_top hTne hXne hXU hUG
      (by simpa [X] using closure_liftFinsetToClosure_eq_top R)
  have hgLocal : IsSourceAdaptiveGrowthPhase R₀ E R Q := by
    simpa [IsSourceAdaptiveGrowthStep, R] using hg
  have hmax := sourceAdaptivePhasePick_internal_maximal
    hb R₀ E hE hdiverse Q R hRne hgLocal x
      (mem_liftFinsetToClosure.mp hxX)
  have hmax' : (translationNew T x).card ≤
      (translationNew T
        (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
          AddSubgroup.subset_closure
            (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne)⟩ : H)).card := by
    simpa [T, H, R] using hmax
  have hboundary : L ≤
      (translationNew T
        (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
          AddSubgroup.subset_closure
            (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne)⟩ : H)).card := by
    have hRL : 16 * L ≤ X.card := by simpa [hXcard] using hLroom
    omega
  have heq := sourceAdaptiveInternalCard_succ_eq_add_translationNew
    hb R₀ E hE hdiverse Q hi hmod
  dsimp only at heq
  rw [heq]
  dsimp only [sourceAdaptiveInternalCard, modularInternalCard]
  change L + T.card ≤ T.card +
    (translationNew T
      (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
        AddSubgroup.subset_closure
          (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hRne)⟩ : H)).card
  omega

/-- Source unsaturation at step `i`.  This intentionally has the same
existential fibre formulation as the paper. -/
noncomputable def IsSourceAdaptiveUnsaturatedStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    (i : ℕ) : Prop :=
  ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i ∧
    ∃ u : ZMod b,
      (sourceAdaptiveFiber R₀ E
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) u).Nonempty ∧
      Q < (sourceAdaptiveFiber R₀ E
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) u).card ∧
      (sourceAdaptiveFiber R₀ E
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) u).card <
          sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i)

/-- The residual source case: no small fibre and no fibre below the
saturation target. -/
noncomputable def IsSourceAdaptiveSaturatedStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    (i : ℕ) : Prop :=
  ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i ∧
    ¬ IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse Q sat i

lemma sourceAdaptive_wide_of_half
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) {i : ℕ}
    (hi : 2 * i ≤ R₀.card) :
    R₀.card ≤ 2 *
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card := by
  rw [card_sourceAdaptiveRemainder hb R₀ E hE hdiverse Q (by omega)]
  omega

/-- A saturated source phase already occupies the target number of
ambient residues. -/
lemma sourceAdaptive_saturated_phase_card
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    {i : ℕ} (hi : 2 * i ≤ R₀.card)
    (hsat : IsSourceAdaptiveSaturatedStep
      hb R₀ E hE hdiverse Q sat i) :
    sourceAdaptiveModulus hb R₀ E hE hdiverse Q i *
        sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) ≤
      (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i).card := by
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  have hwide : R₀.card ≤ 2 * R.card :=
    sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q hi
  have hRsub : R ⊆ R₀ :=
    sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i
  have hnotGrowth : ¬ IsSourceAdaptiveGrowthPhase R₀ E R Q := by
    simpa [IsSourceAdaptiveGrowthStep, R] using hsat.1
  have hlarge : ∀ u : ZMod b,
      sat (closureModulus hb R) ≤
        (sourceAdaptiveFiber R₀ E R u).card := by
    intro u
    have huNe := sourceAdaptiveFiber_nonempty
      hb R₀ E R hE hdiverse hRsub hwide u
    by_contra hnot
    have hlt : (sourceAdaptiveFiber R₀ E R u).card <
        sat (closureModulus hb R) := by omega
    have hQlt : Q < (sourceAdaptiveFiber R₀ E R u).card := by
      by_contra hnotQ
      apply hnotGrowth
      exact ⟨u, huNe, by omega⟩
    apply hsat.2
    refine ⟨hsat.1, u, huNe, hQlt, ?_⟩
    simpa [sourceAdaptiveModulus, R] using hlt
  simpa [sourceAdaptiveModulus, sourceAdaptivePhaseSums,
    sourceAdaptiveFiber, sourceAdaptivePhaseSet, R] using
    (closureModulus_mul_le_card_of_all_fibers hb R
      (sourceAdaptivePhaseSet R₀ E R)
      (sat (closureModulus hb R)) hlarge)

/-- In an indexed unsaturated phase, the canonical fibre selected by the
recursion is nonempty and has exactly the source-required strict bounds. -/
lemma sourceAdaptiveMinFiber_bounds_of_unsaturated
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    {i : ℕ} (hi : 2 * i ≤ R₀.card)
    (hu : IsSourceAdaptiveUnsaturatedStep
      hb R₀ E hE hdiverse Q sat i) :
    let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
    let u := sourceAdaptiveMinFiberCenter R₀ E R
    (sourceAdaptiveFiber R₀ E R u).Nonempty ∧
      Q < (sourceAdaptiveFiber R₀ E R u).card ∧
      (sourceAdaptiveFiber R₀ E R u).card <
        sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) := by
  dsimp only
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  have hwide : R₀.card ≤ 2 * R.card :=
    sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q hi
  have hRsub : R ⊆ R₀ :=
    sourceAdaptiveRemainder_subset_initial hb R₀ E hE hdiverse Q i
  have hne := sourceAdaptiveMinFiber_nonempty
    hb R₀ E R hE hdiverse hRsub hwide
  have hnotGrowth : ¬ IsSourceAdaptiveGrowthPhase R₀ E R Q := by
    simpa [IsSourceAdaptiveGrowthStep, R] using hu.1
  have hgt := sourceAdaptiveMinFiber_gt_of_not_growth
    hb R₀ E R hE hdiverse hRsub hwide Q hnotGrowth
  have hlt := sourceAdaptiveMinFiber_lt_of_exists R₀ E R
    (s := sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i))
    ⟨Classical.choose hu.2, (Classical.choose_spec hu.2).2.2⟩
  exact ⟨hne, hgt, hlt⟩

lemma sourceAdaptivePhasePick_eq_normalized_of_unsaturated
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    {i : ℕ}
    (hu : IsSourceAdaptiveUnsaturatedStep
      hb R₀ E hE hdiverse Q sat i) :
    sourceAdaptivePhasePick hb R₀ E hE hdiverse Q
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) =
      normalizedFiberMaxPick R₀ E
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) := by
  have hnotGrowth : ¬ IsSourceAdaptiveGrowthPhase R₀ E
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i) Q := by
    simpa [IsSourceAdaptiveGrowthStep] using hu.1
  exact sourceAdaptivePhasePick_eq_normalized_of_not_growth
    hb R₀ E hE hdiverse Q _ hnotGrowth

/-- The indexed maximality statement consumed by the normalized inverse
theorem in an unsaturated phase. -/
lemma sourceAdaptivePhasePick_maximal_of_unsaturated
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    {i : ℕ} (hi : i < R₀.card)
    (hu : IsSourceAdaptiveUnsaturatedStep
      hb R₀ E hE hdiverse Q sat i) :
    let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let U := sourceAdaptiveFiber R₀ E R
      (sourceAdaptiveMinFiberCenter R₀ E R)
    let X := liftFinsetToClosure R
    TranslationNewMaximal U X
      (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
        AddSubgroup.subset_closure
          (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R
            (by
              apply Finset.card_pos.mp
              rw [card_sourceAdaptiveRemainder
                hb R₀ E hE hdiverse Q (show i ≤ R₀.card by omega)]
              omega))⟩ : H) := by
  classical
  dsimp only
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    rw [card_sourceAdaptiveRemainder
      hb R₀ E hE hdiverse Q (show i ≤ R₀.card by omega)]
    omega
  have heq := sourceAdaptivePhasePick_eq_normalized_of_unsaturated
    hb R₀ E hE hdiverse Q sat hu
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := sourceAdaptiveFiber R₀ E R
    (sourceAdaptiveMinFiberCenter R₀ E R)
  let X := liftFinsetToClosure R
  have hmax := normalizedFiberMaxPick_maximal R₀ E R hR
  have hpick :
      (⟨sourceAdaptivePhasePick hb R₀ E hE hdiverse Q R,
        AddSubgroup.subset_closure
          (sourceAdaptivePhasePick_mem hb R₀ E hE hdiverse Q R hR)⟩ : H) =
      (⟨normalizedFiberMaxPick R₀ E R,
        AddSubgroup.subset_closure
          (normalizedFiberMaxPick_mem R₀ E R hR)⟩ : H) := by
    exact Subtype.ext heq
  rw [hpick]
  exact hmax

end Recursion

end Erdos360

#print axioms Erdos360.sourceAdaptivePhasePick_internal_growth
#print axioms Erdos360.normalizedFiberMaxPick_maximal
#print axioms Erdos360.card_sourceAdaptiveRemainder
#print axioms Erdos360.sourceAdaptivePhaseSums_succ
