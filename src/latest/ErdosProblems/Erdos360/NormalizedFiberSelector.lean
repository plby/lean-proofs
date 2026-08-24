/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ConstantLossModularBridge

/-!
# Maximal translation selection in the true cyclic ambient group

At a modular phase the remaining residues generally generate a proper
subgroup of the original `ZMod b`.  Applying a cyclic inverse theorem in the
original ambient group would therefore leave an unavoidable (and usually
true) proper-subgroup alternative.  The definitions below instead move the
chosen occupied fibre and all remaining shifts into

`ZMod (Nat.card (AddSubgroup.closure R))`.

The lifted remaining set generates this coordinate group, and the chosen
shift genuinely maximizes the translation error of the normalized fibre.
Both facts are proved here rather than included as phase assumptions.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- A cyclic coordinate system on a subgroup of a finite cyclic group. -/
noncomputable def subgroupZModEquiv
    {b : ℕ} [NeZero b] (H : AddSubgroup (ZMod b)) :
    ZMod (Nat.card H) ≃+ H :=
  zmodAddCyclicAddEquiv inferInstance

/-- Pull a finite subset of a cyclic subgroup back to standard `ZMod`
coordinates. -/
noncomputable def subgroupCoordinates
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (X : Finset H) : Finset (ZMod (Nat.card H)) :=
  X.map (subgroupZModEquiv H).symm.toEmbedding

/-- Coordinates defined by an explicitly chosen cyclic equivalence.  The
source-facing proof uses this form so it can retain literal division
coordinates; `subgroupCoordinates` is the arbitrary-equivalence wrapper. -/
noncomputable def equivCoordinates
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (e : ZMod (Nat.card H) ≃+ H) (X : Finset H) :
    Finset (ZMod (Nat.card H)) :=
  X.map e.symm.toEmbedding

@[simp] lemma mem_equivCoordinates_iff
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    {e : ZMod (Nat.card H) ≃+ H} {X : Finset H}
    {z : ZMod (Nat.card H)} :
    z ∈ equivCoordinates e X ↔ e z ∈ X := by
  simp [equivCoordinates]

@[simp] lemma card_equivCoordinates
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (e : ZMod (Nat.card H) ≃+ H) (X : Finset H) :
    (equivCoordinates e X).card = X.card := by
  simp [equivCoordinates]

lemma equivCoordinates_lift_generates
    {b : ℕ} [NeZero b] (R : Finset (ZMod b))
    (e : ZMod (Nat.card (AddSubgroup.closure
      ((R : Finset (ZMod b)) : Set (ZMod b)))) ≃+
        AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))) :
    AddSubgroup.closure
        ((equivCoordinates e (liftFinsetToClosure R) :
          Finset (ZMod (Nat.card (AddSubgroup.closure
            ((R : Finset (ZMod b)) : Set (ZMod b)))))) :
          Set (ZMod (Nat.card (AddSubgroup.closure
            ((R : Finset (ZMod b)) : Set (ZMod b)))))) = ⊤ := by
  classical
  let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
  let X : Finset H := liftFinsetToClosure R
  let K : AddSubgroup (ZMod (Nat.card H)) :=
    AddSubgroup.closure ((equivCoordinates e X : Finset (ZMod (Nat.card H))) :
      Set (ZMod (Nat.card H)))
  have hXgen : AddSubgroup.closure ((X : Finset H) : Set H) = ⊤ :=
    closure_liftFinsetToClosure_eq_top R
  have hle : AddSubgroup.closure ((X : Finset H) : Set H) ≤
      K.comap e.symm.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).2
    intro x hx
    change e.symm x ∈ K
    exact AddSubgroup.subset_closure
      (mem_equivCoordinates_iff.mpr (by simpa [X] using hx))
  change K = ⊤
  apply top_unique
  intro z _
  have hzX : e z ∈ AddSubgroup.closure ((X : Finset H) : Set H) := by
    rw [hXgen]
    simp
  have hz := hle hzX
  change e.symm (e z) ∈ K at hz
  simpa using hz

lemma translationNew_equivCoordinates_card
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (e : ZMod (Nat.card H) ≃+ H) (U : Finset H) (x : H) :
    (translationNew (equivCoordinates e U) (e.symm x)).card =
      (translationNew U x).card := by
  classical
  have hmap :
      (translationNew (equivCoordinates e U) (e.symm x)).map e.toEmbedding =
        translationNew U x := by
    ext y
    simp [translationNew, equivCoordinates]
  calc
    (translationNew (equivCoordinates e U) (e.symm x)).card =
        ((translationNew (equivCoordinates e U) (e.symm x)).map
          e.toEmbedding).card := by simp
    _ = (translationNew U x).card := by rw [hmap]

@[simp] lemma mem_subgroupCoordinates_iff
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    {X : Finset H} {z : ZMod (Nat.card H)} :
    z ∈ subgroupCoordinates X ↔ subgroupZModEquiv H z ∈ X := by
  simp [subgroupCoordinates]

@[simp] lemma card_subgroupCoordinates
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (X : Finset H) :
    (subgroupCoordinates X).card = X.card := by
  simp [subgroupCoordinates]

lemma subgroupCoordinates_lift_generates
    {b : ℕ} [NeZero b] (R : Finset (ZMod b)) :
    AddSubgroup.closure
        ((subgroupCoordinates (liftFinsetToClosure R) :
          Finset (ZMod (Nat.card (AddSubgroup.closure
            ((R : Finset (ZMod b)) : Set (ZMod b)))))) :
          Set (ZMod (Nat.card (AddSubgroup.closure
            ((R : Finset (ZMod b)) : Set (ZMod b)))))) = ⊤ := by
  classical
  let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
  let e : ZMod (Nat.card H) ≃+ H := subgroupZModEquiv H
  let X : Finset H := liftFinsetToClosure R
  let K : AddSubgroup (ZMod (Nat.card H)) :=
    AddSubgroup.closure ((subgroupCoordinates X : Finset (ZMod (Nat.card H))) :
      Set (ZMod (Nat.card H)))
  have hXgen : AddSubgroup.closure ((X : Finset H) : Set H) = ⊤ :=
    closure_liftFinsetToClosure_eq_top R
  have hle : AddSubgroup.closure ((X : Finset H) : Set H) ≤
      K.comap e.symm.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).2
    intro x hx
    change e.symm x ∈ K
    exact AddSubgroup.subset_closure
      (mem_subgroupCoordinates_iff.mpr (by simpa [e, X] using hx))
  change K = ⊤
  apply top_unique
  intro z _
  have hzX : e z ∈ AddSubgroup.closure ((X : Finset H) : Set H) := by
    rw [hXgen]
    simp
  have hz := hle hzX
  change e.symm (e z) ∈ K at hz
  simpa using hz

/-- A point of `X` which maximizes the translation error of `U`. -/
noncomputable def subgroupFiberMaxPick
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (U X : Finset H) (hX : X.Nonempty) : H :=
  Classical.choose
    (Finset.exists_max_image X (fun x ↦ (translationNew U x).card) hX)

lemma subgroupFiberMaxPick_mem
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (U X : Finset H) (hX : X.Nonempty) :
    subgroupFiberMaxPick U X hX ∈ X :=
  (Classical.choose_spec
    (Finset.exists_max_image X (fun x ↦ (translationNew U x).card) hX)).1

lemma subgroupFiberMaxPick_maximal
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (U X : Finset H) (hX : X.Nonempty) :
    TranslationNewMaximal U X (subgroupFiberMaxPick U X hX) := by
  intro x hx
  exact (Classical.choose_spec
    (Finset.exists_max_image X (fun x ↦ (translationNew U x).card) hX)).2 x hx

lemma translationNew_subgroupCoordinates_card
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (U : Finset H) (x : H) :
    (translationNew (subgroupCoordinates U)
        ((subgroupZModEquiv H).symm x)).card =
      (translationNew U x).card := by
  classical
  let e : ZMod (Nat.card H) ≃+ H := subgroupZModEquiv H
  have hmap :
      (translationNew (subgroupCoordinates U) (e.symm x)).map e.toEmbedding =
        translationNew U x := by
    ext y
    simp [translationNew, subgroupCoordinates, e]
  calc
    (translationNew (subgroupCoordinates U) (e.symm x)).card =
        ((translationNew (subgroupCoordinates U) (e.symm x)).map
          e.toEmbedding).card := by simp
    _ = (translationNew U x).card := by rw [hmap]

lemma liftFinsetToClosure_nonempty_of_nonempty
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {R : Finset G} (hR : R.Nonempty) :
    (liftFinsetToClosure R).Nonempty := by
  obtain ⟨r, hr⟩ := hR
  exact ⟨⟨r, AddSubgroup.subset_closure hr⟩,
    mem_liftFinsetToClosure.mpr hr⟩

lemma subgroupCoordinates_maxPick_maximal
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (U X : Finset H) (hX : X.Nonempty) :
    TranslationNewMaximal (subgroupCoordinates U) (subgroupCoordinates X)
      ((subgroupZModEquiv H).symm (subgroupFiberMaxPick U X hX)) := by
  intro z hz
  have hzX : subgroupZModEquiv H z ∈ X :=
    mem_subgroupCoordinates_iff.mp hz
  calc
    (translationNew (subgroupCoordinates U) z).card =
        (translationNew U (subgroupZModEquiv H z)).card := by
      simpa using translationNew_subgroupCoordinates_card U
        (subgroupZModEquiv H z)
    _ ≤ (translationNew U (subgroupFiberMaxPick U X hX)).card :=
      subgroupFiberMaxPick_maximal U X hX _ hzX
    _ = (translationNew (subgroupCoordinates U)
        ((subgroupZModEquiv H).symm
          (subgroupFiberMaxPick U X hX))).card :=
      (translationNew_subgroupCoordinates_card U
        (subgroupFiberMaxPick U X hX)).symm

lemma equivCoordinates_maxPick_maximal
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    (e : ZMod (Nat.card H) ≃+ H)
    (U X : Finset H) (hX : X.Nonempty) :
    TranslationNewMaximal (equivCoordinates e U) (equivCoordinates e X)
      (e.symm (subgroupFiberMaxPick U X hX)) := by
  intro z hz
  have hzX : e z ∈ X := mem_equivCoordinates_iff.mp hz
  calc
    (translationNew (equivCoordinates e U) z).card =
        (translationNew U (e z)).card := by
      simpa using translationNew_equivCoordinates_card e U (e z)
    _ ≤ (translationNew U (subgroupFiberMaxPick U X hX)).card :=
      subgroupFiberMaxPick_maximal U X hX _ hzX
    _ = (translationNew (equivCoordinates e U)
        (e.symm (subgroupFiberMaxPick U X hX))).card :=
      (translationNew_equivCoordinates_card e U
        (subgroupFiberMaxPick U X hX)).symm

/-- The normalized fibre error is bounded by the error of the same shift in
the whole modular subset-sum set.  This is the bridge which turns an inverse
theorem in the true subgroup ambient into an actual phase increment. -/
lemma subgroupFiberMaxPick_translation_le_global
    {b : ℕ} [NeZero b] (R S : Finset (ZMod b)) (u : ZMod b)
    (hR : R.Nonempty) :
    let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
    let U := normalizedCosetFiber H S u
    let X := liftFinsetToClosure R
    (translationNew U (subgroupFiberMaxPick U X
      (liftFinsetToClosure_nonempty_of_nonempty hR))).card ≤
      (translationNew S (subgroupFiberMaxPick U X
        (liftFinsetToClosure_nonempty_of_nonempty hR)).1).card := by
  dsimp only
  exact card_translationNew_normalizedCosetFiber_le _ _ _ _

/-! ## The normalized constant-loss phase certificate -/

/-- All arithmetic and sieve hypotheses for one normalized fibre phase.
Maximality and generation are intentionally absent: the two preceding
selector lemmas provide them. -/
structure NormalizedFiberLossPhaseConditions
    (A C : ℝ) (n y sieveLevel Q κ e : ℕ) (ratio : ℝ)
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    [NeZero (Nat.card H)]
    (coordinateEquiv : ZMod (Nat.card H) ≃+ H)
    /- Left endpoint of the arithmetic interval used for representatives
    of the canonical closure coordinates. -/
    (base : ℕ) (U X : Finset H) : Prop where
  base_le : base ≤ Nat.card H
  U_nonempty : (equivCoordinates coordinateEquiv U).Nonempty
  e_pos : 0 < e
  large : 8 * e < (equivCoordinates coordinateEquiv U).card
  five_levels : 64 * e ≤ (equivCoordinates coordinateEquiv U).card
  kappa_pos : 0 < κ
  kappa_sparse : 4 * κ < 2000000000
  ambient :
    2000000000 * (equivCoordinates coordinateEquiv U).card ≤ Nat.card H
  polynomial_reverse :
    2 ^ 712 * (equivCoordinates coordinateEquiv U).card ^ 100 <
      ((equivCoordinates coordinateEquiv U).card / (2 * e)) ^ 102 *
        (equivCoordinates coordinateEquiv X).card ^ 100
  localDF : ∀ j, 5 ≤ j →
    j < Nat.log 2 ((equivCoordinates coordinateEquiv U).card / (2 * e)) →
    1000000000 *
        (dyadicFinsetSum
          (almostPeriods (equivCoordinates coordinateEquiv U) e) j).card ≤
      Nat.card H →
    25 *
        (dyadicFinsetSum
          (almostPeriods (equivCoordinates coordinateEquiv U) e)
          (j + 1)).card ≤
      51 *
        (dyadicFinsetSum
          (almostPeriods (equivCoordinates coordinateEquiv U) e) j).card →
    CFPLocalDyadicInverseAlternativeWithLoss κ
      (equivCoordinates coordinateEquiv U) e j
  n_pos : 0 < n
  y_ge : 2 ≤ y
  sieveLevel_ge : 101 ≤ sieveLevel
  Q_pos : 0 < Q
  log_bound : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99
  coprime : ∀ x ∈ intervalZmodValues base
      (equivCoordinates coordinateEquiv X),
    Nat.Coprime (missingPrimeProduct n y) x
  long_scale :
    (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤
      (intervalZmodValues base
        (equivCoordinates coordinateEquiv X)).card
  ratio_nonneg : 0 ≤ ratio
  ratio_bound : ∀ step : ℕ, 0 < step → step ≤ Nat.card H →
    ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio
  sieve_reverse :
    (((192 * κ : ℕ) : ℝ) * e) *
      (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
          (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) <
        (equivCoordinates coordinateEquiv X).card

/-- The selected maximum in a normalized fibre cannot be an `e`-almost
period once the constant-loss inverse and sieve hypotheses hold. -/
theorem subgroupCoordinates_maxPick_not_almostPeriods
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    [NeZero (Nat.card H)]
    (U X : Finset H) (hX : X.Nonempty)
    {n y sieveLevel Q κ e : ℕ} {ratio : ℝ}
    {coordinateEquiv : ZMod (Nat.card H) ≃+ H} {base : ℕ}
    (hc : NormalizedFiberLossPhaseConditions A C n y sieveLevel Q κ e
      ratio coordinateEquiv base U X)
    (hgen : AddSubgroup.closure
      ((equivCoordinates coordinateEquiv X :
        Finset (ZMod (Nat.card H))) :
        Set (ZMod (Nat.card H))) = ⊤) :
    coordinateEquiv.symm (subgroupFiberMaxPick U X hX) ∉
      almostPeriods (equivCoordinates coordinateEquiv U) e := by
  exact picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve_from_five
    (b := Nat.card H) (S := equivCoordinates coordinateEquiv U)
    (R := equivCoordinates coordinateEquiv X)
    (pick := coordinateEquiv.symm (subgroupFiberMaxPick U X hX))
    (e := e) (κ := κ)
    A C hsieve hc.U_nonempty hc.e_pos hc.large hc.five_levels
    hc.kappa_pos hc.kappa_sparse
    hc.ambient (equivCoordinates_maxPick_maximal coordinateEquiv U X hX) hgen
    hc.polynomial_reverse hc.localDF n y sieveLevel Q ratio hc.n_pos hc.y_ge
    hc.sieveLevel_ge hc.Q_pos hc.log_bound hc.base_le hc.coprime
    hc.long_scale
    hc.ratio_nonneg hc.ratio_bound hc.sieve_reverse

/-- Fully normalized one-phase increment.  The inverse theorem is run in the
cyclic group generated by `R`, while the conclusion is an increment of the
original ambient set `S`. -/
theorem normalizedFiberMaxPick_global_increment
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {b : ℕ} [NeZero b] (R S : Finset (ZMod b)) (u : ZMod b)
    (hR : R.Nonempty) {D n y sieveLevel Q κ : ℕ} {ratio : ℝ}
    (hD : 0 < D)
    (coordinateEquiv :
      let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
      ZMod (Nat.card H) ≃+ H)
    (base : ℕ)
    (hc : let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
      let U := normalizedCosetFiber H S u
      let X := liftFinsetToClosure R
      @NormalizedFiberLossPhaseConditions A C n y sieveLevel Q κ (D - 1)
        ratio b inferInstance H
        (by exact ⟨Nat.ne_of_gt Nat.card_pos⟩) coordinateEquiv base U X) :
    let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
    let U := normalizedCosetFiber H S u
    let X := liftFinsetToClosure R
    let hX : X.Nonempty := by
      exact liftFinsetToClosure_nonempty_of_nonempty hR
    let pick : H := subgroupFiberMaxPick U X hX
    D + S.card ≤ (S ∪ Erdos587.addTranslate pick.1 S).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
  let U := normalizedCosetFiber H S u
  let X := liftFinsetToClosure R
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hR
  letI : NeZero (Nat.card H) := ⟨Nat.ne_of_gt Nat.card_pos⟩
  let pick : H := subgroupFiberMaxPick U X hX
  have hnot := subgroupCoordinates_maxPick_not_almostPeriods A C hsieve
    U X hX hc (by simpa [H, X] using
      equivCoordinates_lift_generates R coordinateEquiv)
  have hcoord : D ≤
      (translationNew (equivCoordinates coordinateEquiv U)
        (coordinateEquiv.symm pick)).card := by
    dsimp [pick] at hnot ⊢
    rw [mem_almostPeriods_iff_card_translationNew_le] at hnot
    have hDrecover : D - 1 + 1 = D := Nat.sub_add_cancel (by omega)
    rw [← hDrecover]
    exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
  have hfiber : D ≤ (translationNew U pick).card := by
    rw [translationNew_equivCoordinates_card coordinateEquiv U pick] at hcoord
    exact hcoord
  have hglobal : D ≤ (translationNew S pick.1).card :=
    hfiber.trans (card_translationNew_normalizedCosetFiber_le H S u pick)
  rw [card_union_addTranslate_eq]
  change D + S.card ≤ S.card + (translationNew S pick.1).card
  omega

end Erdos360

#print axioms Erdos360.subgroupCoordinates_lift_generates
#print axioms Erdos360.subgroupCoordinates_maxPick_maximal
#print axioms Erdos360.subgroupFiberMaxPick_translation_le_global
#print axioms Erdos360.subgroupCoordinates_maxPick_not_almostPeriods
#print axioms Erdos360.normalizedFiberMaxPick_global_increment
