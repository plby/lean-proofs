/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4.FullPinned

namespace Erdos4

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval
noncomputable section

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A canonical finite coordinate set with twice as many coordinates as
`H`.  Its numerical values play no arithmetic role because the combined
Bombieri--Vinogradov encoding uses pre-sieve modulus one. -/
def doubledIndexSet (H : Finset ℕ) : Finset ℕ :=
  Finset.range (2 * Fintype.card H)

/-- Split the doubled coordinate set into the first-form and companion-form
copies of `H`. -/
noncomputable def doubledIndexEquiv (H : Finset ℕ) :
    ↑(doubledIndexSet H) ≃ Sum H H := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  simp [doubledIndexSet]
  omega

/-- Join a first divisor tuple and a companion divisor tuple into one tuple
on the doubled coordinate set. -/
noncomputable def combineDivisorTuples
    {H : Finset ℕ} (d e : H → ℕ) : ↑(doubledIndexSet H) → ℕ :=
  fun j => Sum.elim d e (doubledIndexEquiv H j)

@[simp] theorem combineDivisorTuples_inl
    {H : Finset ℕ} (d e : H → ℕ) (h : H) :
    combineDivisorTuples d e ((doubledIndexEquiv H).symm (Sum.inl h)) =
      d h := by
  simp [combineDivisorTuples]

@[simp] theorem combineDivisorTuples_inr
    {H : Finset ℕ} (d e : H → ℕ) (h : H) :
    combineDivisorTuples d e ((doubledIndexEquiv H).symm (Sum.inr h)) =
      e h := by
  simp [combineDivisorTuples]

theorem combineDivisorTuples_injective
    {H : Finset ℕ} :
    Function.Injective
      (fun de : (H → ℕ) × (H → ℕ) =>
        combineDivisorTuples de.1 de.2) := by
  rintro ⟨d, e⟩ ⟨d', e'⟩ heq
  apply Prod.ext
  · funext h
    have hh := congrFun heq ((doubledIndexEquiv H).symm (Sum.inl h))
    simpa using hh
  · funext h
    have hh := congrFun heq ((doubledIndexEquiv H).symm (Sum.inr h))
    simpa using hh

theorem divisorTupleProduct_combineDivisorTuples
    {H : Finset ℕ} (d e : H → ℕ) :
    BoundedGaps.Maynard.divisorTupleProduct (doubledIndexSet H)
        (combineDivisorTuples d e) =
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H e := by
  unfold BoundedGaps.Maynard.divisorTupleProduct combineDivisorTuples
  calc
    (∏ j : ↑(doubledIndexSet H),
        Sum.elim d e (doubledIndexEquiv H j)) =
        ∏ s : Sum H H, Sum.elim d e s :=
      Equiv.prod_comp (doubledIndexEquiv H) (Sum.elim d e)
    _ = _ := Fintype.prod_sum_type (Sum.elim d e)

/-- The two separated Maynard tuples combine to an ordinary tuple of radius
`RD*RE` and modulus one. -/
theorem isMaynardDivisorTuple_combine
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {d : H → ℕ} (hd : d ∈ D) {e : H → ℕ} (he : e ∈ E) :
    BoundedGaps.Maynard.IsMaynardDivisorTuple (doubledIndexSet H)
      (RD * RE) 1 (combineDivisorTuples d e) := by
  let dprod := BoundedGaps.Maynard.divisorTupleProduct H d
  let eprod := BoundedGaps.Maynard.divisorTupleProduct H e
  have hdT := support.first_tuple d hd
  have heT := support.companion_tuple e he
  have hdpos : 0 < dprod := Nat.pos_of_ne_zero hdT.2.2.ne_zero
  have hepos : 0 < eprod := Nat.pos_of_ne_zero heT.2.2.ne_zero
  have hdeCop : dprod.Coprime eprod := by
    unfold dprod eprod BoundedGaps.Maynard.divisorTupleProduct
    apply Nat.Coprime.prod_left
    intro a ha
    apply Nat.Coprime.prod_right
    intro b hb
    exact support.cross_family d hd e he a b
  rw [BoundedGaps.Maynard.IsMaynardDivisorTuple,
    divisorTupleProduct_combineDivisorTuples]
  refine ⟨?_, Nat.coprime_one_right _, ?_⟩
  · exact mul_lt_mul hdT.1 heT.1.le hepos (Nat.zero_le _)
  · exact (Nat.squarefree_mul hdeCop).2 ⟨hdT.2.2, heT.2.2⟩

/-- Finite support of all combined first/companion divisor tuples. -/
noncomputable def combinedDivisorSupport
    {H : Finset ℕ} (D E : Finset (H → ℕ)) :
    Finset (↑(doubledIndexSet H) → ℕ) :=
  (D ×ˢ E).image (fun de => combineDivisorTuples de.1 de.2)

theorem mem_combinedDivisorSupport
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    {t : ↑(doubledIndexSet H) → ℕ} :
    t ∈ combinedDivisorSupport D E ↔
      ∃ d ∈ D, ∃ e ∈ E, combineDivisorTuples d e = t := by
  constructor
  · intro ht
    obtain ⟨de, hde, hdet⟩ := Finset.mem_image.mp ht
    exact ⟨de.1, (Finset.mem_product.mp hde).1, de.2,
      (Finset.mem_product.mp hde).2, hdet⟩
  · rintro ⟨d, hd, e, he, rfl⟩
    exact Finset.mem_image.mpr ⟨(d, e), Finset.mem_product.mpr ⟨hd, he⟩, rfl⟩

theorem combinedDivisorSupport_tuples
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {t : ↑(doubledIndexSet H) → ℕ}
    (ht : t ∈ combinedDivisorSupport D E) :
    BoundedGaps.Maynard.IsMaynardDivisorTuple (doubledIndexSet H)
      (RD * RE) 1 t := by
  obtain ⟨d, hd, e, he, rfl⟩ := mem_combinedDivisorSupport.mp ht
  exact isMaynardDivisorTuple_combine support hd he

/-- The doubled coordinate corresponding to a first-family coordinate. -/
noncomputable def combinedPinnedIndex {H : Finset ℕ} (h : H) :
    ↑(doubledIndexSet H) :=
  (doubledIndexEquiv H).symm (Sum.inl h)

theorem isCrossCoordinateCoprime_combine
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E)
    (hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime (doubledIndexSet H)
      (combineDivisorTuples d e) (combineDivisorTuples d' e') := by
  intro a b hab
  have hsne : doubledIndexEquiv H a ≠ doubledIndexEquiv H b := by
    intro hs
    exact hab ((doubledIndexEquiv H).injective hs)
  generalize ha : doubledIndexEquiv H a = sa at hsne ⊢
  generalize hb : doubledIndexEquiv H b = sb at hsne ⊢
  cases sa with
  | inl ai =>
      cases sb with
      | inl bi =>
          have habH : ai ≠ bi := by simpa [ha, hb] using hsne
          simpa [combineDivisorTuples, ha, hb] using hDD habH
      | inr bi =>
          exact ⟨by
              simpa [combineDivisorTuples, ha, hb] using
                support.cross_family d hd e' he' ai bi,
            by
              simpa [combineDivisorTuples, ha, hb] using
                support.cross_family d' hd' e he ai bi⟩
  | inr ai =>
      cases sb with
      | inl bi =>
          exact ⟨by
              simpa [combineDivisorTuples, ha, hb] using
                (support.cross_family d' hd' e he bi ai).symm,
            by
              simpa [combineDivisorTuples, ha, hb] using
                (support.cross_family d hd e' he' bi ai).symm⟩
      | inr bi =>
          have habH : ai ≠ bi := by simpa [ha, hb] using hsne
          simpa [combineDivisorTuples, ha, hb] using hEE habH

theorem divisorTupleLcm_combineDivisorTuples
    {H : Finset ℕ} (d e d' e' : H → ℕ)
    (j : ↑(doubledIndexSet H)) :
    BoundedGaps.Maynard.divisorTupleLcm (doubledIndexSet H)
        (combineDivisorTuples d e) (combineDivisorTuples d' e') j =
      Sum.elim
        (BoundedGaps.Maynard.divisorTupleLcm H d d')
        (BoundedGaps.Maynard.divisorTupleLcm H e e')
        (doubledIndexEquiv H j) := by
  unfold BoundedGaps.Maynard.divisorTupleLcm combineDivisorTuples
  cases h : doubledIndexEquiv H j <;> simp [h]

theorem divisorPairModulus_combine_eq_fullPinnedOffModulus
    {H : Finset ℕ} {h : H} {d e d' e' : H → ℕ}
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1) :
    BoundedGaps.Maynard.divisorPairModulus (doubledIndexSet H) 1
        (combineDivisorTuples d e) (combineDivisorTuples d' e') =
      fullPinnedOffModulus H h d e d' e' := by
  have hprod :
      (∏ j : ↑(doubledIndexSet H),
          BoundedGaps.Maynard.divisorTupleLcm (doubledIndexSet H)
            (combineDivisorTuples d e) (combineDivisorTuples d' e') j) =
        (∏ j : H, BoundedGaps.Maynard.divisorTupleLcm H d d' j) *
          ∏ j : H, BoundedGaps.Maynard.divisorTupleLcm H e e' j := by
    calc
      _ = ∏ s : Sum H H,
          Sum.elim
            (BoundedGaps.Maynard.divisorTupleLcm H d d')
            (BoundedGaps.Maynard.divisorTupleLcm H e e') s := by
        apply Fintype.prod_equiv (doubledIndexEquiv H)
        intro j
        exact divisorTupleLcm_combineDivisorTuples d e d' e' j
      _ = _ := Fintype.prod_sum_type _
  rw [fullPinnedOffModulus,
    pinnedPairOffModulus_eq_divisorPairModulus_one hdh hd'h,
    pinnedPairOffModulus_eq_divisorPairModulus_one heh he'h]
  unfold BoundedGaps.Maynard.divisorPairModulus
  rw [hprod]
  simp

theorem combinedPinnedIndex_values
    {H : Finset ℕ} (h : H) (d e d' e' : H → ℕ)
    (hdh : d h = 1) (hd'h : d' h = 1) :
    combineDivisorTuples d e (combinedPinnedIndex h) = 1 ∧
      combineDivisorTuples d' e' (combinedPinnedIndex h) = 1 := by
  simpa [combinedPinnedIndex] using And.intro hdh hd'h

abbrev FullPinnedIndexType (H : Finset ℕ) :=
  H × (H → ℕ) × (H → ℕ) × (H → ℕ) × (H → ℕ)

/-- Finite index of all compatible pinned quadruples. -/
def fullPinnedIndex
    (H : Finset ℕ) (D E : Finset (H → ℕ)) :
    Finset (FullPinnedIndexType H) := by
  classical
  exact (Finset.univ.product
    (D.product (E.product (D.product E)))).filter fun x =>
      FullPinnedRestricted x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- Encode a full pinned quadruple as an ordinary compatible pair-shift
index on the doubled coordinate set. -/
noncomputable def encodeFullPinnedIndex
    {H : Finset ℕ} (x : FullPinnedIndexType H) :
    (((↑(doubledIndexSet H) → ℕ) ×
        (↑(doubledIndexSet H) → ℕ)) × ↑(doubledIndexSet H)) :=
  ((combineDivisorTuples x.2.1 x.2.2.1,
      combineDivisorTuples x.2.2.2.1 x.2.2.2.2),
    combinedPinnedIndex x.1)

theorem encodeFullPinnedIndex_injective {H : Finset ℕ} :
    Function.Injective (encodeFullPinnedIndex (H := H)) := by
  rintro ⟨h, d, e, d', e'⟩ ⟨k, a, b, a', b'⟩ hEq
  have hde : combineDivisorTuples d e = combineDivisorTuples a b :=
    congrArg (fun x => x.1.1) hEq
  have hde' : combineDivisorTuples d' e' = combineDivisorTuples a' b' :=
    congrArg (fun x => x.1.2) hEq
  have hhk : combinedPinnedIndex h = combinedPinnedIndex k :=
    congrArg (fun x => x.2) hEq
  have hpair : (d, e) = (a, b) := by
    apply combineDivisorTuples_injective
    exact hde
  have hpair' : (d', e') = (a', b') := by
    apply combineDivisorTuples_injective
    exact hde'
  have hhk' : h = k := by
    have hs := congrArg (doubledIndexEquiv H) hhk
    simpa [combinedPinnedIndex] using hs
  subst k
  cases hpair
  cases hpair'
  rfl

theorem encodeFullPinnedIndex_mem_compatible
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {x : FullPinnedIndexType H} (hx : x ∈ fullPinnedIndex H D E) :
    encodeFullPinnedIndex x ∈
      BoundedGaps.Maynard.compatiblePairShiftIndex (doubledIndexSet H)
        (combinedDivisorSupport D E) := by
  have hxData := Finset.mem_filter.mp hx
  have hprod := Finset.mem_product.mp hxData.1
  have htail := Finset.mem_product.mp hprod.2
  have htail2 := Finset.mem_product.mp htail.2
  have htail3 := Finset.mem_product.mp htail2.2
  have hD : x.2.1 ∈ D := htail.1
  have hE : x.2.2.1 ∈ E := htail2.1
  have hD' : x.2.2.2.1 ∈ D := htail3.1
  have hE' : x.2.2.2.2 ∈ E := htail3.2
  have hr := hxData.2
  unfold BoundedGaps.Maynard.compatiblePairShiftIndex
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨mem_combinedDivisorSupport.mpr
            ⟨x.2.1, hD, x.2.2.1, hE, rfl⟩,
          mem_combinedDivisorSupport.mpr
            ⟨x.2.2.2.1, hD', x.2.2.2.2, hE', rfl⟩⟩
      · exact isCrossCoordinateCoprime_combine support hD hD' hE hE'
          hr.1 hr.2.1
    · exact Finset.mem_univ _
  · exact combinedPinnedIndex_values x.1 x.2.1 x.2.2.1
      x.2.2.2.1 x.2.2.2.2 hr.2.2.1 hr.2.2.2.1

theorem compatiblePairShiftModulus_encodeFullPinnedIndex
    {H : Finset ℕ} {x : FullPinnedIndexType H}
    (hr : FullPinnedRestricted x.1 x.2.1 x.2.2.1
      x.2.2.2.1 x.2.2.2.2) :
    BoundedGaps.Maynard.compatiblePairShiftModulus (doubledIndexSet H) 1
        (encodeFullPinnedIndex x) =
      fullPinnedOffModulus H x.1 x.2.1 x.2.2.1
        x.2.2.2.1 x.2.2.2.2 := by
  unfold BoundedGaps.Maynard.compatiblePairShiftModulus
    encodeFullPinnedIndex
  exact divisorPairModulus_combine_eq_fullPinnedOffModulus
    hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2

/-- The unweighted maximal-discrepancy envelope over full pinned
quadruples. -/
noncomputable def fullPinnedMaxDiscrepancySum
    (H : Finset ℕ) (D E : Finset (H → ℕ)) (x : ℕ) : ℝ :=
  ∑ i ∈ fullPinnedIndex H D E,
    BoundedGaps.Maynard.maxProgressionDiscrepancy x
      (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
        i.2.2.2.1 i.2.2.2.2)

/-- The doubled-coordinate encoding injects the full pinned discrepancy
sum into the standard compatible pair-shift discrepancy sum. -/
theorem fullPinnedMaxDiscrepancySum_le_standard
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q x : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q) :
    fullPinnedMaxDiscrepancySum H D E x ≤
      ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          (doubledIndexSet H) (combinedDivisorSupport D E),
        BoundedGaps.Maynard.maxProgressionDiscrepancy x
          (BoundedGaps.Maynard.compatiblePairShiftModulus
            (doubledIndexSet H) 1 i) := by
  let f := encodeFullPinnedIndex (H := H)
  let S := fullPinnedIndex H D E
  let T := BoundedGaps.Maynard.compatiblePairShiftIndex
    (doubledIndexSet H) (combinedDivisorSupport D E)
  have hf : Function.Injective f := encodeFullPinnedIndex_injective
  have hsub : S.image f ⊆ T := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact encodeFullPinnedIndex_mem_compatible support hj
  calc
    fullPinnedMaxDiscrepancySum H D E x =
        ∑ i ∈ S.image f,
          BoundedGaps.Maynard.maxProgressionDiscrepancy x
            (BoundedGaps.Maynard.compatiblePairShiftModulus
              (doubledIndexSet H) 1 i) := by
      unfold fullPinnedMaxDiscrepancySum
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        have hr := (Finset.mem_filter.mp hi).2
        rw [compatiblePairShiftModulus_encodeFullPinnedIndex hr]
      · intro a ha b hb hab
        exact hf hab
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i hiT hiS =>
        BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

/-- Reindex a nested restricted quadruple sum by `fullPinnedIndex`. -/
theorem sum_fullPinnedIndex_eq_nested
    {H : Finset ℕ} (D E : Finset (H → ℕ))
    (f : FullPinnedIndexType H → ℝ) :
    (∑ i ∈ fullPinnedIndex H D E, f i) =
      ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        if FullPinnedRestricted h d e d' e' then
          f (h, d, e, d', e') else 0 := by
  classical
  unfold fullPinnedIndex
  rw [Finset.sum_filter]
  let g : FullPinnedIndexType H → ℝ := fun i =>
    if FullPinnedRestricted i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2
      then f i else 0
  change (∑ i ∈ (Finset.univ : Finset H).product
      (D.product (E.product (D.product E))), g i) = _
  calc
    _ = ∑ h : H, ∑ r ∈ D.product (E.product (D.product E)),
        g (h, r) := Finset.sum_product _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      calc
        (∑ r ∈ D.product (E.product (D.product E)), g (h, r)) =
            ∑ d ∈ D, ∑ r ∈ E.product (D.product E),
              g (h, d, r) := Finset.sum_product _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro d hd
          calc
            (∑ r ∈ E.product (D.product E), g (h, d, r)) =
                ∑ e ∈ E, ∑ r ∈ D.product E,
                  g (h, d, e, r) := Finset.sum_product _ _ _
            _ = _ := by
              apply Finset.sum_congr rfl
              intro e he
              calc
                (∑ r ∈ D.product E, g (h, d, e, r)) =
                    ∑ d' ∈ D, ∑ e' ∈ E,
                      g (h, d, e, d', e') := Finset.sum_product _ _ _
                _ = _ := by rfl

/-- The coefficient-weighted full pinned error is controlled by the two
unweighted maximal-discrepancy envelopes. -/
theorem abs_fullPinnedRestrictedErrorSum_le_maxDiscrepancies
    {H : Finset ℕ} {RD RE w Y m p A B : ℕ}
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hbound : ∀ d ∈ separatedFirstSupport H RD Y,
      ∀ e ∈ fullySeparatedCompanionSupport H RE (primorial w) m,
        |lambda d e| ≤ L)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ q ∈ Finset.Ico A B, ∀ h : H,
      h.1 * (primorial w * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |fullPinnedRestrictedErrorSum H
        (separatedFirstSupport H RD Y)
        (fullySeparatedCompanionSupport H RE (primorial w) m)
        lambda w m p (auxiliaryPrimeInterval A B)| ≤
      L ^ 2 *
        (fullPinnedMaxDiscrepancySum H
            (separatedFirstSupport H RD Y)
            (fullySeparatedCompanionSupport H RE (primorial w) m) (B - 1) +
          fullPinnedMaxDiscrepancySum H
            (separatedFirstSupport H RD Y)
            (fullySeparatedCompanionSupport H RE (primorial w) m) (A - 1)) := by
  classical
  let D := separatedFirstSupport H RD Y
  let E := fullySeparatedCompanionSupport H RE (primorial w) m
  let S := fullPinnedIndex H D E
  have herrIndex :
      fullPinnedRestrictedErrorSum H D E lambda w m p
          (auxiliaryPrimeInterval A B) =
        ∑ i ∈ S,
          lambda i.2.1 i.2.2.1 * lambda i.2.2.2.1 i.2.2.2.2 *
            fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
              i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 := by
    unfold fullPinnedRestrictedErrorSum
    symm
    exact sum_fullPinnedIndex_eq_nested D E _
  rw [herrIndex]
  calc
    |∑ i ∈ S,
        lambda i.2.1 i.2.2.1 * lambda i.2.2.2.1 i.2.2.2.2 *
          fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
            i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2| ≤
        ∑ i ∈ S,
          |lambda i.2.1 i.2.2.1 * lambda i.2.2.2.1 i.2.2.2.2 *
            fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
              i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, L ^ 2 *
        (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
            (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
              i.2.2.2.1 i.2.2.2.2) +
          BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
            (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
              i.2.2.2.1 i.2.2.2.2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      have hprod := Finset.mem_product.mp hiData.1
      have htail := Finset.mem_product.mp hprod.2
      have htail2 := Finset.mem_product.mp htail.2
      have htail3 := Finset.mem_product.mp htail2.2
      have hd : i.2.1 ∈ D := htail.1
      have he : i.2.2.1 ∈ E := htail2.1
      have hd' : i.2.2.2.1 ∈ D := htail3.1
      have he' : i.2.2.2.2 ∈ E := htail3.2
      have hr := hiData.2
      have herr := abs_fullPinnedCountError_primeInterval_le_max
        i.1 hd hd' he he' hwY hcover hm hp hRDp hREp hREY hr hpre
        (fun q hq => hmargin q hq i.1) hA hAB
      rw [abs_mul, abs_mul]
      have hcoeff :
          |lambda i.2.1 i.2.2.1| *
              |lambda i.2.2.2.1 i.2.2.2.2| ≤ L ^ 2 := by
        have h₁ := hbound i.2.1 hd i.2.2.1 he
        have h₂ := hbound i.2.2.2.1 hd' i.2.2.2.2 he'
        nlinarith [abs_nonneg (lambda i.2.1 i.2.2.1),
          abs_nonneg (lambda i.2.2.2.1 i.2.2.2.2)]
      exact mul_le_mul hcoeff herr (abs_nonneg _) (sq_nonneg L)
    _ = L ^ 2 *
        (fullPinnedMaxDiscrepancySum H D E (B - 1) +
          fullPinnedMaxDiscrepancySum H D E (A - 1)) := by
      unfold fullPinnedMaxDiscrepancySum
      change (∑ i ∈ S, L ^ 2 *
          (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
              (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
                i.2.2.2.1 i.2.2.2.2) +
            BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
              (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
                i.2.2.2.1 i.2.2.2.2))) =
        L ^ 2 * ((∑ i ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
            (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
              i.2.2.2.1 i.2.2.2.2)) +
          ∑ i ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
            (fullPinnedOffModulus H i.1 i.2.1 i.2.2.1
              i.2.2.2.1 i.2.2.2.2))
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end
end Erdos4
