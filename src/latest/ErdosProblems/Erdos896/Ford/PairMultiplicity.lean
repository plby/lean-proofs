/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.ProfileMass

/-!
# Ordered multiplicity for Ford profile pairs

This file compares the squarefree, unordered profile model with the ordered
slot model.  A valid block selection has exactly the product of the block
factorials many orderings.  Transporting divisor subsets along each ordering
embeds its off-diagonal close pairs in the ordered model.
-/

namespace Erdos896.Ford

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A slot is a block index together with a position in that block. -/
abbrev ProfileSlot (blocks : ℕ) (b : ℕ → ℕ) :=
  Σ i : Fin blocks, Fin (b i)

def profileSlotBlock {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) : ℕ := s.1.1

/-- All ordered prime tuples compatible with a profile; repetitions are
allowed. -/
def profileOrderedTuples (start blocks : ℕ) (b : ℕ → ℕ) :
    Finset (ProfileSlot blocks b → ℕ) :=
  Fintype.piFinset fun s => primeBlock (start + profileSlotBlock s)

def profileOrderedTupleWeight {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) : ℝ :=
  ∏ s, (1 : ℝ) / p s

def profileOrderedDivisorLog {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) (Y : Finset (ProfileSlot blocks b)) : ℝ :=
  ∑ s ∈ Y, Real.log (p s)

def profileOrderedClosePairs {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) :
    Finset (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) :=
  ((Finset.univ.powerset).product (Finset.univ.powerset)).filter fun YZ =>
    |profileOrderedDivisorLog p YZ.1 - profileOrderedDivisorLog p YZ.2| <=
      Real.log 2

def profileOrderedOffDiagonalPairs {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) :
    Finset (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) :=
  (profileOrderedClosePairs p).filter fun YZ => YZ.1 ≠ YZ.2

def profileOrderedOffDiagonalMass
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑ p ∈ profileOrderedTuples start blocks b,
    profileOrderedTupleWeight p * (profileOrderedOffDiagonalPairs p).card

/-- Independent permutations of the slots inside each block. -/
abbrev ProfileBlockPermutations (blocks : ℕ) (b : ℕ → ℕ) :=
  ∀ i : Fin blocks, Equiv.Perm (Fin (b i))

theorem card_profileBlockPermutations (blocks : ℕ) (b : ℕ → ℕ) :
    Fintype.card (ProfileBlockPermutations blocks b) =
      profileFactorial blocks b := by
  rw [Fintype.card_pi]
  simp_rw [Fintype.card_perm, Fintype.card_fin]
  unfold profileFactorial
  exact Fin.prod_univ_eq_prod_range (fun i => (b i).factorial) blocks

/-- Enumerate every selected block by its canonical finite order, followed
by an arbitrary permutation of the positions. -/
def profileTupleOfSelectionPermutation
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) : ProfileSlot blocks b → ℕ :=
  fun s =>
    ((Finset.equivFinOfCardEq
      (profileSelection_card hc s.1.1 (Finset.mem_range.mpr s.1.2))).symm
        (σ s.1 s.2)).1

theorem profileTupleOfSelectionPermutation_mem
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    profileTupleOfSelectionPermutation c hc σ ∈
      profileOrderedTuples start blocks b := by
  apply Fintype.mem_piFinset.mpr
  intro s
  apply profileSelection_subset_block hc s.1.1 (Finset.mem_range.mpr s.1.2)
  exact ((Finset.equivFinOfCardEq
    (profileSelection_card hc s.1.1 (Finset.mem_range.mpr s.1.2))).symm
      (σ s.1 s.2)).2

theorem image_profileTupleOfSelectionPermutation_block
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) (i : Fin blocks) :
    Finset.univ.image (fun r : Fin (b i) =>
      profileTupleOfSelectionPermutation c hc σ ⟨i, r⟩) =
      c i.1 (Finset.mem_range.mpr i.2) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact ((Finset.equivFinOfCardEq
      (profileSelection_card hc i.1 (Finset.mem_range.mpr i.2))).symm
        (σ i r)).2
  · intro hq
    let e := Finset.equivFinOfCardEq
      (profileSelection_card hc i.1 (Finset.mem_range.mpr i.2))
    let r : Fin (b i) := (σ i).symm (e ⟨q, hq⟩)
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_univ _, ?_⟩
    simp [profileTupleOfSelectionPermutation, r, e]

abbrev ProfileEnumeratedSelection
    (start blocks : ℕ) (b : ℕ → ℕ) :=
  {c // c ∈ profileSelections start blocks b} ×
    ProfileBlockPermutations blocks b

def profileEnumeratedTuple
    {start blocks : ℕ} {b : ℕ → ℕ}
    (x : ProfileEnumeratedSelection start blocks b) :
    ProfileSlot blocks b → ℕ :=
  profileTupleOfSelectionPermutation x.1.1 x.1.2 x.2

theorem profileEnumeratedTuple_injective
    (start blocks : ℕ) (b : ℕ → ℕ) :
    Function.Injective
      (@profileEnumeratedTuple start blocks b) := by
  rintro ⟨c, σ⟩ ⟨d, τ⟩ htuple
  have hcdVal : c.1 = d.1 := by
    funext i hi
    let fi : Fin blocks := ⟨i, Finset.mem_range.mp hi⟩
    rw [← image_profileTupleOfSelectionPermutation_block c.1 c.2 σ fi,
      ← image_profileTupleOfSelectionPermutation_block d.1 d.2 τ fi]
    exact congrArg
      (fun p : ProfileSlot blocks b → ℕ =>
        Finset.univ.image (fun r : Fin (b fi) => p ⟨fi, r⟩)) htuple
  have hcd : c = d := Subtype.ext hcdVal
  subst d
  have hστ : σ = τ := by
    funext i
    apply Equiv.ext
    intro r
    let e := Finset.equivFinOfCardEq
      (profileSelection_card c.2 i.1 (Finset.mem_range.mpr i.2))
    have hval := congrFun htuple (Sigma.mk i r)
    change (e.symm (σ i r)).1 = (e.symm (τ i r)).1 at hval
    have hsub : e.symm (σ i r) = e.symm (τ i r) := Subtype.ext hval
    exact e.symm.injective hsub
  subst τ
  rfl

theorem profileTupleOfSelectionPermutation_weight
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    profileOrderedTupleWeight
        (profileTupleOfSelectionPermutation c hc σ) =
      profileSelectionWeight c := by
  classical
  unfold profileOrderedTupleWeight profileSelectionWeight
  rw [Fintype.prod_sigma]
  rw [Finset.attach_eq_univ]
  let eIdx : Fin blocks ≃ {i // i ∈ Finset.range blocks} :=
    Fin.equivSubtype.trans
      (Equiv.subtypeEquivRight fun i => Finset.mem_range.symm)
  apply Fintype.prod_equiv eIdx
  intro i
  let e := (σ i).trans
    (Finset.equivFinOfCardEq
      (profileSelection_card hc i.1 (eIdx i).2)).symm
  calc
    (∏ r : Fin (b i),
        (1 : ℝ) / profileTupleOfSelectionPermutation c hc σ ⟨i, r⟩) =
        ∏ q : (c i.1 (eIdx i).2 : Finset ℕ), (1 : ℝ) / q.1 :=
      Fintype.prod_equiv e
        (fun r : Fin (b i) =>
          (1 : ℝ) / profileTupleOfSelectionPermutation c hc σ ⟨i, r⟩)
        (fun q : (c i.1 (eIdx i).2 : Finset ℕ) => (1 : ℝ) / q.1)
        (fun r => by rfl)
    _ = ∏ p ∈ c i.1 (eIdx i).2, (1 : ℝ) / p := by
      have h := Finset.prod_attach (c i.1 (eIdx i).2)
        (fun p : ℕ => (1 : ℝ) / p)
      rw [Finset.attach_eq_univ] at h
      exact h

theorem profileTupleOfSelectionPermutation_injective
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    Function.Injective (profileTupleOfSelectionPermutation c hc σ) := by
  rintro ⟨i, r⟩ ⟨j, u⟩ hval
  have hij : i.1 = j.1 := by
    by_contra hne
    have hi := profileSelection_subset_block hc i.1
      (Finset.mem_range.mpr i.2)
      ((Finset.equivFinOfCardEq
        (profileSelection_card hc i.1 (Finset.mem_range.mpr i.2))).symm
          (σ i r)).2
    have hj := profileSelection_subset_block hc j.1
      (Finset.mem_range.mpr j.2)
      ((Finset.equivFinOfCardEq
        (profileSelection_card hc j.1 (Finset.mem_range.mpr j.2))).symm
          (σ j u)).2
    have hd := primeBlock_disjoint_of_ne
      (by omega : start + i.1 ≠ start + j.1)
    have hi' : profileTupleOfSelectionPermutation c hc σ ⟨i, r⟩ ∈
        primeBlock (start + i.1) := hi
    have hj' : profileTupleOfSelectionPermutation c hc σ ⟨j, u⟩ ∈
        primeBlock (start + j.1) := hj
    rw [← hval] at hj'
    exact (Finset.disjoint_left.mp hd) hi' hj'
  have hijFin : i = j := Fin.ext hij
  subst j
  let e := Finset.equivFinOfCardEq
    (profileSelection_card hc i.1 (Finset.mem_range.mpr i.2))
  change (e.symm (σ i r)).1 = (e.symm (σ i u)).1 at hval
  have hsub : e.symm (σ i r) = e.symm (σ i u) := Subtype.ext hval
  have hru : r = u := (σ i).injective (e.symm.injective hsub)
  subst u
  rfl

theorem image_profileTupleOfSelectionPermutation_univ
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    Finset.univ.image (profileTupleOfSelectionPermutation c hc σ) =
      profileSelectionPrimes c := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨s.1.1, Finset.mem_range.mpr s.1.2⟩,
      Finset.mem_attach _ _, ?_⟩
    exact ((Finset.equivFinOfCardEq
      (profileSelection_card hc s.1.1 (Finset.mem_range.mpr s.1.2))).symm
        (σ s.1 s.2)).2
  · intro hq
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hq
    have hblock := congrArg (fun t : Finset ℕ => q ∈ t)
      (image_profileTupleOfSelectionPermutation_block c hc σ
        ⟨i.1, Finset.mem_range.mp i.2⟩)
    rw [← hblock] at hqi
    obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hqi
    apply Finset.mem_image.mpr
    exact ⟨⟨⟨i.1, Finset.mem_range.mp i.2⟩, r⟩,
      Finset.mem_univ _, hrq⟩

/-- Pull a selected-prime subset back to the corresponding subset of
ordered slots. -/
def profileLiftPrimeSubset
    {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) (T : Finset ℕ) :
    Finset (ProfileSlot blocks b) :=
  Finset.univ.filter fun s => p s ∈ T

theorem image_profileLiftPrimeSubset
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) {T : Finset ℕ}
    (hT : T ⊆ profileSelectionPrimes c) :
    (profileLiftPrimeSubset
      (profileTupleOfSelectionPermutation c hc σ) T).image
        (profileTupleOfSelectionPermutation c hc σ) = T := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hs).2
  · intro hq
    have hqS := hT hq
    have hqImage : q ∈ Finset.univ.image
        (profileTupleOfSelectionPermutation c hc σ) := by
      rw [image_profileTupleOfSelectionPermutation_univ c hc σ]
      exact hqS
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp hqImage
    apply Finset.mem_image.mpr
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsq ▸ hq⟩, hsq⟩

theorem profileLiftPrimeSubset_injOn
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    Set.InjOn
      (profileLiftPrimeSubset
        (profileTupleOfSelectionPermutation c hc σ))
      (↑(profileSelectionPrimes c).powerset) := by
  intro T hT U hU hTU
  have hTi := image_profileLiftPrimeSubset c hc σ
    (Finset.mem_powerset.mp hT)
  have hUi := image_profileLiftPrimeSubset c hc σ
    (Finset.mem_powerset.mp hU)
  rw [← hTi, ← hUi, hTU]

theorem profileOrderedDivisorLog_lift
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) {T : Finset ℕ}
    (hT : T ⊆ profileSelectionPrimes c) :
    profileOrderedDivisorLog
        (profileTupleOfSelectionPermutation c hc σ)
        (profileLiftPrimeSubset
          (profileTupleOfSelectionPermutation c hc σ) T) =
      Real.log (∏ q ∈ T, q) := by
  classical
  let p := profileTupleOfSelectionPermutation c hc σ
  let L := profileLiftPrimeSubset p T
  have hp : Function.Injective p :=
    profileTupleOfSelectionPermutation_injective c hc σ
  have himage : L.image p = T :=
    image_profileLiftPrimeSubset c hc σ hT
  have hnz : ∀ q ∈ T, (q : ℝ) ≠ 0 := by
    intro q hq
    exact_mod_cast (prime_of_mem_profileSelectionPrimes hc (hT hq)).ne_zero
  unfold profileOrderedDivisorLog
  change (∑ s ∈ L, Real.log (p s)) = _
  calc
    (∑ s ∈ L, Real.log (p s)) =
        ∑ q ∈ L.image p, Real.log q := by
      rw [Finset.sum_image hp.injOn]
    _ = ∑ q ∈ T, Real.log q := by rw [himage]
    _ = Real.log (∏ q ∈ T, (q : ℝ)) :=
      (Real.log_prod hnz).symm
    _ = Real.log (∏ q ∈ T, q) := by rfl

/-- Pull back both components of a prime-subset pair to slot subsets. -/
def profileLiftPrimePair
    {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) (TU : Finset ℕ × Finset ℕ) :
    Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b) :=
  (profileLiftPrimeSubset p TU.1, profileLiftPrimeSubset p TU.2)

theorem profileLiftPrimePair_injOn
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    Set.InjOn
      (profileLiftPrimePair
        (profileTupleOfSelectionPermutation c hc σ))
      (↑((profileSelectionPrimes c).powerset.product
        (profileSelectionPrimes c).powerset)) := by
  intro TU hTU VW hVW hEq
  have hT := (Finset.mem_product.mp hTU).1
  have hU := (Finset.mem_product.mp hTU).2
  have hV := (Finset.mem_product.mp hVW).1
  have hW := (Finset.mem_product.mp hVW).2
  apply Prod.ext
  · exact profileLiftPrimeSubset_injOn c hc σ hT hV
      (congrArg Prod.fst hEq)
  · exact profileLiftPrimeSubset_injOn c hc σ hU hW
      (congrArg Prod.snd hEq)

theorem profileLiftPrimePair_mapsTo_offDiagonal
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    Set.MapsTo
      (profileLiftPrimePair
        (profileTupleOfSelectionPermutation c hc σ))
      (↑((profileSelectionClosePairs c).filter fun TU => TU.1 ≠ TU.2))
      (↑(profileOrderedOffDiagonalPairs
        (profileTupleOfSelectionPermutation c hc σ))) := by
  intro TU hTU
  have hTU' := Finset.mem_filter.mp hTU
  have hclose := Finset.mem_filter.mp hTU'.1
  have hT : TU.1 ⊆ profileSelectionPrimes c :=
    Finset.mem_powerset.mp (Finset.mem_product.mp hclose.1).1
  have hU : TU.2 ⊆ profileSelectionPrimes c :=
    Finset.mem_powerset.mp (Finset.mem_product.mp hclose.1).2
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_powerset.mpr <;>
        exact Finset.subset_univ _
    · simp only [profileLiftPrimePair]
      rw [profileOrderedDivisorLog_lift c hc σ hT,
        profileOrderedDivisorLog_lift c hc σ hU]
      simpa [dyadicSigma] using hclose.2
  · intro hEq
    apply hTU'.2
    exact profileLiftPrimeSubset_injOn c hc σ
      (Finset.mem_product.mp hclose.1).1
      (Finset.mem_product.mp hclose.1).2 hEq

theorem profileSelectionOffDiagonalCount_le_ordered
    {start blocks : ℕ} {b : ℕ → ℕ}
    (c : ProfileSelection blocks) (hc : c ∈ profileSelections start blocks b)
    (σ : ProfileBlockPermutations blocks b) :
    profileSelectionOffDiagonalCount c ≤
      (profileOrderedOffDiagonalPairs
        (profileTupleOfSelectionPermutation c hc σ)).card := by
  unfold profileSelectionOffDiagonalCount
  apply Finset.card_le_card_of_injOn
    (profileLiftPrimePair
      (profileTupleOfSelectionPermutation c hc σ))
    (profileLiftPrimePair_mapsTo_offDiagonal c hc σ)
  apply (profileLiftPrimePair_injOn c hc σ).mono
  intro TU hTU
  exact (Finset.mem_filter.mp
    (Finset.mem_filter.mp hTU).1).1

/-- All valid selections, each equipped with one of its blockwise
orderings. -/
noncomputable def profileEnumeratedSelectionsFinset
    (start blocks : ℕ) (b : ℕ → ℕ) :
    Finset (ProfileEnumeratedSelection start blocks b) :=
  (profileSelections start blocks b).attach.product Finset.univ

theorem profileEnumeratedTuple_mem_ordered
    {start blocks : ℕ} {b : ℕ → ℕ}
    (x : ProfileEnumeratedSelection start blocks b) :
    profileEnumeratedTuple x ∈ profileOrderedTuples start blocks b :=
  profileTupleOfSelectionPermutation_mem x.1.1 x.1.2 x.2

theorem image_profileEnumeratedTuple_subset_ordered
    (start blocks : ℕ) (b : ℕ → ℕ) :
    (profileEnumeratedSelectionsFinset start blocks b).image
        (@profileEnumeratedTuple start blocks b) ⊆
      profileOrderedTuples start blocks b := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  exact profileEnumeratedTuple_mem_ordered x

private theorem profileEnumeratedOffDiagonalTerm_le
    {start blocks : ℕ} {b : ℕ → ℕ}
    (x : ProfileEnumeratedSelection start blocks b) :
    (profileSelectionOffDiagonalCount x.1.1 : ℝ) *
        profileSelectionWeight x.1.1 ≤
      profileOrderedTupleWeight (profileEnumeratedTuple x) *
        (profileOrderedOffDiagonalPairs
          (profileEnumeratedTuple x)).card := by
  have hcount := profileSelectionOffDiagonalCount_le_ordered
    x.1.1 x.1.2 x.2
  have hcountR : (profileSelectionOffDiagonalCount x.1.1 : ℝ) ≤
      ((profileOrderedOffDiagonalPairs
        (profileEnumeratedTuple x)).card : ℝ) := by
    exact_mod_cast hcount
  change (profileSelectionOffDiagonalCount x.1.1 : ℝ) *
      profileSelectionWeight x.1.1 ≤
    profileOrderedTupleWeight
        (profileTupleOfSelectionPermutation x.1.1 x.1.2 x.2) *
      (profileOrderedOffDiagonalPairs
        (profileTupleOfSelectionPermutation x.1.1 x.1.2 x.2)).card
  rw [profileTupleOfSelectionPermutation_weight]
  calc
    (profileSelectionOffDiagonalCount x.1.1 : ℝ) *
        profileSelectionWeight x.1.1 ≤
      ((profileOrderedOffDiagonalPairs
        (profileEnumeratedTuple x)).card : ℝ) *
          profileSelectionWeight x.1.1 := by
      apply mul_le_mul_of_nonneg_right hcountR
      unfold profileSelectionWeight
      positivity
    _ = profileSelectionWeight x.1.1 *
        (profileOrderedOffDiagonalPairs
          (profileEnumeratedTuple x)).card := by ring

/-- Each unordered profile selection occurs with exactly the product of
the block factorials among the injectively enumerated ordered tuples.
Consequently its off-diagonal pair mass, with that multiplicity, is
bounded by the full ordered-tuple off-diagonal mass. -/
theorem profileFactorial_mul_profileOffDiagonalMass_le_ordered
    (start blocks : ℕ) (b : ℕ → ℕ) :
    (profileFactorial blocks b : ℝ) *
        profileOffDiagonalMass start blocks b ≤
      profileOrderedOffDiagonalMass start blocks b := by
  classical
  let P := ProfileBlockPermutations blocks b
  let S := profileSelections start blocks b
  let E := profileEnumeratedSelectionsFinset start blocks b
  let f := @profileEnumeratedTuple start blocks b
  let g : (ProfileSlot blocks b → ℕ) → ℝ := fun p =>
    profileOrderedTupleWeight p * (profileOrderedOffDiagonalPairs p).card
  have hfactor : (profileFactorial blocks b : ℝ) =
      (Fintype.card P : ℝ) := by
    exact_mod_cast (card_profileBlockPermutations blocks b).symm
  calc
    (profileFactorial blocks b : ℝ) *
        profileOffDiagonalMass start blocks b =
      ∑ c ∈ S, ∑ _σ : P,
        (profileSelectionOffDiagonalCount c : ℝ) *
          profileSelectionWeight c := by
      unfold profileOffDiagonalMass S P
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]
      rw [hfactor]
    _ = ∑ x ∈ E,
        (profileSelectionOffDiagonalCount x.1.1 : ℝ) *
          profileSelectionWeight x.1.1 := by
      unfold E profileEnumeratedSelectionsFinset S P
      rw [Finset.product_eq_sprod, Finset.sum_product]
      exact (Finset.sum_attach
        (profileSelections start blocks b)
        (fun c => ∑ _σ : ProfileBlockPermutations blocks b,
          (profileSelectionOffDiagonalCount c : ℝ) *
            profileSelectionWeight c)).symm
    _ ≤ ∑ x ∈ E, g (f x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact profileEnumeratedOffDiagonalTerm_le x
    _ = ∑ p ∈ E.image f, g p := by
      rw [Finset.sum_image]
      exact (profileEnumeratedTuple_injective start blocks b).injOn
    _ ≤ ∑ p ∈ profileOrderedTuples start blocks b, g p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (image_profileEnumeratedTuple_subset_ordered start blocks b)
      intro p hp hnot
      unfold g profileOrderedTupleWeight
      positivity
    _ = profileOrderedOffDiagonalMass start blocks b := by
      rfl

end

end Erdos896.Ford
