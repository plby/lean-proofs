/-
This file incorporates the unconditional octahedral Tucker proof from
`xiangyazi24/proof_in_the_book` (commit `8ccc127c6c0109fa30ac61541420101376b24482`),
with small compatibility repairs for Lean/Mathlib v4.33.0.
-/

import ErdosProblems.Erdos95.External.Chapter39
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation

/-- **Pigeonhole on a maximal chain.** The `n` labels of a signed-permutation prefix chain,
valued in `SignedLabel (n-1)`, cannot all have distinct indices: two share an index. -/
theorem exists_same_index_in_prefixChain {n : ℕ} (hn : 1 ≤ n)
    (label : NonzeroSignedSubset n → SignedLabel (n - 1)) (P : SignedPermutation n) :
    ∃ i j : Fin n, i ≠ j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index := by
  have hcard : Fintype.card (Fin (n - 1)) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin n => (label (P.prefixChain i)).index) hcard
  exact ⟨i, j, hij, heq⟩

/-- **Sound reduction for Tucker.** If every antipodal labeling admits a maximal chain with two
positions `i < j` whose labels share an index but differ in sign, then `TuckerLemmaStatement n`
holds.  (Those two prefix subsets are comparable by `prefixChain_le`, and same-index/opposite-sign
means each label is the negation of the other — a complementary comparable pair.) -/
theorem tuckerLemmaStatement_of_chain_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti
  refine ⟨P.prefixChain i, P.prefixChain j, prefixChain_le P (le_of_lt hij), ?_⟩
  refine SignedLabel.ext ?_ ?_
  · -- positive components are opposite
    simp only [SignedLabel.neg]
    revert hsign
    cases hpi : (label (P.prefixChain i)).positive <;>
      cases hpj : (label (P.prefixChain j)).positive <;> simp
  · -- indices agree (neg keeps the index)
    simp only [SignedLabel.neg]
    exact hidx

theorem tuckerLemmaStatement_of_chain_complementary_of_no_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti hno
  have hcomp : label (P.prefixChain i) = (label (P.prefixChain j)).neg := by
    refine SignedLabel.ext ?_ ?_
    · simp only [SignedLabel.neg]
      revert hsign
      cases hpi : (label (P.prefixChain i)).positive <;>
        cases hpj : (label (P.prefixChain j)).positive <;> simp
    · simp only [SignedLabel.neg]
      exact hidx
  exact hno (P.prefixChain i) (P.prefixChain j)
    (prefixChain_le P (le_of_lt hij)) hcomp

/-! ## Hemisphere and equator model -/

theorem signedSubset_ext_pos_neg {n : ℕ} {X Y : SignedSubset n}
    (hpos : X.pos = Y.pos) (hneg : X.neg = Y.neg) : X = Y := by
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

/-- The upper hemisphere `B⁺_{r+1}`: the last coordinate is not negative. -/
def UpperHemisphere {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.neg

/-- The equator of `B⁺_{r+1}`: the last coordinate is zero. -/
def Equator {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.pos ∧ Fin.last r ∉ X.1.neg

theorem equator_subset_upperHemisphere {r : ℕ} {X : NonzeroSignedSubset (r + 1)}
    (hX : Equator X) : UpperHemisphere X :=
  hX.2

theorem upperHemisphere_of_le {r : ℕ} {X Y : NonzeroSignedSubset (r + 1)}
    (hXY : SignedSubset.Le X.1 Y.1) (hY : UpperHemisphere Y) :
    UpperHemisphere X := by
  intro hneg
  exact hY (hXY.2 hneg)

/-- Embed a sign vector on the first `r` coordinates into the equator of
`{−1,0,1}^{r+1}`. -/
def signedSubsetEquatorEmbed {r : ℕ} (X : SignedSubset r) : SignedSubset (r + 1) where
  pos := X.pos.image Fin.castSucc
  neg := X.neg.image Fin.castSucc
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hypos hyneg
    rcases Finset.mem_image.mp hypos with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hyneg with ⟨b, hbmem, hb⟩
    have hba : b = a := by
      apply Fin.ext
      simpa using congrArg Fin.val hb
    subst b
    exact (Finset.disjoint_left.mp X.disjoint) ha hbmem

/-- The equator embedding on nonzero sign vectors. -/
def equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) : NonzeroSignedSubset (r + 1) :=
  ⟨signedSubsetEquatorEmbed X.1, by
    rcases X.2 with hpos | hneg
    · rcases hpos with ⟨i, hi⟩
      left
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩
    · rcases hneg with ⟨i, hi⟩
      right
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩⟩

theorem equatorEmbed_mem_equator {r : ℕ} (X : NonzeroSignedSubset r) :
    Equator (equatorEmbed X) := by
  constructor
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega

/-- The predecessor of a non-last coordinate. -/
def finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) : Fin r :=
  ⟨i.val, by
    have hle : i.val ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hne : i.val ≠ r := by
      intro hval
      exact hi (Fin.ext hval)
    omega⟩

@[simp]
theorem castSucc_finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) :
    Fin.castSucc (finPredOfNotLast i hi) = i := by
  apply Fin.ext
  rfl

/-- Drop the last zero coordinate from an equatorial sign vector. -/
def equatorDropSignedSubset {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : SignedSubset r where
  pos := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.pos
  neg := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.neg
  disjoint := by
    rw [Finset.disjoint_left]
    intro i hip hin
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hip hin
    exact (Finset.disjoint_left.mp X.1.disjoint) hip hin

theorem equatorDrop_nonzero {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) : (equatorDropSignedSubset X).Nonzero := by
  rcases X.2 with hpos | hneg
  · rcases hpos with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.1 (by simpa [hlast] using hi)
    left
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩
  · rcases hneg with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.2 (by simpa [hlast] using hi)
    right
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩

/-- The inverse map from the equator back to `K_r`. -/
def equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1)) (hX : Equator X) :
    NonzeroSignedSubset r :=
  ⟨equatorDropSignedSubset X, equatorDrop_nonzero X hX⟩

theorem equatorDrop_equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorDrop (equatorEmbed X) (equatorEmbed_mem_equator X) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]

theorem equatorEmbed_equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) :
    equatorEmbed (equatorDrop X hX) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.1 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.2 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast

/-- The equator of the upper hemisphere in `K_{r+1}` is canonically `K_r`. -/
noncomputable def equatorEquiv (r : ℕ) :
    NonzeroSignedSubset r ≃ {X : NonzeroSignedSubset (r + 1) // Equator X} where
  toFun X := ⟨equatorEmbed X, equatorEmbed_mem_equator X⟩
  invFun X := equatorDrop X.1 X.2
  left_inv := by
    intro X
    exact equatorDrop_equatorEmbed X
  right_inv := by
    intro X
    cases X with
    | mk X hX =>
        apply Subtype.ext
        exact equatorEmbed_equatorDrop X hX

theorem equatorEmbed_le {r : ℕ} {X Y : NonzeroSignedSubset r}
    (hXY : SignedSubset.Le X.1 Y.1) :
    SignedSubset.Le (equatorEmbed X).1 (equatorEmbed Y).1 := by
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.1 hi, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.2 hi, rfl⟩

theorem signedSubsetEquatorEmbed_antipode {r : ℕ} (X : SignedSubset r) :
    signedSubsetEquatorEmbed X.antipode = (signedSubsetEquatorEmbed X).antipode := by
  apply signedSubset_ext_pos_neg
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]

theorem equatorEmbed_antipode {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorEmbed X.antipode = (equatorEmbed X).antipode := by
  apply Subtype.ext
  exact signedSubsetEquatorEmbed_antipode X.1

noncomputable def equatorRestrictedLabel {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    NonzeroSignedSubset d → SignedLabel d :=
  fun X => label ((equatorEquiv d) X).1

noncomputable def equatorRestrictedLabelOf {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    NonzeroSignedSubset r → SignedLabel m :=
  fun X => label ((equatorEquiv r) X).1

theorem equatorRestrictedLabelOf_antipodal {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabelOf label X.antipode =
      (equatorRestrictedLabelOf label X).neg := by
  intro X
  simpa [equatorRestrictedLabelOf, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabelOf_noComplementary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabelOf label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabelOf, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

theorem equatorRestrictedLabel_antipodal {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabel label X.antipode =
      (equatorRestrictedLabel label X).neg := by
  intro X
  simpa [equatorRestrictedLabel, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabel_noComplementary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabel label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabel, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

/-- A maximal chain of the equator, transported from a signed permutation of `K_r`. -/
def equatorPrefixChain {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    NonzeroSignedSubset (r + 1) :=
  equatorEmbed (P.prefixChain i)

theorem equatorPrefixChain_mem_equator {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    Equator (equatorPrefixChain P i) :=
  equatorEmbed_mem_equator (P.prefixChain i)

theorem equatorPrefixChain_le {r : ℕ} (P : SignedPermutation r) {i j : Fin r}
    (hij : i ≤ j) :
    SignedSubset.Le (equatorPrefixChain P i).1 (equatorPrefixChain P j).1 :=
  equatorEmbed_le (P.prefixChain_le hij)

/-- Under the equator equivalence, the transported equator chain is exactly
the original maximal chain in `K_r`. -/
theorem equatorPrefixChain_projects {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    (equatorEquiv r).symm
        ⟨equatorPrefixChain P i, equatorPrefixChain_mem_equator P i⟩ =
      P.prefixChain i :=
  equatorDrop_equatorEmbed (P.prefixChain i)

/-! ## Label-set `A` ridges and the local sigma-degree count -/

/-- The alternating label `α_k = (-1)^k(k+1)` in zero-based `Fin d` notation. -/
def alternatingLabel (k : Fin d) : SignedLabel d where
  positive := decide (Even k.val)
  index := k

@[simp]
theorem alternatingLabel_index (k : Fin d) : (alternatingLabel k).index = k := rfl

@[simp]
theorem alternatingLabel_positive (k : Fin d) :
    (alternatingLabel k).positive = decide (Even k.val) := rfl

theorem alternatingLabel_inj {d : ℕ} {a b : Fin d} :
    alternatingLabel a = alternatingLabel b ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg SignedLabel.index h
    simpa [alternatingLabel] using hidx
  · intro h
    subst h
    rfl

theorem alternatingLabel_neg_ne {d : ℕ} (a b : Fin d) :
    (alternatingLabel a).neg ≠ alternatingLabel b := by
  intro h
  have hidx : a = b := by
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabel, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabel, SignedLabel.neg] at hpos

theorem signedLabel_eq_alternating_or_neg {d : ℕ} (L : SignedLabel d) :
    L = alternatingLabel L.index ∨ L = (alternatingLabel L.index).neg := by
  cases L with
  | mk positive index =>
      by_cases h : positive = decide (Even index.val)
      · left
        apply SignedLabel.ext
        · exact h
        · rfl
      · right
        apply SignedLabel.ext
        · cases positive <;> cases hidx : decide (Even index.val) <;>
            simp [hidx, SignedLabel.neg] at h ⊢
        · rfl

/-- The concrete `A = {+1,-2,+3,...}` label set. -/
noncomputable def alternatingLabelSetA (d : ℕ) : Finset (SignedLabel d) :=
  Finset.univ.image fun k : Fin d => alternatingLabel k

theorem alternatingLabelSetA_card (d : ℕ) :
    (alternatingLabelSetA d).card = d := by
  classical
  rw [alternatingLabelSetA, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact alternatingLabel_inj.mp h

/-! ### Alternating labels along an arbitrary increasing index set -/

/-- The alternating label attached to the `a`th element of an index map.  The
sign alternates with the position `a`; the absolute label is `idx a`. -/
def alternatingLabelOf {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    SignedLabel m where
  positive := decide (Even a.val)
  index := idx a

@[simp]
theorem alternatingLabelOf_index {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).index = idx a := rfl

@[simp]
theorem alternatingLabelOf_positive {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).positive = decide (Even a.val) := rfl

theorem alternatingLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    alternatingLabelOf idx a = alternatingLabelOf idx b ↔ a = b := by
  constructor
  · intro h
    apply hidx
    simpa [alternatingLabelOf] using congrArg SignedLabel.index h
  · intro h
    subst h
    rfl

theorem alternatingLabelOf_neg_ne {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) (a b : Fin r) :
    (alternatingLabelOf idx a).neg ≠ alternatingLabelOf idx b := by
  intro h
  have hab : a = b := by
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabelOf, SignedLabel.neg] at hpos

/-- The alternating label set determined by an index map. -/
noncomputable def alternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => alternatingLabelOf idx a

theorem alternatingLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingLabelSetOf idx).card = r := by
  classical
  rw [alternatingLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingLabelOf_inj hidx).mp h

/-- The negative-first alternating label set determined by an index map. -/
noncomputable def alternatingNegLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => (alternatingLabelOf idx a).neg

theorem alternatingNegLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    (alternatingLabelOf idx a).neg = (alternatingLabelOf idx b).neg ↔ a = b := by
  constructor
  · intro h
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  · intro h
    subst h
    rfl

theorem alternatingNegLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingNegLabelSetOf idx).card = r := by
  classical
  rw [alternatingNegLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingNegLabelOf_inj hidx).mp h

theorem alternatingLabelSetOf_range_eq_of_eq {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (h : alternatingLabelSetOf idx = alternatingLabelSetOf eta) :
    Set.range idx = Set.range eta := by
  classical
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf eta := by
      rw [← h]
      simp [alternatingLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf] using hidx.symm⟩
  · rintro ⟨a, rfl⟩
    have hmem : alternatingLabelOf eta a ∈ alternatingLabelSetOf idx := by
      rw [h]
      simp [alternatingLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf] using hidx.symm⟩

theorem alternatingLabelSetOf_idx_unique {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h : alternatingLabelSetOf idx = alternatingLabelSetOf eta) :
    idx = eta := by
  exact (StrictMono.range_inj hidx heta).mp (alternatingLabelSetOf_range_eq_of_eq h)

theorem alternatingNegLabelSetOf_range_eq_of_eq {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (h : alternatingNegLabelSetOf idx = alternatingNegLabelSetOf eta) :
    Set.range idx = Set.range eta := by
  classical
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hmem : (alternatingLabelOf idx a).neg ∈ alternatingNegLabelSetOf eta := by
      rw [← h]
      simp [alternatingNegLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf, SignedLabel.neg] using hidx.symm⟩
  · rintro ⟨a, rfl⟩
    have hmem : (alternatingLabelOf eta a).neg ∈ alternatingNegLabelSetOf idx := by
      rw [h]
      simp [alternatingNegLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf, SignedLabel.neg] using hidx.symm⟩

theorem alternatingNegLabelSetOf_idx_unique {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h : alternatingNegLabelSetOf idx = alternatingNegLabelSetOf eta) :
    idx = eta := by
  exact (StrictMono.range_inj hidx heta).mp (alternatingNegLabelSetOf_range_eq_of_eq h)

/-- The label set carried by an ordered simplex.  The property below does not
use the order except to enumerate the finitely many vertices. -/
noncomputable def simplexLabelSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin k => label (sigma a)

/-- Positive-first alternating simplex, with its index set read off from the
simplex itself.  The `idx` below is an internal witness, not an external
summation parameter. -/
def IsAltPos {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingLabelSetOf idx

/-- Negative-first alternating simplex, with the same self-contained indexing
convention as `IsAltPos`. -/
def IsAltNeg {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingNegLabelSetOf idx

noncomputable instance isAltPos_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltPos label sigma) := by
  classical
  unfold IsAltPos
  infer_instance

noncomputable instance isAltNeg_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltNeg label sigma) := by
  classical
  unfold IsAltNeg
  infer_instance

theorem IsAltPos.idx_unique {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n}
    {idx eta : Fin k → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h₁ : simplexLabelSet label sigma = alternatingLabelSetOf idx)
    (h₂ : simplexLabelSet label sigma = alternatingLabelSetOf eta) :
    idx = eta :=
  alternatingLabelSetOf_idx_unique hidx heta (h₁.symm.trans h₂)

theorem IsAltNeg.idx_unique {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n}
    {idx eta : Fin k → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h₁ : simplexLabelSet label sigma = alternatingNegLabelSetOf idx)
    (h₂ : simplexLabelSet label sigma = alternatingNegLabelSetOf eta) :
    idx = eta :=
  alternatingNegLabelSetOf_idx_unique hidx heta (h₁.symm.trans h₂)

/-! ### Pure sign-sequence deletion parity -/

def signSeqAltPos {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = decide (Even i.val)

def signSeqAltNeg {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = !decide (Even i.val)

def signSeqDoor {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  (∀ j : Fin (k + 1), j < i → s j = decide (Even j.val)) ∧
    (∀ j : Fin (k + 1), i < j → s j = !decide (Even j.val))

noncomputable def signSeqDoorSet {k : ℕ} (s : Fin (k + 1) → Bool) :
    Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter (signSeqDoor s)

noncomputable instance signSeqDoor_decidable {k : ℕ} (s : Fin (k + 1) → Bool) :
    DecidablePred (signSeqDoor s) := by
  classical
  exact inferInstance

def signSeqBad {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  s i = !decide (Even i.val)

theorem signSeq_not_bad_iff {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    ¬ signSeqBad s i ↔ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeq_bad_iff_not_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqBad s i ↔ ¬ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeqDoor_iff_bad_cut {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    signSeqDoor s i ↔
      (∀ j : Fin (k + 1), j < i → ¬ signSeqBad s j) ∧
        (∀ j : Fin (k + 1), i < j → signSeqBad s j) := by
  constructor
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mpr (h.1 j hji)
    · intro j hij
      exact h.2 j hij
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mp (h.1 j hji)
    · intro j hij
      exact h.2 j hij

theorem signSeq_not_even_succ_decide (a : ℕ) :
    (!decide (Even (a + 1))) = decide (Even a) := by
  by_cases ha : Even a <;> simp [ha, Nat.even_add_one]

theorem signSeq_even_succ_decide (a : ℕ) :
    decide (Even (a + 1)) = (!decide (Even a)) := by
  by_cases ha : Even a <;> simp [ha, Nat.even_add_one]

theorem signSeqDoor_iff_remove_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a)) := by
  constructor
  · intro h a
    by_cases hlt : i.succAbove a < i
    · have hs := h.1 (i.succAbove a) hlt
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hlt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : (i.succAbove a).val = a.val := by
        rw [hsa]
        rfl
      simpa [hval] using hs
    · have hgt : i < i.succAbove a := by
        have hne : i ≠ i.succAbove a := Fin.ne_succAbove i a
        exact lt_of_le_of_ne (le_of_not_gt hlt) hne
      have hs := h.2 (i.succAbove a) hgt
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hgt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : (i.succAbove a).val = a.val + 1 := by
        rw [hsa]
        rfl
      change s (i.succAbove a) = decide (Even a.val)
      rw [hs, hval]
      exact signSeq_not_even_succ_decide a.val
  · intro h
    constructor
    · intro j hji
      have hne : j ≠ i := ne_of_lt hji
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_lt : i.succAbove a < i := by
        simpa [ha] using hji
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hsa_lt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : a.val = j.val := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      simpa [hval] using hs_j
    · intro j hij
      have hne : j ≠ i := ne_of_gt hij
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_gt : i < i.succAbove a := by
        simpa [ha] using hij
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hsa_gt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : j.val = a.val + 1 := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv.symm
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      rw [hs_j, hval]
      exact (signSeq_not_even_succ_decide a.val).symm

theorem signSeqDoor_nonadjacent_false {k : ℕ} {s : Fin (k + 1) → Bool}
    {i j : Fin (k + 1)} (hi : signSeqDoor s i) (hj : signSeqDoor s j)
    (_hij : i < j) :
    j.val ≤ i.val + 1 := by
  by_contra hle
  have hlt : i.val + 1 < j.val := by omega
  let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  have hit : i < t := by
    exact Fin.lt_iff_val_lt_val.mpr (by simp [t])
  have htj : t < j := by
    exact Fin.lt_iff_val_lt_val.mpr (by simpa [t] using hlt)
  have hbad : signSeqBad s t := (signSeqDoor_iff_bad_cut s i).mp hi |>.2 t hit
  have hnot : ¬ signSeqBad s t := (signSeqDoor_iff_bad_cut s j).mp hj |>.1 t htj
  exact hnot hbad

theorem signSeqDoorSet_card_le_two {k : ℕ} (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card ≤ 2 := by
  classical
  by_contra hle
  have htwo : 2 < (signSeqDoorSet s).card := by omega
  rcases Finset.two_lt_card.mp htwo with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have hdoor_a : signSeqDoor s a := by simpa [signSeqDoorSet] using ha
  have hdoor_b : signSeqDoor s b := by simpa [signSeqDoorSet] using hb
  have hdoor_c : signSeqDoor s c := by simpa [signSeqDoorSet] using hc
  have hcontr_pair :
      ∀ {x y : Fin (k + 1)}, signSeqDoor s x → signSeqDoor s y → x < y →
        x.val + 1 < y.val → False := by
    intro x y hx hy hxy hgap
    have hle' := signSeqDoor_nonadjacent_false hx hy hxy
    omega
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_trichotomy c a with hca | hcaeq | haclt
    · exact hcontr_pair hdoor_c hdoor_b (lt_trans hca hablt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hca
        have h2 := Fin.lt_iff_val_lt_val.mp hablt
        omega)
    · exact hac hcaeq.symm
    · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
      · exact hcontr_pair hdoor_a hdoor_b hablt (by
          have h1 := Fin.lt_iff_val_lt_val.mp haclt
          have h2 := Fin.lt_iff_val_lt_val.mp hcb
          omega)
      · exact hbc hcbeq.symm
      · exact hcontr_pair hdoor_a hdoor_c (lt_trans hablt hbclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hablt
          have h2 := Fin.lt_iff_val_lt_val.mp hbclt
          omega)
  · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
    · exact hcontr_pair hdoor_c hdoor_a (lt_trans hcb hbalt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hcb
        have h2 := Fin.lt_iff_val_lt_val.mp hbalt
        omega)
    · exact hbc hcbeq.symm
    · rcases lt_trichotomy c a with hca | hcaeq | haclt
      · exact hcontr_pair hdoor_b hdoor_a hbalt (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbclt
          have h2 := Fin.lt_iff_val_lt_val.mp hca
          omega)
      · exact hac hcaeq.symm
      · exact hcontr_pair hdoor_b hdoor_c (lt_trans hbalt haclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbalt
          have h2 := Fin.lt_iff_val_lt_val.mp haclt
          omega)

theorem signSeqDoor_next_of_not_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hnot : ¬ signSeqBad s i) (hik : i.val < k) :
    signSeqDoor s ⟨i.val + 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    have hjv : j.val < i.val + 1 := Fin.lt_iff_val_lt_val.mp hj
    by_cases hji : j < i
    · exact hi.1 j hji
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : i.val ≤ j.val := by
          exact le_of_not_gt (by
            intro hv
            exact hji (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hnot
  · intro j hj
    apply hi.2
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : i.val + 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
      omega)

theorem signSeqDoor_prev_of_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hbad : signSeqBad s i) (hi0 : 0 < i.val) :
    signSeqDoor s ⟨i.val - 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    apply hi.1
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : j.val < i.val - 1 := Fin.lt_iff_val_lt_val.mp hj
      omega)
  · intro j hj
    have hjv : i.val - 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
    by_cases hij : i < j
    · exact hi.2 j hij
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : j.val ≤ i.val := by
          exact le_of_not_gt (by
            intro hv
            exact hij (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hbad

theorem signSeqDoorSet_eq_singleton_last_of_altPos {k : ℕ}
    {s : Fin (k + 1) → Bool} (hpos : signSeqAltPos s) :
    signSeqDoorSet s = {Fin.last k} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hilast : i = Fin.last k
    · simp [hilast]
    · have hlt : i < Fin.last k := Fin.lt_last_iff_ne_last.mpr hilast
      have hsuf := hdoor.2 (Fin.last k) hlt
      have hposlast := hpos (Fin.last k)
      have hbad : decide (Even (Fin.last k).val) = !decide (Even (Fin.last k).val) :=
        hposlast.symm.trans hsuf
      cases decide (Even (Fin.last k).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (Fin.last k) := by
      constructor
      · intro j _hj
        exact hpos j
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.le_last j)) hj)
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDoorSet_eq_singleton_zero_of_altNeg {k : ℕ}
    {s : Fin (k + 1) → Bool} (hneg : signSeqAltNeg s) :
    signSeqDoorSet s = {0} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hlt : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have hpref := hdoor.1 0 hlt
      have hneg0 := hneg 0
      have hbad : decide (Even (0 : Fin (k + 1)).val) =
          !decide (Even (0 : Fin (k + 1)).val) :=
        hpref.symm.trans hneg0
      cases decide (Even (0 : Fin (k + 1)).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (0 : Fin (k + 1)) := by
      constructor
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
      · intro j _hj
        exact hneg j
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDoorSet_card_eq_zero_or_one_or_two {k : ℕ}
    (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card = 0 ∨ (signSeqDoorSet s).card = 1 ∨
      (signSeqDoorSet s).card = 2 := by
  have hle := signSeqDoorSet_card_le_two s
  omega

theorem signSeqDeletionParity {k : ℕ} (s : Fin (k + 1) → Bool) :
    Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s := by
  classical
  constructor
  · intro hodd
    have hle := signSeqDoorSet_card_le_two s
    have hcard : (signSeqDoorSet s).card = 1 := by
      rcases hodd with ⟨a, ha⟩
      omega
    have hposcard : 0 < (signSeqDoorSet s).card := by omega
    obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp hposcard
    have hi : signSeqDoor s i := by simpa [signSeqDoorSet] using hi_mem
    by_cases hk0 : k = 0
    · subst k
      fin_cases i
      by_cases hs0 : s 0 = true
      · left
        intro j
        fin_cases j
        simpa [hs0]
      · right
        have hsfalse : s 0 = false := by
          cases h : s 0 <;> simp [h] at hs0 ⊢
        intro j
        fin_cases j
        simpa [hsfalse]
    · have hend : i = 0 ∨ i = Fin.last k := by
        by_contra hend
        push_neg at hend
        have hi0v : 0 < i.val := Fin.pos_iff_ne_zero.mpr hend.1
        have hikv : i.val < k := by
          have hilast : i ≠ Fin.last k := hend.2
          have hlelast : i ≤ Fin.last k := Fin.le_last i
          have hneval : i.val ≠ k := by
            intro hv
            exact hilast (Fin.ext (by simpa [Fin.last] using hv))
          have hleval : i.val ≤ k := Fin.le_iff_val_le_val.mp hlelast
          omega
        by_cases hbad : signSeqBad s i
        · let p : Fin (k + 1) := ⟨i.val - 1, by omega⟩
          have hp : signSeqDoor s p := signSeqDoor_prev_of_bad hi hbad hi0v
          have hp_mem : p ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hp
          have hp_ne : p ≠ i := by
            intro hpi
            have hv := congrArg Fin.val hpi
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hp_mem, i, hi_mem, hp_ne⟩
          omega
        · let q : Fin (k + 1) := ⟨i.val + 1, by omega⟩
          have hq : signSeqDoor s q := signSeqDoor_next_of_not_bad hi hbad hikv
          have hq_mem : q ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hq
          have hq_ne : q ≠ i := by
            intro hqi
            have hv := congrArg Fin.val hqi
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hq_mem, i, hi_mem, hq_ne⟩
          omega
      rcases hend with hi0 | hilast
      · right
        intro j
        subst i
        by_cases hj0 : j = 0
        · subst j
          by_contra hnot
          let q : Fin (k + 1) := ⟨1, by omega⟩
          have hnext : signSeqDoor s q := by
            have hkpos : 0 < k := by omega
            have hzero : (0 : Fin (k + 1)).val < k := by simpa using hkpos
            exact signSeqDoor_next_of_not_bad hi
              (by
                intro hb
                exact hnot hb) hzero
          have hnext_mem : q ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hnext
          have hne : q ≠ 0 := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hnext_mem, 0, hi_mem, hne⟩
          omega
        · have hlt : (0 : Fin (k + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
          exact hi.2 j hlt
      · left
        intro j
        subst i
        by_cases hjlast : j = Fin.last k
        · subst j
          by_contra hnot
          let p : Fin (k + 1) := ⟨k - 1, by omega⟩
          have hprev : signSeqDoor s p := by
            exact signSeqDoor_prev_of_bad hi
              ((signSeq_bad_iff_not_altPos s (Fin.last k)).mpr hnot)
              (by simp [Fin.last]; omega)
          have hprev_mem : p ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hprev
          have hne : p ≠ Fin.last k := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hprev_mem, Fin.last k, hi_mem, hne⟩
          omega
        · have hlt : j < Fin.last k := Fin.lt_last_iff_ne_last.mpr hjlast
          exact hi.1 j hlt
  · intro h
    rcases h with hpos | hneg
    · rw [signSeqDoorSet_eq_singleton_last_of_altPos hpos]
      simp
    · rw [signSeqDoorSet_eq_singleton_zero_of_altNeg hneg]
      simp

/-! ### Sorted label-sequence deletion parity -/

noncomputable def labelSeqSet {k m : ℕ} (L : Fin k → SignedLabel m) :
    Finset (SignedLabel m) :=
  Finset.univ.image L

def IsAltPosLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingLabelSetOf idx

def IsAltNegLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingNegLabelSetOf idx

noncomputable instance isAltPosLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltPosLabelSeq L) := by
  classical
  unfold IsAltPosLabelSeq
  infer_instance

noncomputable instance isAltNegLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltNegLabelSeq L) := by
  classical
  unfold IsAltNegLabelSeq
  infer_instance

theorem sortedLabelSeq_isAltPos_iff_signSeqAltPos {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltPosLabelSeq L ↔ signSeqAltPos sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : alternatingLabelOf eta b ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]

theorem sortedLabelSeq_isAltNeg_iff_signSeqAltNeg {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltNegLabelSeq L ↔ signSeqAltNeg sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingNegLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : (alternatingLabelOf eta b).neg ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingNegLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingNegLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]

noncomputable def labelSeqAltPosDeletionSet {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun j => IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a))

theorem sortedLabelSeq_deletion_iff_signSeqDoor {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a })
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔ signSeqDoor sgn j := by
  have hidx_del : StrictMono fun a : Fin k => idx (j.succAbove a) :=
    hidx.comp (Fin.strictMono_succAbove j)
  have hL_del :
      ∀ a : Fin k,
        (fun a : Fin k => L (j.succAbove a)) a =
          { positive := (fun a : Fin k => sgn (j.succAbove a)) a,
            index := (fun a : Fin k => idx (j.succAbove a)) a } := by
    intro a
    exact hL (j.succAbove a)
  exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx_del hL_del).trans
    (signSeqDoor_iff_remove_altPos sgn j).symm

theorem sortedLabelSeq_deletionParity {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  have hset : labelSeqAltPosDeletionSet L = signSeqDoorSet sgn := by
    ext j
    simp [labelSeqAltPosDeletionSet, signSeqDoorSet,
      sortedLabelSeq_deletion_iff_signSeqDoor hidx hL j]
  rw [hset, signSeqDeletionParity]
  constructor
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mpr hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mpr hneg
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mp hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mp hneg

theorem IsAltPos_iff_labelSeq {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltPos label sigma ↔ IsAltPosLabelSeq (fun a : Fin k => label (sigma a)) := by
  rfl

theorem IsAltNeg_iff_labelSeq {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltNeg label sigma ↔ IsAltNegLabelSeq (fun a : Fin k => label (sigma a)) := by
  rfl

noncomputable def simplexAltPosDeletionSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin (k + 1) → NonzeroSignedSubset n) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun j => IsAltPos label (fun a : Fin k => sigma (j.succAbove a))

theorem simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin (k + 1) → NonzeroSignedSubset n) :
    simplexAltPosDeletionSet label sigma =
      labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => label (sigma a)) := by
  classical
  ext j
  simp [simplexAltPosDeletionSet, labelSeqAltPosDeletionSet, IsAltPos_iff_labelSeq]

theorem sortedSimplex_deletionParity {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin (k + 1) → NonzeroSignedSubset n}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool}
    (hlabel :
      ∀ a : Fin (k + 1),
        label (sigma a) = { positive := sgn a, index := idx a }) :
    Odd (simplexAltPosDeletionSet label sigma).card ↔
      IsAltPos label sigma ∨ IsAltNeg label sigma := by
  rw [simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet]
  have hseq :=
    sortedLabelSeq_deletionParity (idx := idx) hidx
      (sgn := sgn) (L := fun a : Fin (k + 1) => label (sigma a)) hlabel
  exact hseq.trans (or_congr IsAltPos_iff_labelSeq.symm IsAltNeg_iff_labelSeq.symm)

theorem labelSeqSet_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    labelSeqSet (fun a : Fin k => L (e a)) = labelSeqSet L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e a, Finset.mem_univ _, ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e.symm a, Finset.mem_univ _, by simpa using ha⟩

theorem IsAltPosLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltPosLabelSeq L := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem IsAltNegLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltNegLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltNegLabelSeq L := by
  unfold IsAltNegLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem labelSeqSet_delete_comp_perm_eq {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (e (j.succAbove a))) =
      labelSeqSet (fun a : Fin k => L ((e j).succAbove a)) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    have hne : e (j.succAbove a) ≠ e j :=
      e.injective.ne (Fin.succAbove_ne j a)
    rcases Fin.exists_succAbove_eq hne with ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, by simpa [← hb] using ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨b, _hb, hb⟩
    let y : Fin (k + 1) := (e j).succAbove b
    have hne_pre : e.symm y ≠ j := by
      intro hy
      have hy' : y = e j := by
        calc
          y = e (e.symm y) := by simp [y]
          _ = e j := by rw [hy]
      exact Fin.succAbove_ne (e j) b (by simpa [y] using hy')
    rcases Fin.exists_succAbove_eq hne_pre with ⟨a, ha⟩
    have hey : e (j.succAbove a) = y := by
      rw [ha]
      simp [y]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simpa [y, ← hey] using hb⟩

theorem IsAltPosLabelSeq_delete_comp_perm_iff {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e (j.succAbove a))) ↔
      IsAltPosLabelSeq (fun a : Fin k => L ((e j).succAbove a)) := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_delete_comp_perm_eq L e j]

theorem IsAltNegLabelSeq_delete_comp_perm_iff {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    IsAltNegLabelSeq (fun a : Fin k => L (e (j.succAbove a))) ↔
      IsAltNegLabelSeq (fun a : Fin k => L ((e j).succAbove a)) := by
  unfold IsAltNegLabelSeq
  rw [labelSeqSet_delete_comp_perm_eq L e j]

theorem labelSeqAltPosDeletionSet_comp_perm_card {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1))) :
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
      (labelSeqAltPosDeletionSet L).card := by
  classical
  have hmap :
      (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding =
        labelSeqAltPosDeletionSet L := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      subst j
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        simpa [labelSeqAltPosDeletionSet] using hi
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      simpa [labelSeqAltPosDeletionSet] using hiff.mp hi'
    · intro hj
      have hj' : IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj
      let i : Fin (k + 1) := e.symm j
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        apply hiff.mpr
        simpa [i] using hj'
      refine Finset.mem_map.mpr ⟨i, ?_, by simp [i]⟩
      simpa [labelSeqAltPosDeletionSet] using hi'
  calc
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
        ((labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding).card := by
          rw [Finset.card_map]
    _ = (labelSeqAltPosDeletionSet L).card := by rw [hmap]

theorem permutedSortedLabelSeq_deletionParity {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool}
    (hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  have hsorted :=
    sortedLabelSeq_deletionParity (idx := idx) hidx
      (sgn := sgn) (L := fun a : Fin (k + 1) => L (e a)) hLsort
  rw [labelSeqAltPosDeletionSet_comp_perm_card L e] at hsorted
  exact hsorted.trans
    (or_congr (IsAltPosLabelSeq_comp_perm L e) (IsAltNegLabelSeq_comp_perm L e))

theorem permutedSortedSimplex_deletionParity {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin (k + 1) → NonzeroSignedSubset n}
    (e : Equiv.Perm (Fin (k + 1)))
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool}
    (hlabelSort :
      ∀ a : Fin (k + 1),
        label (sigma (e a)) = { positive := sgn a, index := idx a }) :
    Odd (simplexAltPosDeletionSet label sigma).card ↔
      IsAltPos label sigma ∨ IsAltNeg label sigma := by
  rw [simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet]
  have hseq :=
    permutedSortedLabelSeq_deletionParity
      (L := fun a : Fin (k + 1) => label (sigma a)) e hidx hlabelSort
  exact hseq.trans (or_congr IsAltPos_iff_labelSeq.symm IsAltNeg_iff_labelSeq.symm)

def NoOppositeLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∀ i j : Fin k, L i ≠ (L j).neg

theorem signedLabel_eq_or_eq_neg_of_index_eq {m : ℕ} (A B : SignedLabel m)
    (hidx : A.index = B.index) : A = B ∨ A = B.neg := by
  cases A with
  | mk apos aidx =>
      cases B with
      | mk bpos bidx =>
          dsimp at hidx
          subst aidx
          cases apos <;> cases bpos <;>
            simp [SignedLabel.neg]

theorem labelSeq_index_injective_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin k → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Function.Injective fun i : Fin k => (L i).index := by
  intro i j hidx
  rcases signedLabel_eq_or_eq_neg_of_index_eq (L i) (L j) hidx with h | h
  · exact hinj h
  · exact False.elim (hno i j h)

theorem labelSeq_deletionParity_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  let idxOf : Fin (k + 1) → Fin m := fun a => (L a).index
  let e : Equiv.Perm (Fin (k + 1)) := Tuple.sort idxOf
  let idx : Fin (k + 1) → Fin m := fun a => idxOf (e a)
  let sgn : Fin (k + 1) → Bool := fun a => (L (e a)).positive
  have hidxOf : Function.Injective idxOf :=
    labelSeq_index_injective_of_injective_of_noOpposite
      (L := L) hinj hno
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    apply e.injective
    exact hidxOf hab
  have hidx_mono : Monotone idx := by
    exact Tuple.monotone_sort idxOf
  have hidx : StrictMono idx :=
    hidx_mono.strictMono_of_injective hidx_inj
  have hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a } := by
    intro a
    apply SignedLabel.ext <;> rfl
  exact permutedSortedLabelSeq_deletionParity
    (L := L) e (idx := idx) hidx (sgn := sgn) hLsort

/-! ## Ky Fan parity statement on the non-degenerate range -/

/-- Ky Fan parity in the range actually used by Tucker: `r ≥ 1`, `m ≥ r`.
It counts positive-first alternating maximal chains of `K_r`; this is not the
degenerate `Fin r → Fin (r-1)` full-chain pigeonhole setup. -/
def KyFanParityStatement (r m : ℕ) : Prop :=
  1 ≤ r →
    r ≤ m →
      ∀ label : NonzeroSignedSubset r → SignedLabel m,
        (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
            Odd (positiveAlternatingPrefixLabelChains label).card

theorem alternatingPrefixLabelChains_card_one_any {m : ℕ}
    (label : NonzeroSignedSubset 1 → SignedLabel m) :
    (alternatingPrefixLabelChains label).card = 2 := by
  classical
  have huniv : alternatingPrefixLabelChains label = (Finset.univ : Finset (SignedPermutation 1)) := by
    ext P
    simp only [Finset.mem_univ, iff_true]
    change P ∈ positiveAlternatingPrefixLabelChains label ∪
      negativeAlternatingPrefixLabelChains label
    rw [Finset.mem_union]
    have hstrict : StrictMono fun i : Fin 1 => (label (P.prefixChain i)).index := by
      intro a b hab
      fin_cases a
      fin_cases b
      omega
    cases h : (label (P.prefixChain 0)).positive
    · right
      have hneg : NegativeAlternatingPrefixLabels label P := by
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      simpa only [negativeAlternatingPrefixLabelChains, Finset.mem_filter,
        Finset.mem_univ, true_and] using hneg
    · left
      have hpos : PositiveAlternatingPrefixLabels label P := by
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      simpa only [positiveAlternatingPrefixLabelChains, Finset.mem_filter,
        Finset.mem_univ, true_and] using hpos
  rw [huniv]
  calc
    (Finset.univ : Finset (SignedPermutation 1)).card =
        Fintype.card (SignedPermutation 1) := by
      simp
    _ = Fintype.card (Equiv.Perm (Fin 1) × (Fin 1 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 1)
    _ = 2 := by simp

/-- Base case of the non-degenerate Ky Fan parity statement: for `r = 1` and
any nonempty label set, the two antipodal vertices have opposite signs, hence
exactly one positive-first chain. -/
theorem kyFanParityStatement_one {m : ℕ} (_hm : 1 ≤ m) :
    KyFanParityStatement 1 m := by
  intro _hr _hm label hantipodal _hno
  have halt := alternatingPrefixLabelChains_card_one_any label
  have htwice := alternatingPrefixLabelChains_card (n := 1) (m := m) (by omega) label hantipodal
  rw [halt] at htwice
  have hpos : (positiveAlternatingPrefixLabelChains label).card = 1 := by
    omega
  rw [hpos]
  exact odd_one

theorem equatorRestrictedLabel_positiveAlternating_odd {d : ℕ}
    (hd : 1 ≤ d) (hKy : KyFanParityStatement d d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (positiveAlternatingPrefixLabelChains (equatorRestrictedLabel label)).card :=
  hKy hd le_rfl (equatorRestrictedLabel label)
    (equatorRestrictedLabel_antipodal hantipodal)
    (equatorRestrictedLabel_noComplementary hno)

/-- A `d`-vertex ridge whose labels are exactly the label set `A`.  In the
Tucker reduction `d = n - 1`, so this is the dim-`(n-2)` simplex, not a full
`n`-vertex chain. -/
def AlternatingLabelSetARidge {d n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel d)
    (rho : Fin d → NonzeroSignedSubset n) : Prop :=
  (∀ i j, i < j → SignedSubset.Le (rho i).1 (rho j).1) ∧
    Function.Injective rho ∧
      ∀ k : Fin d, label (rho k) = alternatingLabel k

/-- After deleting `j` from a `(d+1)`-vertex sigma, every label in `A` still
appears.  Since exactly `d` vertices remain, this is the label-set-`A` door
condition used in the deletion count. -/
def SigmaDeletionHasAlternatingLabelSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) (j : Fin (d + 1)) : Prop :=
  ∀ a : Fin d, ∃ t : Fin (d + 1), t ≠ j ∧ sigmaLabel t = alternatingLabel a

/-- The door set of a sigma: deletions that leave the alternating label set `A`. -/
noncomputable def sigmaDoorSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) : Finset (Fin (d + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSet sigmaLabel j

/-- The parameterized deletion condition: deleting `j` leaves the alternating
label set determined by `idx`. -/
def SigmaDeletionHasAlternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) (j : Fin (r + 1)) : Prop :=
  ∀ a : Fin r, ∃ t : Fin (r + 1), t ≠ j ∧
    sigmaLabel t = alternatingLabelOf idx a

/-- Door set for a fixed increasing index set. -/
noncomputable def sigmaDoorSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) : Finset (Fin (r + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j

theorem sigmaDeletionHasAlternatingLabelSetOf_extra {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra := by
  intro a
  exact ⟨extra.succAbove a, Fin.succAbove_ne extra a, hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel (extra.succAbove k) := by
  intro a
  by_cases ha : a = k
  · subst a
    exact ⟨extra, Fin.ne_succAbove extra k, hextra⟩
  · exact ⟨extra.succAbove a, by
      intro h
      exact ha (Fin.succAbove_right_injective h), hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      j = extra ∨ j = extra.succAbove k := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact Or.inl hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      by_cases hak : a = k
      · subst a
        exact Or.inr ha.symm
      · have hmissing := hdoor a
        rcases hmissing with ⟨t, htne, htlabel⟩
        by_cases htextra : t = extra
        · subst t
          rw [hextra] at htlabel
          exact False.elim (hak ((alternatingLabelOf_inj hidx).mp htlabel).symm)
        · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
          rw [← hb, hridge b] at htlabel
          have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
          exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    rcases h with rfl | rfl
    · exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge
    · exact sigmaDeletionHasAlternatingLabelSetOf_duplicate hridge hextra

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_opposite {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = (alternatingLabelOf idx k).neg) (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        rw [hextra] at htlabel
        exact False.elim (alternatingLabelOf_neg_ne hidx k a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge

theorem sigmaDoorSetOf_card_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  have hset :
      sigmaDoorSetOf idx sigmaLabel = {extra, extra.succAbove k} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_duplicate hidx hridge hextra j, eq_comm]
  rw [hset]
  exact Finset.card_pair (Fin.ne_succAbove extra k)

theorem sigmaDoorSetOf_card_opposite {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = (alternatingLabelOf idx k).neg) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_opposite hidx hridge hextra j]
  rw [hset]
  simp

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_not_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k)
    (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        exact False.elim (hnot a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge

theorem sigmaDoorSetOf_card_not_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_not_duplicate hidx hridge hnot j]
  rw [hset]
  simp

theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra t : Fin (r + 1)} {k : Fin r}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply (alternatingLabelOf_inj hidx).mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetOf idx ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetOf] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetOf idx).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = r := by
      simp [retained]
    simpa [alternatingLabelSetOf_card hidx, hretained] using himage_le
  have hEq : alternatingLabelSetOf idx = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_injOn {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
    (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetOf_card hidx]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door
      (idx := idx) hidx (extra := extra) (t := t) (k := k)
      hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := (alternatingLabelOf_inj hidx).mp
            (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSetOf] using hdoorExtra
      · simpa [sigmaDoorSetOf] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem sigmaDoorSetOf_card_not_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact hnot b hulabel
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSetOf] using hdoorExtra
  rw [hset]
  simp

theorem sigmaDoorSetOf_odd_iff_card_one_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Odd (sigmaDoorSetOf idx sigmaLabel).card ↔
      (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  by_cases hdup : ∃ k : Fin r, sigmaLabel extra = alternatingLabelOf idx k
  · rcases hdup with ⟨k, hk⟩
    have hcard :=
      sigmaDoorSetOf_card_duplicate_of_door
        (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) (k := k)
        hdoorExtra hk
    rw [hcard]
    simp
  · have hcard :=
      sigmaDoorSetOf_card_not_duplicate_of_door
        (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra)
        hdoorExtra (by intro k hk; exact hdup ⟨k, hk⟩)
    rw [hcard]
    simp

theorem labelSeqSet_delete_eq_erase_image {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
      (Finset.univ.erase j).image L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr
      ⟨j.succAbove a, by simp [Fin.succAbove_ne], ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    rcases Fin.exists_succAbove_eq htne with ⟨a, ha⟩
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, by simpa [← ha] using htlabel⟩

theorem SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {j : Fin (r + 1)} :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      alternatingLabelSetOf idx ⊆ (Finset.univ.erase j).image sigmaLabel := by
  classical
  constructor
  · intro hdoor x hx
    rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr
      ⟨t, by simp [htne], htlabel.trans ha⟩
  · intro hsub a
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
      simp [alternatingLabelSetOf]
    have himage := hsub hmem
    rcases Finset.mem_image.mp himage with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    exact ⟨t, htne, htlabel⟩

theorem IsAltPosLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltPosLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltNegLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltNegLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingNegLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {L : Fin (k + 1) → SignedLabel m}
    (horig : labelSeqSet L = alternatingLabelSetOf idx)
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔
      SigmaDeletionHasAlternatingLabelSetOf idx L j := by
  classical
  constructor
  · intro hdel
    rcases hdel with ⟨eta, heta, hdelSet⟩
    let retained : Finset (Fin (k + 1)) := Finset.univ.erase j
    have hret_eq_del :
        labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
          retained.image L := by
      simpa [retained] using labelSeqSet_delete_eq_erase_image L j
    have hret_subset :
        retained.image L ⊆ alternatingLabelSetOf idx := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
      have hxorig : x ∈ labelSeqSet L := by
        rw [← htlabel]
        simp [labelSeqSet]
      simpa [horig] using hxorig
    have hret_card : (retained.image L).card = k := by
      rw [← hret_eq_del, hdelSet, alternatingLabelSetOf_card heta.injective]
    have halt_card : (alternatingLabelSetOf idx).card = k :=
      alternatingLabelSetOf_card hidx.injective
    have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
      apply Finset.eq_of_subset_of_card_le hret_subset
      rw [hret_card, halt_card]
    exact SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image.mpr
      (by simpa [retained, hret_eq_alt])
  · intro hdoor
    refine ⟨idx, hidx, ?_⟩
    have himage :=
      sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
        (idx := idx) hidx.injective (sigmaLabel := L) (extra := j) hdoor
    rw [labelSeqSet_delete_eq_erase_image, himage]

theorem labelSeq_deletionParity_of_not_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hnot : ¬ Function.Injective L)
    (_hno : NoOppositeLabelSeq L) :
    Even (labelSeqAltPosDeletionSet L).card ∧
      ¬ IsAltPosLabelSeq L ∧ ¬ IsAltNegLabelSeq L := by
  classical
  have hnotAltPos : ¬ IsAltPosLabelSeq L := by
    intro h
    exact hnot h.injective
  have hnotAltNeg : ¬ IsAltNegLabelSeq L := by
    intro h
    exact hnot h.injective
  have heven : Even (labelSeqAltPosDeletionSet L).card := by
    by_cases hnonempty : (labelSeqAltPosDeletionSet L).Nonempty
    · rcases hnonempty with ⟨j0, hj0⟩
      have hdel0 :
          IsAltPosLabelSeq (fun a : Fin k => L (j0.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj0
      rcases hdel0 with ⟨idx, hidx, hdelSet⟩
      let retained : Finset (Fin (k + 1)) := Finset.univ.erase j0
      have hret_eq_del :
          labelSeqSet (fun a : Fin k => L (j0.succAbove a)) =
            retained.image L := by
        simpa [retained] using labelSeqSet_delete_eq_erase_image L j0
      have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
        rw [← hret_eq_del, hdelSet]
      have hret_subset_orig : retained.image L ⊆ labelSeqSet L := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
        rw [← htlabel]
        simp [labelSeqSet]
      have hcard_orig_le : (labelSeqSet L).card ≤ k := by
        have himage_le :
            (labelSeqSet L).card ≤ k + 1 := by
          simpa [labelSeqSet] using
            (Finset.card_image_le :
              (Finset.univ.image L).card ≤
                (Finset.univ : Finset (Fin (k + 1))).card)
        have hneq : (labelSeqSet L).card ≠ k + 1 := by
          intro hcard
          have hcard_image :
              (Finset.univ.image L).card =
                (Finset.univ : Finset (Fin (k + 1))).card := by
            simpa [labelSeqSet] using hcard
          have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin (k + 1))) :=
            (Finset.card_image_iff).mp hcard_image
          exact hnot (by
            intro a b hab
            exact hinjOn (by simp) (by simp) hab)
        omega
      have hcard_ret : (retained.image L).card = k := by
        rw [hret_eq_alt, alternatingLabelSetOf_card hidx.injective]
      have hcard_orig_ge : k ≤ (labelSeqSet L).card := by
        have hle : (retained.image L).card ≤ (labelSeqSet L).card :=
          Finset.card_le_card hret_subset_orig
        omega
      have hcard_orig : (labelSeqSet L).card = k := by
        omega
      have hret_eq_orig : retained.image L = labelSeqSet L := by
        apply Finset.eq_of_subset_of_card_le hret_subset_orig
        rw [hcard_orig, hcard_ret]
      have horig : labelSeqSet L = alternatingLabelSetOf idx := by
        rw [← hret_eq_orig, hret_eq_alt]
      have hdoor0 : SigmaDeletionHasAlternatingLabelSetOf idx L j0 := by
        exact (IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
          (idx := idx) hidx (L := L) horig j0).mp
          ⟨idx, hidx, hdelSet⟩
      have hextra_mem : L j0 ∈ alternatingLabelSetOf idx := by
        have hmem : L j0 ∈ labelSeqSet L := by
          simp [labelSeqSet]
        simpa [horig] using hmem
      rcases (by simpa [alternatingLabelSetOf] using hextra_mem) with ⟨a, ha⟩
      have hextra : L j0 = alternatingLabelOf idx a := ha.symm
      have hfixedCard :
          (sigmaDoorSetOf idx L).card = 2 :=
        sigmaDoorSetOf_card_duplicate_of_door
          (idx := idx) hidx.injective (sigmaLabel := L) (extra := j0)
          (k := a) hdoor0 hextra
      have hset :
          labelSeqAltPosDeletionSet L = sigmaDoorSetOf idx L := by
        ext j
        simp [labelSeqAltPosDeletionSet, sigmaDoorSetOf,
          IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
            (idx := idx) hidx (L := L) horig j]
      rw [hset, hfixedCard]
      simp
    · have hempty : labelSeqAltPosDeletionSet L = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simp
  exact ⟨heven, hnotAltPos, hnotAltNeg⟩

theorem labelSeq_deletionParity_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  by_cases hinj : Function.Injective L
  · exact labelSeq_deletionParity_of_injective_of_noOpposite
      (L := L) hinj hno
  · rcases labelSeq_deletionParity_of_not_injective_of_noOpposite
      (L := L) hinj hno with ⟨heven, hnotPos, hnotNeg⟩
    constructor
    · intro hodd
      rcases hodd with ⟨a, ha⟩
      rcases heven with ⟨b, hb⟩
      omega
    · intro h
      rcases h with hpos | hneg
      · exact False.elim (hnotPos hpos)
      · exact False.elim (hnotNeg hneg)

theorem simplex_deletionParity_of_noOpposite {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin (k + 1) → NonzeroSignedSubset n}
    (hno : NoOppositeLabelSeq (fun a : Fin (k + 1) => label (sigma a))) :
    Odd (simplexAltPosDeletionSet label sigma).card ↔
      IsAltPos label sigma ∨ IsAltNeg label sigma := by
  rw [simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet]
  exact (labelSeq_deletionParity_of_noOpposite
    (L := fun a : Fin (k + 1) => label (sigma a)) hno).trans
    (or_congr IsAltPos_iff_labelSeq.symm IsAltNeg_iff_labelSeq.symm)

theorem sigmaDeletionHasAlternatingLabelSet_extra {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel extra := by
  intro a
  exact ⟨extra.succAbove a, Fin.succAbove_ne extra a, hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSet_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel (extra.succAbove k) := by
  intro a
  by_cases ha : a = k
  · subst a
    exact ⟨extra, Fin.ne_succAbove extra k, hextra⟩
  · exact ⟨extra.succAbove a, by
      intro h
      exact ha (Fin.succAbove_right_injective h), hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSet_iff_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) (j : Fin (d + 1)) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel j ↔
      j = extra ∨ j = extra.succAbove k := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact Or.inl hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      by_cases hak : a = k
      · subst a
        exact Or.inr ha.symm
      · have hmissing := hdoor a
        rcases hmissing with ⟨t, htne, htlabel⟩
        by_cases htextra : t = extra
        · subst t
          rw [hextra] at htlabel
          exact False.elim (hak ((alternatingLabel_inj.mp htlabel).symm))
        · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
          rw [← hb, hridge b] at htlabel
          have hba : b = a := alternatingLabel_inj.mp htlabel
          exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    rcases h with rfl | rfl
    · exact sigmaDeletionHasAlternatingLabelSet_extra hridge
    · exact sigmaDeletionHasAlternatingLabelSet_duplicate hridge hextra

theorem sigmaDeletionHasAlternatingLabelSet_iff_opposite {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) (j : Fin (d + 1)) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        rw [hextra] at htlabel
        exact False.elim (alternatingLabel_neg_ne k a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := alternatingLabel_inj.mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSet_extra hridge

theorem sigmaDoorSet_card_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    (sigmaDoorSet sigmaLabel).card = 2 := by
  classical
  have hset :
      sigmaDoorSet sigmaLabel = {extra, extra.succAbove k} := by
    ext j
    simp [sigmaDoorSet, sigmaDeletionHasAlternatingLabelSet_iff_duplicate hridge hextra j,
      eq_comm]
  rw [hset]
  exact Finset.card_pair (Fin.ne_succAbove extra k)

theorem sigmaDoorSet_card_opposite {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSet, sigmaDeletionHasAlternatingLabelSet_iff_opposite hridge hextra j]
  rw [hset]
  simp

theorem sigmaDoorSet_card_eq_one_iff_extra_opposite {d : ℕ} (_hd : 0 < d)
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a) :
    (sigmaDoorSet sigmaLabel).card = 1 ↔
      ∃ k : Fin d, sigmaLabel extra = (alternatingLabel k).neg := by
  constructor
  · intro hcard
    rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
    · have htwo := sigmaDoorSet_card_duplicate (extra := extra)
        (k := (sigmaLabel extra).index) hridge hpos
      omega
    · exact ⟨(sigmaLabel extra).index, hneg⟩
  · rintro ⟨k, hk⟩
    exact sigmaDoorSet_card_opposite hridge hk

theorem sigma_opposite_extra_gives_complementary_labels {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    sigmaLabel extra = (sigmaLabel (extra.succAbove k)).neg := by
  rw [hridge k]
  exact hextra

/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/

theorem finset_card_filter_cast_zmod_two {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ZMod 2) =
      ∑ x ∈ s, if p x then (1 : ZMod 2) else 0 := by
  rw [Finset.sum_boole]

theorem fintype_card_subtype_cast_zmod_two {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (Fintype.card {x : α // p x} : ZMod 2) =
      ∑ x : α, if p x then (1 : ZMod 2) else 0 := by
  classical
  rw [← finset_card_filter_cast_zmod_two (Finset.univ : Finset α) p]
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (Fintype.card_subtype p)

/-- In a finite bipartite graph, the number of odd-degree vertices on the
left equals the number of odd-degree vertices on the right modulo two. -/
theorem bipartite_odd_degree_card_eq_mod_two
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by
  classical
  rw [fintype_card_subtype_cast_zmod_two, fintype_card_subtype_cast_zmod_two]
  calc
    (∑ r : R, if Odd (Fintype.card {s : S // edge r s}) then (1 : ZMod 2) else 0)
        = ∑ r : R, (Fintype.card {s : S // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hodd : Odd (Fintype.card {s : S // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two.symm
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {s : S // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two.symm
    _ = ∑ r : R, ∑ s : S, if edge r s then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [← fintype_card_subtype_cast_zmod_two (fun s : S => edge r s)]
    _ = ∑ s : S, ∑ r : R, if edge r s then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (Fintype.card {r : R // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          rw [← fintype_card_subtype_cast_zmod_two (fun r : R => edge r s)]
    _ = ∑ s : S, if Odd (Fintype.card {r : R // edge r s}) then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          by_cases hodd : Odd (Fintype.card {r : R // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {r : R // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two

theorem bipartite_boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge]
    (boundary : R → Prop) [DecidablePred boundary]
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hr :
      ∀ r : R,
        (Odd (Fintype.card {s : S // edge r s}) ↔ boundary r))
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  have hodd := bipartite_odd_degree_card_eq_mod_two (R := R) (S := S) edge
  have hR :
      Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} =
        Fintype.card {r : R // boundary r} := by
    exact Fintype.card_congr
      { toFun := fun r => ⟨r.1, (hr r.1).mp r.2⟩
        invFun := fun r => ⟨r.1, (hr r.1).mpr r.2⟩
        left_inv := by intro r; cases r; rfl
        right_inv := by intro r; cases r; rfl }
  have hS :
      Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} =
        Fintype.card {s : S // topOdd s} := by
    exact Fintype.card_congr
      { toFun := fun s => ⟨s.1, (hs s.1).mp s.2⟩
        invFun := fun s => ⟨s.1, (hs s.1).mpr s.2⟩
        left_inv := by intro s; cases s; rfl
        right_inv := by intro s; cases s; rfl }
  simpa [hR, hS] using hodd

/-- A checked, non-degenerate package for the codimension-one rho degree in
the upper hemisphere.  `R` is the finite type of actual `(r-2)`-ridges and `S`
the finite type of upper top simplices incident to them; `nonempty_R` records
that the ridge side has not collapsed to an empty type. -/
structure RhoDegreeManifoldData (R S : Type*) [Fintype R] [Fintype S] where
  edge : R → S → Prop
  edge_decidable : DecidableRel edge
  boundary : R → Prop
  boundary_decidable : DecidablePred boundary
  nonempty_R : Nonempty R
  degree_card :
    ∀ r : R,
      Fintype.card {s : S // edge r s} = if boundary r then 1 else 2

namespace RhoDegreeManifoldData

attribute [instance] edge_decidable boundary_decidable

theorem odd_degree_iff_boundary
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S) (r : R) :
    Odd (Fintype.card {s : S // D.edge r s}) ↔ D.boundary r := by
  rw [D.degree_card r]
  by_cases hb : D.boundary r <;> simp [hb]

theorem boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // D.boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  exact bipartite_boundary_top_parity D.edge D.boundary topOdd
    (D.odd_degree_iff_boundary) hs

end RhoDegreeManifoldData

/-- The sigma-degree fact used in the final Tucker reduction: once the ridge
labels are exactly `A`, a one-door top simplex has an extra label opposite to
one ridge label. -/
theorem sigmaDoorSet_card_one_gives_complementary_labels {d : ℕ} (hd : 0 < d)
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ k : Fin d,
      sigmaLabel extra = (sigmaLabel (extra.succAbove k)).neg := by
  rcases (sigmaDoorSet_card_eq_one_iff_extra_opposite hd hridge).mp hcard with ⟨k, hk⟩
  exact ⟨k, sigma_opposite_extra_gives_complementary_labels hridge hk⟩

/-- Final local reduction from a one-door `σ` in the label-set-`A` graph to
the same-index, opposite-sign pair on that chain. -/
theorem sigmaDoorSet_card_one_gives_chain_complementary_pair {d : ℕ} (hd : 0 < d)
    {sigma : Fin (d + 1) → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, label (sigma (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (sigma i))).card = 1) :
    ∃ i j : Fin (d + 1), i ≠ j ∧
      (label (sigma i)).index = (label (sigma j)).index ∧
      (label (sigma i)).positive ≠ (label (sigma j)).positive := by
  obtain ⟨k, hk⟩ :=
    sigmaDoorSet_card_one_gives_complementary_labels (d := d) hd
      (sigmaLabel := fun i => label (sigma i)) (extra := extra) hridge hcard
  refine ⟨extra, extra.succAbove k, Fin.ne_succAbove extra k, ?_, ?_⟩
  · have hidx := congrArg SignedLabel.index hk
    simpa [SignedLabel.neg] using hidx
  · have hpos := congrArg SignedLabel.positive hk
    cases h₁ : (label (sigma extra)).positive <;>
      cases h₂ : (label (sigma (extra.succAbove k))).positive <;>
        simp [SignedLabel.neg, h₁, h₂] at hpos ⊢

theorem unordered_chain_complementary_pair_order {N d : ℕ}
    {sigma : Fin N → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {i j : Fin N}
    (hij : i ≠ j)
    (hidx : (label (sigma i)).index = (label (sigma j)).index)
    (hsign : (label (sigma i)).positive ≠ (label (sigma j)).positive) :
    ∃ a b : Fin N, a < b ∧
      (label (sigma a)).index = (label (sigma b)).index ∧
      (label (sigma a)).positive ≠ (label (sigma b)).positive := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hidx, hsign⟩
  · exact ⟨j, i, hgt, hidx.symm, hsign.symm⟩

theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair {d : ℕ} (hd : 0 < d)
    {sigma : Fin (d + 1) → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, label (sigma (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (sigma i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (sigma i)).index = (label (sigma j)).index ∧
      (label (sigma i)).positive ≠ (label (sigma j)).positive := by
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_chain_complementary_pair (d := d) hd hridge hcard
  exact unordered_chain_complementary_pair_order hij hidx hsign

theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {P : SignedPermutation (d + 1)} {extra : Fin (d + 1)}
    (hridge :
      ∀ a : Fin d, label (P.prefixChain (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (P.prefixChain i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive :=
  sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair
    (n := d + 1) (d := d) hd (sigma := fun i => P.prefixChain i)
    (label := label) (extra := extra) hridge hcard

theorem sigmaDeletionHasAlternatingLabelSet_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra t : Fin (d + 1)} {k : Fin d}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply alternatingLabel_inj.mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_image_eq {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetA d := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetA d ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetA] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetA d).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = d := by
      simp [retained]
    simpa [alternatingLabelSetA_card, hretained] using himage_le
  have hEq : alternatingLabelSetA d = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_injOn {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSet_retained_image_eq
    (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetA_card]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSet_card_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    (sigmaDoorSet sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
      (extra := extra) (t := t) (k := k) hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := alternatingLabel_inj.mp (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSet] using hdoorExtra
      · simpa [sigmaDoorSet] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem sigmaDoorSet_card_opposite_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact alternatingLabel_neg_ne k b (hextra.symm.trans hulabel)
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSet] using hdoorExtra
  rw [hset]
  simp

theorem sigmaDoorSet_odd_iff_card_one_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Odd (sigmaDoorSet sigmaLabel).card ↔ (sigmaDoorSet sigmaLabel).card = 1 := by
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · have hcard :=
      sigmaDoorSet_card_duplicate_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hpos
    rw [hcard]
    simp
  · have hcard :=
      sigmaDoorSet_card_opposite_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hneg
    rw [hcard]
    simp

theorem sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i ≠ j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  classical
  have hextra_mem : extra ∈ sigmaDoorSet sigmaLabel := by
    simpa [sigmaDoorSet] using hdoorExtra
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    have htdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
      sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
        (extra := extra) (t := t) (k := k) hdoorExtra hpos htne htlabel
    have ht_mem : t ∈ sigmaDoorSet sigmaLabel := by
      simpa [sigmaDoorSet] using htdoor
    have hle : (sigmaDoorSet sigmaLabel).card ≤ 1 := by omega
    have hteq : t = extra :=
      (Finset.card_le_one_iff.mp hle) ht_mem hextra_mem
    exact False.elim (htne hteq)
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    refine ⟨extra, t, htne.symm, ?_, ?_⟩
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hidx := congrArg SignedLabel.index hcomp
      simpa [SignedLabel.neg] using hidx
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hpos' := congrArg SignedLabel.positive hcomp
      cases h₁ : (sigmaLabel extra).positive <;>
        cases h₂ : (sigmaLabel t).positive <;>
          simp [SignedLabel.neg, h₁, h₂] at hpos' ⊢

theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door hdoorExtra hcard
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hidx, hsign⟩
  · exact ⟨j, i, hgt, hidx.symm, hsign.symm⟩

theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {P : SignedPermutation (d + 1)} {extra : Fin (d + 1)}
    (hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (P.prefixChain i)) extra)
    (hcard : (sigmaDoorSet (fun i => label (P.prefixChain i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive :=
  sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door
    (sigmaLabel := fun i => label (P.prefixChain i)) hdoorExtra hcard

namespace SignedPermutation

theorem ext_order_positive {n : ℕ} {P Q : SignedPermutation n}
    (horder : P.order = Q.order) (hpositive : P.positive = Q.positive) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq] at horder hpositive
  subst horder
  subst hpositive
  rfl

/-- Reindex the positions of a signed permutation, moving the signed atoms
together.  For adjacent swaps this is the second top simplex through a
punctured full flag. -/
def reindexPositions {n : ℕ} (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) :
    SignedPermutation n where
  order := τ.trans P.order
  positive := fun i => P.positive (τ i)

theorem reindexPositions_reindexPositions {n : ℕ}
    (P : SignedPermutation n) (τ υ : Equiv.Perm (Fin n)) :
    (P.reindexPositions τ).reindexPositions υ =
      P.reindexPositions (υ.trans τ) := by
  apply ext_order_positive
  · apply Equiv.ext
    intro i
    rfl
  · funext i
    rfl

theorem reindexPositions_swap_involutive {n : ℕ}
    (P : SignedPermutation n) (a b : Fin n) :
    (P.reindexPositions (Equiv.swap a b)).reindexPositions (Equiv.swap a b) = P := by
  rw [reindexPositions_reindexPositions]
  apply ext_order_positive
  · apply Equiv.ext
    intro i
    simp [reindexPositions]
  · funext i
    simp [reindexPositions]

theorem reindexPositions_swap_ne_self {n : ℕ}
    (P : SignedPermutation n) {a b : Fin n} (hab : a ≠ b) :
    P.reindexPositions (Equiv.swap a b) ≠ P := by
  intro h
  have horder := congrArg SignedPermutation.order h
  have hfun := congrArg (fun e : Equiv.Perm (Fin n) => e a) horder
  simp [reindexPositions] at hfun
  exact hab hfun.symm

/-- The successor of a non-last deleted rank, as an element of the same `Fin`
type. -/
def gapNext {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) : Fin (n + 1) :=
  ⟨gap.val + 1, by omega⟩

theorem gapNext_val {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (gapNext gap hgap).val = gap.val + 1 :=
  rfl

theorem reindexPositions_swap_gap_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    P.reindexPositions (Equiv.swap gap (gapNext gap hgap)) ≠ P := by
  apply P.reindexPositions_swap_ne_self
  intro h
  have hval := congrArg Fin.val h
  simp [gapNext] at hval

/-- Flip the sign introduced at one position, keeping the order fixed. -/
def flipSignAt {n : ℕ} (P : SignedPermutation n) (j : Fin n) : SignedPermutation n where
  order := P.order
  positive := fun i => if i = j then !P.positive i else P.positive i

theorem flipSignAt_involutive {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    (P.flipSignAt j).flipSignAt j = P := by
  apply ext_order_positive
  · rfl
  · funext i
    by_cases hij : i = j <;> simp [flipSignAt, hij]

theorem flipSignAt_ne_self {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    P.flipSignAt j ≠ P := by
  intro h
  have hpositive := congrArg SignedPermutation.positive h
  have hj := congrFun hpositive j
  cases hsign : P.positive j <;> simp [flipSignAt, hsign] at hj

theorem prefixSignedSubset_support {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).support =
      Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i := by
  ext x
  by_cases hpos : P.positive (P.order.symm x)
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]

theorem prefix_support_eq_order_image_Iic {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i) =
      (Finset.Iic i).map P.order.toEmbedding := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_map.mpr ⟨P.order.symm x, ?_, by simp⟩
    simpa using hx
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
    simpa using hj

theorem prefix_support_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i).card = i.val + 1 := by
  rw [prefix_support_eq_order_image_Iic P i, Finset.card_map]
  simp

theorem prefixSignedSubset_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).card = i.val + 1 := by
  have hsupport_card :
      (P.prefixSignedSubset i).support.card = (P.prefixSignedSubset i).card := by
    simp [SignedSubset.support, SignedSubset.card, prefixSignedSubset,
      Finset.card_union_of_disjoint (P.prefix_disjoint i)]
  rw [← hsupport_card, prefixSignedSubset_support, prefix_support_card]

theorem prefixChain_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixChain i).1.card = i.val + 1 :=
  P.prefixSignedSubset_card i

theorem prefixChain_card_lt_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    (P.prefixChain i).1.card < (P.prefixChain j).1.card := by
  rw [P.prefixChain_card i, P.prefixChain_card j]
  omega

theorem prefixChain_ne_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    P.prefixChain i ≠ P.prefixChain j := by
  intro h
  have hcard := congrArg (fun X : NonzeroSignedSubset n => X.1.card) h
  have hlt := P.prefixChain_card_lt_of_lt hij
  exact (ne_of_lt hlt) hcard

theorem prefixChain_injective {n : ℕ} (P : SignedPermutation n) :
    Function.Injective P.prefixChain := by
  intro i j hij
  by_cases h : i = j
  · exact h
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (P.prefixChain_ne_of_lt hlt hij).elim
    · exact (P.prefixChain_ne_of_lt hgt hij.symm).elim

theorem prefixChain_eq_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    P.prefixChain i = P.prefixChain j ↔ i = j := by
  constructor
  · intro h
    exact P.prefixChain_injective h
  · intro h
    rw [h]

theorem prefixChain_le_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 ↔ i ≤ j := by
  constructor
  · intro hle
    have hpos_le : (P.prefixChain i).1.pos.card ≤ (P.prefixChain j).1.pos.card :=
      Finset.card_le_card hle.1
    have hneg_le : (P.prefixChain i).1.neg.card ≤ (P.prefixChain j).1.neg.card :=
      Finset.card_le_card hle.2
    have hcard : (P.prefixChain i).1.card ≤ (P.prefixChain j).1.card := by
      simp [SignedSubset.card]
      omega
    rw [P.prefixChain_card i, P.prefixChain_card j] at hcard
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro hij
    exact P.prefixChain_le hij

theorem order_mem_prefixPos_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixPos j ↔ i ≤ j ∧ P.positive i := by
  simp [prefixPos]

theorem order_mem_prefixNeg_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixNeg j ↔ i ≤ j ∧ !P.positive i := by
  simp [prefixNeg]

theorem order_mem_prefix_support_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ (P.prefixSignedSubset j).support ↔ i ≤ j := by
  by_cases hpos : P.positive i
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]

theorem prefix_support_mem_order_iff {n : ℕ} (P : SignedPermutation n)
    (x : Fin n) (j : Fin n) :
    x ∈ (P.prefixSignedSubset j).support ↔ P.order.symm x ≤ j := by
  simpa using
    (order_mem_prefix_support_iff P (P.order.symm x) j :
      P.order (P.order.symm x) ∈ (P.prefixSignedSubset j).support ↔
        P.order.symm x ≤ j)

theorem order_positive_eq_of_prefixChain_eq_of_prev_eq {n : ℕ}
    (P Q : SignedPermutation n) (i : Fin n)
    (hcur : Q.prefixChain i = P.prefixChain i)
    (hprev :
      ∀ j : Fin n, j.val + 1 = i.val →
        Q.prefixChain j = P.prefixChain j) :
    Q.order i = P.order i ∧ Q.positive i = P.positive i := by
  let x : Fin n := Q.order i
  have hxQ : x ∈ (Q.prefixSignedSubset i).support := by
    simpa [x, prefixChain] using
      ((order_mem_prefix_support_iff Q i i).mpr le_rfl)
  have hsupport_cur :
      (Q.prefixSignedSubset i).support = (P.prefixSignedSubset i).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset n => X.1.support) hcur
  have hxP : x ∈ (P.prefixSignedSubset i).support := by
    simpa [hsupport_cur] using hxQ
  have hle : P.order.symm x ≤ i :=
    (prefix_support_mem_order_iff P x i).mp hxP
  have hnotlt : ¬ P.order.symm x < i := by
    intro hlt
    have hi_pos : 0 < i.val := by
      have hvlt := Fin.lt_iff_val_lt_val.mp hlt
      omega
    let ipred : Fin n := ⟨i.val - 1, by omega⟩
    have hipred_val : ipred.val + 1 = i.val := by
      dsimp [ipred]
      omega
    have hlePred : P.order.symm x ≤ ipred := by
      exact Fin.le_iff_val_le_val.mpr (by
        have hvlt := Fin.lt_iff_val_lt_val.mp hlt
        dsimp [ipred]
        omega)
    have hxPprev : x ∈ (P.prefixSignedSubset ipred).support :=
      (prefix_support_mem_order_iff P x ipred).mpr hlePred
    have hsupport_prev :
        (Q.prefixSignedSubset ipred).support =
          (P.prefixSignedSubset ipred).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.support)
          (hprev ipred hipred_val)
    have hxQprev : x ∈ (Q.prefixSignedSubset ipred).support := by
      simpa [hsupport_prev] using hxPprev
    have hqle : i ≤ ipred := by
      simpa [x] using (prefix_support_mem_order_iff Q x ipred).mp hxQprev
    have hvle := Fin.le_iff_val_le_val.mp hqle
    dsimp [ipred] at hvle
    omega
  have hsymm : P.order.symm x = i := le_antisymm hle (le_of_not_gt hnotlt)
  have horder : Q.order i = P.order i := by
    change x = P.order i
    simpa [x] using congrArg P.order hsymm
  have hsign : Q.positive i = P.positive i := by
    by_cases hqpos : Q.positive i
    · have hxQpos : x ∈ Q.prefixPos i := by
        simpa [x, order_mem_prefixPos_iff, hqpos]
      have hpos_cur : Q.prefixPos i = P.prefixPos i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hcur
      have hxPpos : P.order i ∈ P.prefixPos i := by
        simpa [x, horder, hpos_cur] using hxQpos
      have hppos : P.positive i := (order_mem_prefixPos_iff P i i).mp hxPpos |>.2
      simp [hqpos, hppos]
    · have hxQneg : x ∈ Q.prefixNeg i := by
        simpa [x, order_mem_prefixNeg_iff, hqpos]
      have hneg_cur : Q.prefixNeg i = P.prefixNeg i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hcur
      have hxPneg : P.order i ∈ P.prefixNeg i := by
        simpa [x, horder, hneg_cur] using hxQneg
      have hpneg : !P.positive i := (order_mem_prefixNeg_iff P i i).mp hxPneg |>.2
      cases hp : P.positive i <;> simp [hqpos, hp] at hpneg ⊢
  exact ⟨horder, hsign⟩

theorem positive_eq_of_order_eq_of_prefixChain_eq {n : ℕ}
    (P Q : SignedPermutation n) {i p j : Fin n}
    (horder : Q.order i = P.order p) (hij : i ≤ j) (hpj : p ≤ j)
    (hprefix : Q.prefixChain j = P.prefixChain j) :
    Q.positive i = P.positive p := by
  by_cases hqpos : Q.positive i
  · have hxQpos : Q.order i ∈ Q.prefixPos j := by
      simpa [order_mem_prefixPos_iff, hij, hqpos]
    have hpos_eq : Q.prefixPos j = P.prefixPos j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hprefix
    have hxPpos : P.order p ∈ P.prefixPos j := by
      simpa [horder, hpos_eq] using hxQpos
    have hppos : P.positive p := (order_mem_prefixPos_iff P p j).mp hxPpos |>.2
    simp [hqpos, hppos]
  · have hxQneg : Q.order i ∈ Q.prefixNeg j := by
      simpa [order_mem_prefixNeg_iff, hij, hqpos]
    have hneg_eq : Q.prefixNeg j = P.prefixNeg j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hprefix
    have hxPneg : P.order p ∈ P.prefixNeg j := by
      simpa [horder, hneg_eq] using hxQneg
    have hpneg : !P.positive p := (order_mem_prefixNeg_iff P p j).mp hxPneg |>.2
    cases hp : P.positive p <;> simp [hqpos, hp] at hpneg ⊢

theorem prefixPos_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixPos i = P.prefixPos i := by
  ext x
  simp [prefixPos, reindexPositions, hτ (P.order.symm x)]

theorem prefixNeg_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixNeg i = P.prefixNeg i := by
  ext x
  simp [prefixNeg, reindexPositions, hτ (P.order.symm x)]

theorem prefixSignedSubset_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixSignedSubset i = P.prefixSignedSubset i := by
  cases P with
  | mk order positive =>
      simp [prefixSignedSubset, prefixPos, prefixNeg, reindexPositions, hτ]

theorem prefixChain_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_reindexPositions_of_symm_le_iff τ i hτ

theorem swap_adjacent_symm_le_iff_of_ne_left {n : ℕ} {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    ∀ k : Fin n, (Equiv.swap a b).symm k ≤ i ↔ k ≤ i := by
  have habne : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  intro k
  by_cases hka : k = a
  · subst k
    have hswap : (Equiv.swap a b).symm a = b := by
      simp
    rw [hswap]
    constructor
    · intro h
      exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · intro h
      exact Fin.le_iff_val_le_val.mpr (by
        have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
        have hne : i.val ≠ a.val := by
          intro hval
          exact hi (Fin.ext hval)
        omega)
  · by_cases hkb : k = b
    · subst k
      have hswap : (Equiv.swap a b).symm b = a := by
        simp
      rw [hswap]
      constructor
      · intro h
        exact Fin.le_iff_val_le_val.mpr (by
          have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
          have hne : i.val ≠ a.val := by
            intro hval
            exact hi (Fin.ext hval)
          omega)
      · intro h
        exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · have hswap : (Equiv.swap a b).symm k = k := by
        simp [Equiv.swap_apply_def, hka, hkb]
      rw [hswap]

theorem prefixChain_reindexPositions_swap_adjacent_of_ne_left {n : ℕ}
    (P : SignedPermutation n) {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    (P.reindexPositions (Equiv.swap a b)).prefixChain i = P.prefixChain i :=
  P.prefixChain_reindexPositions_of_symm_le_iff (Equiv.swap a b) i
    (swap_adjacent_symm_le_iff_of_ne_left hab hi)

theorem prefixChain_reindexPositions_swap_gap_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (i : Fin n) :
    (P.reindexPositions (Equiv.swap gap (gapNext gap hgap))).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
  · exact gapNext_val gap hgap
  · exact Fin.succAbove_ne gap i

theorem prefixPos_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixPos i = P.prefixPos i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixPos, flipSignAt, hle, hne]
  · simp [prefixPos, flipSignAt, hle]

theorem prefixNeg_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixNeg i = P.prefixNeg i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixNeg, flipSignAt, hle, hne]
  · simp [prefixNeg, flipSignAt, hle]

theorem prefixSignedSubset_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixSignedSubset i = P.prefixSignedSubset i := by
  exact signedSubset_ext_pos_neg
    (P.prefixPos_flipSignAt_of_lt hij)
    (P.prefixNeg_flipSignAt_of_lt hij)

theorem prefixChain_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_flipSignAt_of_lt hij

theorem prefixChain_flipSignAt_last_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin n) :
    (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
      P.prefixChain ((Fin.last n).succAbove i) := by
  simpa [Fin.succAbove_last] using
    (P.prefixChain_flipSignAt_of_lt (j := Fin.last n) (Fin.castSucc_lt_last i))

end SignedPermutation

/-- Maximal chains lying in the upper hemisphere. -/
def UpperPrefixChain {n : ℕ} (P : SignedPermutation (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), UpperHemisphere (P.prefixChain i)

/-- A represented codimension-one ridge of the upper hemisphere is boundary
exactly when the deleted rank is the top rank and the last coordinate has not
appeared in the retained punctured flag. -/
def RepresentedUpperRidgeBoundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  gap = Fin.last n ∧ P.order.symm (Fin.last n) = Fin.last n

noncomputable instance representedUpperRidgeBoundary_decidable {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Decidable (RepresentedUpperRidgeBoundary P gap) := by
  classical
  exact inferInstance

/-- The second local top coface of a represented full-rank punctured flag in
the cross-polytope order complex: swap adjacent ranks when the missing rank is
internal, and flip the final inserted sign when the missing rank is top. -/
noncomputable def representedRidgePartner {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    SignedPermutation (n + 1) :=
  if hgap : gap.val < n then
    P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))
  else
    P.flipSignAt (Fin.last n)

theorem representedRidgePartner_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    representedRidgePartner P gap ≠ P := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap
  · simpa [hgap] using SignedPermutation.flipSignAt_ne_self P (Fin.last n)

theorem representedRidgePartner_deletion_eq {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (i : Fin n) :
    (representedRidgePartner P gap).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using
      P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using P.prefixChain_flipSignAt_last_succAbove i

theorem deletion_gap_eq_of_prefixChain_eq {d : ℕ} (hd : 0 < d)
    {P Q : SignedPermutation (d + 1)} {gap eta : Fin (d + 1)}
    (hdel :
      ∀ a : Fin d,
        Q.prefixChain (eta.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    eta = gap := by
  apply Fin.succAbove_left_injective
  funext a
  apply Fin.ext
  have hcard :=
    congrArg (fun X : NonzeroSignedSubset (d + 1) => X.1.card) (hdel a)
  have hcard' :
      (eta.succAbove a).val + 1 = (gap.succAbove a).val + 1 := by
    simpa [SignedPermutation.prefixChain_card] using hcard
  omega

theorem eq_or_flipSignAt_last_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain ((Fin.last n).succAbove a) =
          P.prefixChain ((Fin.last n).succAbove a)) :
    Q = P ∨ Q = P.flipSignAt (Fin.last n) := by
  have hprefix_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hatom_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hi
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_last i hi
    · intro j hj
      apply hprefix_ne_last
      intro hjlast
      have hivallast : i.val = n + 1 := by
        rw [← hj, hjlast]
        simp [Fin.last]
      exact Nat.ne_of_lt i.isLt hivallast
  have horder_last : Q.order (Fin.last n) = P.order (Fin.last n) := by
    let k : Fin (n + 1) := P.order.symm (Q.order (Fin.last n))
    by_cases hk : k = Fin.last n
    · change Q.order (Fin.last n) = P.order (Fin.last n)
      calc
        Q.order (Fin.last n) = P.order k := by
          dsimp [k]
          simp
        _ = P.order (Fin.last n) := congrArg P.order hk
    · have hkorder : Q.order k = P.order k := (hatom_ne_last k hk).1
      have hPk : P.order k = Q.order (Fin.last n) := by
        dsimp [k]
        simp
      have hQeq : Q.order k = Q.order (Fin.last n) := hkorder.trans hPk
      exact False.elim (hk (Q.order.injective hQeq))
  by_cases hlastSign : Q.positive (Fin.last n) = P.positive (Fin.last n)
  · left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        exact hlastSign
      · exact (hatom_ne_last i hi).2
  · right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        cases hq : Q.positive (Fin.last n) <;>
          cases hp : P.positive (Fin.last n) <;>
            simp [flipSignAt, hq, hp] at hlastSign ⊢
      · simp [flipSignAt, hi, (hatom_ne_last i hi).2]

theorem eq_or_reindex_swap_of_internal_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨
      Q = P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hnext_val : next.val = gap.val + 1 := rfl
  have hnext_ne_gap : next ≠ gap := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [next, SignedPermutation.gapNext] at hval
    omega
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hprefix_ne_gap :
      ∀ i : Fin (n + 1), i ≠ gap → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hprefix_next : Q.prefixChain next = P.prefixChain next :=
    hprefix_ne_gap next hnext_ne_gap
  have hatom_fixed :
      ∀ i : Fin (n + 1), i ≠ gap → i ≠ next →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hig hinext
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_gap i hig
    · intro j hj
      apply hprefix_ne_gap
      intro hjgap
      apply hinext
      apply Fin.ext
      rw [← hj, hjgap]
      dsimp [next, SignedPermutation.gapNext]
  let xgap : Fin (n + 1) := Q.order gap
  have hxQnext : xgap ∈ (Q.prefixSignedSubset next).support := by
    exact (prefix_support_mem_order_iff Q xgap next).mpr (by
      change Q.order.symm (Q.order gap) ≤ next
      simpa [xgap] using hgap_le_next)
  have hsupport_next :
      (Q.prefixSignedSubset next).support = (P.prefixSignedSubset next).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support) hprefix_next
  have hxPnext : xgap ∈ (P.prefixSignedSubset next).support := by
    simpa [hsupport_next] using hxQnext
  have hPgap_le_next : P.order.symm xgap ≤ next :=
    (prefix_support_mem_order_iff P xgap next).mp hxPnext
  have hnot_lt_gap : ¬ P.order.symm xgap < gap := by
    intro hlt
    let j : Fin (n + 1) := P.order.symm xgap
    have hjne : j ≠ gap := by
      intro hj
      exact (ne_of_lt hlt) hj
    have hxPj : xgap ∈ (P.prefixSignedSubset j).support := by
      exact (prefix_support_mem_order_iff P xgap j).mpr (by simp [j])
    have hsupport_j :
        (Q.prefixSignedSubset j).support = (P.prefixSignedSubset j).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support)
          (hprefix_ne_gap j hjne)
    have hxQj : xgap ∈ (Q.prefixSignedSubset j).support := by
      simpa [hsupport_j] using hxPj
    have hqle : gap ≤ j := by
      simpa [xgap, j] using (prefix_support_mem_order_iff Q xgap j).mp hxQj
    exact not_lt_of_ge hqle hlt
  have hgap_le_Pgap : gap ≤ P.order.symm xgap := le_of_not_gt hnot_lt_gap
  have hPgap_cases :
      P.order.symm xgap = gap ∨ P.order.symm xgap = next := by
    have hge := Fin.le_iff_val_le_val.mp hgap_le_Pgap
    have hle := Fin.le_iff_val_le_val.mp hPgap_le_next
    have hnextv : next.val = gap.val + 1 := by
      dsimp [next, SignedPermutation.gapNext]
    by_cases hv : (P.order.symm xgap).val = gap.val
    · left
      exact Fin.ext hv
    · right
      apply Fin.ext
      omega
  have horder_gap_cases : Q.order gap = P.order gap ∨ Q.order gap = P.order next := by
    rcases hPgap_cases with hsymm | hsymm
    · left
      change xgap = P.order gap
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order gap := congrArg P.order hsymm
    · right
      change xgap = P.order next
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order next := congrArg P.order hsymm
  rcases horder_gap_cases with hgapOrder | hgapOrder
  · have hnextOrder : Q.order next = P.order next := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hknext : k = next
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order next := congrArg P.order hknext
      · by_cases hkgap : k = gap
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order gap := hgapOrder
              _ = P.order k := by rw [hkgap]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap.symm (Q.order.injective hQeq))
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next hgap_le_next
        hprefix_next
    have hnextSign : Q.positive next = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl le_rfl hprefix_next
    left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        exact hgapOrder
      · by_cases hin : i = next
        · subst i
          exact hnextOrder
        · exact (hatom_fixed i hig hin).1
    · funext i
      by_cases hig : i = gap
      · subst i
        exact hgapSign
      · by_cases hin : i = next
        · subst i
          exact hnextSign
        · exact (hatom_fixed i hig hin).2
  · have hnextOrder : Q.order next = P.order gap := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hkgap : k = gap
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order gap := congrArg P.order hkgap
      · by_cases hknext : k = next
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order next := hgapOrder
              _ = P.order k := by rw [hknext]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap (Q.order.injective hQeq).symm)
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next le_rfl
        hprefix_next
    have hnextSign : Q.positive next = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl hgap_le_next
        hprefix_next
    right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapOrder, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextOrder, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).1]
          change P.order i = P.order ((Equiv.swap gap next) i)
          rw [hswap]
    · funext i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapSign, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextSign, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).2]
          change P.positive i = P.positive ((Equiv.swap gap next) i)
          rw [hswap]

theorem eq_or_representedRidgePartner_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨ Q = representedRidgePartner P gap := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · rcases eq_or_reindex_swap_of_internal_deletion_eq P Q gap hgap hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    rcases eq_or_flipSignAt_last_of_deletion_eq P Q hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)

theorem reindex_swap_gap_prefix_le_next {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    SignedSubset.Le
      ((P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain gap).1
      (P.prefixChain (SignedPermutation.gapNext gap hgap)).1 := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hswap_le :
      ∀ k : Fin (n + 1), (Equiv.swap gap next) k ≤ gap → k ≤ next := by
    intro k hk
    by_cases hkg : k = gap
    · subst k
      exact hgap_le_next
    · by_cases hkn : k = next
      · subst k
        exact le_rfl
      · have hswap : (Equiv.swap gap next) k = k := by
          simp [Equiv.swap_apply_def, hkg, hkn]
        exact le_trans (by simpa [hswap] using hk) hgap_le_next
  constructor
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixNeg, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩

theorem flipSignAt_last_upperPrefixChain_of_not_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hnot : ¬ RepresentedUpperRidgeBoundary P (Fin.last n)) :
    UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hcoord : P.order.symm (Fin.last n) ≠ Fin.last n := by
    intro hcoord
    exact hnot ⟨rfl, hcoord⟩
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    intro hneg
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
        SignedPermutation.flipSignAt, hcoord] using hneg)
  · have hlt : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have heq :
        (P.flipSignAt (Fin.last n)).prefixChain i = P.prefixChain i :=
      P.prefixChain_flipSignAt_of_lt (j := Fin.last n) hlt
    simpa [heq] using hP i

theorem flipSignAt_last_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hcoord : P.order.symm (Fin.last n) = Fin.last n) :
    ¬ UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hposLast : P.positive (Fin.last n) := by
    by_contra hpos
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg, hcoord] using hpos)
  intro hflip
  exact hflip (Fin.last n) (by
    simp [UpperHemisphere, SignedPermutation.prefixChain,
      SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
      SignedPermutation.flipSignAt, hcoord, hposLast])

theorem representedRidgePartner_upperPrefixChain {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hnot : ¬ RepresentedUpperRidgeBoundary P gap) :
    UpperPrefixChain (representedRidgePartner P gap) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · intro i
    by_cases hi : i = gap
    · subst i
      simpa [hgap] using
        upperHemisphere_of_le (reindex_swap_gap_prefix_le_next P gap hgap)
          (hP (SignedPermutation.gapNext gap hgap))
    · have heq :
          (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain i =
            P.prefixChain i := by
        apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
        · exact SignedPermutation.gapNext_val gap hgap
        · exact hi
      simpa [hgap, heq] using hP i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using flipSignAt_last_upperPrefixChain_of_not_boundary P hP hnot

theorem representedRidgePartner_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hb : RepresentedUpperRidgeBoundary P gap) :
    ¬ UpperPrefixChain (representedRidgePartner P gap) := by
  rcases hb with ⟨hgapEq, hcoord⟩
  subst gap
  unfold representedRidgePartner
  have hgapLast : ¬ (Fin.last n).val < n := by
    simp [Fin.last]
  simpa [hgapLast] using flipSignAt_last_not_upperPrefixChain_of_boundary P hP hcoord

theorem last_mem_prefixPos_of_upper_of_order_le {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin (n + 1))
    (hupper : UpperHemisphere (P.prefixChain i))
    (hle : P.order.symm (Fin.last n) ≤ i) :
    Fin.last n ∈ (P.prefixChain i).1.pos := by
  by_cases hpos : P.positive (P.order.symm (Fin.last n))
  · simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, hle, hpos]
  · have hneg : Fin.last n ∈ (P.prefixChain i).1.neg := by
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hle, hpos]
    exact False.elim (hupper hneg)

/-- The local upper cofaces of a represented rho.  Boundary ridges retain only
the upper coface; interior ridges retain both local cofaces. -/
noncomputable def representedUpperRidgeLocalCofaces {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Finset (SignedPermutation (n + 1)) :=
  by
    classical
    exact
      if RepresentedUpperRidgeBoundary P gap then
        {P}
      else
        {P, representedRidgePartner P gap}

theorem representedUpperRidgeLocalCofaces_card {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (representedUpperRidgeLocalCofaces P gap).card =
      if RepresentedUpperRidgeBoundary P gap then 1 else 2 := by
  classical
  by_cases hb : RepresentedUpperRidgeBoundary P gap
  · rw [representedUpperRidgeLocalCofaces, if_pos hb, if_pos hb]
    simp
  · rw [representedUpperRidgeLocalCofaces, if_neg hb, if_neg hb]
    exact Finset.card_pair (representedRidgePartner_ne_self P gap).symm

theorem representedUpperRidgeLocalCofaces_nonempty {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (representedUpperRidgeLocalCofaces P gap).Nonempty := by
  classical
  unfold representedUpperRidgeLocalCofaces
  by_cases hb : RepresentedUpperRidgeBoundary P gap
  · rw [if_pos hb]
    simp
  · rw [if_neg hb]
    simp

/-! ## Actual upper-hemisphere label-set-`A` graph -/

noncomputable instance signedSubset_fintype (n : ℕ) : Fintype (SignedSubset n) := by
  classical
  refine Fintype.ofInjective (fun X : SignedSubset n => (X.pos, X.neg)) ?_
  intro X Y h
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance nonzeroSignedSubset_fintype (n : ℕ) :
    Fintype (NonzeroSignedSubset n) := by
  classical
  refine Fintype.ofInjective
    (fun X : NonzeroSignedSubset n => (X.1.pos, X.1.neg)) ?_
  intro X Y h
  apply Subtype.ext
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A concrete ordered codimension-one ridge in the upper hemisphere whose
retained labels are exactly `A`.  The ridge is an actual ordered chain of
vertices; the existential signed-permutation/gap field only certifies that it
is a genuine punctured maximal chain. -/
def ActualHemisphereARidge {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset (d + 1) //
    (∀ a : Fin d, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (d + 1), ∀ a : Fin d,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance actualHemisphereARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereARidge label) := by
  classical
  dsimp [ActualHemisphereARidge]
  infer_instance

/-- Upper-hemisphere maximal chains which contain at least one label-set-`A`
ridge. -/
def ActualHemisphereAChain {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {P : SignedPermutation (d + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (d + 1), ∀ a : Fin d,
        ∃ t : Fin d, label (P.prefixChain (gap.succAbove t)) = alternatingLabel a}

noncomputable instance actualHemisphereAChain_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereAChain label) := by
  classical
  dsimp [ActualHemisphereAChain]
  infer_instance

/-- Incidence between an actual ridge and an upper maximal chain: deleting one
rank of the chain gives exactly the ordered ridge. -/
def actualHemisphereAEdge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) (sigma : ActualHemisphereAChain label) : Prop :=
  ∃ gap : Fin (d + 1), ∀ a : Fin d,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAEdge_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidableRel (actualHemisphereAEdge (label := label)) := by
  classical
  exact inferInstance

/-- Boundary ridges are exactly those whose retained vertices all lie in the
equator. -/
def actualHemisphereABoundary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) : Prop :=
  ∀ a : Fin d, Equator (rho.1 a)

noncomputable instance actualHemisphereABoundary_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereABoundary (label := label)) := by
  classical
  exact inferInstance

/-- Unordered maximal label-set-`A` objects on the equator, expressed in the
same data language as `ActualHemisphereARidge`: the vertices are transported
through `equatorEquiv`, and the maximal-equator witness is a boundary punctured
flag in the upper hemisphere. -/
def EquatorActualARidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset d //
    (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last d) ∧
        ∀ a : Fin d,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last d).succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance equatorActualARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype (EquatorActualARidge label) := by
  classical
  dsimp [EquatorActualARidge]
  infer_instance

theorem actualHemisphereABoundary_iff_represented {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereABoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last d := by
      by_contra hne
      have hlast_ne_gap : Fin.last d ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last d ∈ (P.prefixChain (Fin.last d)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last d) (hP (Fin.last d))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last d) = Fin.last d := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last d ∈ (P.prefixChain (P.order.symm (Fin.last d))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last d))
          (hP (P.order.symm (Fin.last d))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

noncomputable def equatorBoundaryARidgeEquiv {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    {rho : ActualHemisphereARidge label // actualHemisphereABoundary rho} ≃
      EquatorActualARidge (equatorRestrictedLabel label) where
  toFun rho := by
    classical
    let dropped : Fin d → NonzeroSignedSubset d :=
      fun a => (equatorEquiv d).symm ⟨rho.1.1 a, rho.2 a⟩
    have hrepr :
        ∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
          RepresentedUpperRidgeBoundary P (Fin.last d) ∧
            ∀ a : Fin d,
              equatorEmbed (dropped a) =
                P.prefixChain ((Fin.last d).succAbove a) := by
      rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
      have hb := (actualHemisphereABoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
      rcases hb with ⟨hgap, hcoord⟩
      subst gap
      refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
      intro a
      calc
        equatorEmbed (dropped a) = rho.1.1 a := by
          dsimp [dropped, equatorEquiv]
          exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
        _ = P.prefixChain ((Fin.last d).succAbove a) := hrho a
    refine ⟨dropped, hrepr, ?_⟩
    intro a
    rcases rho.1.2.2.2 a with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    dsimp [dropped, equatorRestrictedLabel, equatorEquiv]
    simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht
  invFun rho := by
    classical
    let lifted : Fin d → NonzeroSignedSubset (d + 1) := fun a => equatorEmbed (rho.1 a)
    have hupper : ∀ a : Fin d, UpperHemisphere (lifted a) := by
      intro a
      exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
    let hactual : ActualHemisphereARidge label :=
      ⟨lifted, by
        refine ⟨hupper, ?_, ?_⟩
        · rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
          exact ⟨P, hP, ⟨Fin.last d, hrepr⟩⟩
        · intro a
          rcases rho.2.2 a with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          dsimp [lifted, equatorRestrictedLabel, equatorEquiv] at ht ⊢
          simpa using ht⟩
    refine ⟨hactual, ?_⟩
    intro a
    change Equator (equatorEmbed (rho.1 a))
    exact equatorEmbed_mem_equator (rho.1 a)
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp
    exact equatorDrop_equatorEmbed (rho.1 a)

def KyFanUnorderedParityStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset d → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card (EquatorActualARidge label))

theorem equatorRestrictedLabel_unordered_odd {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))) :=
  hKy (equatorRestrictedLabel label)
    (equatorRestrictedLabel_antipodal hantipodal)
    (equatorRestrictedLabel_noComplementary hno)

/-- A top chain is one-door when deleting exactly one of its vertices leaves
the alternating label set `A`. -/
def actualHemisphereAOneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) : Prop :=
  (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereAOneDoor_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereAOneDoor (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereAIncidentRepresentedCofaceEquiv {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereAChain label // actualHemisphereAEdge rho sigma} ≃
      {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (d + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin d, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hd (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin d,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2.1))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin d, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    let sigma : ActualHemisphereAChain label :=
      ⟨Q.1, hQupper, ⟨gap, fun a => by
        rcases rho.2.2.2 a with ⟨t, ht⟩
        exact ⟨t, by simpa [hQdel t] using ht⟩⟩⟩
    exact ⟨sigma, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereA_rho_degree_card {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) :
    Fintype.card
        {sigma : ActualHemisphereAChain label //
          actualHemisphereAEdge rho sigma} =
      if actualHemisphereABoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereAIncidentRepresentedCofaceEquiv hd rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereABoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereABoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualRidgeOfChainGap {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    ActualHemisphereARidge label :=
  ⟨fun a : Fin d => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2.1 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2.1, ⟨gap.1, fun a => rfl⟩⟩,
      fun a => by
        rcases gap.2 a with ⟨t, htne, htlabel⟩
        rcases Fin.exists_succAbove_eq htne with ⟨b, hb⟩
        exact ⟨b, by simpa [← hb] using htlabel⟩⟩⟩

theorem actualRidgeOfChainGap_edge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    actualHemisphereAEdge (actualRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereAEdge_gives_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {rho : ActualHemisphereARidge label} {sigma : ActualHemisphereAChain label}
    (hedge : actualHemisphereAEdge rho sigma) :
    ∃ gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j},
      rho = actualRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdoor : SigmaDeletionHasAlternatingLabelSet
      (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases rho.2.2.2 a with ⟨b, hb⟩
    exact ⟨gap.succAbove b, Fin.succAbove_ne gap b, by
      simpa [← hgap b] using hb⟩
  refine ⟨⟨gap, hdoor⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualRidgeOfChainGap_injective {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Function.Injective (actualRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereAIncidentDoorEquiv {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} ≃
      {j : Fin (d + 1) //
        SigmaDeletionHasAlternatingLabelSet
          (fun i => label (sigma.1.prefixChain i)) j} where
  toFun rho :=
    Classical.choose (actualHemisphereAEdge_gives_door rho.2)
  invFun gap :=
    ⟨actualRidgeOfChainGap sigma gap, actualRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereAEdge_gives_door rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereAEdge_gives_door (actualRidgeOfChainGap_edge sigma gap))
    apply actualRidgeOfChainGap_injective sigma
    exact hspec.symm

theorem actualHemisphereA_sigma_degree_card {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Fintype.card
        {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} =
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereAIncidentDoorEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (d + 1) //
            SigmaDeletionHasAlternatingLabelSet
              (fun i => label (sigma.1.prefixChain i)) j} =
        (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem actualHemisphereA_sigma_odd_degree_iff_oneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma}) ↔
      actualHemisphereAOneDoor sigma := by
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  rw [actualHemisphereA_sigma_degree_card sigma, actualHemisphereAOneDoor]
  exact sigmaDoorSet_odd_iff_card_one_of_door hdoorExtra

theorem actualHemisphereA_sigma_degree_one_gives_prefixChain_complementary_pair {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (hdegree :
      Fintype.card
          {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (sigma.1.prefixChain i)).index = (label (sigma.1.prefixChain j)).index ∧
      (label (sigma.1.prefixChain i)).positive ≠
        (label (sigma.1.prefixChain j)).positive := by
  have hdoorCard :
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1 := by
    simpa [actualHemisphereA_sigma_degree_card sigma] using hdegree
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  exact sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door
    (label := label) (P := sigma.1) (extra := gap)
    hdoorExtra hdoorCard

theorem actualHemisphereARidge_nonempty_of_boundary_odd {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    Nonempty (ActualHemisphereARidge label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩

noncomputable def actualHemisphereRhoDegreeDataOfDegreeCard {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label))
    (hdegree :
      ∀ rho : ActualHemisphereARidge label,
        Fintype.card
            {sigma : ActualHemisphereAChain label //
              actualHemisphereAEdge rho sigma} =
          if actualHemisphereABoundary rho then 1 else 2) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) where
  edge := actualHemisphereAEdge
  edge_decidable := actualHemisphereAEdge_decidable
  boundary := actualHemisphereABoundary
  boundary_decidable := actualHemisphereABoundary_decidable
  nonempty_R := hR
  degree_card := hdegree

noncomputable def actualHemisphereRhoDegreeData {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label)) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
  actualHemisphereRhoDegreeDataOfDegreeCard hR
    (actualHemisphereA_rho_degree_card hd)

/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/

def ActualHemisphereIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxRidge idx label) := by
  classical
  dsimp [ActualHemisphereIdxRidge]
  infer_instance

def ActualHemisphereIdxChain {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (r + 1), ∀ a : Fin r,
        ∃ t : Fin r,
          label (P.prefixChain (gap.succAbove t)) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxChain_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxChain idx label) := by
  classical
  dsimp [ActualHemisphereIdxChain]
  infer_instance

def actualHemisphereIdxEdge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereIdxEdge_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereIdxEdge (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereIdxBoundary {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereIdxBoundary_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxBoundary (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def EquatorActualIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance equatorActualIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualIdxRidge idx label) := by
  classical
  dsimp [EquatorActualIdxRidge]
  infer_instance

theorem actualHemisphereIdxBoundary_iff_represented {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereIdxBoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last r := by
      by_contra hne
      have hlast_ne_gap : Fin.last r ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last r ∈ (P.prefixChain (Fin.last r)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last r) (hP (Fin.last r))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last r) = Fin.last r := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last r ∈ (P.prefixChain (P.order.symm (Fin.last r))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last r))
          (hP (P.order.symm (Fin.last r))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

noncomputable def equatorBoundaryIdxRidgeToEquator {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : {rho : ActualHemisphereIdxRidge idx label //
      actualHemisphereIdxBoundary rho}) :
    EquatorActualIdxRidge idx (equatorRestrictedLabelOf label) := by
  classical
  let dropped : Fin r → NonzeroSignedSubset r :=
    fun a => (equatorEquiv r).symm ⟨rho.1.1 a, rho.2 a⟩
  have hrepr :
      ∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        RepresentedUpperRidgeBoundary P (Fin.last r) ∧
          ∀ a : Fin r,
            equatorEmbed (dropped a) =
              P.prefixChain ((Fin.last r).succAbove a) := by
    rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
    have hb := (actualHemisphereIdxBoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
    rcases hb with ⟨hgap, hcoord⟩
    subst gap
    refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
    intro a
    calc
      equatorEmbed (dropped a) = rho.1.1 a := by
        dsimp [dropped, equatorEquiv]
        exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
      _ = P.prefixChain ((Fin.last r).succAbove a) := hrho a
  refine ⟨dropped, hrepr, ?_⟩
  intro a
  rcases rho.1.2.2.2 a with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv]
  simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht

noncomputable def equatorBoundaryIdxRidgeFromEquator {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : EquatorActualIdxRidge idx (equatorRestrictedLabelOf label)) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxBoundary rho} := by
  classical
  let lifted : Fin r → NonzeroSignedSubset (r + 1) := fun a => equatorEmbed (rho.1 a)
  have hupper : ∀ a : Fin r, UpperHemisphere (lifted a) := by
    intro a
    exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
  let hactual : ActualHemisphereIdxRidge idx label :=
    ⟨lifted, by
      refine ⟨hupper, ?_, ?_⟩
      · rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
        exact ⟨P, hP, ⟨Fin.last r, hrepr⟩⟩
      · intro a
        rcases rho.2.2 a with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv] at ht ⊢
        simpa using ht⟩
  refine ⟨hactual, ?_⟩
  intro a
  change Equator (equatorEmbed (rho.1 a))
  exact equatorEmbed_mem_equator (rho.1 a)

noncomputable def equatorBoundaryIdxRidgeEquiv {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxBoundary rho} ≃
      EquatorActualIdxRidge idx (equatorRestrictedLabelOf label) where
  toFun := equatorBoundaryIdxRidgeToEquator
  invFun := equatorBoundaryIdxRidgeFromEquator
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryIdxRidgeToEquator, equatorBoundaryIdxRidgeFromEquator]
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryIdxRidgeToEquator, equatorBoundaryIdxRidgeFromEquator]
    exact equatorDrop_equatorEmbed (rho.1 a)

abbrev StrictIndexMap (r m : ℕ) :=
  {idx : Fin r → Fin m // StrictMono idx}

@[implicit_reducible]
noncomputable def strictIndexMapFintype (r m : ℕ) :
    Fintype (StrictIndexMap r m) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx)
    (by
      intro idx
      change idx ∈
          ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx) ↔
        StrictMono idx
      simp)

abbrev EquatorActualAnyIdxRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  Σ idx : StrictIndexMap r m, EquatorActualIdxRidge idx.1 label

@[implicit_reducible]
noncomputable def equatorActualAnyIdxRidgeFintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAnyIdxRidge label) := by
  classical
  letI : Fintype (StrictIndexMap r m) := strictIndexMapFintype r m
  infer_instance

noncomputable def equatorActualAnyIdxRidgeCard {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) : ℕ :=
  @Fintype.card (EquatorActualAnyIdxRidge label) (equatorActualAnyIdxRidgeFintype label)

def KyFanUnorderedParityStatement2 (r m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset r → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (equatorActualAnyIdxRidgeCard label)

def actualHemisphereIdxOneDoor {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereIdxOneDoor_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxOneDoor (idx := idx) (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereIdxIncidentRepresentedCofaceEquiv {r m : ℕ}
    (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereIdxChain idx label // actualHemisphereIdxEdge rho sigma} ≃
      {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (r + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin r, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hr (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin r,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2.1))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin r, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    let sigma : ActualHemisphereIdxChain idx label :=
      ⟨Q.1, hQupper, ⟨gap, fun a => by
        rcases rho.2.2.2 a with ⟨t, ht⟩
        exact ⟨t, by simpa [hQdel t] using ht⟩⟩⟩
    exact ⟨sigma, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereIdx_rho_degree_card {r m : ℕ} (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) :
    Fintype.card
        {sigma : ActualHemisphereIdxChain idx label //
          actualHemisphereIdxEdge rho sigma} =
      if actualHemisphereIdxBoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereIdxIncidentRepresentedCofaceEquiv hr rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereIdxBoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereIdxBoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualIdxRidgeOfChainGap {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label)
    (gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j}) :
    ActualHemisphereIdxRidge idx label :=
  ⟨fun a : Fin r => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2.1 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2.1, ⟨gap.1, fun a => rfl⟩⟩,
      fun a => by
        rcases gap.2 a with ⟨t, htne, htlabel⟩
        rcases Fin.exists_succAbove_eq htne with ⟨b, hb⟩
        exact ⟨b, by simpa [← hb] using htlabel⟩⟩⟩

theorem actualIdxRidgeOfChainGap_edge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label)
    (gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j}) :
    actualHemisphereIdxEdge (actualIdxRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereIdxEdge_gives_door {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    {rho : ActualHemisphereIdxRidge idx label}
    {sigma : ActualHemisphereIdxChain idx label}
    (hedge : actualHemisphereIdxEdge rho sigma) :
    ∃ gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j},
      rho = actualIdxRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdoor : SigmaDeletionHasAlternatingLabelSetOf idx
      (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases rho.2.2.2 a with ⟨b, hb⟩
    exact ⟨gap.succAbove b, Fin.succAbove_ne gap b, by
      simpa [← hgap b] using hb⟩
  refine ⟨⟨gap, hdoor⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualIdxRidgeOfChainGap_injective {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Function.Injective (actualIdxRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereIdxIncidentDoorEquiv {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxEdge rho sigma} ≃
      {j : Fin (r + 1) //
        SigmaDeletionHasAlternatingLabelSetOf idx
          (fun i => label (sigma.1.prefixChain i)) j} where
  toFun rho :=
    Classical.choose (actualHemisphereIdxEdge_gives_door rho.2)
  invFun gap :=
    ⟨actualIdxRidgeOfChainGap sigma gap, actualIdxRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereIdxEdge_gives_door rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereIdxEdge_gives_door (actualIdxRidgeOfChainGap_edge sigma gap))
    apply actualIdxRidgeOfChainGap_injective sigma
    exact hspec.symm

theorem actualHemisphereIdx_sigma_degree_card {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Fintype.card
        {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxEdge rho sigma} =
      (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereIdxIncidentDoorEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (r + 1) //
            SigmaDeletionHasAlternatingLabelSetOf idx
              (fun i => label (sigma.1.prefixChain i)) j} =
        (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem actualHemisphereIdx_sigma_odd_degree_iff_oneDoor {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereIdxRidge idx label //
            actualHemisphereIdxEdge rho sigma}) ↔
      actualHemisphereIdxOneDoor sigma := by
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  rw [actualHemisphereIdx_sigma_degree_card sigma, actualHemisphereIdxOneDoor]
  exact sigmaDoorSetOf_odd_iff_card_one_of_door hidx hdoorExtra

theorem actualHemisphereIdxRidge_nonempty_of_boundary_odd {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereIdxRidge idx label //
          actualHemisphereIdxBoundary rho})) :
    Nonempty (ActualHemisphereIdxRidge idx label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereIdxRidge idx label //
          actualHemisphereIdxBoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩

noncomputable def actualHemisphereIdxRhoDegreeDataOfDegreeCard {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereIdxRidge idx label))
    (hdegree :
      ∀ rho : ActualHemisphereIdxRidge idx label,
        Fintype.card
            {sigma : ActualHemisphereIdxChain idx label //
              actualHemisphereIdxEdge rho sigma} =
          if actualHemisphereIdxBoundary rho then 1 else 2) :
    RhoDegreeManifoldData
      (ActualHemisphereIdxRidge idx label) (ActualHemisphereIdxChain idx label) where
  edge := actualHemisphereIdxEdge
  edge_decidable := actualHemisphereIdxEdge_decidable
  boundary := actualHemisphereIdxBoundary
  boundary_decidable := actualHemisphereIdxBoundary_decidable
  nonempty_R := hR
  degree_card := hdegree

noncomputable def actualHemisphereIdxRhoDegreeData {r m : ℕ} (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereIdxRidge idx label)) :
    RhoDegreeManifoldData
      (ActualHemisphereIdxRidge idx label) (ActualHemisphereIdxChain idx label) :=
  actualHemisphereIdxRhoDegreeDataOfDegreeCard hR
    (actualHemisphereIdx_rho_degree_card hr)

/-! ## Actual upper-hemisphere graph with self-contained alternating labels -/

def ActualHemisphereAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance actualHemisphereAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltRidge label) := by
  classical
  dsimp [ActualHemisphereAltRidge]
  infer_instance

def ActualHemisphereAltChain {r m : ℕ}
    (_label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) // UpperPrefixChain P}

noncomputable instance actualHemisphereAltChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltChain label) := by
  classical
  dsimp [ActualHemisphereAltChain]
  infer_instance

def actualHemisphereAltEdge {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (sigma : ActualHemisphereAltChain label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAltEdge_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereAltEdge (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereAltBoundary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereAltBoundary_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltBoundary (label := label)) := by
  classical
  exact inferInstance

theorem actualHemisphereAltBoundary_iff_represented {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereAltBoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last r := by
      by_contra hne
      have hlast_ne_gap : Fin.last r ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last r ∈ (P.prefixChain (Fin.last r)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last r) (hP (Fin.last r))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last r) = Fin.last r := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last r ∈ (P.prefixChain (P.order.symm (Fin.last r))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last r))
          (hP (P.order.symm (Fin.last r))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

def actualHemisphereAltTop {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) : Prop :=
  IsAltPos label (fun i : Fin (r + 1) => sigma.1.prefixChain i) ∨
    IsAltNeg label (fun i : Fin (r + 1) => sigma.1.prefixChain i)

noncomputable instance actualHemisphereAltTop_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltTop (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereAltIncidentRepresentedCofaceEquiv {r m : ℕ}
    (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltEdge rho sigma} ≃
      {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (r + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin r, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hr (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin r,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin r, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    exact ⟨⟨Q.1, hQupper⟩, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereAlt_rho_degree_card {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label) :
    Fintype.card
        {sigma : ActualHemisphereAltChain label //
          actualHemisphereAltEdge rho sigma} =
      if actualHemisphereAltBoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereAltIncidentRepresentedCofaceEquiv hr rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereAltBoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereAltBoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualAltRidgeOfChainGap {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label)
    (gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))}) :
    ActualHemisphereAltRidge label :=
  ⟨fun a : Fin r => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2, ⟨gap.1, fun a => rfl⟩⟩,
      gap.2⟩⟩

theorem actualAltRidgeOfChainGap_edge {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label)
    (gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))}) :
    actualHemisphereAltEdge (actualAltRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereAltEdge_gives_gap {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    {rho : ActualHemisphereAltRidge label}
    {sigma : ActualHemisphereAltChain label}
    (hedge : actualHemisphereAltEdge rho sigma) :
    ∃ gap : {j : Fin (r + 1) //
      IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))},
      rho = actualAltRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdel : IsAltPos label (fun a : Fin r => sigma.1.prefixChain (gap.succAbove a)) := by
    have hfun :
        (fun a : Fin r => sigma.1.prefixChain (gap.succAbove a)) = rho.1 := by
      funext a
      exact (hgap a).symm
    rw [hfun]
    exact rho.2.2.2
  refine ⟨⟨gap, hdel⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualAltRidgeOfChainGap_injective {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    Function.Injective (actualAltRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereAltIncidentDeletionEquiv {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltEdge rho sigma} ≃
      {j : Fin (r + 1) //
        IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))} where
  toFun rho :=
    Classical.choose (actualHemisphereAltEdge_gives_gap rho.2)
  invFun gap :=
    ⟨actualAltRidgeOfChainGap sigma gap, actualAltRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereAltEdge_gives_gap rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereAltEdge_gives_gap (actualAltRidgeOfChainGap_edge sigma gap))
    apply actualAltRidgeOfChainGap_injective sigma
    exact hspec.symm

theorem actualHemisphereAlt_sigma_degree_card {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    Fintype.card
        {rho : ActualHemisphereAltRidge label // actualHemisphereAltEdge rho sigma} =
      (simplexAltPosDeletionSet label
        (fun i : Fin (r + 1) => sigma.1.prefixChain i)).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereAltIncidentDeletionEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (r + 1) //
            IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))} =
        (simplexAltPosDeletionSet label
          (fun i : Fin (r + 1) => sigma.1.prefixChain i)).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem noOppositeLabelSeq_of_chain_of_noComplementary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (r + 1)) :
    NoOppositeLabelSeq (fun i : Fin (r + 1) => label (P.prefixChain i)) := by
  intro i j hcomp
  by_cases hij : i ≤ j
  · exact hno (P.prefixChain i) (P.prefixChain j) (P.prefixChain_le hij) hcomp
  · have hji : j ≤ i := le_of_not_ge hij
    have hcomp' :
        label (P.prefixChain j) = (label (P.prefixChain i)).neg := by
      apply SignedLabel.ext
      · have hp := congrArg SignedLabel.positive hcomp
        cases hi : (label (P.prefixChain i)).positive <;>
          cases hj : (label (P.prefixChain j)).positive <;>
            simp [SignedLabel.neg, hi, hj] at hp ⊢
      · have hidx := congrArg SignedLabel.index hcomp
        simpa [SignedLabel.neg] using hidx.symm
    exact hno (P.prefixChain j) (P.prefixChain i) (P.prefixChain_le hji) hcomp'

theorem actualHemisphereAlt_sigma_odd_degree_iff_top {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (sigma : ActualHemisphereAltChain label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereAltRidge label //
            actualHemisphereAltEdge rho sigma}) ↔
      actualHemisphereAltTop sigma := by
  rw [actualHemisphereAlt_sigma_degree_card sigma, actualHemisphereAltTop]
  exact simplex_deletionParity_of_noOpposite
    (label := label) (sigma := fun i : Fin (r + 1) => sigma.1.prefixChain i)
    (noOppositeLabelSeq_of_chain_of_noComplementary hno sigma.1)

theorem actualHemisphereAltRidge_nonempty_of_boundary_odd {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho})) :
    Nonempty (ActualHemisphereAltRidge label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩

noncomputable def actualHemisphereAltRhoDegreeData {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereAltRidge label)) :
    RhoDegreeManifoldData
      (ActualHemisphereAltRidge label) (ActualHemisphereAltChain label) where
  edge := actualHemisphereAltEdge
  edge_decidable := actualHemisphereAltEdge_decidable
  boundary := actualHemisphereAltBoundary
  boundary_decidable := actualHemisphereAltBoundary_decidable
  nonempty_R := hR
  degree_card := actualHemisphereAlt_rho_degree_card hr

theorem ball_parity {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho})) :
    Odd (Fintype.card
      {sigma : ActualHemisphereAltChain label //
        actualHemisphereAltTop sigma}) := by
  classical
  let D : RhoDegreeManifoldData
      (ActualHemisphereAltRidge label) (ActualHemisphereAltChain label) :=
    actualHemisphereAltRhoDegreeData hr
      (actualHemisphereAltRidge_nonempty_of_boundary_odd hboundaryOdd)
  have hmod := D.boundary_top_parity
    (topOdd := actualHemisphereAltTop (label := label))
    (actualHemisphereAlt_sigma_odd_degree_iff_top hno)
  have hb :
      (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} : ZMod 2) = 1 :=
    hboundaryOdd.natCast_zmod_two
  have hbD :
      (Fintype.card
        {rho : ActualHemisphereAltRidge label // D.boundary rho} : ZMod 2) = 1 := by
    change (Fintype.card
      {rho : ActualHemisphereAltRidge label // actualHemisphereAltBoundary rho} : ZMod 2) = 1
    exact hb
  have ht :
      (Fintype.card
        {sigma : ActualHemisphereAltChain label //
          actualHemisphereAltTop sigma} : ZMod 2) = 1 := by
    simpa [hbD] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht

def EquatorActualAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance equatorActualAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAltRidge label) := by
  classical
  dsimp [EquatorActualAltRidge]
  infer_instance

noncomputable def equatorBoundaryAltRidgeToEquator {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : {rho : ActualHemisphereAltRidge label //
      actualHemisphereAltBoundary rho}) :
    EquatorActualAltRidge (equatorRestrictedLabelOf label) := by
  classical
  let dropped : Fin r → NonzeroSignedSubset r :=
    fun a => (equatorEquiv r).symm ⟨rho.1.1 a, rho.2 a⟩
  have hrepr :
      ∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        RepresentedUpperRidgeBoundary P (Fin.last r) ∧
          ∀ a : Fin r,
            equatorEmbed (dropped a) =
              P.prefixChain ((Fin.last r).succAbove a) := by
    rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
    have hb := (actualHemisphereAltBoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
    rcases hb with ⟨hgap, hcoord⟩
    subst gap
    refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
    intro a
    calc
      equatorEmbed (dropped a) = rho.1.1 a := by
        dsimp [dropped, equatorEquiv]
        exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
      _ = P.prefixChain ((Fin.last r).succAbove a) := hrho a
  have halt : IsAltPos (equatorRestrictedLabelOf label) dropped := by
    rcases rho.1.2.2.2 with ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hx' : label (rho.1.1 a) ∈ simplexLabelSet label rho.1.1 := by
        simp [simplexLabelSet]
      rw [hset] at hx'
      convert hx' using 1
      dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv] at ha ⊢
      simpa [equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)] using ha.symm
    · intro hx
      have hx' : x ∈ simplexLabelSet label rho.1.1 := by
        rw [hset]
        exact hx
      rcases Finset.mem_image.mp hx' with ⟨t, _ht, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv]
      simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht
  exact ⟨dropped, hrepr, halt⟩

noncomputable def equatorBoundaryAltRidgeFromEquator {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : EquatorActualAltRidge (equatorRestrictedLabelOf label)) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltBoundary rho} := by
  classical
  let lifted : Fin r → NonzeroSignedSubset (r + 1) := fun a => equatorEmbed (rho.1 a)
  have hupper : ∀ a : Fin r, UpperHemisphere (lifted a) := by
    intro a
    exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
  have halt : IsAltPos label lifted := by
    rcases rho.2.2 with ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hx' :
          equatorRestrictedLabelOf label (rho.1 a) ∈
            simplexLabelSet (equatorRestrictedLabelOf label) rho.1 := by
        simp [simplexLabelSet]
      rw [hset] at hx'
      convert hx' using 1
      dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv] at ha ⊢
      simpa using ha.symm
    · intro hx
      have hx' :
          x ∈
            simplexLabelSet (equatorRestrictedLabelOf label) rho.1 := by
        rw [hset]
        exact hx
      rcases Finset.mem_image.mp hx' with ⟨t, _ht, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv]
      change label (equatorEmbed (rho.1 t)) = x
      change label (equatorEmbed (rho.1 t)) = x at ht
      exact ht
  let hactual : ActualHemisphereAltRidge label :=
    ⟨lifted, by
      refine ⟨hupper, ?_, halt⟩
      rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
      exact ⟨P, hP, ⟨Fin.last r, hrepr⟩⟩⟩
  refine ⟨hactual, ?_⟩
  intro a
  change Equator (equatorEmbed (rho.1 a))
  exact equatorEmbed_mem_equator (rho.1 a)

noncomputable def equatorBoundaryAltRidgeEquiv {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    {rho : ActualHemisphereAltRidge label // actualHemisphereAltBoundary rho} ≃
      EquatorActualAltRidge (equatorRestrictedLabelOf label) where
  toFun := equatorBoundaryAltRidgeToEquator
  invFun := equatorBoundaryAltRidgeFromEquator
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryAltRidgeToEquator, equatorBoundaryAltRidgeFromEquator]
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryAltRidgeToEquator, equatorBoundaryAltRidgeFromEquator]
    exact equatorDrop_equatorEmbed (rho.1 a)

theorem equatorBoundaryAltCardBridge {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} =
      Fintype.card (EquatorActualAltRidge (equatorRestrictedLabelOf label)) :=
  Fintype.card_congr (equatorBoundaryAltRidgeEquiv label)

/-! ## Antipodal and hemisphere bridges for self-contained alternating chains -/

theorem labelSeqSet_alternatingLabelOf {k m : ℕ} (idx : Fin k → Fin m) :
    labelSeqSet (fun a : Fin k => alternatingLabelOf idx a) = alternatingLabelSetOf idx := by
  simp [labelSeqSet, alternatingLabelSetOf]

theorem IsAltPosLabelSeq.not_isAltNeg {k m : ℕ} (hk : 0 < k)
    {L : Fin k → SignedLabel m} :
    IsAltPosLabelSeq L → IsAltNegLabelSeq L → False := by
  classical
  rintro ⟨idx, hidx, hsetPos⟩ hneg
  let Lpos : Fin k → SignedLabel m := fun a => alternatingLabelOf idx a
  have hLposSet : labelSeqSet Lpos = labelSeqSet L := by
    rw [hsetPos]
    exact labelSeqSet_alternatingLabelOf idx
  have hnegPos : IsAltNegLabelSeq Lpos := by
    rcases hneg with ⟨eta, heta, hsetNeg⟩
    exact ⟨eta, heta, hLposSet.trans hsetNeg⟩
  let sgn : Fin k → Bool := fun a => decide (Even a.val)
  have hLpos :
      ∀ a : Fin k, Lpos a = { positive := sgn a, index := idx a } := by
    intro a
    rfl
  have hsgnNeg : signSeqAltNeg sgn :=
    (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hLpos).mp hnegPos
  let i : Fin k := ⟨0, hk⟩
  have hi := hsgnNeg i
  simp [signSeqAltNeg, sgn, i] at hi

theorem IsAltPos.not_isAltNeg {k m n : ℕ} (hk : 0 < k)
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltPos label sigma → IsAltNeg label sigma → False :=
  IsAltPosLabelSeq.not_isAltNeg hk

theorem IsAltPosLabelSeq_neg_iff_isAltNeg {k m : ℕ} {L : Fin k → SignedLabel m} :
    IsAltPosLabelSeq (fun a => (L a).neg) ↔ IsAltNegLabelSeq L := by
  classical
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      have hxneg : x.neg ∈ labelSeqSet (fun a : Fin k => (L a).neg) := by
        rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
        refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
        rw [← ha]
      rw [hset] at hxneg
      rcases (by simpa [alternatingLabelSetOf] using hxneg) with ⟨a, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
      rw [ha]
      simp [SignedLabel.neg]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxpos : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
        simp [alternatingLabelSetOf]
      rw [← hset] at hxpos
      rcases Finset.mem_image.mp hxpos with ⟨b, _hb, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha]
      have hb' := congrArg SignedLabel.neg hb
      apply SignedLabel.ext
      · simpa [SignedLabel.neg] using congrArg SignedLabel.positive hb'
      · simpa [SignedLabel.neg] using congrArg SignedLabel.index hb'
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxneg : L a ∈ alternatingNegLabelSetOf idx := by
        rw [← hset]
        simp [labelSeqSet]
      rcases (by simpa [alternatingNegLabelSetOf] using hxneg) with ⟨b, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha, ← hb]
      simp [SignedLabel.neg, alternatingLabelOf]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      have hxorig : (alternatingLabelOf idx a).neg ∈ labelSeqSet L := by
        rw [hset]
        simp [alternatingNegLabelSetOf]
      rcases Finset.mem_image.mp hxorig with ⟨b, _hb, hb⟩
      refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
      rw [← ha, hb]
      simp [SignedLabel.neg, alternatingLabelOf]

theorem IsAltNegLabelSeq_neg_iff_isAltPos {k m : ℕ} {L : Fin k → SignedLabel m} :
    IsAltNegLabelSeq (fun a => (L a).neg) ↔ IsAltPosLabelSeq L := by
  constructor
  · intro h
    have h' :=
      (IsAltPosLabelSeq_neg_iff_isAltNeg
        (L := fun a : Fin k => (L a).neg)).mpr h
    simpa [SignedLabel.neg] using h'
  · intro h
    apply (IsAltPosLabelSeq_neg_iff_isAltNeg
      (L := fun a : Fin k => (L a).neg)).mp
    simpa [SignedLabel.neg] using h

theorem IsAltPos_antipode_iff_isAltNeg {m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    IsAltPos label (fun i : Fin n => P.antipode.prefixChain i) ↔
      IsAltNeg label (fun i : Fin n => P.prefixChain i) := by
  have hfun :
      (fun i : Fin n => label (P.antipode.prefixChain i)) =
        fun i : Fin n => (label (P.prefixChain i)).neg := by
    funext i
    rw [SignedPermutation.prefixChain_antipode]
    exact hantipodal (P.prefixChain i)
  change
    IsAltPosLabelSeq (fun i : Fin n => label (P.antipode.prefixChain i)) ↔
      IsAltNegLabelSeq (fun i : Fin n => label (P.prefixChain i))
  rw [hfun]
  exact IsAltPosLabelSeq_neg_iff_isAltNeg

theorem IsAltNeg_antipode_iff_isAltPos {m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    IsAltNeg label (fun i : Fin n => P.antipode.prefixChain i) ↔
      IsAltPos label (fun i : Fin n => P.prefixChain i) := by
  have hfun :
      (fun i : Fin n => label (P.antipode.prefixChain i)) =
        fun i : Fin n => (label (P.prefixChain i)).neg := by
    funext i
    rw [SignedPermutation.prefixChain_antipode]
    exact hantipodal (P.prefixChain i)
  change
    IsAltNegLabelSeq (fun i : Fin n => label (P.antipode.prefixChain i)) ↔
      IsAltPosLabelSeq (fun i : Fin n => label (P.prefixChain i))
  rw [hfun]
  exact IsAltNegLabelSeq_neg_iff_isAltPos

theorem upperPrefixChain_iff_last_positive {n : ℕ} (P : SignedPermutation (n + 1)) :
    UpperPrefixChain P ↔ P.positive (P.order.symm (Fin.last n)) := by
  constructor
  · intro hupper
    by_contra hpos
    exact hupper (P.order.symm (Fin.last n)) (by
      simp [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg, hpos])
  · intro hpos i hneg
    have hmem : Fin.last n ∈ (P.prefixChain i).1.neg := hneg
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixNeg, hpos] at hmem

theorem upperPrefixChain_antipode_iff_not {n : ℕ} (P : SignedPermutation (n + 1)) :
    UpperPrefixChain P.antipode ↔ ¬ UpperPrefixChain P := by
  rw [upperPrefixChain_iff_last_positive P.antipode,
    upperPrefixChain_iff_last_positive P]
  simp [SignedPermutation.antipode]

@[simp]
theorem finPredOfNotLast_castSucc {r : ℕ} (i : Fin r)
    (h : Fin.castSucc i ≠ Fin.last r) :
    finPredOfNotLast (Fin.castSucc i) h = i := by
  apply Fin.ext
  rfl

noncomputable def equatorExtendOrder {r : ℕ} (e : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r + 1)) where
  toFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e (finPredOfNotLast i hi))
  invFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e.symm (finPredOfNotLast i hi))
  left_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]
  right_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e.symm (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]

@[simp]
theorem equatorExtendOrder_apply_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    equatorExtendOrder e (Fin.last r) = Fin.last r := by
  simp [equatorExtendOrder]

@[simp]
theorem equatorExtendOrder_symm_apply_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    (equatorExtendOrder e).symm (Fin.last r) = Fin.last r := by
  simp [equatorExtendOrder]

@[simp]
theorem equatorExtendOrder_apply_castSucc {r : ℕ} (e : Equiv.Perm (Fin r))
    (i : Fin r) :
    equatorExtendOrder e (Fin.castSucc i) = Fin.castSucc (e i) := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [equatorExtendOrder, h]

@[simp]
theorem equatorExtendOrder_symm_apply_castSucc {r : ℕ} (e : Equiv.Perm (Fin r))
    (i : Fin r) :
    (equatorExtendOrder e).symm (Fin.castSucc i) = Fin.castSucc (e.symm i) := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [equatorExtendOrder, h]

noncomputable def signedPermutationEquatorExtend {r : ℕ}
    (P : SignedPermutation r) : SignedPermutation (r + 1) where
  order := equatorExtendOrder P.order
  positive := fun i =>
    if hi : i = Fin.last r then true
    else P.positive (finPredOfNotLast i hi)

@[simp]
theorem signedPermutationEquatorExtend_positive_last {r : ℕ}
    (P : SignedPermutation r) :
    (signedPermutationEquatorExtend P).positive (Fin.last r) = true := by
  simp [signedPermutationEquatorExtend]

@[simp]
theorem signedPermutationEquatorExtend_positive_castSucc {r : ℕ}
    (P : SignedPermutation r) (i : Fin r) :
    (signedPermutationEquatorExtend P).positive (Fin.castSucc i) = P.positive i := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [signedPermutationEquatorExtend, h]

theorem signedPermutationEquatorExtend_upperPrefixChain {r : ℕ}
    (P : SignedPermutation r) :
    UpperPrefixChain (signedPermutationEquatorExtend P) := by
  rw [upperPrefixChain_iff_last_positive]
  simp [signedPermutationEquatorExtend]

theorem signedPermutationEquatorExtend_boundary {r : ℕ}
    (P : SignedPermutation r) :
    RepresentedUpperRidgeBoundary (signedPermutationEquatorExtend P) (Fin.last r) := by
  exact ⟨rfl, by simp [signedPermutationEquatorExtend]⟩

theorem signedPermutationEquatorExtend_prefixChain_castSucc {r : ℕ}
    (P : SignedPermutation r) (i : Fin r) :
    (signedPermutationEquatorExtend P).prefixChain (Fin.castSucc i) =
      equatorEmbed (P.prefixChain i) := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend, Fin.castSucc_le_castSucc_iff]
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorExtend, Fin.castSucc_le_castSucc_iff]

theorem equatorEmbed_injective {r : ℕ} :
    Function.Injective (@equatorEmbed r) := by
  intro X Y h
  exact (equatorEquiv r).injective (Subtype.ext h)

theorem signedPermutation_eq_of_prefixChain_eq {n : ℕ}
    (P Q : SignedPermutation n)
    (hprefix : ∀ i : Fin n, Q.prefixChain i = P.prefixChain i) :
    Q = P := by
  apply SignedPermutation.ext_order_positive
  · apply Equiv.ext
    intro i
    exact (order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
      (hprefix i) (fun j _hj => hprefix j)).1
  · funext i
    exact (order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
      (hprefix i) (fun j _hj => hprefix j)).2

theorem perm_apply_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    e (Fin.last r) = Fin.last r := by
  calc
    e (Fin.last r) = e (e.symm (Fin.last r)) := by rw [hcoord]
    _ = Fin.last r := by simp

theorem perm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e.symm hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

theorem perm_symm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e.symm (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [perm_apply_last_of_symm_last e hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

noncomputable def equatorDropOrder {r : ℕ} (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    Equiv.Perm (Fin r) where
  toFun i :=
    finPredOfNotLast (e (Fin.castSucc i))
      (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  invFun i :=
    finPredOfNotLast (e.symm (Fin.castSucc i))
      (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  left_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e.symm
              (Fin.castSucc
                (finPredOfNotLast (e (Fin.castSucc i))
                  (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e (Fin.castSucc i))
                (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e.symm
          (Fin.castSucc
            (finPredOfNotLast (e (Fin.castSucc i))
              (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e.symm (e (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp
  right_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e
              (Fin.castSucc
                (finPredOfNotLast (e.symm (Fin.castSucc i))
                  (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e.symm (Fin.castSucc i))
                (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e
          (Fin.castSucc
            (finPredOfNotLast (e.symm (Fin.castSucc i))
              (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e (e.symm (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp

@[simp]
theorem equatorDropOrder_apply_castSucc {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    Fin.castSucc (equatorDropOrder e hcoord i) = e (Fin.castSucc i) := by
  dsimp [equatorDropOrder]
  rw [castSucc_finPredOfNotLast]

@[simp]
theorem equatorDropOrder_symm_apply_castSucc {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    Fin.castSucc ((equatorDropOrder e hcoord).symm i) =
      e.symm (Fin.castSucc i) := by
  dsimp [equatorDropOrder]
  rw [castSucc_finPredOfNotLast]

noncomputable def signedPermutationEquatorDrop {r : ℕ}
    (P : SignedPermutation (r + 1))
    (hcoord : P.order.symm (Fin.last r) = Fin.last r) :
    SignedPermutation r where
  order := equatorDropOrder P.order hcoord
  positive := fun i => P.positive (Fin.castSucc i)

theorem signedPermutationEquatorDrop_prefixChain_castSucc {r : ℕ}
    (P : SignedPermutation (r + 1))
    (hcoord : P.order.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    equatorEmbed ((signedPermutationEquatorDrop P hcoord).prefixChain i) =
      P.prefixChain (Fin.castSucc i) := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hcoord]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      have hleiff :
          ((equatorDropOrder P.order hcoord).symm y ≤ i) ↔
            P.order.symm (Fin.castSucc y) ≤ Fin.castSucc i := by
        constructor
        · intro hle
          rw [← equatorDropOrder_symm_apply_castSucc P.order hcoord y]
          exact Fin.castSucc_le_castSucc_iff.mpr hle
        · intro hle
          apply Fin.castSucc_le_castSucc_iff.mp
          rwa [equatorDropOrder_symm_apply_castSucc P.order hcoord y]
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hleiff]
  · ext x
    by_cases hxlast : x = Fin.last r
    · subst x
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hcoord]
    · rcases Fin.exists_succAbove_eq hxlast with ⟨y, hy⟩
      have hcast : Fin.castSucc y = x := by
        simpa [Fin.succAbove_last] using hy
      subst x
      have hleiff :
          ((equatorDropOrder P.order hcoord).symm y ≤ i) ↔
            P.order.symm (Fin.castSucc y) ≤ Fin.castSucc i := by
        constructor
        · intro hle
          rw [← equatorDropOrder_symm_apply_castSucc P.order hcoord y]
          exact Fin.castSucc_le_castSucc_iff.mpr hle
        · intro hle
          apply Fin.castSucc_le_castSucc_iff.mp
          rwa [equatorDropOrder_symm_apply_castSucc P.order hcoord y]
      simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, signedSubsetEquatorEmbed, equatorEmbed,
        signedPermutationEquatorDrop, hleiff]

def FullAltPosChain {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {P : SignedPermutation r // IsAltPos label (fun i : Fin r => P.prefixChain i)}

noncomputable instance fullAltPosChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (FullAltPosChain label) := by
  classical
  dsimp [FullAltPosChain]
  infer_instance

noncomputable def fullAltPosToEquatorActualAltRidge {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (P : FullAltPosChain label) :
    EquatorActualAltRidge label := by
  classical
  refine ⟨fun i : Fin r => P.1.prefixChain i, ?_, P.2⟩
  refine ⟨signedPermutationEquatorExtend P.1,
    signedPermutationEquatorExtend_upperPrefixChain P.1,
    signedPermutationEquatorExtend_boundary P.1, ?_⟩
  intro a
  simpa [Fin.succAbove_last] using
    (signedPermutationEquatorExtend_prefixChain_castSucc P.1 a).symm

noncomputable def equatorActualAltRidgeToFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (rho : EquatorActualAltRidge label) :
    FullAltPosChain label := by
  classical
  let P : SignedPermutation (r + 1) := Classical.choose rho.2.1
  have hspec :
      UpperPrefixChain P ∧ RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho.1 a) = P.prefixChain ((Fin.last r).succAbove a) :=
    Classical.choose_spec rho.2.1
  let Q : SignedPermutation r := signedPermutationEquatorDrop P hspec.2.1.2
  have hprefix : ∀ a : Fin r, Q.prefixChain a = rho.1 a := by
    intro a
    apply equatorEmbed_injective
    calc
      equatorEmbed (Q.prefixChain a) = P.prefixChain (Fin.castSucc a) := by
        exact signedPermutationEquatorDrop_prefixChain_castSucc P hspec.2.1.2 a
      _ = P.prefixChain ((Fin.last r).succAbove a) := by
        simp [Fin.succAbove_last]
      _ = equatorEmbed (rho.1 a) := (hspec.2.2 a).symm
  refine ⟨Q, ?_⟩
  have hfun : (fun i : Fin r => Q.prefixChain i) = rho.1 := by
    funext i
    exact hprefix i
  simpa [hfun] using rho.2.2

theorem equatorActualAltRidgeToFullAltPos_prefixChain {r m : ℕ}
    {label : NonzeroSignedSubset r → SignedLabel m}
    (rho : EquatorActualAltRidge label) (i : Fin r) :
    (equatorActualAltRidgeToFullAltPos rho).1.prefixChain i = rho.1 i := by
  classical
  unfold equatorActualAltRidgeToFullAltPos
  dsimp
  let P : SignedPermutation (r + 1) := Classical.choose rho.2.1
  have hspec :
      UpperPrefixChain P ∧ RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho.1 a) = P.prefixChain ((Fin.last r).succAbove a) :=
    Classical.choose_spec rho.2.1
  apply equatorEmbed_injective
  calc
    equatorEmbed ((signedPermutationEquatorDrop P hspec.2.1.2).prefixChain i) =
        P.prefixChain (Fin.castSucc i) := by
      exact signedPermutationEquatorDrop_prefixChain_castSucc P hspec.2.1.2 i
    _ = P.prefixChain ((Fin.last r).succAbove i) := by
      simp [Fin.succAbove_last]
    _ = equatorEmbed (rho.1 i) := (hspec.2.2 i).symm

noncomputable def equatorActualAltRidgeEquivFullAltPos {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    EquatorActualAltRidge label ≃ FullAltPosChain label where
  toFun := equatorActualAltRidgeToFullAltPos
  invFun := fullAltPosToEquatorActualAltRidge
  left_inv := by
    intro rho
    apply Subtype.ext
    funext i
    exact equatorActualAltRidgeToFullAltPos_prefixChain rho i
  right_inv := by
    intro P
    apply Subtype.ext
    apply signedPermutation_eq_of_prefixChain_eq P.1
    intro i
    simpa [fullAltPosToEquatorActualAltRidge] using
      equatorActualAltRidgeToFullAltPos_prefixChain
        (fullAltPosToEquatorActualAltRidge P) i

theorem equatorActualAlt_card_eq_full_alt_pos {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype.card (EquatorActualAltRidge label) =
      Fintype.card (FullAltPosChain label) :=
  Fintype.card_congr (equatorActualAltRidgeEquivFullAltPos label)

noncomputable def upperTopToFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (sigma : {sigma : ActualHemisphereAltChain label //
      actualHemisphereAltTop sigma}) :
    FullAltPosChain label := by
  classical
  let P : SignedPermutation (r + 1) := sigma.1.1
  by_cases hpos : IsAltPos label (fun i : Fin (r + 1) => P.prefixChain i)
  · exact ⟨P, hpos⟩
  · have hneg : IsAltNeg label (fun i : Fin (r + 1) => P.prefixChain i) := by
      rcases sigma.2 with h | h
      · exact False.elim (hpos h)
      · exact h
    exact ⟨P.antipode, (IsAltPos_antipode_iff_isAltNeg hantipodal P).mpr hneg⟩

noncomputable def fullAltPosToUpperTop {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : FullAltPosChain label) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} := by
  classical
  by_cases hupper : UpperPrefixChain P.1
  · exact ⟨⟨P.1, hupper⟩, Or.inl P.2⟩
  · have hupperAnti : UpperPrefixChain P.1.antipode :=
      (upperPrefixChain_antipode_iff_not P.1).mpr hupper
    have hnegAnti :
        IsAltNeg label (fun i : Fin (r + 1) => P.1.antipode.prefixChain i) :=
      (IsAltNeg_antipode_iff_isAltPos hantipodal P.1).mpr P.2
    exact ⟨⟨P.1.antipode, hupperAnti⟩, Or.inr hnegAnti⟩

noncomputable def upperTopEquivFullAltPos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} ≃
      FullAltPosChain label where
  toFun := upperTopToFullAltPos hantipodal
  invFun := fullAltPosToUpperTop hantipodal
  left_inv := by
    intro sigma
    classical
    dsimp [upperTopToFullAltPos, fullAltPosToUpperTop]
    let P : SignedPermutation (r + 1) := sigma.1.1
    have hupper : UpperPrefixChain P := sigma.1.2
    by_cases hpos : IsAltPos label (fun i : Fin (r + 1) => P.prefixChain i)
    · simp [P, hpos, hupper]
      apply Subtype.ext
      apply Subtype.ext
      rfl
    · have hnotUpperAnti : ¬ UpperPrefixChain P.antipode := by
        intro h
        exact (upperPrefixChain_antipode_iff_not P).mp h hupper
      simp [P, hpos, hnotUpperAnti]
      apply Subtype.ext
      apply Subtype.ext
      exact SignedPermutation.antipode_involutive P
  right_inv := by
    intro P
    classical
    dsimp [upperTopToFullAltPos, fullAltPosToUpperTop]
    by_cases hupper : UpperPrefixChain P.1
    · have hposP : IsAltPos label (fun i : Fin (r + 1) => P.1.prefixChain i) := P.2
      simp [hupper, hposP]
      apply Subtype.ext
      rfl
    · have hupperAnti : UpperPrefixChain P.1.antipode :=
        (upperPrefixChain_antipode_iff_not P.1).mpr hupper
      have hnotPosAnti :
          ¬ IsAltPos label (fun i : Fin (r + 1) => P.1.antipode.prefixChain i) := by
        intro hposAnti
        have hnegP :
            IsAltNeg label (fun i : Fin (r + 1) => P.1.prefixChain i) :=
          (IsAltPos_antipode_iff_isAltNeg hantipodal P.1).mp hposAnti
        exact IsAltPos.not_isAltNeg (Nat.succ_pos r) P.2 hnegP
      simp [hupper, hupperAnti, hnotPosAnti]
      apply Subtype.ext
      exact SignedPermutation.antipode_involutive P.1

theorem upper_top_card_eq_full_alt_pos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Fintype.card
        {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} =
      Fintype.card (FullAltPosChain label) :=
  Fintype.card_congr (upperTopEquivFullAltPos hantipodal)

theorem IsAltPos_one_iff_positiveAlternatingPrefixLabels {m : ℕ}
    (label : NonzeroSignedSubset 1 → SignedLabel m)
    (P : SignedPermutation 1) :
    IsAltPos label (fun i : Fin 1 => P.prefixChain i) ↔
      PositiveAlternatingPrefixLabels label P := by
  classical
  constructor
  · rintro ⟨idx, _hidx, hset⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a
      fin_cases b
      omega
    · intro i
      fin_cases i
      have hmem :
          label (P.prefixChain 0) ∈
            alternatingLabelSetOf idx := by
        have hmemSimplex :
            label (P.prefixChain 0) ∈
              simplexLabelSet label (fun i : Fin 1 => P.prefixChain i) := by
          simp [simplexLabelSet]
        simpa [hset] using hmemSimplex
      have hlabel :
          label (P.prefixChain 0) = alternatingLabelOf idx 0 := by
        simpa [alternatingLabelSetOf] using hmem
      simpa [alternatingLabelOf] using
        congrArg SignedLabel.positive hlabel
  · rintro ⟨hstrict, hsign⟩
    refine ⟨fun i : Fin 1 => (label (P.prefixChain i)).index, hstrict, ?_⟩
    have hlabel :
        label (P.prefixChain 0) =
          alternatingLabelOf
            (fun i : Fin 1 => (label (P.prefixChain i)).index) 0 := by
      apply SignedLabel.ext
      · simpa [alternatingLabelOf] using hsign 0
      · rfl
    ext x
    constructor
    · intro hx
      have hx0 : x = label (P.prefixChain 0) := by
        simpa [simplexLabelSet] using hx
      rw [hx0]
      simp [alternatingLabelSetOf, hlabel]
    · intro hx
      have hx0 :
          x =
            alternatingLabelOf
              (fun i : Fin 1 => (label (P.prefixChain i)).index) 0 := by
        simpa [alternatingLabelSetOf] using hx
      rw [hx0]
      simp [simplexLabelSet, hlabel]

noncomputable def fullAltPosChainEquivPositiveAlternatingPrefixLabelChains_one
    {m : ℕ} (label : NonzeroSignedSubset 1 → SignedLabel m) :
    FullAltPosChain label ≃
      {P : SignedPermutation 1 // P ∈ positiveAlternatingPrefixLabelChains label} where
  toFun P :=
    ⟨P.1, by
      classical
      have hpos :
          PositiveAlternatingPrefixLabels label P.1 :=
        (IsAltPos_one_iff_positiveAlternatingPrefixLabels label P.1).mp P.2
      simpa [positiveAlternatingPrefixLabelChains, hpos]⟩
  invFun P :=
    ⟨P.1, by
      classical
      apply (IsAltPos_one_iff_positiveAlternatingPrefixLabels label P.1).mpr
      have hmem := P.2
      change P.1 ∈
        (Finset.univ.filter fun P : SignedPermutation 1 =>
          PositiveAlternatingPrefixLabels label P) at hmem
      exact (Finset.mem_filter.mp hmem).2⟩
  left_inv := by
    intro P
    rfl
  right_inv := by
    intro P
    rfl

theorem fullAltPosChain_card_eq_positiveAlternatingPrefixLabelChains_one
    {m : ℕ} (label : NonzeroSignedSubset 1 → SignedLabel m) :
    Fintype.card (FullAltPosChain label) =
      (positiveAlternatingPrefixLabelChains label).card := by
  calc
    Fintype.card (FullAltPosChain label) =
        Fintype.card
          {P : SignedPermutation 1 // P ∈ positiveAlternatingPrefixLabelChains label} :=
      Fintype.card_congr
        (fullAltPosChainEquivPositiveAlternatingPrefixLabelChains_one label)
    _ = (positiveAlternatingPrefixLabelChains label).card := by
      rw [Fintype.card_subtype]
      simp

theorem fullAltPosChain_one_odd {m : ℕ} (hm : 1 ≤ m)
    {label : NonzeroSignedSubset 1 → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (Fintype.card (FullAltPosChain label)) := by
  have hposOdd :=
    (kyFanParityStatement_one (m := m) hm) (by omega) hm
      label hantipodal hno
  rw [fullAltPosChain_card_eq_positiveAlternatingPrefixLabelChains_one]
  exact hposOdd

theorem fan_sphere_parity :
    ∀ r m : ℕ,
      1 ≤ r →
        r ≤ m →
          ∀ label : NonzeroSignedSubset r → SignedLabel m,
            (∀ X, label X.antipode = (label X).neg) →
              NoComplementaryComparableLabels label →
                Odd (Fintype.card (FullAltPosChain label)) := by
  intro r
  induction r with
  | zero =>
      intro m hr _hm _label _hantipodal _hno
      omega
  | succ r ih =>
      cases r with
      | zero =>
          intro m _hr hm label hantipodal hno
          exact fullAltPosChain_one_odd hm hantipodal hno
      | succ r =>
          intro m _hr hm label hantipodal hno
          let labelEq : NonzeroSignedSubset (r + 1) → SignedLabel m :=
            equatorRestrictedLabelOf label
          have heqOdd :
              Odd (Fintype.card (FullAltPosChain labelEq)) := by
            exact ih m (by omega) (by omega) labelEq
              (equatorRestrictedLabelOf_antipodal hantipodal)
              (equatorRestrictedLabelOf_noComplementary hno)
          have hboundaryOdd :
              Odd (Fintype.card
                {rho : ActualHemisphereAltRidge label //
                  actualHemisphereAltBoundary rho}) := by
            have hboundaryCard := equatorBoundaryAltCardBridge label
            have heqCard := equatorActualAlt_card_eq_full_alt_pos labelEq
            rw [hboundaryCard, heqCard]
            exact heqOdd
          have htopOdd :
              Odd (Fintype.card
                {sigma : ActualHemisphereAltChain label //
                  actualHemisphereAltTop sigma}) :=
            ball_parity (hr := by omega) hno hboundaryOdd
          rw [upper_top_card_eq_full_alt_pos hantipodal] at htopOdd
          exact htopOdd

theorem strictMono_fin_self_eq_id {d : ℕ} {idx : Fin d → Fin d}
    (hidx : StrictMono idx) :
    idx = fun i => i := by
  funext i
  exact le_antisymm (StrictMono.le_id hidx i) (StrictMono.id_le hidx i)

theorem IsAltPos_iff_label_set_A {d : ℕ}
    {label : NonzeroSignedSubset d → SignedLabel d}
    {rho : Fin d → NonzeroSignedSubset d} :
    IsAltPos label rho ↔
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a := by
  classical
  constructor
  · rintro ⟨idx, hidx, hset⟩ a
    have hidxId : idx = fun i : Fin d => i :=
      strictMono_fin_self_eq_id hidx
    subst idx
    have hmemAlt :
        alternatingLabel a ∈
          alternatingLabelSetOf (fun i : Fin d => i) := by
      simp [alternatingLabelSetOf, alternatingLabelOf, alternatingLabel]
    have hmemSimplex :
        alternatingLabel a ∈ simplexLabelSet label rho := by
      simpa [hset] using hmemAlt
    rcases (by simpa [simplexLabelSet] using hmemSimplex) with ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro hA
    refine ⟨fun i : Fin d => i, (fun _ _ h => h), ?_⟩
    have hsubset :
        alternatingLabelSetOf (fun i : Fin d => i) ⊆
          simplexLabelSet label rho := by
      intro x hx
      rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
      rcases hA a with ⟨t, ht⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      rw [← ha]
      simpa [alternatingLabelOf, alternatingLabel] using ht
    have hsimplexCard :
        (simplexLabelSet label rho).card ≤ d := by
      dsimp [simplexLabelSet]
      calc
        (Finset.univ.image fun a : Fin d => label (rho a)).card ≤
            (Finset.univ : Finset (Fin d)).card :=
          Finset.card_image_le
        _ = d := by simp
    have hAltCard :
        (alternatingLabelSetOf (fun i : Fin d => i)).card = d :=
      alternatingLabelSetOf_card (Function.injective_id)
    have hcard :
        (simplexLabelSet label rho).card ≤
          (alternatingLabelSetOf (fun i : Fin d => i)).card := by
      simpa [hAltCard] using hsimplexCard
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

noncomputable def equatorActualARidgeEquivEquatorActualAltRidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    EquatorActualARidge label ≃ EquatorActualAltRidge label where
  toFun rho :=
    ⟨rho.1, rho.2.1, (IsAltPos_iff_label_set_A).mpr rho.2.2⟩
  invFun rho :=
    ⟨rho.1, rho.2.1, (IsAltPos_iff_label_set_A).mp rho.2.2⟩
  left_inv := by
    intro rho
    rfl
  right_inv := by
    intro rho
    rfl

theorem equatorActualARidge_card_eq_full_alt_pos {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype.card (EquatorActualARidge label) =
      Fintype.card (FullAltPosChain label) := by
  calc
    Fintype.card (EquatorActualARidge label) =
        Fintype.card (EquatorActualAltRidge label) :=
      Fintype.card_congr (equatorActualARidgeEquivEquatorActualAltRidge label)
    _ = Fintype.card (FullAltPosChain label) :=
      equatorActualAlt_card_eq_full_alt_pos label

/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/

/-- One induction step of Ky Fan parity from the equator count and the two
degree facts.  This is the formal handshaking step; the remaining geometric
work is to instantiate `RhoDegreeManifoldData` for actual hemisphere ridges
and prove the corresponding sigma degree classifier. -/
theorem kyFan_parity_step_from_rho_sigma_data
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topAlternating : S → Prop) [DecidablePred topAlternating]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topAlternating s))
    (hboundary :
      Odd (Fintype.card {r : R // D.boundary r})) :
    Odd (Fintype.card {s : S // topAlternating s}) := by
  have hmod := D.boundary_top_parity topAlternating hs
  have hb : (Fintype.card {r : R // D.boundary r} : ZMod 2) = 1 :=
    hboundary.natCast_zmod_two
  have ht : (Fintype.card {s : S // topAlternating s} : ZMod 2) = 1 := by
    simpa [hb] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht

/-- The final reduction data from the Chapter 39 proof note: the boundary
label-set-`A` ridges are odd, rho degrees are `1/2`, and sigma degree one is
classified by the local `sigmaDoorSet` lemma above.  This theorem is deliberately
not an empty-type shortcut: it requires an explicit `Nonempty R`. -/
theorem final_reduction_from_label_set_A_graph
    {R M : Type*} [Fintype R] [Fintype M]
    (D : RhoDegreeManifoldData R M)
    (oneDoor : M → Prop) [DecidablePred oneDoor]
    (hm :
      ∀ m : M,
        (Odd (Fintype.card {r : R // D.edge r m}) ↔ oneDoor m))
    (hboundaryOdd : Odd (Fintype.card {r : R // D.boundary r})) :
    ∃ m : M, oneDoor m := by
  have hodd : Odd (Fintype.card {m : M // oneDoor m}) :=
    kyFan_parity_step_from_rho_sigma_data D oneDoor hm hboundaryOdd
  have hpos : 0 < Fintype.card {m : M // oneDoor m} := by
    rcases hodd with ⟨a, ha⟩
    omega
  obtain ⟨m⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨m.1, m.2⟩

theorem actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair {d : ℕ}
    (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    ∃ P : SignedPermutation (d + 1), ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive := by
  classical
  let D : RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
    actualHemisphereRhoDegreeData hd
      (actualHemisphereARidge_nonempty_of_boundary_odd hboundaryOdd)
  obtain ⟨sigma, hsigmaOneDoor⟩ :=
    final_reduction_from_label_set_A_graph
      (D := D)
      (oneDoor := actualHemisphereAOneDoor (label := label))
      (hm := actualHemisphereA_sigma_odd_degree_iff_oneDoor)
      hboundaryOdd
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet
        (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  have hdoorCard :
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1 := by
    simpa [actualHemisphereAOneDoor] using hsigmaOneDoor
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door
      (label := label) (P := sigma.1) (extra := gap)
      hdoorExtra hdoorCard
  exact ⟨sigma.1, i, j, hij, hidx, hsign⟩

def ActualHemisphereBoundaryOddStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card
          {rho : ActualHemisphereARidge label //
            actualHemisphereABoundary rho})

def EquatorBoundaryCardBridgeStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Fintype.card
            {rho : ActualHemisphereARidge label //
              actualHemisphereABoundary rho} =
          Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))

theorem equatorBoundaryCardBridge (d : ℕ) :
    EquatorBoundaryCardBridgeStatement d := by
  intro label _hantipodal _hno
  exact Fintype.card_congr (equatorBoundaryARidgeEquiv label)

theorem actualHemisphereBoundaryOdd_of_equator_card_bridge {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    ActualHemisphereBoundaryOddStatement d := by
  intro label hantipodal hno
  have hodd :=
    equatorRestrictedLabel_unordered_odd hKy hantipodal hno
  have hcard := hbridge label hantipodal hno
  simpa [hcard] using hodd

theorem tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd {d : ℕ}
    (hd : 0 < d)
    (hboundaryOdd : ActualHemisphereBoundaryOddStatement d) :
    TuckerLemmaStatement (d + 1) := by
  apply tuckerLemmaStatement_of_chain_complementary_of_no_complementary
  intro label hantipodal hno
  exact actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair hd
    (hboundaryOdd label hantipodal hno)

theorem tuckerLemmaStatement_succ_of_equator_boundary_card_bridge {d : ℕ}
    (hd : 1 ≤ d) (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    TuckerLemmaStatement (d + 1) :=
  tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd hd
    (actualHemisphereBoundaryOdd_of_equator_card_bridge hKy hbridge)

theorem tuckerLemma_pos_of_kyFanUnordered
    (hKy : ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ d =>
      cases d with
      | zero =>
          exact tuckerLemmaStatement_one
      | succ e =>
          exact tuckerLemmaStatement_succ_of_equator_boundary_card_bridge
            (d := e + 1) (by omega) (hKy (e + 1) (by omega))
            (equatorBoundaryCardBridge (e + 1))

theorem kyFanUnordered_all :
    ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d := by
  intro d hd label hantipodal hno
  have hfull :
      Odd (Fintype.card (FullAltPosChain label)) :=
    fan_sphere_parity d d hd le_rfl label hantipodal hno
  rw [equatorActualARidge_card_eq_full_alt_pos label]
  exact hfull

theorem tuckerLemma_pos :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n :=
  tuckerLemma_pos_of_kyFanUnordered kyFanUnordered_all

/-- Fan parity induction, separated from the geometric hemisphere step.  The
step is intended to be supplied by `kyFan_parity_step_from_rho_sigma_data`
after transporting the equator by `equatorEquiv`. -/
theorem kyFanParityStatement_of_induction_steps
    (hstep :
      ∀ r m : ℕ,
        1 ≤ r →
          r + 1 ≤ m →
            KyFanParityStatement r m →
              KyFanParityStatement (r + 1) m) :
    ∀ r m : ℕ, 1 ≤ r → r ≤ m → KyFanParityStatement r m := by
  intro r
  induction r with
  | zero =>
      intro m hr _hm
      omega
  | succ r ih =>
      cases r with
      | zero =>
          intro m _hr hm
          exact kyFanParityStatement_one hm
      | succ r =>
          intro m _hr hm
          apply hstep (r + 1) m
          · omega
          · simpa [Nat.succ_eq_add_one, add_assoc] using hm
          · exact ih m (by omega) (by omega)

/-- The final label-set-`A` graph reduction, with the graph-theoretic parity
and the local sigma-door classifier separated.  This is the precise output
needed by `tuckerLemmaStatement_of_chain_complementary`. -/
theorem final_reduction_graph_gives_prefixChain_complementary_pair {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {R M : Type*} [Fintype R] [Fintype M]
    (D : RhoDegreeManifoldData R M)
    (oneDoor : M → Prop) [DecidablePred oneDoor]
    (hm :
      ∀ m : M,
        (Odd (Fintype.card {r : R // D.edge r m}) ↔ oneDoor m))
    (hboundaryOdd : Odd (Fintype.card {r : R // D.boundary r}))
    (chainOf : M → SignedPermutation (d + 1))
    (extraOf : M → Fin (d + 1))
    (hridge :
      ∀ m : M,
        oneDoor m →
          ∀ a : Fin d,
            label ((chainOf m).prefixChain ((extraOf m).succAbove a)) = alternatingLabel a)
    (hdoor :
      ∀ m : M,
        oneDoor m →
          (sigmaDoorSet (fun i => label ((chainOf m).prefixChain i))).card = 1) :
    ∃ P : SignedPermutation (d + 1), ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive := by
  obtain ⟨m, hmone⟩ :=
    final_reduction_from_label_set_A_graph D oneDoor hm hboundaryOdd
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_prefixChain_complementary_pair (d := d) hd
      (label := label) (P := chainOf m) (extra := extraOf m)
      (hridge m hmone) (hdoor m hmone)
  exact ⟨chainOf m, i, j, hij, hidx, hsign⟩

/-- **Kneser–Lovász theorem (Chapter 39), unconditional.**  The chromatic number of the
Kneser graph `KG(n, k)` (for `1 ≤ k` and `2k ≤ n`) is exactly `n - 2k + 2`: there is a proper
colouring with `n - 2k + 2` colours and none with `n - 2k + 1`.  The Tucker hypothesis of
`chapter39` is discharged by the now-proven `tuckerLemma_pos`, since `2k ≤ n` and `1 ≤ k`
give `1 ≤ n`. -/
theorem chapter39_unconditional {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemma_pos n (by omega))

end ProofsInTheBook.Chapter39
