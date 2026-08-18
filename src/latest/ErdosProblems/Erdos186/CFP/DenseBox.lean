/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Elementary
import ErdosProblems.Erdos186.CFP.FiniteGroupCover
import ErdosProblems.Erdos186.CFP.Lev
import ErdosProblems.Erdos186.CFP.AdaptedHNF
import ErdosProblems.Erdos186.CFP.AdaptedHNFInverse
import ErdosProblems.Erdos186.CFP.LatticeQuotientCover
import ErdosProblems.Erdos186.CFP.SymmetricGAP

/-!
# Dense subsets of integer boxes

This file formalizes Definitions 2.13 and 2.14 and the conclusion of
Lemma 2.15 in Conlon--Fox--Pham, *Homogeneous structures in subset sums and
non-averaging sets*.

An `AxisBox d` is a nonempty axis-parallel box in `Z^d`, recorded by its
lower corner and its positive widths.  A finite set is `Reduced` if its image
in every nontrivial rectangular quotient is not contained in a coset of a
proper subgroup.  The quotient formulation is literally Definition 2.14:
the rectangular subgroup attached to `v` is
`v 0 * Z x ... x v (d-1) * Z`.

We use `heterogeneousSumset` for `A_0 + ... + A_(ell-1)`.  The natural-number
dilation `Q.dilate k` has widths `k * (w_i - 1) + 1`; hence it is a translate
of the usual `k`-fold sum of `Q`.  Stating the quantitative conclusion with
`k = ell / C` is the exact integer-rounded form of "a translate of
`gamma * ell * Q`", with `gamma = 1 / C`.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

noncomputable section

abbrev BoxPoint (d : ℕ) := LatticePoint d

/-! ## Axis-parallel integer boxes -/

/-- A nonempty axis-parallel box in `Z^d`, presented by its lower corner and
positive coordinate widths. -/
structure AxisBox (d : ℕ) where
  lower : BoxPoint d
  widths : Fin d → ℕ
  width_pos : ∀ i, 0 < widths i

namespace AxisBox

variable {d : ℕ}

/-- The closed integer interval in coordinate `i`. -/
def interval (Q : AxisBox d) (i : Fin d) : Finset ℤ :=
  Finset.Icc (Q.lower i) (Q.lower i + (Q.widths i : ℤ) - 1)

/-- The finite carrier of an axis-parallel integer box. -/
def carrier (Q : AxisBox d) : Finset (BoxPoint d) :=
  Fintype.piFinset Q.interval

@[simp] theorem mem_interval_iff (Q : AxisBox d) {i : Fin d} {x : ℤ} :
    x ∈ Q.interval i ↔ Q.lower i ≤ x ∧
      x < Q.lower i + (Q.widths i : ℤ) := by
  simp only [interval, Finset.mem_Icc]
  omega

@[simp] theorem mem_carrier_iff (Q : AxisBox d) {x : BoxPoint d} :
    x ∈ Q.carrier ↔ ∀ i, Q.lower i ≤ x i ∧
      x i < Q.lower i + (Q.widths i : ℤ) := by
  simp [carrier]

/-- The displayed volume of a box. -/
def volume (Q : AxisBox d) : ℕ :=
  ∏ i, Q.widths i

@[simp] theorem card_interval (Q : AxisBox d) (i : Fin d) :
    (Q.interval i).card = Q.widths i := by
  rw [interval, Int.card_Icc]
  have h : Q.lower i + (Q.widths i : ℤ) - 1 + 1 - Q.lower i =
      (Q.widths i : ℤ) := by ring
  rw [h]
  simp

@[simp] theorem card_carrier (Q : AxisBox d) :
    Q.carrier.card = Q.volume := by
  simp [carrier, volume]

/-- Translation changes only the lower corner. -/
def translate (t : BoxPoint d) (Q : AxisBox d) : AxisBox d where
  lower := t + Q.lower
  widths := Q.widths
  width_pos := Q.width_pos

@[simp] theorem translate_widths (t : BoxPoint d) (Q : AxisBox d) :
    (Q.translate t).widths = Q.widths := rfl

theorem carrier_translate (t : BoxPoint d) (Q : AxisBox d) :
    (Q.translate t).carrier = Elementary.translate t Q.carrier := by
  classical
  ext x
  rw [mem_carrier_iff, Elementary.mem_translate_iff]
  constructor
  · intro hx
    refine ⟨x - t, ?_, by simp⟩
    rw [mem_carrier_iff]
    intro i
    simpa [translate, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hx i
  · rintro ⟨y, hy, rfl⟩
    rw [mem_carrier_iff] at hy
    intro i
    simpa [translate, add_assoc, add_comm, add_left_comm] using hy i

/-- The origin-based box with the shape of the `k`-fold sum of `Q`.
Its coordinate widths are `k * (w_i - 1) + 1`. -/
def dilate (k : ℕ) (Q : AxisBox d) : AxisBox d where
  lower := 0
  widths := fun i ↦ k * (Q.widths i - 1) + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp] theorem dilate_lower (k : ℕ) (Q : AxisBox d) :
    (Q.dilate k).lower = 0 := rfl

@[simp] theorem dilate_width (k : ℕ) (Q : AxisBox d) (i : Fin d) :
    (Q.dilate k).widths i = k * (Q.widths i - 1) + 1 := rfl

@[simp] theorem dilate_zero_carrier (Q : AxisBox d) :
    (Q.dilate 0).carrier = {0} := by
  classical
  ext x
  simp only [mem_carrier_iff, dilate_lower, Pi.zero_apply, dilate_width,
    zero_mul, zero_add, Nat.cast_one, add_zero, Finset.mem_singleton]
  constructor
  · intro hx
    funext i
    have hi := hx i
    change x i = 0
    omega
  · rintro rfl
    intro i
    change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < 1
    omega

/-- The minimum displayed width.  In dimension zero it is set to zero; the
dense-box theorem is only asserted in positive dimension. -/
def minWidth (Q : AxisBox d) : ℕ :=
  if h : 0 < d then
    Finset.univ.inf' (show Finset.univ.Nonempty from
      ⟨⟨0, h⟩, Finset.mem_univ _⟩) Q.widths
  else 0

theorem minWidth_le (Q : AxisBox d) (hd : 0 < d) (i : Fin d) :
    Q.minWidth ≤ Q.widths i := by
  rw [minWidth, dif_pos hd]
  exact Finset.inf'_le Q.widths (Finset.mem_univ i)

end AxisBox

/-! ## Rectangular quotients and reduction -/

/-- The finite quotient by the rectangular subgroup
`v_0 Z x ... x v_(d-1) Z`. -/
abbrev RectangularQuotient {d : ℕ} (v : Fin d → ℕ) :=
  (i : Fin d) → ZMod (v i)

/-- Reduction modulo a rectangular subgroup. -/
def rectangularResidue {d : ℕ} (v : Fin d → ℕ) (x : BoxPoint d) :
    RectangularQuotient v :=
  fun i ↦ (x i : ZMod (v i))

@[simp] theorem rectangularResidue_zero {d : ℕ} (v : Fin d → ℕ) :
    rectangularResidue v 0 = 0 := by
  funext i
  simp [rectangularResidue]

@[simp] theorem rectangularResidue_add {d : ℕ} (v : Fin d → ℕ)
    (x y : BoxPoint d) :
    rectangularResidue v (x + y) = rectangularResidue v x + rectangularResidue v y := by
  funext i
  simp [rectangularResidue]

/-- A tuple of positive periods defines a proper rectangular subgroup when
at least one period is greater than one. -/
def ProperRectangularPeriods {d : ℕ} (v : Fin d → ℕ) : Prop :=
  (∀ i, 0 < v i) ∧ ∃ i, 1 < v i

/-- Definition 2.14 (Conlon--Fox--Pham): the image in no nontrivial
rectangular quotient is contained in a coset of a proper subgroup. -/
def Reduced {d : ℕ} (A : Finset (BoxPoint d)) : Prop :=
  ∀ (v : Fin d → ℕ), ProperRectangularPeriods v →
    ∀ (H : AddSubgroup (RectangularQuotient v)), H ≠ ⊤ →
      ∀ a : RectangularQuotient v,
        ∃ x ∈ A, rectangularResidue v x - a ∉ H

theorem reduced_iff_notInProperCoset {d : ℕ} {A : Finset (BoxPoint d)} :
    Reduced A ↔ ∀ (v : Fin d → ℕ), ProperRectangularPeriods v →
      ∀ (H : AddSubgroup (RectangularQuotient v)), H ≠ ⊤ →
        ∀ a : RectangularQuotient v,
          ∃ x ∈ A, rectangularResidue v x - a ∉ H := by
  rfl

/-- Quotient formulation of `Reduced`, using the no-proper-coset predicate
from CFP Claim 2.12.  The all-periods-one quotient is trivial and the claim
there is automatic. -/
theorem Reduced.notInProperCoset_residue {d : ℕ}
    {A : Finset (BoxPoint d)} (hA : Reduced A) (v : Fin d → ℕ)
    (hv : ∀ i, 0 < v i) :
    NotInProperCoset
      ((A.image (rectangularResidue v) : Finset (RectangularQuotient v)) :
        Set (RectangularQuotient v)) := by
  classical
  letI (i : Fin d) : NeZero (v i) := ⟨Nat.ne_of_gt (hv i)⟩
  intro H hH a hcontained
  by_cases hproper : ∃ i, 1 < v i
  · obtain ⟨x, hx, hxout⟩ := hA v ⟨hv, hproper⟩ H hH a
    exact hxout (hcontained (rectangularResidue v x)
      (by exact Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  · have hvone : ∀ i, v i = 1 := by
      intro i
      have := hv i
      have hnot : ¬ 1 < v i := fun hi ↦ hproper ⟨i, hi⟩
      omega
    have hsubsingleton : Subsingleton (RectangularQuotient v) := by
      constructor
      intro x y
      funext i
      have hi : Fintype.card (ZMod (v i)) ≤ 1 := by
        rw [ZMod.card, hvone i]
      letI : Subsingleton (ZMod (v i)) := ⟨Fintype.card_le_one_iff.mp hi⟩
      exact Subsingleton.elim _ _
    letI : Subsingleton (RectangularQuotient v) := hsubsingleton
    exact hH (Subsingleton.elim H ⊤)

/-- Reduction is invariant under translation. -/
theorem reduced_translate {d : ℕ} (t : BoxPoint d)
    (A : Finset (BoxPoint d)) (hA : Reduced A) :
    Reduced (Elementary.translate t A) := by
  classical
  intro v hv H hH a
  obtain ⟨x, hx, hxa⟩ := hA v hv H hH (a - rectangularResidue v t)
  refine ⟨t + x, Elementary.mem_translate_iff.mpr ⟨x, hx, rfl⟩, ?_⟩
  simpa [rectangularResidue, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    using hxa

theorem reduced_translate_iff {d : ℕ} (t : BoxPoint d)
    (A : Finset (BoxPoint d)) :
    Reduced (Elementary.translate t A) ↔ Reduced A := by
  constructor
  · intro h
    have h' := reduced_translate (-t) (Elementary.translate t A) h
    simpa [Elementary.translate_translate] using h'
  · exact reduced_translate t A

/-! ## Heterogeneous iterated sumsets -/

/-- The pointwise sum of a family of finite sets indexed by `Fin ell`.
For `ell = 0` this is the singleton `{0}`. -/
def heterogeneousSumset {d ell : ℕ}
    (A : Fin ell → Finset (BoxPoint d)) : Finset (BoxPoint d) :=
  (List.ofFn A).sum

@[simp] theorem heterogeneousSumset_zero {d : ℕ}
    (A : Fin 0 → Finset (BoxPoint d)) :
    heterogeneousSumset A = {0} := by
  rfl

/-- Membership in a heterogeneous sumset is witnessed by one choice from
each summand. -/
theorem mem_heterogeneousSumset {d ell : ℕ}
    {A : Fin ell → Finset (BoxPoint d)} {x : BoxPoint d} :
    x ∈ heterogeneousSumset A ↔
      ∃ a : Fin ell → BoxPoint d, (∀ i, a i ∈ A i) ∧ ∑ i, a i = x := by
  classical
  rw [heterogeneousSumset, Finset.mem_sum_list_ofFn]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i ↦ f i, fun i ↦ (f i).property, ?_⟩
    simpa [List.sum_ofFn] using hf
  · rintro ⟨a, ha, hsum⟩
    let f : ∀ i : Fin ell, A i := fun i ↦ ⟨a i, ha i⟩
    refine ⟨f, ?_⟩
    simpa [f, List.sum_ofFn] using hsum

/-- Heterogeneous sumsets are monotone in every summand. -/
theorem heterogeneousSumset_mono {d ell : ℕ}
    {A B : Fin ell → Finset (BoxPoint d)}
    (hAB : ∀ i, A i ⊆ B i) :
    heterogeneousSumset A ⊆ heterogeneousSumset B := by
  intro x hx
  rw [mem_heterogeneousSumset] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, fun i ↦ hAB i (ha i), rfl⟩

/-- Translating every summand translates the iterated sumset by the sum of
the translation vectors. -/
theorem heterogeneousSumset_translate {d ell : ℕ}
    (t : Fin ell → BoxPoint d) (A : Fin ell → Finset (BoxPoint d)) :
    heterogeneousSumset (fun i ↦ Elementary.translate (t i) (A i)) =
      Elementary.translate (∑ i, t i) (heterogeneousSumset A) := by
  classical
  ext x
  rw [mem_heterogeneousSumset, Elementary.mem_translate_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    choose b hb hab using fun i ↦ Elementary.mem_translate_iff.mp (ha i)
    refine ⟨∑ i, b i, mem_heterogeneousSumset.mpr ⟨b, hb, rfl⟩, ?_⟩
    simp_rw [← hab]
    rw [← Finset.sum_add_distrib]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_heterogeneousSumset.mp hx
    refine ⟨fun i ↦ t i + a i, ?_, ?_⟩
    · exact fun i ↦ Elementary.mem_translate_iff.mpr ⟨a i, ha i, rfl⟩
    · rw [Finset.sum_add_distrib]

/-- Choosing one point from every summand gives a point of the heterogeneous
sumset. -/
theorem sum_mem_heterogeneousSumset {d ell : ℕ}
    {A : Fin ell → Finset (BoxPoint d)}
    (a : Fin ell → BoxPoint d) (ha : ∀ i, a i ∈ A i) :
    (∑ i, a i) ∈ heterogeneousSumset A :=
  mem_heterogeneousSumset.mpr ⟨a, ha, rfl⟩

/-- Pointwise sum over a selected set of indices. -/
def partialSumset {d ell : ℕ} (A : Fin ell → Finset (BoxPoint d))
    (I : Finset (Fin ell)) : Finset (BoxPoint d) :=
  ∑ i ∈ I, A i

/-- An injectively reindexed heterogeneous sum is exactly the partial
sumset over the image indices.  This lets each coordinate block be handled
with a convenient `Fin m` index while retaining disjoint source indices. -/
theorem heterogeneousSumset_reindex_injective {d ell m : ℕ}
    (A : Fin ell → Finset (BoxPoint d)) (e : Fin m → Fin ell)
    (he : Function.Injective e) :
    heterogeneousSumset (fun i ↦ A (e i)) =
      partialSumset A (Finset.univ.image e) := by
  classical
  rw [heterogeneousSumset, List.sum_ofFn]
  change (∑ i, A (e i)) = ∑ i ∈ Finset.univ.image e, A i
  exact (Finset.sum_image (Set.injOn_of_injective he)).symm

/-- The natural-number and finite-index presentations of the first `m`
summands agree. -/
theorem iteratedSumset_fin {d m : ℕ}
    (A : Fin m → Finset (BoxPoint d)) :
    iteratedSumset
        (fun i ↦ if hi : i < m then A ⟨i, hi⟩ else {0}) m =
      heterogeneousSumset A := by
  classical
  rw [iteratedSumset, heterogeneousSumset, List.sum_ofFn]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [i.isLt]

theorem elementary_sumset_eq_pointwise_add {d : ℕ}
    (S T : Finset (BoxPoint d)) :
    Elementary.sumset S T = S + T := by
  classical
  ext x
  rw [Elementary.mem_sumset_iff, Finset.mem_add]

/-- Translating the right summand translates the whole sumset. -/
theorem elementary_sumset_translate_right {d : ℕ}
    (S T : Finset (BoxPoint d)) (r : BoxPoint d) :
    Elementary.sumset S (Elementary.translate r T) =
      Elementary.translate r (Elementary.sumset S T) := by
  classical
  ext x
  simp only [Elementary.mem_sumset_iff, Elementary.mem_translate_iff]
  constructor
  · rintro ⟨s, hs, y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨s + t, ⟨s, hs, t, ht, rfl⟩, by abel⟩
  · rintro ⟨z, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, r + t, ⟨t, ht, rfl⟩, by abel⟩

theorem partialSumset_union_of_disjoint {d ell : ℕ}
    (A : Fin ell → Finset (BoxPoint d)) {I J : Finset (Fin ell)}
    (hIJ : Disjoint I J) :
    Elementary.sumset (partialSumset A I) (partialSumset A J) =
      partialSumset A (I ∪ J) := by
  rw [elementary_sumset_eq_pointwise_add]
  change (∑ i ∈ I, A i) + (∑ i ∈ J, A i) = ∑ i ∈ I ∪ J, A i
  exact (Finset.sum_union hIJ).symm

theorem heterogeneousSumset_eq_partial_add_complement {d ell : ℕ}
    (A : Fin ell → Finset (BoxPoint d)) (I : Finset (Fin ell)) :
    heterogeneousSumset A =
      partialSumset A I + partialSumset A (Finset.univ \ I) := by
  classical
  rw [heterogeneousSumset, List.sum_ofFn]
  rw [show (∑ i, A i) =
      (∑ i ∈ Finset.univ \ I, A i) + ∑ i ∈ I, A i by
    exact (Finset.sum_sdiff (Finset.subset_univ I)).symm]
  simp only [partialSumset, add_comm]

theorem partialSumset_nonempty {d ell : ℕ}
    {A : Fin ell → Finset (BoxPoint d)} (hA : ∀ i, (A i).Nonempty)
    (I : Finset (Fin ell)) :
    (partialSumset A I).Nonempty := by
  classical
  apply Finset.sum_induction A (fun S : Finset (BoxPoint d) ↦ S.Nonempty)
  · intro S T hS hT
    exact hS.add hT
  · exact Finset.zero_nonempty
  · intro i _
    exact hA i

/-- Summing partial sumsets indexed by pairwise-disjoint selected blocks is
the partial sumset over the image of the product index.  Encoding
disjointness as injectivity of the product map makes this identity directly
usable for the coordinate blocks in Lemma 2.15. -/
theorem heterogeneousSumset_partialSumset_product {d ell L : ℕ}
    (A : Fin ell → Finset (BoxPoint d))
    (e : Fin d → Fin L → Fin ell)
    (he : Function.Injective (fun p : Fin d × Fin L ↦ e p.1 p.2)) :
    heterogeneousSumset
        (fun k ↦ partialSumset A (Finset.univ.image (e k))) =
      partialSumset A
        (Finset.univ.image (fun p : Fin d × Fin L ↦ e p.1 p.2)) := by
  classical
  have hek (k : Fin d) : Function.Injective (e k) := by
    intro i j hij
    have hp : (k, i) = (k, j) := he hij
    exact congrArg Prod.snd hp
  rw [heterogeneousSumset, List.sum_ofFn]
  simp only [partialSumset]
  have hinner (k : Fin d) :
      (∑ i ∈ Finset.univ.image (e k), A i) = ∑ i : Fin L, A (e k i) := by
    rw [Finset.sum_image (Set.injOn_of_injective (hek k))]
  simp_rw [hinner]
  rw [Finset.sum_image (Set.injOn_of_injective he)]
  simpa using
    (Fintype.sum_prod_type
      (f := fun p : Fin d × Fin L => A (e p.1 p.2))).symm

/-- Any structured subset made using only selected summands survives in the
full heterogeneous sumset, up to one harmless translation contributed by
the unused nonempty summands. -/
theorem exists_translate_subset_heterogeneousSumset_of_partial {d ell : ℕ}
    {A : Fin ell → Finset (BoxPoint d)} (hA : ∀ i, (A i).Nonempty)
    (I : Finset (Fin ell)) {S : Finset (BoxPoint d)}
    (hS : S ⊆ partialSumset A I) :
    ∃ t : BoxPoint d, Elementary.translate t S ⊆ heterogeneousSumset A := by
  classical
  obtain ⟨t, ht⟩ := partialSumset_nonempty hA (Finset.univ \ I)
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Elementary.mem_translate_iff.mp hx
  rw [heterogeneousSumset_eq_partial_add_complement A I]
  exact Finset.mem_add.mpr
    ⟨s, hS hs, t, ht, add_comm s t⟩

/-! ## Coordinate fibres -/

/-- The cross-section obtained by fixing coordinate `k` at the lower face
of `Q`.  It contains one representative for every line parallel to the
`k`-th coordinate axis which meets `Q`. -/
def coordinateBase {d : ℕ} (Q : AxisBox d) (k : Fin d) :
    Finset (BoxPoint d) :=
  Fintype.piFinset fun i ↦
    if i = k then {Q.lower i} else Q.interval i

/-- Projection to the lower `k`-face, retaining every other coordinate. -/
def coordinateBaseProjection {d : ℕ} (Q : AxisBox d) (k : Fin d)
    (x : BoxPoint d) : BoxPoint d :=
  Function.update x k (Q.lower k)

@[simp] theorem coordinateBaseProjection_same {d : ℕ} (Q : AxisBox d)
    (k : Fin d) (x : BoxPoint d) :
    coordinateBaseProjection Q k x k = Q.lower k := by
  simp [coordinateBaseProjection]

@[simp] theorem coordinateBaseProjection_ne {d : ℕ} (Q : AxisBox d)
    {k i : Fin d} (hki : i ≠ k) (x : BoxPoint d) :
    coordinateBaseProjection Q k x i = x i := by
  simp [coordinateBaseProjection, hki]

theorem coordinateBaseProjection_mem {d : ℕ} (Q : AxisBox d)
    (k : Fin d) {x : BoxPoint d} (hx : x ∈ Q.carrier) :
    coordinateBaseProjection Q k x ∈ coordinateBase Q k := by
  classical
  rw [AxisBox.mem_carrier_iff] at hx
  simp only [coordinateBase, Fintype.mem_piFinset]
  intro i
  by_cases hik : i = k
  · subst i
    simp
  · simp only [hik, ↓reduceIte]
    rw [AxisBox.mem_interval_iff]
    simpa [coordinateBaseProjection, hik] using hx i

/-- The points of `A` lying on the coordinate line represented by `y`. -/
def coordinateFiber {d : ℕ} (Q : AxisBox d) (A : Finset (BoxPoint d))
    (k : Fin d) (y : BoxPoint d) : Finset (BoxPoint d) :=
  A.filter fun x ↦ coordinateBaseProjection Q k x = y

/-- The set of `k`-th coordinates occurring in a coordinate fibre. -/
def coordinateFiberValues {d : ℕ} (Q : AxisBox d)
    (A : Finset (BoxPoint d)) (k : Fin d) (y : BoxPoint d) : Finset ℤ :=
  (coordinateFiber Q A k y).image fun x ↦ x k

theorem coordinateFiberValues_subset_interval {d : ℕ}
    (Q : AxisBox d) {A : Finset (BoxPoint d)} (hA : A ⊆ Q.carrier)
    (k : Fin d) (y : BoxPoint d) :
    coordinateFiberValues Q A k y ⊆ Q.interval k := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  exact (AxisBox.mem_interval_iff Q).2
    (((AxisBox.mem_carrier_iff Q).1 (hA (Finset.mem_filter.mp hx).1)) k)

theorem card_coordinateFiberValues {d : ℕ} (Q : AxisBox d)
    (A : Finset (BoxPoint d)) (k : Fin d) (y : BoxPoint d) :
    (coordinateFiberValues Q A k y).card =
      (coordinateFiber Q A k y).card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx z hz hxz
  have hpx : coordinateBaseProjection Q k x = y :=
    (Finset.mem_filter.mp hx).2
  have hpz : coordinateBaseProjection Q k z = y :=
    (Finset.mem_filter.mp hz).2
  funext i
  by_cases hik : i = k
  · subst i
    exact hxz
  · have hi := congrFun (hpx.trans hpz.symm) i
    simpa [coordinateBaseProjection, hik] using hi

theorem coordinateBase_nonempty {d : ℕ} (Q : AxisBox d) (k : Fin d) :
    (coordinateBase Q k).Nonempty := by
  classical
  refine ⟨coordinateBaseProjection Q k Q.lower, ?_⟩
  simp only [coordinateBase, Fintype.mem_piFinset]
  intro i
  by_cases hik : i = k
  · subst i
    simp
  · simp only [hik, ↓reduceIte]
    rw [AxisBox.mem_interval_iff]
    simp [coordinateBaseProjection, hik, Q.width_pos i]

theorem card_coordinateBase_mul_width {d : ℕ} (Q : AxisBox d) (k : Fin d) :
    (coordinateBase Q k).card * Q.widths k = Q.volume := by
  classical
  simp only [coordinateBase, Fintype.card_piFinset, AxisBox.volume]
  rw [← Finset.prod_erase_mul Finset.univ Q.widths (Finset.mem_univ k)]
  rw [Finset.prod_eq_mul_prod_diff_singleton k
    (fun i ↦ (if i = k then {Q.lower i} else Q.interval i).card) (by simp)]
  simp only [if_pos, Finset.card_singleton, one_mul, Finset.sdiff_singleton_eq_erase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := Finset.ne_of_mem_erase hi
  simp [hik]

/-- A pigeonhole form of the fibre-density step.  The arithmetic hypothesis
is separated from its later density estimate: if `b` times the number of
coordinate lines is at most `|A|`, one line contains at least `b` points. -/
theorem exists_large_coordinateFiber {d : ℕ} (Q : AxisBox d)
    {A : Finset (BoxPoint d)} (hA : A ⊆ Q.carrier) (k : Fin d) (b : ℕ)
    (hb : (coordinateBase Q k).card * b ≤ A.card) :
    ∃ y ∈ coordinateBase Q k,
      b ≤ (coordinateFiberValues Q A k y).card := by
  classical
  obtain ⟨y, hy, hcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := A) (t := coordinateBase Q k)
      (f := coordinateBaseProjection Q k)
      (fun x hx ↦ coordinateBaseProjection_mem Q k (hA hx))
      (coordinateBase_nonempty Q k) hb
  refine ⟨y, hy, ?_⟩
  rw [card_coordinateFiberValues]
  exact hcard

/-- Density supplies a coordinate fibre with a number of points linear in
the coordinate width.  The deliberately coarse denominator `2*cDen` leaves
room for all subsequent integer roundings. -/
theorem exists_dense_coordinateFiber {d : ℕ} (Q : AxisBox d)
    {A : Finset (BoxPoint d)} (hA : A ⊆ Q.carrier) (k : Fin d)
    (cNum cDen : ℕ) (hcNum : 0 < cNum) (hcDen : 0 < cDen)
    (hdensity : cNum * Q.volume ≤ cDen * A.card) :
    ∃ y ∈ coordinateBase Q k,
      Q.widths k / (2 * cDen) ≤
        (coordinateFiberValues Q A k y).card := by
  let b := Q.widths k / (2 * cDen)
  have hbden : b * cDen ≤ Q.widths k := by
    calc
      b * cDen ≤ b * (2 * cDen) := by
        exact Nat.mul_le_mul_left b (by omega)
      _ ≤ Q.widths k := by
        simpa [b, mul_comm] using Nat.div_mul_le_self (Q.widths k) (2 * cDen)
  have hbase : (coordinateBase Q k).card * b ≤ A.card := by
    apply Nat.le_of_mul_le_mul_left (c := cDen) ?_ hcDen
    calc
      cDen * ((coordinateBase Q k).card * b) =
          (coordinateBase Q k).card * (b * cDen) := by ring
      _ ≤ (coordinateBase Q k).card * Q.widths k :=
        Nat.mul_le_mul_left _ hbden
      _ = Q.volume := card_coordinateBase_mul_width Q k
      _ ≤ cNum * Q.volume := by
        exact Nat.le_mul_of_pos_left _ hcNum
      _ ≤ cDen * A.card := hdensity
  simpa [b] using exists_large_coordinateFiber Q hA k b hbase

/-! ## Primitive normalization of one-dimensional fibres -/

/-- Canonical gcd normalization data for a finite one-dimensional fibre.
Every original point is obtained from the normalized primitive set by the
same positive integral dilation and translation. -/
structure PrimitiveNormalization (S : Finset ℤ) where
  anchor : ℤ
  anchor_mem : anchor ∈ S
  anchor_le : ∀ x ∈ S, anchor ≤ x
  step : ℕ
  step_pos : 0 < step
  normalized : Finset ℤ
  normalized_primitive : Lev.Primitive normalized
  card_normalized : normalized.card = S.card
  image_normalized :
    normalized.image (fun z ↦ anchor + (step : ℤ) * z) = S

/-- Dividing all differences from an anchor by their finite gcd produces a
primitive set.  The cardinality-two assumption is exactly what makes the gcd
positive; it will follow from the density and large-width hypotheses in
Lemma 2.15. -/
theorem exists_primitiveNormalization (S : Finset ℤ) (hcard : 2 ≤ S.card) :
    Nonempty (PrimitiveNormalization S) := by
  classical
  have hS : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro h
    rw [h] at hcard
    simp at hcard)
  let a : ℤ := S.min' hS
  let g : ℤ := S.gcd fun x ↦ x - a
  have hxne : ∃ x ∈ S, x - a ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : S ⊆ {a} := by
      intro x hx
      have := h x hx
      simp only [sub_eq_zero] at this
      simpa using this
    have hle := Finset.card_le_card hsub
    simpa using (hcard.trans hle)
  have hg_ne : g ≠ 0 := by
    change S.gcd (fun x ↦ x - a) ≠ 0
    rw [Finset.gcd_ne_zero_iff]
    simpa [a] using hxne
  have hg_nonneg : 0 ≤ g := Finset.Int.finsetGcd_nonneg
  have hg_pos : 0 < g := lt_of_le_of_ne hg_nonneg (Ne.symm hg_ne)
  let T : Finset ℤ := S.image fun x ↦ (x - a) / g
  have hdiv (x : ℤ) (hx : x ∈ S) : g ∣ x - a := by
    exact Finset.gcd_dvd hx
  have hreconstruct (x : ℤ) (hx : x ∈ S) :
      a + g * ((x - a) / g) = x := by
    have hm := Int.ediv_mul_cancel (hdiv x hx)
    rw [mul_comm g, hm]
    ring
  have hTcard : T.card = S.card := by
    change (S.image fun x ↦ (x - a) / g).card = S.card
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hxrec := hreconstruct x hx
    have hyrec := hreconstruct y hy
    change (x - a) / g = (y - a) / g at hxy
    calc
      x = a + g * ((x - a) / g) := hxrec.symm
      _ = a + g * ((y - a) / g) := by rw [hxy]
      _ = y := hyrec
  have hgcd_one : S.gcd (fun x ↦ (x - a) / g) = 1 := by
    obtain ⟨x, hxS, hx0⟩ := hxne
    exact Finset.gcd_div_eq_one hxS hx0
  have haS : a ∈ S := Finset.min'_mem S hS
  have hTprimitive : Lev.Primitive T := by
    by_contra hnot
    obtain ⟨m, hm, hall⟩ := (Lev.not_primitive_iff T).mp hnot
    have hdivall : ∀ x ∈ S, (m : ℤ) ∣ (x - a) / g := by
      intro x hx
      have hxT : (x - a) / g ∈ T :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have haT : (a - a) / g ∈ T :=
        Finset.mem_image.mpr ⟨a, haS, rfl⟩
      have hd := hall ((x - a) / g) hxT ((a - a) / g) haT
      simpa using hd
    have hmone : (m : ℤ) ∣ 1 := by
      rw [← hgcd_one]
      exact Finset.dvd_gcd hdivall
    have hmnat : m ∣ 1 := by exact_mod_cast hmone
    have : m ≤ 1 := Nat.le_of_dvd (by omega) hmnat
    omega
  let v : ℕ := g.natAbs
  have hvcast : (v : ℤ) = g := by
    change (g.natAbs : ℤ) = g
    rw [Int.natCast_natAbs, abs_of_nonneg hg_nonneg]
  have hvpos : 0 < v := by
    exact Int.natAbs_pos.mpr hg_ne
  refine ⟨⟨a, haS, (fun x hx ↦ Finset.min'_le S x hx),
    v, hvpos, T, hTprimitive, hTcard, ?_⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hyS, hyz⟩ := Finset.mem_image.mp hzT
    rw [← hyz]
    rw [hvcast]
    rw [hreconstruct y hyS]
    exact hyS
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(x - a) / g, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    rw [hvcast]
    exact hreconstruct x hx

/-- A primitive normalization of a set in an interval satisfies the sharp
spacing estimate `step * (|S|-1) ≤ intervalLength`.  In particular, a dense
fibre can only have bounded primitive step. -/
theorem PrimitiveNormalization.step_mul_card_sub_one_le
    {S : Finset ℤ} (N : PrimitiveNormalization S) (lo : ℤ) (W : ℕ)
    (hS : S ⊆ Finset.Icc lo (lo + (W : ℤ))) :
    N.step * (S.card - 1) ≤ W := by
  classical
  have hnonneg : ∀ z ∈ N.normalized, 0 ≤ z := by
    intro z hz
    have hx : N.anchor + (N.step : ℤ) * z ∈ S := by
      have hz' : N.anchor + (N.step : ℤ) * z ∈
          N.normalized.image (fun q ↦ N.anchor + (N.step : ℤ) * q) :=
        Finset.mem_image.mpr ⟨z, hz, rfl⟩
      exact (congrArg
        (fun U : Finset ℤ ↦ N.anchor + (N.step : ℤ) * z ∈ U)
        N.image_normalized).mp hz'
    have hle := N.anchor_le _ hx
    have hspos : (0 : ℤ) < (N.step : ℤ) := by exact_mod_cast N.step_pos
    nlinarith
  have hmul : ∀ z ∈ N.normalized, N.step * z.toNat ≤ W := by
    intro z hz
    have hx : N.anchor + (N.step : ℤ) * z ∈ S := by
      have hz' : N.anchor + (N.step : ℤ) * z ∈
          N.normalized.image (fun q ↦ N.anchor + (N.step : ℤ) * q) :=
        Finset.mem_image.mpr ⟨z, hz, rfl⟩
      exact (congrArg
        (fun U : Finset ℤ ↦ N.anchor + (N.step : ℤ) * z ∈ U)
        N.image_normalized).mp hz'
    have hanchorBounds := Finset.mem_Icc.mp (hS N.anchor_mem)
    have hxBounds := Finset.mem_Icc.mp (hS hx)
    have hz0 := hnonneg z hz
    have hZ : (N.step : ℤ) * (z.toNat : ℤ) ≤ (W : ℤ) := by
      rw [Int.toNat_of_nonneg hz0]
      nlinarith
    exact_mod_cast hZ
  have himage : N.normalized.image Int.toNat ⊆
      Finset.range (W / N.step + 1) := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply (Nat.le_div_iff_mul_le N.step_pos).2
    simpa [mul_comm] using hmul z hz
  have hinj : Set.InjOn Int.toNat (N.normalized : Set ℤ) := by
    intro x hx y hy hxy
    have hx0 := hnonneg x hx
    have hy0 := hnonneg y hy
    rw [← Int.toNat_of_nonneg hx0, ← Int.toNat_of_nonneg hy0, hxy]
  have hcardle : S.card ≤ W / N.step + 1 := by
    rw [← N.card_normalized, ← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card himage).trans_eq (Finset.card_range _)
  have hsub : S.card - 1 ≤ W / N.step := by
    apply Nat.sub_le_of_le_add
    simpa [add_comm] using hcardle
  calc
    N.step * (S.card - 1) ≤ N.step * (W / N.step) :=
      Nat.mul_le_mul_left _ hsub
    _ ≤ W := Nat.mul_div_le W N.step

/-- The normalized set lies in the origin-based interval having the same
length as any interval containing the original set.  This deliberately uses
the coarser upper bound `W`, rather than dividing by the normalization step,
so that a whole equal-step block has uniform Lev parameters. -/
theorem PrimitiveNormalization.normalized_subset_Icc_zero
    {S : Finset ℤ} (N : PrimitiveNormalization S) (lo : ℤ) (W : ℕ)
    (hS : S ⊆ Finset.Icc lo (lo + (W : ℤ))) :
    N.normalized ⊆ Finset.Icc 0 (W : ℤ) := by
  intro z hz
  have hx : N.anchor + (N.step : ℤ) * z ∈ S := by
    have hz' : N.anchor + (N.step : ℤ) * z ∈
        N.normalized.image (fun q ↦ N.anchor + (N.step : ℤ) * q) :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    exact (congrArg
      (fun U : Finset ℤ ↦ N.anchor + (N.step : ℤ) * z ∈ U)
      N.image_normalized).mp hz'
  have ha := Finset.mem_Icc.mp (hS N.anchor_mem)
  have hxb := Finset.mem_Icc.mp (hS hx)
  have hax := N.anchor_le _ hx
  have hspos : (0 : ℤ) < (N.step : ℤ) := by exact_mod_cast N.step_pos
  apply Finset.mem_Icc.mpr
  constructor <;> nlinarith

/-- Quantitative fibre normalization used in CFP Lemma 2.15.  Once a width
is at least `8*cDen`, density `cNum/cDen` (with `cNum ≥ 1`) gives a primitive
normalization whose step is at most `4*cDen`.  This is the finite range used
by the later equal-step pigeonhole argument. -/
theorem exists_boundedStep_primitive_coordinateFiber {d : ℕ}
    (Q : AxisBox d) {A : Finset (BoxPoint d)} (hA : A ⊆ Q.carrier)
    (k : Fin d) (cNum cDen : ℕ) (hcNum : 0 < cNum)
    (hcDen : 0 < cDen)
    (hdensity : cNum * Q.volume ≤ cDen * A.card)
    (hwidth : 8 * cDen ≤ Q.widths k) :
    ∃ y ∈ coordinateBase Q k,
      ∃ N : PrimitiveNormalization (coordinateFiberValues Q A k y),
        Q.widths k / (2 * cDen) ≤ N.normalized.card ∧
        N.step ≤ 4 * cDen := by
  let b := Q.widths k / (2 * cDen)
  obtain ⟨y, hy, hfiber⟩ :=
    exists_dense_coordinateFiber Q hA k cNum cDen hcNum hcDen hdensity
  have hb4 : 4 ≤ b := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
    calc
      4 * (2 * cDen) = 8 * cDen := by ring
      _ ≤ Q.widths k := hwidth
  have hcard2 : 2 ≤ (coordinateFiberValues Q A k y).card :=
    (by omega : 2 ≤ b).trans hfiber
  obtain ⟨N⟩ := exists_primitiveNormalization
    (coordinateFiberValues Q A k y) hcard2
  have hinterval : coordinateFiberValues Q A k y ⊆
      Finset.Icc (Q.lower k)
        (Q.lower k + ((Q.widths k - 1 : ℕ) : ℤ)) := by
    intro x hx
    have hx' := coordinateFiberValues_subset_interval Q hA k y hx
    rw [AxisBox.mem_interval_iff] at hx'
    apply Finset.mem_Icc.mpr
    constructor
    · exact hx'.1
    · have hwpos := Q.width_pos k
      push_cast
      omega
  have hspacing := N.step_mul_card_sub_one_le
    (Q.lower k) (Q.widths k - 1) hinterval
  have hbcard : b ≤ N.normalized.card := by
    rw [N.card_normalized]
    exact hfiber
  have hbcardS : b ≤ (coordinateFiberValues Q A k y).card := hfiber
  have hstepb : N.step * (b - 1) ≤ Q.widths k - 1 := by
    exact (Nat.mul_le_mul_left N.step
      (Nat.sub_le_sub_right hbcardS 1)).trans hspacing
  have hwlt : Q.widths k < (2 * cDen) * (b + 1) := by
    simpa [b] using Nat.lt_mul_div_succ (Q.widths k)
      (by positivity : 0 < 2 * cDen)
  have hfactor : b + 1 ≤ 2 * (b - 1) := by omega
  have hwlt' : Q.widths k < (4 * cDen) * (b - 1) := by
    calc
      Q.widths k < (2 * cDen) * (b + 1) := hwlt
      _ ≤ (2 * cDen) * (2 * (b - 1)) :=
        Nat.mul_le_mul_left _ hfactor
      _ = (4 * cDen) * (b - 1) := by ring
  have hwsub : Q.widths k - 1 < Q.widths k :=
    Nat.sub_lt (Q.width_pos k) Nat.zero_lt_one
  have hmul : N.step * (b - 1) < (4 * cDen) * (b - 1) :=
    hstepb.trans_lt (hwsub.trans hwlt')
  have hstep : N.step < 4 * cDen :=
    (Nat.mul_lt_mul_right (by omega : 0 < b - 1)).mp hmul
  exact ⟨y, hy, N, hbcard, hstep.le⟩

/-- Finite pigeonhole in the form used to choose coordinate blocks in CFP
Lemma 2.15.  If `V * L` indices carry positive labels at most `V`, then
`L` of the indices have exactly the same label.  The chosen indices are
returned as an injection from `Fin L`, which is the form consumed by the
heterogeneous sumset and Lev interfaces. -/
theorem exists_injective_constant_of_bounded {m L V : ℕ}
    (hV : 0 < V) (hsize : V * L ≤ m) (f : Fin m → ℕ)
    (hf : ∀ i, 0 < f i ∧ f i ≤ V) :
    ∃ v : ℕ, 0 < v ∧ v ≤ V ∧
      ∃ e : Fin L → Fin m, Function.Injective e ∧ ∀ i, f (e i) = v := by
  classical
  let label : Fin m → ℕ := fun i ↦ f i - 1
  have hlabel : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      label i ∈ Finset.range V := by
    intro i _
    rw [Finset.mem_range]
    dsimp [label]
    have hfi := hf i
    omega
  obtain ⟨q, hq, hqcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Finset (Fin m))) (t := Finset.range V)
      (f := label) (n := L) hlabel
      ⟨0, Finset.mem_range.mpr hV⟩ (by simpa using hsize)
  let J : Finset (Fin m) := Finset.univ.filter fun i ↦ label i = q
  have hJL : L ≤ J.card := by simpa [J] using hqcard
  obtain ⟨K, hKJ, hKcard⟩ := Finset.exists_subset_card_eq hJL
  let eK : Fin L ≃ K := Fintype.equivOfCardEq (by simp [hKcard])
  let e : Fin L → Fin m := fun i ↦ (eK i : Fin m)
  have he : Function.Injective e := by
    intro i j hij
    apply eK.injective
    apply Subtype.ext
    exact hij
  refine ⟨q + 1, Nat.zero_lt_succ q, ?_, e, he, ?_⟩
  · rw [Finset.mem_range] at hq
    omega
  · intro i
    have hiK : (e i) ∈ K := (eK i).property
    have hiJ : e i ∈ J := hKJ hiK
    have hilabel : label (e i) = q := (Finset.mem_filter.mp hiJ).2
    dsimp [label] at hilabel
    have hpos := (hf (e i)).1
    omega

/-! ## From coordinate lines to a rectangular grid -/

/-- The vector supported in coordinate `k` with value `z`. -/
def axisVector {d : ℕ} (k : Fin d) (z : ℤ) : BoxPoint d :=
  fun i ↦ if i = k then z else 0

@[simp] theorem axisVector_same {d : ℕ} (k : Fin d) (z : ℤ) :
    axisVector k z k = z := by simp [axisVector]

@[simp] theorem axisVector_ne {d : ℕ} {i k : Fin d} (hik : i ≠ k)
    (z : ℤ) : axisVector k z i = 0 := by
  simp [axisVector, hik]

/-- Embed a one-dimensional integer set as a coordinate line through `y`. -/
def coordinateLineImage {d : ℕ} (y : BoxPoint d) (k : Fin d)
    (S : Finset ℤ) : Finset (BoxPoint d) :=
  S.image fun z ↦ y + axisVector k z

/-- The coordinate values of a fibre, after subtracting the lower-face
coordinate from its base point, recover actual points of the original set. -/
theorem coordinateLineImage_fiber_subset {d : ℕ} (Q : AxisBox d)
    (A : Finset (BoxPoint d)) (k : Fin d) (y : BoxPoint d) :
    coordinateLineImage (y - axisVector k (Q.lower k)) k
        (coordinateFiberValues Q A k y) ⊆ A := by
  classical
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
  have hxfiber := Finset.mem_filter.mp hx
  have hproj : coordinateBaseProjection Q k x = y := hxfiber.2
  have hcoord : x k = u := hxu
  have heq :
      y - axisVector k (Q.lower k) + axisVector k u = x := by
    funext i
    by_cases hik : i = k
    · subst i
      have hyk := congrFun hproj k
      simp [coordinateBaseProjection] at hyk
      simp [axisVector, hyk, hcoord]
    · have hi := congrFun hproj i
      simp [coordinateBaseProjection, hik] at hi
      simp [axisVector, hik, hi]
  rw [heq]
  exact hxfiber.1

/-- Coordinate-line embeddings commute exactly with heterogeneous sums.
This is the bridge from Lev's one-dimensional `familySumset` to the
axis-parallel blocks used in the multidimensional argument. -/
theorem heterogeneousSumset_coordinateLineImage {d ell : ℕ}
    (y : Fin ell → BoxPoint d) (k : Fin d)
    (S : Fin ell → Finset ℤ) :
    heterogeneousSumset (fun i ↦ coordinateLineImage (y i) k (S i)) =
      coordinateLineImage (∑ i, y i) k (Lev.familySumset S) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := mem_heterogeneousSumset.mp hx
    choose z hzS hza using fun i ↦ Finset.mem_image.mp (ha i)
    have hzsum : (∑ i, z i) ∈ Lev.familySumset S :=
      Lev.mem_familySumset_iff.mpr ⟨z, hzS, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨∑ i, z i, hzsum, ?_⟩
    rw [← hax]
    simp_rw [← hza]
    rw [Finset.sum_add_distrib]
    congr 1
    funext j
    by_cases hjk : j = k
    · subst j
      simp [axisVector]
    · simp [axisVector, hjk]
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    obtain ⟨f, hf, hfz⟩ := Lev.mem_familySumset_iff.mp hz
    apply mem_heterogeneousSumset.mpr
    refine ⟨fun i ↦ y i + axisVector k (f i), fun i ↦ ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f i, hf i, rfl⟩
    · rw [Finset.sum_add_distrib]
      rw [← hzx]
      congr 1
      funext j
      by_cases hjk : j = k
      · subst j
        simp [axisVector, hfz]
      · simp [axisVector, hjk]

/-- A finite arithmetic line in direction of the `k`-th coordinate axis. -/
def axisLine {d : ℕ} (y : BoxPoint d) (k : Fin d) (v n : ℕ) :
    Finset (BoxPoint d) :=
  (Finset.range (n + 1)).image fun (b : ℕ) ↦
    y + axisVector k ((v : ℤ) * (b : ℤ))

@[simp] theorem mem_axisLine_iff {d : ℕ} {y : BoxPoint d} {k : Fin d}
    {v n : ℕ} {x : BoxPoint d} :
    x ∈ axisLine y k v n ↔
      ∃ b : ℕ, b ≤ n ∧
        y + axisVector k ((v : ℤ) * (b : ℤ)) = x := by
  classical
  simp [axisLine, Nat.lt_succ_iff]

/-- An arithmetic axis line is the coordinate-line image of its scalar
arithmetic progression. -/
theorem axisLine_subset_coordinateLineImage_affine {d : ℕ}
    (y : BoxPoint d) (k : Fin d) (c : ℤ) (v M : ℕ) :
    axisLine (y + axisVector k c) k v M ⊆
      coordinateLineImage y k
        ((Finset.Icc (0 : ℤ) (M : ℤ)).image
          (fun j ↦ c + (v : ℤ) * j)) := by
  classical
  intro x hx
  obtain ⟨b, hb, rfl⟩ := mem_axisLine_iff.mp hx
  apply Finset.mem_image.mpr
  refine ⟨c + (v : ℤ) * (b : ℤ), ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨b, ?_, rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le b
    · exact_mod_cast hb
  · funext j
    by_cases hj : j = k
    · subst j
      simp [axisVector]
      ring
    · simp [axisVector, hj]

/-- Exact assembly of an affine one-dimensional interval into a coordinate
line in a selected partial sumset. -/
theorem exists_axisLine_subset_of_affine_interval {d ell L : ℕ}
    (A : Fin ell → Finset (BoxPoint d)) (k : Fin d)
    (e : Fin L → Fin ell) (he : Function.Injective e)
    (base : Fin L → BoxPoint d) (T : Fin L → Finset ℤ) (v M : ℕ)
    (hline : ∀ i, coordinateLineImage (base i) k (T i) ⊆ A (e i))
    (hinterval : ∃ c : ℤ,
      (Finset.Icc (0 : ℤ) (M : ℤ)).image
        (fun j ↦ c + (v : ℤ) * j) ⊆ Lev.familySumset T) :
    ∃ t : BoxPoint d,
      axisLine t k v M ⊆ partialSumset A (Finset.univ.image e) := by
  classical
  obtain ⟨c, hc⟩ := hinterval
  refine ⟨(∑ i, base i) + axisVector k c,
    (axisLine_subset_coordinateLineImage_affine
      (∑ i, base i) k c v M).trans ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hzsum := hc hz
  have hzline :
      (∑ i, base i) + axisVector k z ∈ heterogeneousSumset
        (fun i ↦ coordinateLineImage (base i) k (T i)) := by
    rw [heterogeneousSumset_coordinateLineImage]
    exact Finset.mem_image.mpr ⟨z, hzsum, rfl⟩
  have hzA : (∑ i, base i) + axisVector k z ∈
      heterogeneousSumset (fun i ↦ A (e i)) := by
    apply heterogeneousSumset_mono (A := fun i ↦
      coordinateLineImage (base i) k (T i))
      (B := fun i ↦ A (e i)) hline hzline
  rw [heterogeneousSumset_reindex_injective A e he] at hzA
  exact hzA

/-- One complete coordinate block in the proof of CFP Lemma 2.15.  From
`V*L` disjoint candidate summands it selects `L` whose dense fibres have a
common primitive step, applies the literal Lev interval statement to their
normalizations, and lifts the resulting interval to an axis line.  The
selector into the candidate block is retained for the later disjointness
argument. -/
theorem exists_coordinateLineBlock {d ell L V : ℕ}
    (Q : AxisBox d) (A : Fin ell → Finset (BoxPoint d)) (k : Fin d)
    (cand : Fin (V * L) → Fin ell) (hcand : Function.Injective cand)
    (cNum cDen : ℕ) (hcNum : 0 < cNum) (hcDen : 0 < cDen)
    (hsubset : ∀ i, A i ⊆ Q.carrier)
    (hdensity : ∀ i, cNum * Q.volume ≤ cDen * (A i).card)
    (hV : V = 4 * cDen) (hL : 1 ≤ L)
    (hwidth : 8 * cDen ≤ Q.widths k)
    (hLevLarge :
      2 * (((Q.widths k - 1) - 1 +
          (Q.widths k / (2 * cDen) - 2) - 1) /
        (Q.widths k / (2 * cDen) - 2)) ≤ L) :
    ∃ v : ℕ, 0 < v ∧ v ≤ V ∧
      ∃ sel : Fin L → Fin (V * L), Function.Injective sel ∧
        ∃ t : BoxPoint d,
          axisLine t k v
              (L * (Q.widths k / (2 * cDen) - 1)) ⊆
            partialSumset A (Finset.univ.image (cand ∘ sel)) := by
  classical
  let b := Q.widths k / (2 * cDen)
  choose y hy N hcard hstep using fun i : Fin (V * L) ↦
    exists_boundedStep_primitive_coordinateFiber Q (hsubset (cand i)) k
      cNum cDen hcNum hcDen (hdensity (cand i)) hwidth
  have hstepV (i : Fin (V * L)) : (N i).step ≤ V := by
    simpa [hV] using hstep i
  obtain ⟨v, hvpos, hvV, sel, hsel, hsame⟩ :=
    exists_injective_constant_of_bounded (m := V * L) (L := L) (V := V)
      (by simpa [hV] using Nat.mul_pos (by omega : 0 < 4) hcDen)
      (by simp) (fun i ↦ (N i).step)
      (fun i ↦ ⟨(N i).step_pos, hstepV i⟩)
  let e : Fin L → Fin ell := cand ∘ sel
  have he : Function.Injective e := hcand.comp hsel
  let S : Fin L → Finset ℤ := fun i ↦ (N (sel i)).normalized
  have hb4 : 4 ≤ b := by
    dsimp [b]
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
    calc
      4 * (2 * cDen) = 8 * cDen := by ring
      _ ≤ Q.widths k := hwidth
  have hq : 1 ≤ Q.widths k - 1 := by omega
  have hb3 : 3 ≤ b := by omega
  have hScard : ∀ i, b ≤ (S i).card := by
    intro i
    dsimp [S]
    exact hcard (sel i)
  have hSinterval : ∀ i, ∃ a : ℤ,
      S i ⊆ Finset.Icc a (a + ((Q.widths k - 1 : ℕ) : ℤ)) := by
    intro i
    refine ⟨0, ?_⟩
    have hfiber : coordinateFiberValues Q (A (cand (sel i))) k (y (sel i)) ⊆
        Finset.Icc (Q.lower k)
          (Q.lower k + ((Q.widths k - 1 : ℕ) : ℤ)) := by
      intro x hx
      have hx' := coordinateFiberValues_subset_interval Q
        (hsubset (cand (sel i))) k (y (sel i)) hx
      rw [AxisBox.mem_interval_iff] at hx'
      apply Finset.mem_Icc.mpr
      constructor
      · exact hx'.1
      · have hwpos := Q.width_pos k
        omega
    simpa [S] using
      (N (sel i)).normalized_subset_Icc_zero
        (Q.lower k) (Q.widths k - 1) hfiber
  have hSprim : ∀ i, Lev.Primitive (S i) :=
    fun i ↦ (N (sel i)).normalized_primitive
  obtain ⟨a, ha⟩ := Lev.lev_interval hL hq hb3
    (by simpa [b] using hLevLarge)
    S hScard hSinterval hSprim
  let T : Fin L → Finset ℤ := fun i ↦
    (S i).image fun z ↦ (N (sel i)).anchor + (v : ℤ) * z
  obtain ⟨c, hc⟩ := Lev.affine_interval_of_interval S
    (fun i ↦ (N (sel i)).anchor) (v : ℤ) a ha
  have hTline (i : Fin L) :
      coordinateLineImage
          (y (sel i) - axisVector k (Q.lower k)) k (T i) ⊆ A (e i) := by
    have hTi : T i = coordinateFiberValues Q (A (e i)) k (y (sel i)) := by
      dsimp [T, S, e]
      simpa [hsame i] using (N (sel i)).image_normalized
    rw [hTi]
    exact coordinateLineImage_fiber_subset Q (A (e i)) k (y (sel i))
  obtain ⟨t, ht⟩ := exists_axisLine_subset_of_affine_interval A k e he
    (fun i ↦ y (sel i) - axisVector k (Q.lower k)) T v
    (L * (b - 1)) hTline ⟨c, hc⟩
  exact ⟨v, hvpos, hvV, sel, hsel, t, by simpa [b, e] using ht⟩

/-- The rectangular grid with step `v i` and coefficient range
`0, ..., n i` in coordinate `i`. -/
def rectangularGrid {d : ℕ} (v n : Fin d → ℕ) :
    Finset (BoxPoint d) :=
  Fintype.piFinset fun i ↦
    (Finset.range (n i + 1)).image fun (b : ℕ) ↦ (v i : ℤ) * (b : ℤ)

@[simp] theorem mem_rectangularGrid_iff {d : ℕ} {v n : Fin d → ℕ}
    {x : BoxPoint d} :
    x ∈ rectangularGrid v n ↔
      ∃ b : Fin d → ℕ, (∀ i, b i ≤ n i) ∧
        x = fun i ↦ (v i : ℤ) * (b i : ℤ) := by
  classical
  constructor
  · intro hx
    rw [rectangularGrid, Fintype.mem_piFinset] at hx
    choose b hb hbx using fun i ↦ Finset.mem_image.mp (hx i)
    refine ⟨b, fun i ↦ Nat.lt_succ_iff.mp (Finset.mem_range.mp (hb i)), ?_⟩
    funext i
    exact (hbx i).symm
  · rintro ⟨b, hb, rfl⟩
    rw [rectangularGrid, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr
      ⟨b i, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hb i)), rfl⟩

/-- Summing one coordinate line in every direction gives exactly a translate
of the corresponding rectangular sublattice grid. -/
theorem heterogeneousSumset_axisLine {d : ℕ} (y : Fin d → BoxPoint d)
    (v n : Fin d → ℕ) :
    heterogeneousSumset (fun k ↦ axisLine (y k) k (v k) (n k)) =
      Elementary.translate (∑ k, y k) (rectangularGrid v n) := by
  classical
  ext x
  rw [mem_heterogeneousSumset, Elementary.mem_translate_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    choose b hb hab using fun k ↦ mem_axisLine_iff.mp (ha k)
    refine ⟨fun i ↦ (v i : ℤ) * (b i : ℤ),
      mem_rectangularGrid_iff.mpr ⟨b, hb, rfl⟩, ?_⟩
    calc
      (∑ k, y k) + (fun i ↦ (v i : ℤ) * (b i : ℤ)) =
          (∑ k, y k) + ∑ k, axisVector k ((v k : ℤ) * (b k : ℤ)) := by
            congr 1
            funext i
            simp [axisVector]
      _ = ∑ k, (y k + axisVector k ((v k : ℤ) * (b k : ℤ))) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ k, a k := by
        apply Finset.sum_congr rfl
        intro k _
        exact hab k
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_rectangularGrid_iff.mp hz
    refine ⟨fun k ↦ y k + axisVector k ((v k : ℤ) * (b k : ℤ)), ?_, ?_⟩
    · intro k
      exact mem_axisLine_iff.mpr ⟨b k, hb k, rfl⟩
    · calc
        (∑ k, (y k + axisVector k ((v k : ℤ) * (b k : ℤ)))) =
            (∑ k, y k) + ∑ k, axisVector k ((v k : ℤ) * (b k : ℤ)) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ k, y k) + (fun i ↦ (v i : ℤ) * (b i : ℤ)) := by
          congr 1
          funext i
          simp [axisVector]

/-- Coordinatewise line containment is enough to obtain the translated
grid in the sum of the line-producing blocks. -/
theorem rectangularGrid_subset_heterogeneousSumset_of_axisLines {d : ℕ}
    {B : Fin d → Finset (BoxPoint d)} (y : Fin d → BoxPoint d)
    (v n : Fin d → ℕ)
    (hline : ∀ k, axisLine (y k) k (v k) (n k) ⊆ B k) :
    Elementary.translate (∑ k, y k) (rectangularGrid v n) ⊆
      heterogeneousSumset B := by
  rw [← heterogeneousSumset_axisLine]
  exact heterogeneousSumset_mono hline

/-! ## The lattice generated by a dense set -/

/-- The integral lattice generated by a finite set.  When `0 ∈ A`, this is
the group denoted `⟨A⟩` in CFP Lemma 2.16. -/
def generatedSublattice {d : ℕ} (A : Finset (BoxPoint d)) :
    LatticeBasis.Sublattice d :=
  AddSubgroup.closure (A : Set (BoxPoint d))

theorem subset_generatedSublattice {d : ℕ} (A : Finset (BoxPoint d)) :
    (A : Set (BoxPoint d)) ⊆ generatedSublattice A := by
  exact AddSubgroup.subset_closure

/-- Regard the generators as elements of the subgroup they generate. -/
noncomputable def generatedLift {d : ℕ} (A : Finset (BoxPoint d)) :
    Finset (generatedSublattice A) :=
  A.attach.image fun x ↦
    ⟨x.1, subset_generatedSublattice A x.2⟩

@[simp] theorem mem_generatedLift_iff {d : ℕ}
    (A : Finset (BoxPoint d)) (x : generatedSublattice A) :
    x ∈ generatedLift A ↔ (x : BoxPoint d) ∈ A := by
  classical
  constructor
  · intro hx
    obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hx
    rw [← hax]
    exact a.2
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
    exact Subtype.ext rfl

/-- The lifted generators generate their ambient generated subgroup. -/
theorem closure_generatedLift_eq_top {d : ℕ}
    (A : Finset (BoxPoint d)) :
    AddSubgroup.closure (generatedLift A : Set (generatedSublattice A)) = ⊤ := by
  let K := AddSubgroup.closure
    (generatedLift A : Set (generatedSublattice A))
  have hAmap : (A : Set (BoxPoint d)) ⊆
      K.map (generatedSublattice A).subtype := by
    intro x hx
    refine ⟨⟨x, subset_generatedSublattice A hx⟩, ?_, rfl⟩
    exact AddSubgroup.subset_closure
      ((mem_generatedLift_iff A _).2 hx)
  have hclosure : generatedSublattice A ≤
      K.map (generatedSublattice A).subtype :=
    (AddSubgroup.closure_le _).2 hAmap
  apply top_unique
  intro y _
  obtain ⟨z, hz, hzy⟩ := hclosure y.property
  have hzy' : z = y := Subtype.ext hzy
  simpa [K, hzy'] using hz

@[simp] theorem image_generatedLift_subtype {d : ℕ}
    (A : Finset (BoxPoint d)) :
    (generatedLift A).image
        ((generatedSublattice A).subtype : generatedSublattice A →+ BoxPoint d) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    exact (mem_generatedLift_iff A y).1 hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨⟨x, subset_generatedSublattice A hx⟩, ?_, rfl⟩
    exact (mem_generatedLift_iff A _).2 hx

/-- Every constant-family iterated sum belongs to the lattice generated by
the summand. -/
theorem iteratedSumset_const_subset_generatedSublattice {d : ℕ}
    (A : Finset (BoxPoint d)) (m : ℕ) :
    (iteratedSumset (fun _ ↦ A) m : Set (BoxPoint d)) ⊆
      generatedSublattice A := by
  induction m with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      simpa [hx0]
  | succ m ih =>
      rw [iteratedSumset_succ]
      intro x hx
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_add.mp hx
      exact (generatedSublattice A).add_mem (ih hs)
        (subset_generatedSublattice A ha)

/-- A translated rectangular grid with at least one step in every direction
forces the full rectangular lattice into the lattice generated by `A`.
This is the first structural implication in the proof of CFP Lemma 2.16. -/
theorem rectangularSubgroup_le_generated_of_grid_subset_iteratedSumset
    {d : ℕ} (A : Finset (BoxPoint d)) (m : ℕ)
    (v n : Fin d → ℕ) (hn : ∀ i, 1 ≤ n i) (t : BoxPoint d)
    (hgrid : Elementary.translate t (rectangularGrid v n) ⊆
      iteratedSumset (fun _ ↦ A) m) :
    LatticeBasis.rectangularSubgroup v ≤ generatedSublattice A := by
  classical
  have hzeroGrid : (0 : BoxPoint d) ∈ rectangularGrid v n := by
    apply mem_rectangularGrid_iff.mpr
    refine ⟨fun _ ↦ 0, fun _ ↦ Nat.zero_le _, ?_⟩
    funext i
    simp
  have ht : t ∈ generatedSublattice A := by
    apply iteratedSumset_const_subset_generatedSublattice A m
    apply hgrid
    exact Elementary.mem_translate_iff.mpr ⟨0, hzeroGrid, by simp⟩
  have haxis (i : Fin d) : LatticeBasis.axisVector v i ∈ generatedSublattice A := by
    let b : Fin d → ℕ := fun j ↦ if j = i then 1 else 0
    have hb : ∀ j, b j ≤ n j := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [b] using hn i
      · simp [b, hji]
    have hbg : (fun j ↦ (v j : ℤ) * (b j : ℤ)) ∈ rectangularGrid v n :=
      mem_rectangularGrid_iff.mpr ⟨b, hb, rfl⟩
    have htb : t + (fun j ↦ (v j : ℤ) * (b j : ℤ)) ∈
        generatedSublattice A := by
      apply iteratedSumset_const_subset_generatedSublattice A m
      exact hgrid (Elementary.mem_translate_iff.mpr
        ⟨_, hbg, rfl⟩)
    have heq : (fun j ↦ (v j : ℤ) * (b j : ℤ)) =
        LatticeBasis.axisVector v i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [b, LatticeBasis.axisVector]
      · simp [b, LatticeBasis.axisVector, hji]
    rw [heq] at htb
    simpa using (generatedSublattice A).sub_mem htb ht
  intro x hx
  rw [LatticeBasis.mem_rectangularSubgroup_iff] at hx
  choose q hq using hx
  have hrepr : x = ∑ i, q i • LatticeBasis.axisVector v i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simpa [LatticeBasis.axisVector, mul_comm] using hq j
    · intro i _ hij
      simp [LatticeBasis.axisVector, hij]
    · simp
  rw [hrepr]
  exact AddSubgroup.sum_mem _ fun i _ ↦
    (generatedSublattice A).zsmul_mem (haxis i) (q i)

/-! ## Filling the rectangular grid from residue representatives -/

/-- `R` contains a representative of every residue class modulo the
rectangular lattice with periods `v`. -/
def RectangularResidueComplete {d : ℕ} (v : Fin d → ℕ)
    (R : Finset (BoxPoint d)) : Prop :=
  ∀ a : RectangularQuotient v,
    ∃ r ∈ R, rectangularResidue v r = a

/-- Residue completeness only for classes represented by a specified
sublattice.  This is the form needed for the non-reduced Lemma 2.16. -/
def RectangularResidueCompleteOn {d : ℕ} (v : Fin d → ℕ)
    (Gamma : LatticeBasis.Sublattice d) (R : Finset (BoxPoint d)) : Prop :=
  ∀ y : Gamma, ∃ r ∈ R,
    rectangularResidue v r = rectangularResidue v (y : BoxPoint d)

/-- A bounded number of copies of a set containing zero meets every
rectangular residue class represented by its generated lattice. -/
theorem rectangularResidueCompleteOn_generated_iteratedSumset
    {d : ℕ} (v : Fin d → ℕ) (hv : ∀ i, 0 < v i)
    (B : Finset (BoxPoint d)) (hzero : (0 : BoxPoint d) ∈ B)
    (hrect : LatticeBasis.rectangularSubgroup v ≤ generatedSublattice B) :
    let r := (LatticeBasis.rectangularSubgroup v).relIndex
      (generatedSublattice B)
    r ≤ ∏ i, v i ∧
      RectangularResidueCompleteOn v (generatedSublattice B)
        (iteratedSumset (fun _ ↦ B) r) := by
  classical
  let Gamma := generatedSublattice B
  let BGamma : Finset Gamma := generatedLift B
  have hzeroGamma : (0 : Gamma) ∈ BGamma := by
    exact (mem_generatedLift_iff B 0).2 hzero
  have hgenGamma : AddSubgroup.closure (BGamma : Set Gamma) = ⊤ := by
    exact closure_generatedLift_eq_top B
  obtain ⟨hr, hcover⟩ := rectangular_iteratedSumset_covers_cosets
    v hv Gamma hrect BGamma hzeroGamma hgenGamma
  refine ⟨hr, ?_⟩
  intro y
  obtain ⟨s, hs, hsub⟩ := hcover y
  let f : Gamma →+ BoxPoint d := Gamma.subtype
  have hsimage : (f s) ∈
      (iteratedSumset (fun _ ↦ BGamma)
        ((LatticeBasis.rectangularSubgroup v).relIndex Gamma)).image f :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have himage := image_iteratedSumset f (fun _ : ℕ ↦ BGamma)
    ((LatticeBasis.rectangularSubgroup v).relIndex Gamma)
  rw [image_generatedLift_subtype] at himage
  have hsambient : (s : BoxPoint d) ∈
      iteratedSumset (fun _ ↦ B)
        ((LatticeBasis.rectangularSubgroup v).relIndex Gamma) := by
    rw [← himage]
    exact hsimage
  refine ⟨(s : BoxPoint d), hsambient, ?_⟩
  funext i
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub
    ((s : BoxPoint d) i) ((y : BoxPoint d) i) (v i)).2
  have hi := (LatticeBasis.mem_rectangularSubgroup_iff.mp hsub) i
  simpa using hi

/-- Constant-family iterated sumsets split at any prescribed index. -/
theorem iteratedSumset_const_add {G : Type*} [AddCommMonoid G]
    [DecidableEq G] (B : Finset G) (m n : ℕ) :
    iteratedSumset (fun _ ↦ B) (m + n) =
      iteratedSumset (fun _ ↦ B) m + iteratedSumset (fun _ ↦ B) n := by
  simp only [iteratedSumset, Finset.sum_range_add]

/-- If a summand contains zero, its constant iterated sumsets increase with
the number of copies. -/
theorem iteratedSumset_const_mono_index {G : Type*} [AddCommMonoid G]
    [DecidableEq G] (B : Finset G) (hzero : 0 ∈ B) {m n : ℕ} (hmn : m ≤ n) :
    iteratedSumset (fun _ ↦ B) m ⊆ iteratedSumset (fun _ ↦ B) n := by
  intro x hx
  have hz : (0 : G) ∈ iteratedSumset (fun _ ↦ B) (n - m) := by
    induction n - m with
    | zero => simp
    | succ k ih =>
        rw [show k + 1 = Nat.succ k by omega, iteratedSumset_succ]
        exact Finset.mem_add.mpr ⟨0, ih, 0, hzero, add_zero 0⟩
  have hadd := Finset.mem_add.mpr ⟨x, hx, 0, hz, add_zero x⟩
  rw [← iteratedSumset_const_add B m (n - m), Nat.add_sub_of_le hmn] at hadd
  exact hadd

/-- Reduction modulo `v` commutes with a finite iterated sumset. -/
theorem image_rectangularResidue_iteratedSumset {d : ℕ}
    (v : Fin d → ℕ) (A : ℕ → Finset (BoxPoint d)) (m : ℕ) :
    (iteratedSumset A m).image (rectangularResidue v) =
      iteratedSumset (fun i ↦ (A i).image (rectangularResidue v)) m := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, iteratedSumset_succ,
        iteratedSumset_succ]
      ext z
      constructor
      · intro hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_add.mp hx
        apply Finset.mem_add.mpr
        refine ⟨rectangularResidue v s, ?_, rectangularResidue v a, ?_, ?_⟩
        · rw [← ih]
          exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
        · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
        · exact (rectangularResidue_add v s a).symm
      · intro hz
        obtain ⟨s, hs, a, ha, hsa⟩ := Finset.mem_add.mp hz
        rw [← ih] at hs
        obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
        apply Finset.mem_image.mpr
        refine ⟨s' + a', Finset.mem_add.mpr ⟨s', hs', a', ha', rfl⟩, ?_⟩
        rw [rectangularResidue_add, hsa]

/-- CFP Claim 2.12 applied to the rectangular quotient: the sum of one full
quotient-cardinality block of reduced nonempty sets supplies every residue
class. -/
theorem reduced_block_residue_complete {d : ℕ} (v : Fin d → ℕ)
    (hv : ∀ i, 0 < v i) (A : ℕ → Finset (BoxPoint d))
    (hAne : ∀ i < ∏ j, v j, (A i).Nonempty)
    (hAred : ∀ i < ∏ j, v j, Reduced (A i)) :
    RectangularResidueComplete v
      (iteratedSumset A (∏ j, v j)) := by
  classical
  letI (i : Fin d) : NeZero (v i) := ⟨Nat.ne_of_gt (hv i)⟩
  have hcard : Fintype.card (RectangularQuotient v) = ∏ j, v j := by
    simp [Fintype.card_pi, ZMod.card]
  let AQ : ℕ → Finset (RectangularQuotient v) :=
    fun i ↦ (A i).image (rectangularResidue v)
  have hAQne : ∀ i < Fintype.card (RectangularQuotient v), (AQ i).Nonempty := by
    intro i hi
    exact (hAne i (by simpa [hcard] using hi)).image _
  have hAQred : ∀ i < Fintype.card (RectangularQuotient v),
      NotInProperCoset ((AQ i : Finset (RectangularQuotient v)) :
        Set (RectangularQuotient v)) := by
    intro i hi
    exact (hAred i (by simpa [hcard] using hi)).notInProperCoset_residue v hv
  have hcover := finite_group_sumset_cover AQ hAQne hAQred
  intro a
  have ha : a ∈ iteratedSumset AQ (∏ j, v j) := by
    rw [← hcard]
    rw [hcover]
    exact Finset.mem_univ _
  rw [← image_rectangularResidue_iteratedSumset] at ha
  exact Finset.mem_image.mp ha

/-- Every representative in `R` is bounded by `M` in each coordinate. -/
def CoordinateBound {d : ℕ} (R : Finset (BoxPoint d))
    (M : Fin d → ℕ) : Prop :=
  ∀ r ∈ R, ∀ i, -((M i : ℕ) : ℤ) ≤ r i ∧ r i ≤ (M i : ℤ)

theorem CoordinateBound.mono {d : ℕ} {R : Finset (BoxPoint d)}
    {M N : Fin d → ℕ} (hR : CoordinateBound R M) (hMN : ∀ i, M i ≤ N i) :
    CoordinateBound R N := by
  intro r hr i
  have hi := hR r hr i
  have hcast : (M i : ℤ) ≤ (N i : ℤ) := by exact_mod_cast hMN i
  constructor <;> omega

/-- Coordinate bounds add through an iterated sumset. -/
theorem coordinateBound_iteratedSumset {d m : ℕ}
    (A : ℕ → Finset (BoxPoint d)) (B : Fin d → ℕ)
    (hA : ∀ j < m, ∀ x ∈ A j, ∀ i,
      -((B i : ℕ) : ℤ) ≤ x i ∧ x i ≤ (B i : ℤ)) :
    CoordinateBound (iteratedSumset A m) (fun i ↦ m * B i) := by
  induction m with
  | zero =>
      intro r hr i
      have hr0 : r = 0 := by simpa using hr
      subst r
      simp
  | succ m ih =>
      rw [iteratedSumset_succ]
      intro r hr i
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_add.mp hr
      have hsbound := ih (fun j hj ↦ hA j (Nat.lt_succ_of_lt hj)) s hs i
      have habound := hA m (Nat.lt_succ_self m) a ha i
      change -(((m + 1) * B i : ℕ) : ℤ) ≤ s i + a i ∧
        s i + a i ≤ (((m + 1) * B i : ℕ) : ℤ)
      push_cast at hsbound habound ⊢
      norm_num [add_mul] at ⊢
      constructor <;> omega

/-- The final residue-filling calculation in CFP Lemma 2.15.

The grid has coefficients `0,...,n i`.  We center the target ordinary box
at coefficient `n i / 2`.  The two displayed inequalities say that the
bounded residue representative cannot push the corrected coefficient below
zero or above `n i`. -/
theorem grid_add_residues_contains_dilate {d : ℕ}
    (Q : AxisBox d) (k : ℕ) (v n M : Fin d → ℕ)
    (hv : ∀ i, 0 < v i)
    (hleft : ∀ i, M i ≤ v i * (n i / 2))
    (hright : ∀ i,
      v i * (n i / 2) + k * (Q.widths i - 1) + M i ≤ v i * n i)
    {G R : Finset (BoxPoint d)} (t : BoxPoint d)
    (hgrid : Elementary.translate t (rectangularGrid v n) ⊆ G)
    (hres : RectangularResidueComplete v R)
    (hbound : CoordinateBound R M) :
    ∃ shift : BoxPoint d,
      Elementary.translate shift (Q.dilate k).carrier ⊆ Elementary.sumset G R := by
  classical
  let center : BoxPoint d := fun i ↦ (v i : ℤ) * (n i / 2 : ℕ)
  refine ⟨t + center, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Elementary.mem_translate_iff.mp hx
  obtain ⟨r, hrR, hrmod⟩ := hres (rectangularResidue v (center + z))
  have hrbounds := hbound r hrR
  have hdvd (i : Fin d) : (v i : ℤ) ∣ (center + z) i - r i := by
    have hi := congrFun hrmod i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (r i) ((center + z) i) (v i)).mp hi
  choose q hq using hdvd
  have hzmem := (AxisBox.mem_carrier_iff (Q.dilate k)).1 hz
  have hqnonneg (i : Fin d) : 0 ≤ q i := by
    have hzlower : 0 ≤ z i := (hzmem i).1
    have hrupper : r i ≤ (M i : ℤ) := (hrbounds i).2
    have hM : (M i : ℤ) ≤ center i := by
      change (M i : ℤ) ≤ ((v i * (n i / 2) : ℕ) : ℤ)
      exact_mod_cast hleft i
    have hdelta : 0 ≤ (center + z) i - r i := by
      rw [Pi.add_apply]
      omega
    have hnonneg : 0 ≤ (v i : ℤ) * q i := by
      rw [← hq i]
      exact hdelta
    exact nonneg_of_mul_nonneg_right hnonneg (by exact_mod_cast hv i)
  have hqle (i : Fin d) : q i ≤ (n i : ℤ) := by
    have hzupper : z i ≤ ((k * (Q.widths i - 1) : ℕ) : ℤ) := by
      have hi := (hzmem i).2
      rw [AxisBox.dilate_lower, Pi.zero_apply, zero_add,
        AxisBox.dilate_width] at hi
      push_cast at hi
      omega
    have hrlower : -((M i : ℕ) : ℤ) ≤ r i := (hrbounds i).1
    have hright' :
        ((v i * (n i / 2) : ℕ) : ℤ) +
            ((k * (Q.widths i - 1) : ℕ) : ℤ) + (M i : ℤ) ≤
          ((v i * n i : ℕ) : ℤ) := by
      exact_mod_cast hright i
    have hcenter : center i = ((v i * (n i / 2) : ℕ) : ℤ) := by
      simp [center]
    have hdeltaLe : (center + z) i - r i ≤ ((v i * n i : ℕ) : ℤ) := by
      calc
        (center + z) i - r i = center i + z i - r i := rfl
        _ ≤ ((v i * (n i / 2) : ℕ) : ℤ) +
              ((k * (Q.widths i - 1) : ℕ) : ℤ) + (M i : ℤ) := by
          rw [hcenter]
          omega
        _ ≤ ((v i * n i : ℕ) : ℤ) := hright'
    have hprod : (v i : ℤ) * q i ≤ (v i : ℤ) * (n i : ℤ) := by
      rw [← hq i]
      simpa only [Nat.cast_mul] using hdeltaLe
    exact (Int.mul_le_mul_left
      (show (0 : ℤ) < (v i : ℤ) by exact_mod_cast hv i)).mp hprod
  let b : Fin d → ℕ := fun i ↦ (q i).toNat
  have hbcast (i : Fin d) : (b i : ℤ) = q i := by
    exact Int.toNat_of_nonneg (hqnonneg i)
  have hb (i : Fin d) : b i ≤ n i := by
    exact Int.toNat_le.mpr (hqle i)
  let g : BoxPoint d := t + fun i ↦ (v i : ℤ) * (b i : ℤ)
  have hg : g ∈ G := hgrid (Elementary.mem_translate_iff.mpr
    ⟨fun i ↦ (v i : ℤ) * (b i : ℤ),
      mem_rectangularGrid_iff.mpr ⟨b, hb, rfl⟩, rfl⟩)
  apply Elementary.mem_sumset_iff.mpr
  refine ⟨g, hg, r, hrR, ?_⟩
  funext i
  change t i + (v i : ℤ) * (b i : ℤ) + r i =
    t i + center i + z i
  rw [hbcast, ← hq i]
  simp only [Pi.add_apply]
  ring

/-- The lattice-relative residue-filling calculation used in CFP
Lemma 2.16.  A centered, coordinate-bounded subset of `Gamma` is covered
after one translated grid block and one block complete modulo the
rectangular sublattice. -/
theorem grid_add_residues_contains_lattice_set {d : ℕ}
    (Gamma : LatticeBasis.Sublattice d) (v n K M : Fin d → ℕ)
    (hv : ∀ i, 0 < v i)
    (hrect : LatticeBasis.rectangularSubgroup v ≤ Gamma)
    (hleft : ∀ i, K i + M i ≤ v i * (n i / 2))
    (hright : ∀ i,
      v i * (n i / 2) + K i + M i ≤ v i * n i)
    {G R S : Finset (BoxPoint d)} (t : BoxPoint d)
    (hgrid : Elementary.translate t (rectangularGrid v n) ⊆ G)
    (hres : RectangularResidueCompleteOn v Gamma R)
    (hboundR : CoordinateBound R M)
    (hSGamma : (S : Set (BoxPoint d)) ⊆ Gamma)
    (hboundS : CoordinateBound S K) :
    ∃ shift : BoxPoint d,
      Elementary.translate shift S ⊆ Elementary.sumset G R := by
  classical
  let center : BoxPoint d := fun i ↦ (v i : ℤ) * (n i / 2 : ℕ)
  have hcenterH : center ∈ LatticeBasis.rectangularSubgroup v := by
    rw [LatticeBasis.mem_rectangularSubgroup_iff]
    intro i
    exact ⟨(n i / 2 : ℕ), by simp [center]⟩
  have hcenterGamma : center ∈ Gamma := hrect hcenterH
  refine ⟨t + center, ?_⟩
  intro x hx
  obtain ⟨z, hzS, rfl⟩ := Elementary.mem_translate_iff.mp hx
  have hzGamma : z ∈ Gamma := hSGamma hzS
  let y : Gamma := ⟨center + z, Gamma.add_mem hcenterGamma hzGamma⟩
  obtain ⟨r, hrR, hrmod⟩ := hres y
  have hrbounds := hboundR r hrR
  have hzbounds := hboundS z hzS
  have hdvd (i : Fin d) : (v i : ℤ) ∣ (center + z) i - r i := by
    have hi := congrFun hrmod i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      (r i) ((center + z) i) (v i)).mp hi
  choose q hq using hdvd
  have hqnonneg (i : Fin d) : 0 ≤ q i := by
    have hzlower : -((K i : ℕ) : ℤ) ≤ z i := (hzbounds i).1
    have hrupper : r i ≤ (M i : ℤ) := (hrbounds i).2
    have hleft' : ((K i + M i : ℕ) : ℤ) ≤ center i := by
      change ((K i + M i : ℕ) : ℤ) ≤
        ((v i * (n i / 2) : ℕ) : ℤ)
      exact_mod_cast hleft i
    have hdelta : 0 ≤ (center + z) i - r i := by
      rw [Pi.add_apply]
      push_cast at hleft'
      omega
    have hnonneg : 0 ≤ (v i : ℤ) * q i := by
      rw [← hq i]
      exact hdelta
    exact nonneg_of_mul_nonneg_right hnonneg (by exact_mod_cast hv i)
  have hqle (i : Fin d) : q i ≤ (n i : ℤ) := by
    have hzupper : z i ≤ (K i : ℤ) := (hzbounds i).2
    have hrlower : -((M i : ℕ) : ℤ) ≤ r i := (hrbounds i).1
    have hright' :
        ((v i * (n i / 2) : ℕ) : ℤ) + (K i : ℤ) + (M i : ℤ) ≤
          ((v i * n i : ℕ) : ℤ) := by
      exact_mod_cast hright i
    have hcenter : center i = ((v i * (n i / 2) : ℕ) : ℤ) := by
      simp [center]
    have hdeltaLe : (center + z) i - r i ≤
        ((v i * n i : ℕ) : ℤ) := by
      rw [Pi.add_apply, hcenter]
      omega
    have hprod : (v i : ℤ) * q i ≤ (v i : ℤ) * (n i : ℤ) := by
      rw [← hq i]
      simpa only [Nat.cast_mul] using hdeltaLe
    exact (Int.mul_le_mul_left
      (show (0 : ℤ) < (v i : ℤ) by exact_mod_cast hv i)).mp hprod
  let b : Fin d → ℕ := fun i ↦ (q i).toNat
  have hbcast (i : Fin d) : (b i : ℤ) = q i :=
    Int.toNat_of_nonneg (hqnonneg i)
  have hb (i : Fin d) : b i ≤ n i := Int.toNat_le.mpr (hqle i)
  let g : BoxPoint d := t + fun i ↦ (v i : ℤ) * (b i : ℤ)
  have hg : g ∈ G := hgrid (Elementary.mem_translate_iff.mpr
    ⟨fun i ↦ (v i : ℤ) * (b i : ℤ),
      mem_rectangularGrid_iff.mpr ⟨b, hb, rfl⟩, rfl⟩)
  apply Elementary.mem_sumset_iff.mpr
  refine ⟨g, hg, r, hrR, ?_⟩
  funext i
  change t i + (v i : ℤ) * (b i : ℤ) + r i =
    t i + center i + z i
  rw [hbcast, ← hq i]
  simp only [Pi.add_apply]
  ring

/-- A finite set contains a translate of a box. -/
def ContainsTranslate {d : ℕ} (S : Finset (BoxPoint d))
    (Q : AxisBox d) : Prop :=
  ∃ t : BoxPoint d, Elementary.translate t Q.carrier ⊆ S

theorem containsTranslate_mono {d : ℕ} {S T : Finset (BoxPoint d)}
    {Q : AxisBox d} (hST : S ⊆ T) (hS : ContainsTranslate S Q) :
    ContainsTranslate T Q := by
  obtain ⟨t, ht⟩ := hS
  exact ⟨t, ht.trans hST⟩

/-- The concrete output of the fibre/Lev/block selection part of CFP
Lemma 2.15.  Unlike `DenseBoxLemma`, this is data rather than an asserted
existence theorem: it records the two disjoint groups of original summands,
the rectangular grid made by the coordinate blocks, and the bounded complete
set of residue representatives made by the final block. -/
structure DenseBoxCertificate {d ell : ℕ}
    (Q : AxisBox d) (A : Fin ell → Finset (BoxPoint d)) (k : ℕ) where
  periods : Fin d → ℕ
  gridLengths : Fin d → ℕ
  bounds : Fin d → ℕ
  gridIndices : Finset (Fin ell)
  residueIndices : Finset (Fin ell)
  indices_disjoint : Disjoint gridIndices residueIndices
  period_pos : ∀ i, 0 < periods i
  left_margin : ∀ i, bounds i ≤ periods i * (gridLengths i / 2)
  right_margin : ∀ i,
    periods i * (gridLengths i / 2) + k * (Q.widths i - 1) + bounds i ≤
      periods i * gridLengths i
  gridTranslate : BoxPoint d
  grid_subset :
    Elementary.translate gridTranslate (rectangularGrid periods gridLengths) ⊆
      partialSumset A gridIndices
  residueTranslate : BoxPoint d
  residue_complete :
    RectangularResidueComplete periods
      (Elementary.translate residueTranslate (partialSumset A residueIndices))
  residue_bound : CoordinateBound
    (Elementary.translate residueTranslate (partialSumset A residueIndices)) bounds

/-- Once the source-paper fibre and block construction has produced a
`DenseBoxCertificate`, the desired translated box follows unconditionally.
This theorem packages the complete grid/residue/unused-index assembly. -/
theorem containsTranslate_of_denseBoxCertificate {d ell : ℕ}
    (Q : AxisBox d) (A : Fin ell → Finset (BoxPoint d)) (k : ℕ)
    (hAne : ∀ i, (A i).Nonempty) (cert : DenseBoxCertificate Q A k) :
    ContainsTranslate (heterogeneousSumset A) (Q.dilate k) := by
  obtain ⟨s, hs⟩ := grid_add_residues_contains_dilate Q k cert.periods
    cert.gridLengths cert.bounds
    cert.period_pos cert.left_margin cert.right_margin cert.gridTranslate
    cert.grid_subset cert.residue_complete cert.residue_bound
  rw [elementary_sumset_translate_right] at hs
  have hs' := Elementary.translate_mono (a := -cert.residueTranslate) hs
  rw [Elementary.translate_translate, Elementary.translate_translate] at hs'
  simp only [neg_add_cancel, Elementary.translate_zero] at hs'
  have hpartial :
      Elementary.sumset (partialSumset A cert.gridIndices)
          (partialSumset A cert.residueIndices) ⊆
        partialSumset A (cert.gridIndices ∪ cert.residueIndices) := by
    rw [partialSumset_union_of_disjoint A cert.indices_disjoint]
  obtain ⟨u, hu⟩ := exists_translate_subset_heterogeneousSumset_of_partial hAne
    (cert.gridIndices ∪ cert.residueIndices) (hs'.trans hpartial)
  refine ⟨u + (-cert.residueTranslate + s), ?_⟩
  rw [← Elementary.translate_translate]
  exact hu

/-- The full fibre/block/residue construction of CFP Lemma 2.15, with the
remaining elementary size estimates exposed as explicit natural-number
hypotheses.  Unlike `DenseBoxCertificate`, this theorem constructs the
certificate from the density and reducedness assumptions. -/
theorem exists_denseBoxCertificate_of_numerics
    {d ell V L R k₀ : ℕ} (hd : 0 < d)
    (Q : AxisBox d) (A : Fin ell → Finset (BoxPoint d))
    (cNum cDen : ℕ) (hcNum : 0 < cNum) (hcDen : 0 < cDen)
    (hsubset : ∀ i, A i ⊆ Q.carrier)
    (hdensity : ∀ i, cNum * Q.volume ≤ cDen * (A i).card)
    (hreduced : ∀ i, Reduced (A i))
    (hV : V = 4 * cDen) (hR : R = V ^ d)
    (htotal : d * (V * L) + R ≤ ell)
    (hwidth : ∀ i, 8 * cDen ≤ Q.widths i)
    (hL : 1 ≤ L)
    (hLevLarge : ∀ i,
      2 * (((Q.widths i - 1) - 1 +
          (Q.widths i / (2 * cDen) - 2) - 1) /
        (Q.widths i / (2 * cDen) - 2)) ≤ L)
    (hmargin : ∀ i,
      (k₀ + R) * (Q.widths i - 1) ≤
        (L * (Q.widths i / (2 * cDen) - 1)) / 2) :
    Nonempty (DenseBoxCertificate Q A k₀) := by
  classical
  let pairEquiv : Fin d × Fin (V * L) ≃ Fin (d * (V * L)) :=
    Fintype.equivOfCardEq (by simp)
  let totalEmbed : Fin (d * (V * L) + R) → Fin ell :=
    Fin.castLE htotal
  have htotalEmbed : Function.Injective totalEmbed := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin ell ↦ x.val) hij
  let cand : Fin d → Fin (V * L) → Fin ell := fun i j ↦
    totalEmbed (Fin.castAdd R (pairEquiv (i, j)))
  have hcandPair : Function.Injective
      (fun p : Fin d × Fin (V * L) ↦ cand p.1 p.2) := by
    intro p q hpq
    apply pairEquiv.injective
    apply Fin.ext
    exact congrArg (fun x : Fin (d * (V * L) + R) ↦ x.val)
      (htotalEmbed hpq)
  have hcand (i : Fin d) : Function.Injective (cand i) := by
    intro x y hxy
    have hp : (i, x) = (i, y) := hcandPair hxy
    exact congrArg Prod.snd hp
  choose periods hperiod_pos hperiod_le selectors hselectors
      lineTranslate hline using fun i : Fin d ↦
    exists_coordinateLineBlock Q A i (cand i) (hcand i)
      cNum cDen hcNum hcDen hsubset hdensity hV hL (hwidth i) (hLevLarge i)
  let source : Fin d → Fin L → Fin ell := fun i j ↦ cand i (selectors i j)
  have hsource : Function.Injective
      (fun p : Fin d × Fin L ↦ source p.1 p.2) := by
    rintro ⟨pi, pj⟩ ⟨qi, qj⟩ hpq
    have hp : (pi, selectors pi pj) = (qi, selectors qi qj) := hcandPair hpq
    have hk : pi = qi :=
      congrArg (fun z : Fin d × Fin (V * L) ↦ z.1) hp
    subst qi
    have hs : selectors pi pj = selectors pi qj :=
      congrArg (fun z : Fin d × Fin (V * L) ↦ z.2) hp
    exact Prod.ext rfl (hselectors pi hs)
  let gridIndices : Finset (Fin ell) :=
    Finset.univ.image (fun p : Fin d × Fin L ↦ source p.1 p.2)
  let gridLengths : Fin d → ℕ := fun i ↦
    L * (Q.widths i / (2 * cDen) - 1)
  have hgrid : Elementary.translate (∑ i, lineTranslate i)
        (rectangularGrid periods gridLengths) ⊆ partialSumset A gridIndices := by
    have hlines : ∀ i,
        axisLine (lineTranslate i) i (periods i) (gridLengths i) ⊆
          partialSumset A (Finset.univ.image (source i)) := by
      intro i
      change axisLine (lineTranslate i) i (periods i)
          (L * (Q.widths i / (2 * cDen) - 1)) ⊆
        partialSumset A (Finset.univ.image (cand i ∘ selectors i))
      exact hline i
    have hraw := rectangularGrid_subset_heterogeneousSumset_of_axisLines
      lineTranslate periods gridLengths hlines
    rw [heterogeneousSumset_partialSumset_product A source hsource] at hraw
    simpa [gridIndices] using hraw
  let r := ∏ i, periods i
  have hrR : r ≤ R := by
    calc
      r ≤ ∏ _i : Fin d, V := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ hperiod_le i)
      _ = V ^ d := by simp
      _ = R := hR.symm
  let residueBase : Fin R → Fin ell := fun j ↦
    totalEmbed (Fin.natAdd (d * (V * L)) j)
  have hresidueBase : Function.Injective residueBase := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val (htotalEmbed hij)
    simpa [residueBase] using hval
  let residueIndex : Fin r → Fin ell := fun j ↦
    residueBase (Fin.castLE hrR j)
  have hresidueIndex : Function.Injective residueIndex := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val (hresidueBase hij)
    exact hval
  let residueIndices : Finset (Fin ell) := Finset.univ.image residueIndex
  have hdisjoint : Disjoint gridIndices residueIndices := by
    rw [Finset.disjoint_left]
    intro x hxg hxr
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hxg
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hxr
    have heq : Fin.castAdd R (pairEquiv (p.1, selectors p.1 p.2)) =
        Fin.natAdd (d * (V * L)) (Fin.castLE hrR j) := by
      apply htotalEmbed
      exact hj.symm
    have hval := congrArg (fun z : Fin (d * (V * L) + R) ↦ z.val) heq
    change (pairEquiv (p.1, selectors p.1 p.2)).val =
      d * (V * L) + (Fin.castLE hrR j).val at hval
    have hpairlt := (pairEquiv (p.1, selectors p.1 p.2)).isLt
    omega
  have hvolume : 0 < Q.volume := by
    exact Finset.prod_pos fun i _ ↦ Q.width_pos i
  have hAne (i : Fin ell) : (A i).Nonempty := by
    rw [← Finset.card_pos]
    have hpos : 0 < cNum * Q.volume := Nat.mul_pos hcNum hvolume
    have hi := hdensity i
    by_contra hz
    have hz' : (A i).card = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero] at hi
    omega
  choose anchor hanchor using fun j : Fin r ↦ hAne (residueIndex j)
  let originalResidue : Fin r → Finset (BoxPoint d) :=
    fun j ↦ A (residueIndex j)
  let normalizedResidue : Fin r → Finset (BoxPoint d) := fun j ↦
    Elementary.translate (-anchor j) (originalResidue j)
  let residueNat : ℕ → Finset (BoxPoint d) := fun j ↦
    if hj : j < r then normalizedResidue ⟨j, hj⟩ else {0}
  have hnorm_ne (j : Fin r) : (normalizedResidue j).Nonempty :=
    (hAne (residueIndex j)).image _
  have hnorm_red (j : Fin r) : Reduced (normalizedResidue j) := by
    exact (reduced_translate_iff (-anchor j) (originalResidue j)).2
      (hreduced (residueIndex j))
  have hcomplete0 : RectangularResidueComplete periods
      (iteratedSumset residueNat r) := by
    apply reduced_block_residue_complete periods hperiod_pos residueNat
    · intro j hj
      dsimp [residueNat]
      rw [dif_pos hj]
      exact hnorm_ne ⟨j, hj⟩
    · intro j hj
      dsimp [residueNat]
      rw [dif_pos hj]
      exact hnorm_red ⟨j, hj⟩
  have hresidueEq : iteratedSumset residueNat r =
      Elementary.translate (∑ j, -anchor j) (partialSumset A residueIndices) := by
    calc
      iteratedSumset residueNat r = heterogeneousSumset normalizedResidue := by
        simpa [residueNat] using iteratedSumset_fin normalizedResidue
      _ = Elementary.translate (∑ j, -anchor j)
          (heterogeneousSumset originalResidue) := by
        simpa [normalizedResidue] using
          heterogeneousSumset_translate (fun j ↦ -anchor j) originalResidue
      _ = Elementary.translate (∑ j, -anchor j)
          (partialSumset A residueIndices) := by
        rw [heterogeneousSumset_reindex_injective A residueIndex hresidueIndex]
  rw [hresidueEq] at hcomplete0
  have hnorm_bound : ∀ j : Fin r, ∀ x ∈ normalizedResidue j, ∀ i,
      -(((Q.widths i - 1 : ℕ)) : ℤ) ≤ x i ∧
        x i ≤ ((Q.widths i - 1 : ℕ) : ℤ) := by
    intro j x hx i
    obtain ⟨y, hy, hyx⟩ := Elementary.mem_translate_iff.mp hx
    have haQ := (AxisBox.mem_carrier_iff Q).mp
      (hsubset (residueIndex j) (hanchor j)) i
    have hyQ := (AxisBox.mem_carrier_iff Q).mp
      (hsubset (residueIndex j) hy) i
    have heqi := congrFun hyx i
    have hw := Q.width_pos i
    simp only [Pi.neg_apply, Pi.add_apply] at heqi
    push_cast
    omega
  have hbound0 : CoordinateBound (iteratedSumset residueNat r)
      (fun i ↦ r * (Q.widths i - 1)) := by
    apply coordinateBound_iteratedSumset residueNat
      (fun i ↦ Q.widths i - 1)
    intro j hj
    dsimp [residueNat]
    rw [dif_pos hj]
    exact hnorm_bound ⟨j, hj⟩
  rw [hresidueEq] at hbound0
  have hbound : CoordinateBound
      (Elementary.translate (∑ j, -anchor j) (partialSumset A residueIndices))
      (fun i ↦ R * (Q.widths i - 1)) := by
    apply hbound0.mono
    intro i
    exact Nat.mul_le_mul_right _ hrR
  have hleft : ∀ i,
      R * (Q.widths i - 1) ≤ periods i * (gridLengths i / 2) := by
    intro i
    calc
      R * (Q.widths i - 1) ≤
          (k₀ + R) * (Q.widths i - 1) := by
        exact Nat.mul_le_mul_right _ (Nat.le_add_left R k₀)
      _ ≤ gridLengths i / 2 := hmargin i
      _ ≤ periods i * (gridLengths i / 2) :=
        Nat.le_mul_of_pos_left _ (hperiod_pos i)
  have hright : ∀ i,
      periods i * (gridLengths i / 2) + k₀ * (Q.widths i - 1) +
          R * (Q.widths i - 1) ≤ periods i * gridLengths i := by
    intro i
    have htail : k₀ * (Q.widths i - 1) + R * (Q.widths i - 1) ≤
        periods i * (gridLengths i / 2) := by
      calc
        k₀ * (Q.widths i - 1) + R * (Q.widths i - 1) =
            (k₀ + R) * (Q.widths i - 1) := by ring
        _ ≤ gridLengths i / 2 := hmargin i
        _ ≤ periods i * (gridLengths i / 2) :=
          Nat.le_mul_of_pos_left _ (hperiod_pos i)
    calc
      periods i * (gridLengths i / 2) + k₀ * (Q.widths i - 1) +
          R * (Q.widths i - 1) =
          periods i * (gridLengths i / 2) +
            (k₀ * (Q.widths i - 1) + R * (Q.widths i - 1)) := by omega
      _ ≤ periods i * (gridLengths i / 2) +
          periods i * (gridLengths i / 2) := Nat.add_le_add_left htail _
      _ = periods i * (2 * (gridLengths i / 2)) := by ring
      _ ≤ periods i * gridLengths i := by
        exact Nat.mul_le_mul_left _ (by omega)
  exact ⟨{
    periods := periods
    gridLengths := gridLengths
    bounds := fun i ↦ R * (Q.widths i - 1)
    gridIndices := gridIndices
    residueIndices := residueIndices
    indices_disjoint := hdisjoint
    period_pos := hperiod_pos
    left_margin := hleft
    right_margin := hright
    gridTranslate := ∑ i, lineTranslate i
    grid_subset := hgrid
    residueTranslate := ∑ j, -anchor j
    residue_complete := hcomplete0
    residue_bound := hbound }⟩

/-! ## Lattice-basis progressions (CFP Lemma 2.16) -/

open Module LatticeBasis

/-- The centered coefficient box attached to a lattice basis. -/
def centeredCoefficientBox {d : ℕ} (r : Fin d → ℕ) :
    Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (-(r i : ℤ)) (r i : ℤ)

@[simp] theorem mem_centeredCoefficientBox_iff {d : ℕ}
    {r : Fin d → ℕ} {a : Fin d → ℤ} :
    a ∈ centeredCoefficientBox r ↔ ∀ i, |a i| ≤ (r i : ℤ) := by
  simp only [centeredCoefficientBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i
    exact (abs_le).2 (h i)
  · intro h i
    exact (abs_le).1 (h i)

/-- The actual proper GAP in `ℤ^d` obtained by applying a lattice basis to
a centered coefficient box.  It is kept as a finite carrier because that is
the representation consumed by the dense-box and subset-sum layers. -/
def basisProgression {d : ℕ} {Γ : Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (r : Fin d → ℕ) : Finset (BoxPoint d) :=
  (centeredCoefficientBox r).image fun a ↦
    ((∑ i, a i • b i : Γ) : BoxPoint d)

/-- Basis coordinates are recovered exactly after evaluating a coefficient
vector.  This is the properness input for the progression. -/
theorem basisCoeff_sum_basis {d : ℕ} {Γ : Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (a : Fin d → ℤ) (i : Fin d) :
    basisCoeff b (∑ j, a j • b j) i = a i := by
  classical
  simp [basisCoeff, Finsupp.single_apply]

/-- Exact membership characterization of a basis progression. -/
theorem mem_basisProgression_iff {d : ℕ} {Γ : Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (r : Fin d → ℕ) (x : Γ) :
    (x : BoxPoint d) ∈ basisProgression b r ↔
      ∀ i, |basisCoeff b x i| ≤ (r i : ℤ) := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    have hsub : (∑ j, a j • b j : Γ) = x := by
      apply Subtype.ext
      exact hax
    intro i
    rw [← hsub, basisCoeff_sum_basis]
    exact (mem_centeredCoefficientBox_iff.mp ha) i
  · intro hx
    let a : Fin d → ℤ := fun i ↦ basisCoeff b x i
    apply Finset.mem_image.mpr
    refine ⟨a, mem_centeredCoefficientBox_iff.mpr hx, ?_⟩
    have hsum : (∑ i, a i • b i : Γ) = x := by
      simpa [a] using sum_basisCoeff_smul b x
    exact congrArg Subtype.val hsum

/-- A basis progression is proper: its displayed coefficient box has exactly
the product of its displayed odd widths. -/
theorem card_basisProgression {d : ℕ} {Γ : Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (r : Fin d → ℕ) :
    (basisProgression b r).card = ∏ i, (2 * r i + 1) := by
  classical
  rw [basisProgression, Finset.card_image_of_injOn]
  · simp only [centeredCoefficientBox, Fintype.card_piFinset, Int.card_Icc]
    apply Finset.prod_congr rfl
    intro i _
    norm_num
    omega
  · intro a ha c hc hac
    have hsub : (∑ i, a i • b i : Γ) = ∑ i, c i • b i := by
      apply Subtype.ext
      exact hac
    funext i
    have hi := congrArg (fun x : Γ ↦ basisCoeff b x i) hsub
    simpa [basisCoeff_sum_basis] using hi

/-- The finite-set basis progression used in the dense-box argument is
exactly the carrier of the source-facing centered basis `GAP`. -/
theorem centeredBasisGAP_carrier_eq_basisProgression {d : ℕ}
    {Γ : Sublattice d} (b : Basis (Fin d) ℤ Γ) (r : Fin d → ℕ) :
    (AdaptedHNF.centeredBasisGAP b r).carrier = basisProgression b r := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
    rw [AdaptedHNF.centeredBasisGAP_coordPoint]
    apply Finset.mem_image.mpr
    let a : Fin d → ℤ := fun i ↦ ((n i : ℕ) : ℤ) - (r i : ℤ)
    refine ⟨a, ?_, rfl⟩
    rw [mem_centeredCoefficientBox_iff]
    intro i
    have hn := (n i).isLt
    simp only [AdaptedHNF.centeredBasisGAP_widths] at hn
    dsimp [a]
    rw [abs_le]
    constructor <;> norm_num at ⊢ <;> omega
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have ha' := mem_centeredCoefficientBox_iff.mp ha
    have hnonneg (i : Fin d) : 0 ≤ a i + (r i : ℤ) := by
      have hi := abs_le.mp (ha' i)
      omega
    have hlt (i : Fin d) :
        (a i + (r i : ℤ)).toNat < 2 * r i + 1 := by
      have hi := (abs_le.mp (ha' i)).2
      rw [Int.toNat_lt]
      · push_cast
        omega
      · exact hnonneg i
    let n : (AdaptedHNF.centeredBasisGAP b r).Coord :=
      fun i ↦ ⟨(a i + (r i : ℤ)).toNat, by
        simpa only [AdaptedHNF.centeredBasisGAP_widths] using hlt i⟩
    apply GAP.mem_carrier_iff.mpr
    refine ⟨n, ?_⟩
    rw [AdaptedHNF.centeredBasisGAP_coordPoint]
    apply congrArg Subtype.val
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [n]
    rw [Int.toNat_of_nonneg (hnonneg i)]
    omega

/-- A symmetric ambient box used to state the quantitative containment half
of CFP Lemma 2.16 without losing anisotropic width information. -/
def symmetricAxisBox {d : ℕ} (w : Fin d → ℕ) : AxisBox d where
  lower := fun i ↦ -(w i : ℤ)
  widths := fun i ↦ 2 * w i + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp] theorem mem_symmetricAxisBox_iff {d : ℕ} {w : Fin d → ℕ}
    {x : BoxPoint d} :
    x ∈ (symmetricAxisBox w).carrier ↔ ∀ i, |x i| ≤ (w i : ℤ) := by
  rw [AxisBox.mem_carrier_iff]
  constructor
  · intro h i
    rw [abs_le]
    have hi := h i
    change -(w i : ℤ) ≤ x i ∧ x i < -(w i : ℤ) + (2 * w i + 1 : ℕ) at hi
    push_cast at hi
    omega
  · intro h i
    have hi := (abs_le.mp (h i))
    change -(w i : ℤ) ≤ x i ∧ x i < -(w i : ℤ) + (2 * w i + 1 : ℕ)
    push_cast
    omega

/-- The unconditional adapted-HNF progression construction needed in CFP
Lemma 2.16.  The progression is proper by `card_basisProgression`, and its
coefficient widths are the ambient widths in sorted order.  Its carrier is
contained in the symmetric box with coordinate radii `d * v_j * w_j`.

The reverse containment `Q ∩ Γ ⊆ P` is a separate inverse-coordinate
estimate; keeping it out of this theorem prevents the source's invalid
arbitrary-basis argument from being smuggled in as an assumption. -/
theorem exists_basisProgression_subset_symmetricBox {d : ℕ}
    (v w : Fin d → ℕ) (hv : ∀ i, 0 < v i) (Γ : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Γ) :
    ∃ (σ : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Γ),
      Monotone (w ∘ σ) ∧
      basisProgression b (w ∘ σ) ⊆
        (symmetricAxisBox (fun j ↦ d * v j * w j)).carrier := by
  classical
  obtain ⟨σ, b, hw, hb⟩ :=
    AdaptedHNF.exists_widthAdapted_basis hv Γ hrect
  refine ⟨σ, b, hw, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_symmetricAxisBox_iff]
  intro j
  have ha' := mem_centeredCoefficientBox_iff.mp ha
  have hbound := hb a ha' j
  simpa only [Nat.cast_mul] using hbound

/-- The reverse half of the actual lattice sandwich in CFP Lemma 2.16.
For the same width-sorted basis used in the adapted-HNF construction, the
intersection of the ambient symmetric box with `Γ` lies in a proper basis
progression whose coefficient radii lose only the explicit constant
`inverseCoefficientConstantNat d (v ∘ σ)`. -/
theorem exists_symmetricBox_inter_lattice_subset_basisProgression
    {d : ℕ} (v w : Fin d → ℕ) (hv : ∀ i, 0 < v i)
    (Γ : Sublattice d) (hrect : rectangularSubgroup v ≤ Γ) :
    ∃ (σ : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Γ),
      Monotone (w ∘ σ) ∧
      ∀ y : Γ,
        (y : BoxPoint d) ∈ (symmetricAxisBox w).carrier →
        (y : BoxPoint d) ∈ basisProgression b
          (fun i ↦ AdaptedHNF.inverseCoefficientConstantNat d (v ∘ σ) *
            w (σ i)) := by
  classical
  obtain ⟨σ, b, hw, _hforward, hreverse⟩ :=
    AdaptedHNF.exists_widthAdapted_basis_with_inverse hv Γ hrect
  refine ⟨σ, b, hw, ?_⟩
  intro y hy
  rw [mem_basisProgression_iff]
  exact hreverse y (mem_symmetricAxisBox_iff.mp hy)

/-- The complete, unconditional lattice-basis sandwich required in CFP
Lemma 2.16.  The same proper basis progression contains the intersection of
the ambient box with `Γ` and is contained in an explicit constant dilate of
that box.  The constant depends only on `d` and the rectangular periods. -/
theorem exists_basisProgression_sandwich_symmetricBox
    {d : ℕ} (v w : Fin d → ℕ) (hv : ∀ i, 0 < v i)
    (Γ : Sublattice d) (hrect : rectangularSubgroup v ≤ Γ) :
    ∃ (σ : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Γ) (C : ℕ),
      C = AdaptedHNF.inverseCoefficientConstantNat d (v ∘ σ) ∧
      (∀ y : Γ,
        (y : BoxPoint d) ∈ (symmetricAxisBox w).carrier →
        (y : BoxPoint d) ∈ basisProgression b
          (fun i ↦ C * w (σ i))) ∧
      basisProgression b (fun i ↦ C * w (σ i)) ⊆
        (symmetricAxisBox (fun j ↦ C * d * v j * w j)).carrier := by
  classical
  obtain ⟨σ, b, _hw, hforward, hreverse⟩ :=
    AdaptedHNF.exists_widthAdapted_basis_with_inverse hv Γ hrect
  let C := AdaptedHNF.inverseCoefficientConstantNat d (v ∘ σ)
  refine ⟨σ, b, C, rfl, ?_, ?_⟩
  · intro y hy
    rw [mem_basisProgression_iff]
    exact hreverse y (mem_symmetricAxisBox_iff.mp hy)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_symmetricAxisBox_iff]
    exact hforward C a (mem_centeredCoefficientBox_iff.mp ha)

/-! ## CFP Lemma 2.15 -/

/-- The exact integer-rounded conclusion of CFP Lemma 2.15.

The denominator `C` represents the reciprocal of the paper's constant
`gamma`; the two thresholds express "ell and the minimum width of Q are
sufficiently large in terms of c and d". -/
def DenseBoxLemma : Prop :=
  ∀ d : ℕ, 0 < d → ∀ cNum cDen : ℕ,
    0 < cNum → cNum ≤ cDen →
    ∃ C ell₀ width₀ : ℕ, 0 < C ∧
      ∀ (ell : ℕ) (Q : AxisBox d)
        (A : Fin ell → Finset (BoxPoint d)),
        ell₀ ≤ ell → width₀ ≤ Q.minWidth →
        (∀ i, A i ⊆ Q.carrier) →
        (∀ i, cNum * Q.volume ≤ cDen * (A i).card) →
        (∀ i, Reduced (A i)) →
        ContainsTranslate (heterogeneousSumset A) (Q.dilate (ell / C))

/-- CFP Lemma 2.15, with explicit constants and all integer roundings. -/
theorem denseBoxLemma : DenseBoxLemma := by
  intro d hd cNum cDen hcNum _hc
  have hcDen : 0 < cDen := lt_of_lt_of_le hcNum _hc
  let V := 4 * cDen
  let R := V ^ d
  let blockCost := d * V * (16 * cDen)
  let C := 2 * blockCost
  let ell₀ := 2 * (blockCost * R + R)
  let width₀ := 24 * cDen * cDen
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hblockCost : 0 < blockCost := by dsimp [blockCost]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, ell₀, width₀, hC, ?_⟩
  intro ell Q A hell hwidthMin hsubset hdensity hreduced
  let k₀ := ell / C
  let L := 16 * cDen * (k₀ + R)
  have hL : 1 ≤ L := by
    have hsum : 0 < k₀ + R := Nat.add_pos_right _ hRpos
    have hLpos : 0 < L := by
      dsimp [L]
      exact Nat.mul_pos (by positivity) hsum
    omega
  have hkhalf : blockCost * k₀ ≤ ell / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    calc
      blockCost * k₀ * 2 = C * k₀ := by simp [C]; ring
      _ ≤ ell := by simpa [k₀] using Nat.mul_div_le ell C
  have hconsthalf : blockCost * R + R ≤ ell / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa [ell₀, mul_comm] using hell
  have htotal : d * (V * L) + R ≤ ell := by
    calc
      d * (V * L) + R = blockCost * k₀ + (blockCost * R + R) := by
        simp only [L, blockCost]
        ring
      _ ≤ ell / 2 + ell / 2 := Nat.add_le_add hkhalf hconsthalf
      _ ≤ ell := by omega
  have hwidth (i : Fin d) : 8 * cDen ≤ Q.widths i := by
    have hwide : width₀ ≤ Q.widths i :=
      hwidthMin.trans (Q.minWidth_le hd i)
    dsimp [width₀] at hwide
    nlinarith
  have hLevLarge (i : Fin d) :
      2 * (((Q.widths i - 1) - 1 +
          (Q.widths i / (2 * cDen) - 2) - 1) /
        (Q.widths i / (2 * cDen) - 2)) ≤ L := by
    let W := Q.widths i
    let b := W / (2 * cDen)
    have hwide : 24 * cDen * cDen ≤ W := by
      simpa [width₀, W] using hwidthMin.trans (Q.minWidth_le hd i)
    have hb12 : 12 * cDen ≤ b := by
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
      convert hwide using 1 <;> ring
    have hbpos : 0 < b - 2 := by omega
    have hwlt : W < (2 * cDen) * (b + 1) := by
      simpa [b] using Nat.lt_mul_div_succ W
        (by positivity : 0 < 2 * cDen)
    have hnum : (W - 1) - 1 + (b - 2) - 1 ≤ 4 * cDen * (b - 2) := by
      have hc : 1 ≤ cDen := hcDen
      have hb2 : 2 ≤ b := by omega
      have hbEq : b = (b - 2) + 2 := by omega
      have hnle : (W - 1) - 1 + (b - 2) - 1 ≤ W + b := by omega
      have hpoly : W + b ≤ 4 * cDen * (b - 2) := by
        nlinarith
      exact hnle.trans hpoly
    have hdiv : ((W - 1) - 1 + (b - 2) - 1) / (b - 2) ≤ 4 * cDen := by
      apply (Nat.div_le_iff_le_mul hbpos).2
      omega
    have hsmall :
        2 * (((W - 1) - 1 + (b - 2) - 1) / (b - 2)) ≤ 8 * cDen := by
      calc
        2 * (((W - 1) - 1 + (b - 2) - 1) / (b - 2)) ≤
            2 * (4 * cDen) := Nat.mul_le_mul_left 2 hdiv
        _ = 8 * cDen := by ring
    have h8L : 8 * cDen ≤ L := by
      have hsum : 0 < k₀ + R := Nat.add_pos_right _ hRpos
      calc
        8 * cDen ≤ 16 * cDen := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (16 * cDen) * (k₀ + R) :=
          Nat.le_mul_of_pos_right _ hsum
        _ = L := by rfl
    simpa [W, b] using hsmall.trans h8L
  have hmargin (i : Fin d) :
      (k₀ + R) * (Q.widths i - 1) ≤
        (L * (Q.widths i / (2 * cDen) - 1)) / 2 := by
    let W := Q.widths i
    let b := W / (2 * cDen)
    have hb4 : 4 ≤ b := by
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
      convert hwidth i using 1 <;> ring
    have hwlt : W < (2 * cDen) * (b + 1) := by
      simpa [b] using Nat.lt_mul_div_succ W
        (by positivity : 0 < 2 * cDen)
    have hfactor : b + 1 ≤ 2 * (b - 1) := by omega
    have hW : W - 1 ≤ 4 * cDen * (b - 1) := by
      have hlt : W < 4 * cDen * (b - 1) := by
        calc
          W < (2 * cDen) * (b + 1) := hwlt
          _ ≤ (2 * cDen) * (2 * (b - 1)) :=
            Nat.mul_le_mul_left _ hfactor
          _ = 4 * cDen * (b - 1) := by ring
      omega
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    calc
      (k₀ + R) * (W - 1) * 2 ≤
          (k₀ + R) * (4 * cDen * (b - 1)) * 2 :=
        Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left _ hW)
      _ ≤ (16 * cDen * (k₀ + R)) * (b - 1) := by nlinarith
      _ = L * (b - 1) := by simp [L]
  obtain ⟨cert⟩ := exists_denseBoxCertificate_of_numerics hd Q A
    cNum cDen hcNum hcDen hsubset hdensity hreduced
    (V := V) (L := L) (R := R) (k₀ := k₀)
    rfl rfl htotal hwidth hL hLevLarge hmargin
  have hAne (i : Fin ell) : (A i).Nonempty := by
    rw [← Finset.card_pos]
    have hvolume : 0 < Q.volume :=
      Finset.prod_pos fun j _ ↦ Q.width_pos j
    have hpos : 0 < cNum * Q.volume := Nat.mul_pos hcNum hvolume
    have hi := hdensity i
    by_contra hz
    have hz' : (A i).card = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero] at hi
    omega
  simpa [k₀] using
    containsTranslate_of_denseBoxCertificate Q A k₀ hAne cert

/-! ## CFP Corollary 2.17 -/

/-- Concrete source-facing output of the reduced case of CFP Corollary 2.17.
Besides the two quantitative containments, the certificate retains the
adapted lattice basis and records exactly that the progression and the
original set generate the same lattice.  The last two fields are the
divisibility data used by the pullback in Lemmas 2.20 and 2.22. -/
structure Corollary217Certificate {d : ℕ}
    (Q : AxisBox d) (B : Finset (BoxPoint d)) where
  constant : ℕ
  constant_pos : 0 < constant
  sigma : Equiv.Perm (Fin d)
  basis : Basis (Fin d) ℤ (generatedSublattice B)
  radius : Fin d → ℕ
  /-- The construction retains at least the original box radius in every
  (permuted) direction.  This quantitative fact is needed when the common
  Corollary 2.17 progression is reused as the ambient box for all blocks. -/
  radius_lower : ∀ i, Q.minWidth - 1 ≤ radius i
  progression : GAP d d
  progression_eq :
    progression = AdaptedHNF.centeredBasisGAP basis radius
  centered : progression.Centered radius
  proper : progression.Proper
  zero_mem : 0 ∈ progression.carrier
  box_lattice_subset : ∀ x ∈ Q.carrier,
    x ∈ generatedSublattice B → x ∈ progression.carrier
  geometricTranslate : BoxPoint d
  geometric_bound : progression.carrier ⊆
    Elementary.translate geometricTranslate (Q.dilate constant).carrier
  sumTranslate : BoxPoint d
  sum_covered : Elementary.translate sumTranslate progression.carrier ⊆
    iteratedSumset (fun _ ↦ B) constant
  generated_carrier_eq :
    generatedSublattice progression.carrier = generatedSublattice B
  offset_mem_generated : progression.offset ∈ generatedSublattice B
  steps_mem_generated : ∀ i, progression.steps i ∈ generatedSublattice B

/-- The reducedness-free output of the coordinate-fibre part of Lemma 2.15.
This is the first input in the proof of CFP Lemma 2.16. -/
structure DenseGridCertificate {d ell : ℕ}
    (Q : AxisBox d) (A : Fin ell → Finset (BoxPoint d))
    (V L cDen : ℕ) where
  periods : Fin d → ℕ
  lengths : Fin d → ℕ
  lengths_eq : ∀ i,
    lengths i = L * (Q.widths i / (2 * cDen) - 1)
  period_pos : ∀ i, 0 < periods i
  period_le : ∀ i, periods i ≤ V
  translate : BoxPoint d
  grid_subset : Elementary.translate translate
    (rectangularGrid periods lengths) ⊆ heterogeneousSumset A

/-- Coordinate blocks alone produce a translated rectangular grid; unlike
`exists_denseBoxCertificate_of_numerics`, this theorem has no reducedness
hypothesis and uses no residue block. -/
theorem exists_denseGridCertificate_of_numerics
    {d ell V L : ℕ} (Q : AxisBox d)
    (A : Fin ell → Finset (BoxPoint d))
    (cNum cDen : ℕ) (hcNum : 0 < cNum) (hcDen : 0 < cDen)
    (hsubset : ∀ i, A i ⊆ Q.carrier)
    (hdensity : ∀ i, cNum * Q.volume ≤ cDen * (A i).card)
    (hV : V = 4 * cDen) (htotal : d * (V * L) ≤ ell)
    (hwidth : ∀ i, 8 * cDen ≤ Q.widths i)
    (hL : 1 ≤ L)
    (hLevLarge : ∀ i,
      2 * (((Q.widths i - 1) - 1 +
          (Q.widths i / (2 * cDen) - 2) - 1) /
        (Q.widths i / (2 * cDen) - 2)) ≤ L) :
    Nonempty (DenseGridCertificate Q A V L cDen) := by
  classical
  let pairEquiv : Fin d × Fin (V * L) ≃ Fin (d * (V * L)) :=
    Fintype.equivOfCardEq (by simp)
  let totalEmbed : Fin (d * (V * L)) → Fin ell := Fin.castLE htotal
  have htotalEmbed : Function.Injective totalEmbed := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin ell ↦ x.val) hij
  let cand : Fin d → Fin (V * L) → Fin ell := fun i j ↦
    totalEmbed (pairEquiv (i, j))
  have hcandPair : Function.Injective
      (fun p : Fin d × Fin (V * L) ↦ cand p.1 p.2) := by
    intro p q hpq
    apply pairEquiv.injective
    exact htotalEmbed hpq
  have hcand (i : Fin d) : Function.Injective (cand i) := by
    intro x y hxy
    have hp : (i, x) = (i, y) := hcandPair hxy
    exact congrArg Prod.snd hp
  choose periods hperiod_pos hperiod_le selectors hselectors
      lineTranslate hline using fun i : Fin d ↦
    exists_coordinateLineBlock Q A i (cand i) (hcand i)
      cNum cDen hcNum hcDen hsubset hdensity hV hL (hwidth i) (hLevLarge i)
  let source : Fin d → Fin L → Fin ell := fun i j ↦ cand i (selectors i j)
  have hsource : Function.Injective
      (fun p : Fin d × Fin L ↦ source p.1 p.2) := by
    rintro ⟨pi, pj⟩ ⟨qi, qj⟩ hpq
    have hp : (pi, selectors pi pj) = (qi, selectors qi qj) :=
      hcandPair hpq
    have hk : pi = qi := congrArg Prod.fst hp
    subst qi
    have hs : selectors pi pj = selectors pi qj := congrArg Prod.snd hp
    exact Prod.ext rfl (hselectors pi hs)
  let gridIndices : Finset (Fin ell) :=
    Finset.univ.image (fun p : Fin d × Fin L ↦ source p.1 p.2)
  let lengths : Fin d → ℕ := fun i ↦
    L * (Q.widths i / (2 * cDen) - 1)
  have hgrid : Elementary.translate (∑ i, lineTranslate i)
        (rectangularGrid periods lengths) ⊆ partialSumset A gridIndices := by
    have hlines : ∀ i,
        axisLine (lineTranslate i) i (periods i) (lengths i) ⊆
          partialSumset A (Finset.univ.image (source i)) := by
      intro i
      change axisLine (lineTranslate i) i (periods i)
          (L * (Q.widths i / (2 * cDen) - 1)) ⊆
        partialSumset A (Finset.univ.image (cand i ∘ selectors i))
      exact hline i
    have hraw := rectangularGrid_subset_heterogeneousSumset_of_axisLines
      lineTranslate periods lengths hlines
    rw [heterogeneousSumset_partialSumset_product A source hsource] at hraw
    simpa [gridIndices] using hraw
  have hvolume : 0 < Q.volume :=
    Finset.prod_pos fun i _ ↦ Q.width_pos i
  have hAne (i : Fin ell) : (A i).Nonempty := by
    rw [← Finset.card_pos]
    have hpos : 0 < cNum * Q.volume := Nat.mul_pos hcNum hvolume
    have hi := hdensity i
    by_contra hz
    have hz' : (A i).card = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero] at hi
    omega
  obtain ⟨u, hu⟩ := exists_translate_subset_heterogeneousSumset_of_partial
    hAne gridIndices hgrid
  rw [Elementary.translate_translate] at hu
  refine ⟨{
    periods := periods
    lengths := lengths
    lengths_eq := fun _ ↦ rfl
    period_pos := hperiod_pos
    period_le := hperiod_le
    translate := u + ∑ i, lineTranslate i
    grid_subset := hu }⟩

/-- A box containing zero is contained in the centered box whose radii are
one less than its displayed widths. -/
theorem carrier_subset_symmetricAxisBox_width_sub_one {d : ℕ}
    (Q : AxisBox d) (hzero : (0 : BoxPoint d) ∈ Q.carrier) :
    Q.carrier ⊆
      (symmetricAxisBox (fun i ↦ Q.widths i - 1)).carrier := by
  intro x hx
  rw [mem_symmetricAxisBox_iff]
  rw [AxisBox.mem_carrier_iff] at hx hzero
  intro i
  have hxi := hx i
  have hzi := hzero i
  simp only [Pi.zero_apply] at hzi
  rw [abs_le]
  have hw := Q.width_pos i
  rw [Nat.cast_sub (by omega : 1 ≤ Q.widths i)]
  push_cast at hxi hzi ⊢
  omega

/-- The origin-based dilation of a box is the unit-step rectangular grid
with the corresponding coordinate lengths. -/
theorem rectangularGrid_one_eq_dilate_carrier {d : ℕ}
    (Q : AxisBox d) (k : ℕ) :
    rectangularGrid (fun _ ↦ 1) (fun i ↦ k * (Q.widths i - 1)) =
      (Q.dilate k).carrier := by
  classical
  ext x
  rw [mem_rectangularGrid_iff, AxisBox.mem_carrier_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩ i
    simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
      zero_add, Nat.cast_one, one_mul]
    constructor
    · exact_mod_cast Nat.zero_le (b i)
    · exact_mod_cast Nat.lt_succ_of_le (hb i)
  · intro hx
    have hxnonneg (i : Fin d) : 0 ≤ x i := (hx i).1
    let b : Fin d → ℕ := fun i ↦ (x i).toNat
    have hbcast (i : Fin d) : (b i : ℤ) = x i := by
      exact Int.toNat_of_nonneg (hxnonneg i)
    refine ⟨b, ?_, ?_⟩
    · intro i
      have hxi := (hx i).2
      have hw := Q.width_pos i
      simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
        zero_add] at hxi
      apply Int.ofNat_le.mp
      rw [hbcast]
      push_cast at hxi ⊢
      omega
    · funext i
      change x i = (1 : ℤ) * (b i : ℤ)
      rw [one_mul, hbcast]

/-- A centered box of coordinate radii `M * (width-1)` fits into the
`k`-dilation after translating its lower corner, provided `2*M ≤ k`. -/
theorem symmetricAxisBox_subset_translate_dilate {d M k : ℕ}
    (Q : AxisBox d) (hMk : 2 * M ≤ k) :
    (symmetricAxisBox (fun i ↦ M * (Q.widths i - 1))).carrier ⊆
      Elementary.translate
        (fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ))
        (Q.dilate k).carrier := by
  intro x hx
  apply Elementary.mem_translate_iff.mpr
  refine ⟨x + (fun i ↦ ((M * (Q.widths i - 1) : ℕ) : ℤ)), ?_, ?_⟩
  · rw [AxisBox.mem_carrier_iff]
    rw [mem_symmetricAxisBox_iff] at hx
    intro i
    have hxi := abs_le.mp (hx i)
    have hw := Q.width_pos i
    have hscale :
        2 * (M * (Q.widths i - 1)) ≤ k * (Q.widths i - 1) := by
      calc
        2 * (M * (Q.widths i - 1)) =
            (2 * M) * (Q.widths i - 1) := by ring
        _ ≤ k * (Q.widths i - 1) := Nat.mul_le_mul_right _ hMk
    have hscaleZ :
        ((2 * (M * (Q.widths i - 1)) : ℕ) : ℤ) ≤
          (k * (Q.widths i - 1) : ℕ) := by exact_mod_cast hscale
    simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
      Pi.add_apply, zero_add]
    push_cast at hxi hscaleZ ⊢
    constructor <;> omega
  · funext i
    simp

/-- Conversely, translating such a centered box by its radius puts it
inside the origin-based dilation. -/
theorem translate_symmetricAxisBox_subset_dilate {d M k : ℕ}
    (Q : AxisBox d) (hMk : 2 * M ≤ k) :
    Elementary.translate
        (fun i ↦ ((M * (Q.widths i - 1) : ℕ) : ℤ))
        (symmetricAxisBox (fun i ↦ M * (Q.widths i - 1))).carrier ⊆
      (Q.dilate k).carrier := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Elementary.mem_translate_iff.mp hx
  rw [AxisBox.mem_carrier_iff]
  rw [mem_symmetricAxisBox_iff] at hy
  intro i
  have hyi := abs_le.mp (hy i)
  have hw := Q.width_pos i
  have hscale :
      2 * (M * (Q.widths i - 1)) ≤ k * (Q.widths i - 1) := by
    calc
      2 * (M * (Q.widths i - 1)) =
          (2 * M) * (Q.widths i - 1) := by ring
      _ ≤ k * (Q.widths i - 1) := Nat.mul_le_mul_right _ hMk
  have hscaleZ :
      ((2 * (M * (Q.widths i - 1)) : ℕ) : ℤ) ≤
        (k * (Q.widths i - 1) : ℕ) := by exact_mod_cast hscale
  simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
    Pi.add_apply, zero_add]
  push_cast at hyi hscaleZ ⊢
  constructor <;> omega

/-- The reduced, full-rank case of CFP Corollary 2.17, constructed
unconditionally from Lemma 2.15 and the adapted-HNF form of Lemma 2.16.
All constants depend only on the dimension and the displayed density. -/
theorem exists_corollary217Certificate_of_reduced
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ widthThreshold : ℕ, ∀ (Q : AxisBox d)
      (B : Finset (BoxPoint d)),
      widthThreshold ≤ Q.minWidth →
      (0 : BoxPoint d) ∈ B →
      B ⊆ Q.carrier →
      cNum * Q.volume ≤ cDen * B.card →
      Reduced B →
      Nonempty (Corollary217Certificate Q B) := by
  obtain ⟨C₀, ell₀, width₀, hC₀, hDense⟩ :=
    denseBoxLemma d hd cNum cDen hcNum hc
  let one : Fin d → ℕ := fun _ ↦ 1
  let H := AdaptedHNF.inverseCoefficientConstantNat d one
  let M := H * d
  let ell := ell₀ + C₀ * (2 * M + 1)
  refine ⟨max width₀ 2, ?_⟩
  intro Q B hwidth hzeroB hBQ hdensity hreduced
  have hwidth₀ : width₀ ≤ Q.minWidth :=
    (Nat.le_max_left _ _).trans hwidth
  have hwidthTwo : 2 ≤ Q.minWidth :=
    (Nat.le_max_right _ _).trans hwidth
  have hzeroQ : (0 : BoxPoint d) ∈ Q.carrier := hBQ hzeroB
  have hell₀ : ell₀ ≤ ell := by simp [ell]
  have hellpos : 0 < ell := by
    dsimp [ell]
    have : 0 < C₀ * (2 * M + 1) := Nat.mul_pos hC₀ (by omega)
    omega
  have hMleEll : 2 * M ≤ ell := by
    dsimp [ell]
    have hmul : 2 * M ≤ C₀ * (2 * M + 1) := by
      calc
        2 * M ≤ 2 * M + 1 := by omega
        _ = 1 * (2 * M + 1) := by simp
        _ ≤ C₀ * (2 * M + 1) :=
          Nat.mul_le_mul_right _ hC₀
    omega
  let k := ell / C₀
  have hk : 2 * M ≤ k := by
    apply (Nat.le_div_iff_mul_le hC₀).2
    calc
      2 * M * C₀ ≤ C₀ * (2 * M + 1) := by
        nlinarith
      _ ≤ ell := by simp [ell]
  have hkpos : 0 < k := by
    have hHpos : 0 < H := by
      simp [H, AdaptedHNF.inverseCoefficientConstantNat]
    have hMpos : 0 < M := Nat.mul_pos hHpos hd
    omega
  let family : Fin ell → Finset (BoxPoint d) := fun _ ↦ B
  have hfill :
      ContainsTranslate (heterogeneousSumset family) (Q.dilate k) := by
    simpa [family, k] using hDense ell Q family hell₀ hwidth₀
      (fun _ ↦ hBQ) (fun _ ↦ hdensity) (fun _ ↦ hreduced)
  obtain ⟨t, ht⟩ := hfill
  have hsumEq :
      heterogeneousSumset family = iteratedSumset (fun _ ↦ B) ell := by
    rw [heterogeneousSumset, List.sum_ofFn, iteratedSumset,
      ← Fin.sum_univ_eq_sum_range]
  rw [hsumEq] at ht
  let n : Fin d → ℕ := fun i ↦ k * (Q.widths i - 1)
  have hn (i : Fin d) : 1 ≤ n i := by
    have hwi : 2 ≤ Q.widths i :=
      hwidthTwo.trans (Q.minWidth_le hd i)
    dsimp [n]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hkpos) (by omega))
  have hgrid :
      Elementary.translate t (rectangularGrid one n) ⊆
        iteratedSumset (fun _ ↦ B) ell := by
    simpa [one, n, rectangularGrid_one_eq_dilate_carrier] using ht
  let Γ := generatedSublattice B
  have hrect : rectangularSubgroup one ≤ Γ :=
    rectangularSubgroup_le_generated_of_grid_subset_iteratedSumset
      B ell one n hn t hgrid
  have hone (i : Fin d) : 0 < one i := by simp [one]
  let w : Fin d → ℕ := fun i ↦ Q.widths i - 1
  obtain ⟨σ, b, H', hH', hreverse, hforward⟩ :=
    exists_basisProgression_sandwich_symmetricBox one w hone Γ hrect
  have hHeq : H' = H := by
    have honecomp : one ∘ σ = one := by
      funext i
      simp [one]
    rw [honecomp] at hH'
    simpa [H] using hH'
  rw [hHeq] at hreverse hforward
  let radius : Fin d → ℕ := fun i ↦ H * w (σ i)
  let P : GAP d d := AdaptedHNF.centeredBasisGAP b radius
  have hHpos : 0 < H := by
    simp [H, AdaptedHNF.inverseCoefficientConstantNat]
  have hradiusLower (i : Fin d) : Q.minWidth - 1 ≤ radius i := by
    have hmin : Q.minWidth - 1 ≤ Q.widths (σ i) - 1 :=
      Nat.sub_le_sub_right (Q.minWidth_le hd (σ i)) 1
    calc
      Q.minWidth - 1 ≤ Q.widths (σ i) - 1 := hmin
      _ = 1 * (Q.widths (σ i) - 1) := by simp
      _ ≤ H * (Q.widths (σ i) - 1) :=
        Nat.mul_le_mul_right _ hHpos
      _ = radius i := rfl
  have hcarrier : P.carrier = basisProgression b radius := by
    exact centeredBasisGAP_carrier_eq_basisProgression b radius
  have hQsym : Q.carrier ⊆ (symmetricAxisBox w).carrier := by
    simpa [w] using carrier_subset_symmetricAxisBox_width_sub_one Q hzeroQ
  have hbox : ∀ x ∈ Q.carrier, x ∈ Γ → x ∈ P.carrier := by
    intro x hxQ hxΓ
    rw [hcarrier]
    exact hreverse ⟨x, hxΓ⟩ (hQsym hxQ)
  have hPsim :
      P.carrier ⊆
        (symmetricAxisBox (fun i ↦ M * (Q.widths i - 1))).carrier := by
    rw [hcarrier]
    intro x hx
    have hx' := hforward hx
    simpa [radius, w, M, one, mul_assoc] using hx'
  have hgeom : P.carrier ⊆
      Elementary.translate
        (fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ))
        (Q.dilate ell).carrier :=
    hPsim.trans (symmetricAxisBox_subset_translate_dilate Q hMleEll)
  have htranslatedP :
      Elementary.translate
          (fun i ↦ ((M * (Q.widths i - 1) : ℕ) : ℤ)) P.carrier ⊆
        (Q.dilate k).carrier :=
    (Elementary.translate_mono hPsim).trans
      (translate_symmetricAxisBox_subset_dilate Q hk)
  have hcovered :
      Elementary.translate
          (t + fun i ↦ ((M * (Q.widths i - 1) : ℕ) : ℤ)) P.carrier ⊆
        iteratedSumset (fun _ ↦ B) ell := by
    rw [← Elementary.translate_translate]
    exact (Elementary.translate_mono htranslatedP).trans ht
  have hcentered : P.Centered radius := by
    exact ⟨rfl, rfl⟩
  have hproper : P.Proper := by
    exact AdaptedHNF.centeredBasisGAP_proper b radius
  have hzeroP : (0 : BoxPoint d) ∈ P.carrier :=
    hcentered.zero_mem_carrier
  have hPΓ : (P.carrier : Set (BoxPoint d)) ⊆ Γ := by
    intro x hx
    rw [hcarrier] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact (∑ i, a i • b i : Γ).property
  have hBP : (B : Set (BoxPoint d)) ⊆ P.carrier := by
    intro x hx
    exact hbox x (hBQ hx) (subset_generatedSublattice B hx)
  have hgenerated : generatedSublattice P.carrier = Γ := by
    apply le_antisymm
    · exact (AddSubgroup.closure_le Γ).2 hPΓ
    · exact AddSubgroup.closure_mono hBP
  have hoffset : P.offset ∈ Γ := by
    let y : Γ := -∑ i, (radius i : ℤ) • b i
    have hy : ((y : Γ) : BoxPoint d) = P.offset := by
      funext j
      simp [y, P, AdaptedHNF.centeredBasisGAP]
    rw [← hy]
    exact y.property
  have hsteps (i : Fin d) : P.steps i ∈ Γ := by
    simpa [P, AdaptedHNF.centeredBasisGAP] using (b i).property
  exact ⟨{
    constant := ell
    constant_pos := hellpos
    sigma := σ
    basis := b
    radius := radius
    radius_lower := hradiusLower
    progression := P
    progression_eq := rfl
    centered := hcentered
    proper := hproper
    zero_mem := hzeroP
    box_lattice_subset := hbox
    geometricTranslate :=
      fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ)
    geometric_bound := hgeom
    sumTranslate :=
      t + fun i ↦ ((M * (Q.widths i - 1) : ℕ) : ℤ)
    sum_covered := hcovered
    generated_carrier_eq := hgenerated
    offset_mem_generated := hoffset
    steps_mem_generated := hsteps }⟩

/-- The fixed block length used in Corollary 2.17 satisfies Lev's numerical
threshold once every side of the box is sufficiently long. -/
theorem corollary217_lev_large {d cDen M R : ℕ} (hcDen : 0 < cDen)
    (hMR : 0 < M + R) (Q : AxisBox d)
    (hwidth : ∀ i, 24 * cDen * cDen ≤ Q.widths i) (i : Fin d) :
    2 * (((Q.widths i - 1) - 1 +
        (Q.widths i / (2 * cDen) - 2) - 1) /
      (Q.widths i / (2 * cDen) - 2)) ≤
        16 * cDen * (M + R) := by
  let W := Q.widths i
  let b := W / (2 * cDen)
  have hwide : 24 * cDen * cDen ≤ W := by simpa [W] using hwidth i
  have hb12 : 12 * cDen ≤ b := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
    convert hwide using 1 <;> ring
  have hbpos : 0 < b - 2 := by omega
  have hwlt : W < (2 * cDen) * (b + 1) := by
    simpa [b] using Nat.lt_mul_div_succ W
      (by positivity : 0 < 2 * cDen)
  have hnum : (W - 1) - 1 + (b - 2) - 1 ≤
      4 * cDen * (b - 2) := by
    have hc' : 1 ≤ cDen := hcDen
    have hb2 : 2 ≤ b := by omega
    have hbEq : b = (b - 2) + 2 := by omega
    have hnle : (W - 1) - 1 + (b - 2) - 1 ≤ W + b := by omega
    have hpoly : W + b ≤ 4 * cDen * (b - 2) := by nlinarith
    exact hnle.trans hpoly
  have hdiv : ((W - 1) - 1 + (b - 2) - 1) / (b - 2) ≤
      4 * cDen := by
    apply (Nat.div_le_iff_le_mul hbpos).2
    omega
  have hsmall :
      2 * (((W - 1) - 1 + (b - 2) - 1) / (b - 2)) ≤
        8 * cDen := by
    calc
      2 * (((W - 1) - 1 + (b - 2) - 1) / (b - 2)) ≤
          2 * (4 * cDen) := Nat.mul_le_mul_left 2 hdiv
      _ = 8 * cDen := by ring
  have h8L : 8 * cDen ≤ 16 * cDen * (M + R) := by
    calc
      8 * cDen ≤ 16 * cDen := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (16 * cDen) * (M + R) := Nat.le_mul_of_pos_right _ hMR
  simpa [W, b] using hsmall.trans h8L

/-- The fixed block length leaves enough space on either side of the
centered progression and its bounded residue representative. -/
theorem corollary217_grid_margin {d cDen M R : ℕ} (hcDen : 0 < cDen)
    (Q : AxisBox d) (hwidth : ∀ i, 8 * cDen ≤ Q.widths i) (i : Fin d) :
    (M + R) * (Q.widths i - 1) ≤
      (16 * cDen * (M + R) *
        (Q.widths i / (2 * cDen) - 1)) / 2 := by
  let W := Q.widths i
  let q := W / (2 * cDen)
  have hq4 : 4 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
    convert hwidth i using 1 <;> ring
  have hwlt : W < (2 * cDen) * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ W
      (by positivity : 0 < 2 * cDen)
  have hfactor : q + 1 ≤ 2 * (q - 1) := by omega
  have hW : W - 1 ≤ 4 * cDen * (q - 1) := by
    have hlt : W < 4 * cDen * (q - 1) := by
      calc
        W < (2 * cDen) * (q + 1) := hwlt
        _ ≤ (2 * cDen) * (2 * (q - 1)) :=
          Nat.mul_le_mul_left _ hfactor
        _ = 4 * cDen * (q - 1) := by ring
    omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  calc
    (M + R) * (W - 1) * 2 ≤
        (M + R) * (4 * cDen * (q - 1)) * 2 :=
      Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left _ hW)
    _ ≤ (16 * cDen * (M + R)) * (q - 1) := by nlinarith
    _ = 16 * cDen * (M + R) * (W / (2 * cDen) - 1) := by simp [q]

/-- Uniformly bound the inverse adapted-basis loss when all rectangular
periods are at most `V`. -/
theorem inverseCoefficientConstantNat_le_uniform {d V : ℕ}
    (v : Fin d → ℕ) (hv : ∀ i, v i ≤ V) (σ : Equiv.Perm (Fin d)) :
    AdaptedHNF.inverseCoefficientConstantNat d (v ∘ σ) ≤
      (1 + d * (d * V)) ^ d := by
  have hsumv : ∑ i, v (σ i) ≤ d * V := by
    calc
      ∑ i, v (σ i) ≤ ∑ _i : Fin d, V :=
        Finset.sum_le_sum fun i _ ↦ hv (σ i)
      _ = d * V := by simp
  dsimp [AdaptedHNF.inverseCoefficientConstantNat]
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_left (Nat.mul_le_mul_left d hsumv) 1

/-
/-- CFP Corollary 2.17(1), with a single uniform constant chosen before the
box and the dense set.  No reducedness assumption is present: the missing
residue classes are supplied by the finite quotient of the generated
lattice by the rectangular lattice produced by the coordinate blocks. -/
theorem exists_corollary217Certificate
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ C widthThreshold : ℕ, 0 < C ∧
      ∀ (Q : AxisBox d) (B : Finset (BoxPoint d)),
        widthThreshold ≤ Q.minWidth →
        (0 : BoxPoint d) ∈ B →
        B ⊆ Q.carrier →
        cNum * Q.volume ≤ cDen * B.card →
        ∃ cert : Corollary217Certificate Q B, cert.constant = C := by
  classical
  have hcDen : 0 < cDen := lt_of_lt_of_le hcNum hc
  let V := 4 * cDen
  let R := V ^ d
  let Hmax := (1 + d * (d * V)) ^ d
  let M := Hmax * d * V
  let L := 16 * cDen * (M + R)
  let ellGrid := d * (V * L)
  let C := ellGrid + R + 2 * M + 1
  let widthThreshold := 24 * cDen * cDen
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hHmaxpos : 0 < Hmax := by dsimp [Hmax]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hsumpos : 0 < M + R := Nat.add_pos_left hMpos _
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.mul_pos (by positivity) hsumpos
  have hCpos : 0 < C := by dsimp [C]; omega
  refine ⟨C, widthThreshold, hCpos, ?_⟩
  intro Q B hwidthMin hzeroB hBQ hdensity
  have hzeroQ : (0 : BoxPoint d) ∈ Q.carrier := hBQ hzeroB
  have hwidth (i : Fin d) : 8 * cDen ≤ Q.widths i := by
    have hwide : widthThreshold ≤ Q.widths i :=
      hwidthMin.trans (Q.minWidth_le hd i)
    dsimp [widthThreshold] at hwide
    nlinarith
  have hLevLarge (i : Fin d) :
      2 * (((Q.widths i - 1) - 1 +
          (Q.widths i / (2 * cDen) - 2) - 1) /
        (Q.widths i / (2 * cDen) - 2)) ≤ L := by
    simpa [L] using corollary217_lev_large hcDen hsumpos Q
      (fun j ↦ by simpa [widthThreshold] using
        hwidthMin.trans (Q.minWidth_le hd j)) i
  let family : Fin ellGrid → Finset (BoxPoint d) := fun _ ↦ B
  obtain ⟨grid⟩ := exists_denseGridCertificate_of_numerics Q family
    cNum cDen hcNum hcDen (V := V) (L := L)
    (fun _ ↦ hBQ) (fun _ ↦ hdensity) rfl (by simp [ellGrid])
    hwidth (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hLpos)) hLevLarge
  have hgridSum : heterogeneousSumset family =
      iteratedSumset (fun _ ↦ B) ellGrid := by
    rw [heterogeneousSumset, List.sum_ofFn, iteratedSumset,
      ← Fin.sum_univ_eq_sum_range]
  rw [hgridSum] at grid.grid_subset
  have hlength (i : Fin d) : 1 ≤ grid.lengths i := by
    have hb4 : 4 ≤ Q.widths i / (2 * cDen) := by
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
      convert hwidth i using 1 <;> ring
    rw [show grid.lengths i =
        L * (Q.widths i / (2 * cDen) - 1) by rfl]
    positivity
  let Gamma := generatedSublattice B
  have hrect : rectangularSubgroup grid.periods ≤ Gamma :=
    rectangularSubgroup_le_generated_of_grid_subset_iteratedSumset
      B ellGrid grid.periods grid.lengths hlength grid.translate
        grid.grid_subset
  let r := (rectangularSubgroup grid.periods).relIndex Gamma
  obtain ⟨hrprod, hres⟩ :=
    rectangularResidueCompleteOn_generated_iteratedSumset
      grid.periods grid.period_pos B hzeroB hrect
  have hprodR : (∏ i, grid.periods i) ≤ R := by
    calc
      (∏ i, grid.periods i) ≤ ∏ _i : Fin d, V :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun i _ ↦ grid.period_le i)
      _ = V ^ d := by simp
      _ = R := rfl
  have hrR : r ≤ R := hrprod.trans hprodR
  let w : Fin d → ℕ := fun i ↦ Q.widths i - 1
  obtain ⟨σ, b, H, hH, hreverse, hforward⟩ :=
    exists_basisProgression_sandwich_symmetricBox
      grid.periods w grid.period_pos Gamma hrect
  have hHle : H ≤ Hmax := by
    rw [hH]
    simpa [Hmax] using inverseCoefficientConstantNat_le_uniform
      grid.periods grid.period_le σ
  let radius : Fin d → ℕ := fun i ↦ H * w (σ i)
  let P : GAP d d := AdaptedHNF.centeredBasisGAP b radius
  have hcarrier : P.carrier = basisProgression b radius :=
    centeredBasisGAP_carrier_eq_basisProgression b radius
  have hQsym : Q.carrier ⊆ (symmetricAxisBox w).carrier := by
    simpa [w] using carrier_subset_symmetricAxisBox_width_sub_one Q hzeroQ
  have hbox : ∀ x ∈ Q.carrier, x ∈ Gamma → x ∈ P.carrier := by
    intro x hxQ hxGamma
    rw [hcarrier]
    exact hreverse ⟨x, hxGamma⟩ (hQsym hxQ)
  have hPsim : P.carrier ⊆
      (symmetricAxisBox (fun i ↦ M * w i)).carrier := by
    rw [hcarrier]
    intro x hx
    have hx' := mem_symmetricAxisBox_iff.mp (hforward hx)
    rw [mem_symmetricAxisBox_iff]
    intro i
    apply (hx' i).trans
    exact_mod_cast Nat.mul_le_mul_right (w i)
      (Nat.mul_le_mul (Nat.mul_le_mul hHle (Nat.le_refl d))
        (grid.period_le i))
  have hBbound : ∀ j < r, ∀ x ∈ (fun _ : ℕ ↦ B) j, ∀ i,
      -((w i : ℕ) : ℤ) ≤ x i ∧ x i ≤ (w i : ℤ) := by
    intro _j _hj x hx i
    exact abs_le.mp ((mem_symmetricAxisBox_iff.mp (hQsym (hBQ hx))) i)
  have hRbound0 : CoordinateBound
      (iteratedSumset (fun _ ↦ B) r) (fun i ↦ r * w i) :=
    coordinateBound_iteratedSumset (fun _ ↦ B) w hBbound
  have hRbound : CoordinateBound
      (iteratedSumset (fun _ ↦ B) r) (fun i ↦ R * w i) := by
    exact hRbound0.mono (fun i ↦ Nat.mul_le_mul_right (w i) hrR)
  have hPbound : CoordinateBound P.carrier (fun i ↦ M * w i) := by
    intro x hx i
    exact abs_le.mp ((mem_symmetricAxisBox_iff.mp (hPsim hx)) i)
  have hmargin (i : Fin d) :
      (M + R) * w i ≤ grid.lengths i / 2 := by
    rw [show grid.lengths i =
      L * (Q.widths i / (2 * cDen) - 1) by rfl]
    simpa [w, L] using corollary217_grid_margin hcDen Q hwidth i
  have hleft (i : Fin d) :
      M * w i + R * w i ≤
        grid.periods i * (grid.lengths i / 2) := by
    calc
      M * w i + R * w i = (M + R) * w i := by ring
      _ ≤ grid.lengths i / 2 := hmargin i
      _ ≤ grid.periods i * (grid.lengths i / 2) :=
        Nat.le_mul_of_pos_left _ (grid.period_pos i)
  have hright (i : Fin d) :
      grid.periods i * (grid.lengths i / 2) + M * w i + R * w i ≤
        grid.periods i * grid.lengths i := by
    have htail := hleft i
    calc
      grid.periods i * (grid.lengths i / 2) + M * w i + R * w i =
          grid.periods i * (grid.lengths i / 2) +
            (M * w i + R * w i) := by omega
      _ ≤ grid.periods i * (grid.lengths i / 2) +
          grid.periods i * (grid.lengths i / 2) := Nat.add_le_add_left htail _
      _ = grid.periods i * (2 * (grid.lengths i / 2)) := by ring
      _ ≤ grid.periods i * grid.lengths i :=
        Nat.mul_le_mul_left _ (by omega)
  have hPGamma : (P.carrier : Set (BoxPoint d)) ⊆ Gamma := by
    intro x hx
    rw [hcarrier] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact (∑ i, a i • b i : Gamma).property
  obtain ⟨shift, hcovered0⟩ := grid_add_residues_contains_lattice_set
    Gamma grid.periods grid.lengths (fun i ↦ M * w i)
      (fun i ↦ R * w i) grid.period_pos hrect hleft hright
      grid.translate grid.grid_subset hres hRbound hPGamma hPbound
  have hcoveredShort : Elementary.translate shift P.carrier ⊆
      iteratedSumset (fun _ ↦ B) (ellGrid + r) := by
    rw [iteratedSumset_const_add, ← elementary_sumset_eq_pointwise_add]
    exact hcovered0
  have hshortC : ellGrid + r ≤ C := by dsimp [C]; omega
  have hcovered : Elementary.translate shift P.carrier ⊆
      iteratedSumset (fun _ ↦ B) C :=
    hcoveredShort.trans
      (iteratedSumset_const_mono_index B hzeroB hshortC)
  have h2MC : 2 * M ≤ C := by dsimp [C]; omega
  have hgeom : P.carrier ⊆
      Elementary.translate
        (fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ))
        (Q.dilate C).carrier := by
    exact hPsim.trans (by simpa [w] using
      symmetricAxisBox_subset_translate_dilate Q h2MC)
  have hcentered : P.Centered radius := ⟨rfl, rfl⟩
  have hproper : P.Proper := AdaptedHNF.centeredBasisGAP_proper b radius
  have hzeroP : (0 : BoxPoint d) ∈ P.carrier := hcentered.zero_mem_carrier
  have hBP : (B : Set (BoxPoint d)) ⊆ P.carrier := by
    intro x hx
    exact hbox x (hBQ hx) (subset_generatedSublattice B hx)
  have hgenerated : generatedSublattice P.carrier = Gamma := by
    apply le_antisymm
    · exact (AddSubgroup.closure_le Gamma).2 hPGamma
    · exact AddSubgroup.closure_mono hBP
  have hoffset : P.offset ∈ Gamma := by
    let y : Gamma := -∑ i, (radius i : ℤ) • b i
    have hy : ((y : Gamma) : BoxPoint d) = P.offset := by
      funext j
      simp [y, P, AdaptedHNF.centeredBasisGAP]
    rw [← hy]
    exact y.property
  have hsteps (i : Fin d) : P.steps i ∈ Gamma := by
    simpa [P, AdaptedHNF.centeredBasisGAP] using (b i).property
  refine ⟨{
    constant := C
    constant_pos := hCpos
    sigma := σ
    basis := b
    radius := radius
    progression := P
    progression_eq := rfl
    centered := hcentered
    proper := hproper
    zero_mem := hzeroP
    box_lattice_subset := hbox
    geometricTranslate :=
      fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ)
    geometric_bound := hgeom
    sumTranslate := shift
    sum_covered := hcovered
    generated_carrier_eq := hgenerated
    offset_mem_generated := hoffset
    steps_mem_generated := hsteps }, rfl⟩
-/

end

end Erdos186.CFP
