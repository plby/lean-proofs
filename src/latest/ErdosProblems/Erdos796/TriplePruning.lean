import ErdosProblems.Erdos796.AdmissibleTriples
import ErdosProblems.Erdos796.BoxPruning
import ErdosProblems.Erdos796.DyadicBoxes
import ErdosProblems.Erdos796.PruningArithmetic
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The three-large-factor pruning step

For every element of an admissible set which has three factors above `Y`, we
choose one such factorization.  Multiplication recovers the original element,
so the chosen triple parametrization is injective.  We then partition these
triples by dyadic scale.  The boxes used for the complete-box estimate are the
full intervals `[2^k,2^(k+1))`, whose cardinalities are exactly `2^k`.
-/

namespace Erdos796

namespace TriplePruning

open scoped BigOperators
open PruningArithmetic AdmissibleTriples DyadicBoxes

/-- Elements of `A` exhibiting the three-large-factor obstruction. -/
noncomputable def badElements (Y : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter (HasThreeLargeFactors Y)

@[simp] theorem mem_badElements {Y a : ℕ} {A : Finset ℕ} :
    a ∈ badElements Y A ↔ a ∈ A ∧ HasThreeLargeFactors Y a := by
  classical
  simp [badElements]

theorem badElements_subset (Y : ℕ) (A : Finset ℕ) :
    badElements Y A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

/-- A canonical chosen witness, with a harmless fallback off the bad set. -/
noncomputable def chosenTriple (Y a : ℕ) : ℕ × ℕ × ℕ := by
  classical
  exact if h : HasThreeLargeFactors Y a then
    (Classical.choose h,
      Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec h)))
  else (0, 0, 0)

theorem chosenTriple_spec {Y a : ℕ} (h : HasThreeLargeFactors Y a) :
    Y < (chosenTriple Y a).1 ∧
      Y < (chosenTriple Y a).2.1 ∧
      Y < (chosenTriple Y a).2.2 ∧
      a = tripleProduct (chosenTriple Y a) := by
  classical
  simpa [chosenTriple, dif_pos h, tripleProduct] using!
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h)))

/-- Chosen factor triples for all bad elements. -/
noncomputable def chosenTriples (Y : ℕ) (A : Finset ℕ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (badElements Y A).image (chosenTriple Y)

@[simp] theorem mem_chosenTriples {Y : ℕ} {A : Finset ℕ}
    {p : ℕ × ℕ × ℕ} :
    p ∈ chosenTriples Y A ↔
      ∃ a ∈ badElements Y A, chosenTriple Y a = p := by
  classical
  simp [chosenTriples]

theorem tripleProduct_chosenTriple {Y a : ℕ}
    (h : HasThreeLargeFactors Y a) :
    tripleProduct (chosenTriple Y a) = a :=
  (chosenTriple_spec h).2.2.2.symm

/-- The chosen triple map is injective on the bad elements. -/
theorem chosenTriple_injective_on {Y : ℕ} {A : Finset ℕ} :
    Set.InjOn (chosenTriple Y) (badElements Y A : Set ℕ) := by
  intro a ha b hb hab
  have haBad := (mem_badElements.mp ha).2
  have hbBad := (mem_badElements.mp hb).2
  calc
    a = tripleProduct (chosenTriple Y a) := (chosenTriple_spec haBad).2.2.2
    _ = tripleProduct (chosenTriple Y b) := congrArg tripleProduct hab
    _ = b := tripleProduct_chosenTriple hbBad

@[simp] theorem card_chosenTriples (Y : ℕ) (A : Finset ℕ) :
    (chosenTriples Y A).card = (badElements Y A).card := by
  classical
  rw [chosenTriples, Finset.card_image_iff]
  exact chosenTriple_injective_on

/-- Multiplication is injective on the chosen triple family. -/
theorem chosenTriples_productInjective (Y : ℕ) (A : Finset ℕ) :
    TripleProductInjective (chosenTriples Y A) := by
  intro p hp q hq hpq
  rcases mem_chosenTriples.mp hp with ⟨a, ha, rfl⟩
  rcases mem_chosenTriples.mp hq with ⟨b, hb, rfl⟩
  have haBad := (mem_badElements.mp ha).2
  have hbBad := (mem_badElements.mp hb).2
  have hab : a = b := by
    rw [tripleProduct_chosenTriple haBad,
      tripleProduct_chosenTriple hbBad] at hpq
    exact hpq
  subst b
  rfl

/-- Every chosen product is an element of the original set. -/
theorem chosenTriples_productsIn (Y : ℕ) (A : Finset ℕ) :
    TripleProductsIn (chosenTriples Y A) A := by
  intro p hp
  rcases mem_chosenTriples.mp hp with ⟨a, ha, rfl⟩
  rw [tripleProduct_chosenTriple (mem_badElements.mp ha).2]
  exact (mem_badElements.mp ha).1

/-- Every chosen coordinate is strictly larger than `Y`. -/
theorem chosenTriples_coordinates_gt {Y : ℕ} {A : Finset ℕ}
    {p : ℕ × ℕ × ℕ} (hp : p ∈ chosenTriples Y A) :
    Y < p.1 ∧ Y < p.2.1 ∧ Y < p.2.2 := by
  rcases mem_chosenTriples.mp hp with ⟨a, ha, rfl⟩
  have hs := chosenTriple_spec (mem_badElements.mp ha).2
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- A positive factor of a positive triple product is at most that product. -/
theorem coordinate_le_tripleProduct
    {p : ℕ × ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2) :
    p.1 ≤ tripleProduct p ∧ p.2.1 ≤ tripleProduct p ∧
      p.2.2 ≤ tripleProduct p := by
  dsimp [tripleProduct]
  constructor
  · simpa [Nat.mul_assoc] using!
      Nat.le_mul_of_pos_right p.1 (Nat.mul_pos hp.2.1 hp.2.2)
  constructor
  · calc
      p.2.1 ≤ p.1 * p.2.1 := Nat.le_mul_of_pos_left _ hp.1
      _ ≤ p.1 * p.2.1 * p.2.2 :=
        Nat.le_mul_of_pos_right _ hp.2.2
  · calc
      p.2.2 ≤ p.2.1 * p.2.2 := Nat.le_mul_of_pos_left _ hp.2.1
      _ ≤ p.1 * (p.2.1 * p.2.2) :=
        Nat.le_mul_of_pos_left _ hp.1
      _ = p.1 * p.2.1 * p.2.2 := by ring

/-- For an admissible `A ⊆ [n]`, all chosen factors lie in `[1,n]`. -/
theorem chosenTriples_subset_ambient
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    chosenTriples Y A ⊆ tripleAmbient n := by
  intro p hp
  have hgt := chosenTriples_coordinates_gt hp
  have hpos : 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by omega
  have hleProd := coordinate_le_tripleProduct hpos
  have hprodA := chosenTriples_productsIn Y A p hp
  have hprodN := (mem_positiveIcc.mp (hA.1 hprodA)).2
  exact mem_tripleAmbient.mpr
    ⟨mem_positiveIcc.mpr ⟨hpos.1, hleProd.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.1, hleProd.2.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.2, hleProd.2.2.trans hprodN⟩⟩

/-! ## Full dyadic boxes -/

/-- The untruncated interval `[2^k,2^(k+1))`. -/
def fullScaleInterval (k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ k) (2 ^ (k + 1))

@[simp] theorem mem_fullScaleInterval {k x : ℕ} :
    x ∈ fullScaleInterval k ↔ 2 ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  simp [fullScaleInterval]

@[simp] theorem card_fullScaleInterval (k : ℕ) :
    (fullScaleInterval k).card = 2 ^ k := by
  rw [fullScaleInterval, Nat.card_Ico, pow_succ]
  omega

/-- Full Cartesian box at a triple of dyadic scales. -/
def fullTripleBox (ijk : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  fullScaleInterval ijk.1 ×ˢ
    (fullScaleInterval ijk.2.1 ×ˢ fullScaleInterval ijk.2.2)

@[simp] theorem mem_fullTripleBox {ijk : ℕ × ℕ × ℕ}
    {p : ℕ × ℕ × ℕ} :
    p ∈ fullTripleBox ijk ↔
      p.1 ∈ fullScaleInterval ijk.1 ∧
      p.2.1 ∈ fullScaleInterval ijk.2.1 ∧
      p.2.2 ∈ fullScaleInterval ijk.2.2 := by
  simp [fullTripleBox, and_assoc]

@[simp] theorem card_fullTripleBox (ijk : ℕ × ℕ × ℕ) :
    (fullTripleBox ijk).card =
      2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) := by
  simp [fullTripleBox]

/-- Every scale fibre is supported in the corresponding full box. -/
theorem tripleBoxPart_subset_fullTripleBox
    {n : ℕ} {H : Finset (ℕ × ℕ × ℕ)}
    (hH : H ⊆ tripleAmbient n) (ijk : ℕ × ℕ × ℕ) :
    tripleBoxPart n H ijk ⊆ fullTripleBox ijk := by
  intro p hp
  have hpbox := tripleBoxPart_subset_tripleBox hH ijk hp
  have hpbox' := mem_tripleBox.mp hpbox
  exact mem_fullTripleBox.mpr
    ⟨by simpa [fullScaleInterval] using!
        scaleInterval_subset_Ico n ijk.1 hpbox'.1,
      by simpa [fullScaleInterval] using!
        scaleInterval_subset_Ico n ijk.2.1 hpbox'.2.1,
      by simpa [fullScaleInterval] using!
        scaleInterval_subset_Ico n ijk.2.2 hpbox'.2.2⟩

/-- Exact side cardinalities make the complete-box theorem applicable to
every nonempty scale fibre. -/
theorem chosenBox_completeBox_bound
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {ijk : ℕ × ℕ × ℕ} :
    ((tripleBoxPart n (chosenTriples Y A) ijk).card : ℝ) ≤
      (4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ)) /
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) := by
  let H := tripleBoxPart n (chosenTriples Y A) ijk
  have hsub : H ⊆
      fullScaleInterval ijk.1 ×ˢ
        (fullScaleInterval ijk.2.1 ×ˢ fullScaleInterval ijk.2.2) :=
    tripleBoxPart_subset_fullTripleBox (chosenTriples_subset_ambient hA) ijk
  have hinj : TripleProductInjective H := by
    intro p hp q hq heq
    exact chosenTriples_productInjective Y A
      (tripleBoxPart_subset n (chosenTriples Y A) ijk hp)
      (tripleBoxPart_subset n (chosenTriples Y A) ijk hq) heq
  have hproducts : TripleProductsIn H A := by
    intro p hp
    exact chosenTriples_productsIn Y A p
      (tripleBoxPart_subset n (chosenTriples Y A) ijk hp)
  simpa only [H, card_fullScaleInterval, Nat.cast_pow, Nat.cast_ofNat] using!
    card_le_completeBox hA hinj hproducts
      (fullScaleInterval ijk.1) (fullScaleInterval ijk.2.1)
      (fullScaleInterval ijk.2.2) hsub (by simp) (by simp) (by simp)

/-- The chosen triples split exactly over at most `(log₂ n+1)^3` active
full boxes. -/
theorem card_chosenTriples_eq_sum_activeBoxes
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (chosenTriples Y A).card =
      ∑ ijk ∈ activeTripleBoxIndices n (chosenTriples Y A),
        (tripleBoxPart n (chosenTriples Y A) ijk).card :=
  card_eq_sum_card_activeTripleBoxParts (chosenTriples_subset_ambient hA)

theorem card_active_chosenBoxes_le
    {n Y : ℕ} {A : Finset ℕ} :
    (activeTripleBoxIndices n (chosenTriples Y A)).card ≤
      (Nat.log 2 n + 1) ^ 3 :=
  card_activeTripleBoxIndices_le n (chosenTriples Y A)

/-- A nonempty chosen box has all three side lengths at least `Y / 2`,
while the product of its side lengths is at most `n`. -/
theorem activeChosenBox_scaleBounds
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈ activeTripleBoxIndices n (chosenTriples Y A)) :
    (Y : ℝ) / 2 ≤
        (Nat.min (2 ^ ijk.1)
          (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) ∧
      (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ (n : ℝ) := by
  rcases (mem_activeTripleBoxIndices.mp hijk).2 with ⟨p, hp⟩
  have hpChosen : p ∈ chosenTriples Y A :=
    tripleBoxPart_subset n (chosenTriples Y A) ijk hp
  have hgt := chosenTriples_coordinates_gt hpChosen
  have hpFull := tripleBoxPart_subset_fullTripleBox
    (chosenTriples_subset_ambient hA) ijk hp
  have hb := mem_fullTripleBox.mp hpFull
  have hb1 := mem_fullScaleInterval.mp hb.1
  have hb2 := mem_fullScaleInterval.mp hb.2.1
  have hb3 := mem_fullScaleInterval.mp hb.2.2
  have hside1 : (Y : ℝ) / 2 ≤ (2 ^ ijk.1 : ℝ) := by
    have hNat : Y < 2 ^ (ijk.1 + 1) := hgt.1.trans hb1.2
    have hReal : (Y : ℝ) < ((2 ^ (ijk.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside2 : (Y : ℝ) / 2 ≤ (2 ^ ijk.2.1 : ℝ) := by
    have hNat : Y < 2 ^ (ijk.2.1 + 1) := hgt.2.1.trans hb2.2
    have hReal : (Y : ℝ) < ((2 ^ (ijk.2.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside3 : (Y : ℝ) / 2 ≤ (2 ^ ijk.2.2 : ℝ) := by
    have hNat : Y < 2 ^ (ijk.2.2 + 1) := hgt.2.2.trans hb3.2
    have hReal : (Y : ℝ) < ((2 ^ (ijk.2.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  constructor
  · rw [Nat.cast_min, Nat.cast_min, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_pow]
    exact le_min hside1 (le_min hside2 hside3)
  · have hvolumeProduct :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          p.1 * (p.2.1 * p.2.2) :=
      Nat.mul_le_mul hb1.1 (Nat.mul_le_mul hb2.1 hb3.1)
    have hvolumeTriple :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          tripleProduct p := by
      simpa [tripleProduct, Nat.mul_assoc] using! hvolumeProduct
    have hproductN : tripleProduct p ≤ n := by
      have hproductA := chosenTriples_productsIn Y A p hpChosen
      exact (mem_positiveIcc.mp (hA.1 hproductA)).2
    have hvolumeN :
        (2 ^ ijk.1 * 2 ^ ijk.2.1) * 2 ^ ijk.2.2 ≤ n := by
      simpa [Nat.mul_assoc] using! hvolumeTriple.trans hproductN
    exact_mod_cast hvolumeN

/-- After imposing `Y ≥ 2`, every active box satisfies one common real
bound.  This is the estimate that can be summed over the active boxes. -/
theorem activeChosenBox_uniformBound
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) (hY : 2 ≤ Y)
    {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈ activeTripleBoxIndices n (chosenTriples Y A)) :
    ((tripleBoxPart n (chosenTriples Y A) ijk).card : ℝ) ≤
      (4 * (n : ℝ)) /
        Tripartite.realFourthRoot ((Y : ℝ) / 2) := by
  have hbox := chosenBox_completeBox_bound hA (Y := Y) (ijk := ijk)
  have hscale := activeChosenBox_scaleBounds hA hijk
  have hhalf : (1 : ℝ) ≤ (Y : ℝ) / 2 := by
    have hYReal : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    linarith
  have hrootPos :
      0 < Tripartite.realFourthRoot ((Y : ℝ) / 2) :=
    Tripartite.realFourthRoot_pos_of_one_le hhalf
  have hrootMono :
      Tripartite.realFourthRoot ((Y : ℝ) / 2) ≤
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) :=
    Tripartite.realFourthRoot_mono hscale.1
  have hnumerator :
      4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ 4 * (n : ℝ) := by
    linarith
  exact hbox.trans
    (div_le_div₀ (by positivity) hnumerator hrootPos hrootMono)

/-- Summed first-pruning estimate.  There are at most
`(Nat.log 2 n + 1)^3` active scale boxes, and each contributes at most the
uniform bound above. -/
theorem card_badElements_le_dyadicPruning
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) (hY : 2 ≤ Y) :
    ((badElements Y A).card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((Y : ℝ) / 2)) := by
  let I := activeTripleBoxIndices n (chosenTriples Y A)
  let H := tripleBoxPart n (chosenTriples Y A)
  let C : ℝ :=
    (4 * (n : ℝ)) / Tripartite.realFourthRoot ((Y : ℝ) / 2)
  have huniform : ∀ ijk ∈ I, ((H ijk).card : ℝ) ≤ C := by
    intro ijk hijk
    exact activeChosenBox_uniformBound hA hY hijk
  have hunion := BoxPruning.card_biUnion_le_card_mul_of_uniform
    I H C huniform
  have hcover : I.biUnion H = chosenTriples Y A := by
    simpa [I, H] using!
      (biUnion_activeTripleBoxParts (chosenTriples_subset_ambient hA))
  rw [hcover, card_chosenTriples] at hunion
  have hcard : (I.card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast card_active_chosenBoxes_le (n := n) (Y := Y) (A := A)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (by positivity)
      (Tripartite.realFourthRoot_nonneg _)
  calc
    ((badElements Y A).card : ℝ) ≤ (I.card : ℝ) * C := hunion
    _ ≤ (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) * C :=
      mul_le_mul_of_nonneg_right hcard hC
    _ = (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((Y : ℝ) / 2)) := rfl

end TriplePruning

end Erdos796
