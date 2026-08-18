import ErdosProblems.Erdos140.Counting
import Mathlib.Algebra.Group.Translate
import Mathlib.Combinatorics.Additive.Convolution
import Mathlib.Data.Real.Basic

/-!
# Normalized convolution on a finite additive group

The normalizations here are probability normalizations: `normalizedIndicator A`
has value `1 / |A|` on `A`, and convolution is defined using an ordinary
(unnormalized) finite sum.  Thus every nonempty normalized indicator, and the
convolution of two such indicators, has total mass one.
-/

open Finset Function
open scoped BigOperators translate

namespace Erdos140

noncomputable section

section Definitions

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The probability-normalized indicator of a finite set.  It is identically
zero when the set is empty. -/
def normalizedIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (#A : ℝ)⁻¹ else 0

/-- Convolution with counting measure on a finite additive group. -/
def normalizedConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

/-- Difference convolution with counting measure.  At `x` it correlates `f`
with the translate `y ↦ g (y - x)`. -/
def normalizedDifferenceConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (y - x)

/-- The counting-measure inner product of two real functions on a finite group. -/
def finiteInner (f g : G → ℝ) : ℝ :=
  ∑ x : G, f x * g x

@[simp]
theorem normalizedIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    normalizedIndicator A x = (#A : ℝ)⁻¹ := by
  simp [normalizedIndicator, hx]

@[simp]
theorem normalizedIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    normalizedIndicator A x = 0 := by
  simp [normalizedIndicator, hx]

theorem normalizedIndicator_nonneg (A : Finset G) (x : G) :
    0 ≤ normalizedIndicator A x := by
  unfold normalizedIndicator
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl

theorem normalizedIndicator_pos_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    0 < normalizedIndicator A x ↔ x ∈ A := by
  unfold normalizedIndicator
  split_ifs with hx
  · simp only [hx, iff_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr hA.card_pos)
  · simp [hx]

theorem normalizedIndicator_ne_zero_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    normalizedIndicator A x ≠ 0 ↔ x ∈ A := by
  unfold normalizedIndicator
  split_ifs with hx
  · simp [hx, hA.card_ne_zero]
  · simp [hx]

theorem sum_normalizedIndicator {A : Finset G} (hA : A.Nonempty) :
    ∑ x : G, normalizedIndicator A x = 1 := by
  change (∑ x ∈ (univ : Finset G), if x ∈ A then (#A : ℝ)⁻¹ else 0) = 1
  rw [← Finset.sum_filter]
  have hfilter : univ.filter (fun x : G ↦ x ∈ A) = A := by ext; simp
  rw [hfilter]
  simp [hA.card_ne_zero]

theorem normalizedConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ normalizedConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (z - x))

theorem normalizedDifferenceConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ normalizedDifferenceConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (x - z))

/-- Convolution of normalized indicators is the normalized cardinality of a
representation fiber. -/
theorem normalizedConvolution_indicators_eq_card (A B : Finset G) (x : G) :
    normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (#(A.filter fun y ↦ x - y ∈ B) : ℝ) * (#A : ℝ)⁻¹ * (#B : ℝ)⁻¹ := by
  have hfilter : (univ.filter fun y : G ↦ x - y ∈ B) ∩ A =
      A.filter fun y ↦ x - y ∈ B := by
    ext y
    simp [and_comm]
  simp [normalizedConvolution, normalizedIndicator, ← Finset.sum_filter,
    mul_assoc, mul_left_comm, hfilter]

/-- The support of the convolution of two nonempty normalized indicators is
exactly the set of sums of one point from each input. -/
theorem normalizedConvolution_indicators_pos_iff {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (x : G) :
    0 < normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x ↔
      ∃ y ∈ A, x - y ∈ B := by
  rw [normalizedConvolution_indicators_eq_card]
  simp [hA.card_pos, hB.card_pos, Nat.cast_pos, inv_pos, Finset.card_pos]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩
  · rintro ⟨y, hyA, hyB⟩
    exact ⟨y, mem_filter.mpr ⟨hyA, hyB⟩⟩

/-- Difference convolution of normalized indicators is the normalized
cardinality of a difference-representation fiber. -/
theorem normalizedDifferenceConvolution_indicators_eq_card (A B : Finset G) (x : G) :
    normalizedDifferenceConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (#(A.filter fun y ↦ y - x ∈ B) : ℝ) * (#A : ℝ)⁻¹ * (#B : ℝ)⁻¹ := by
  have hfilter : (univ.filter fun y : G ↦ y - x ∈ B) ∩ A =
      A.filter fun y ↦ y - x ∈ B := by
    ext y
    simp [and_comm]
  simp [normalizedDifferenceConvolution, normalizedIndicator, ← Finset.sum_filter,
    mul_assoc, mul_left_comm, hfilter]

theorem normalizedDifferenceConvolution_indicators_pos_iff {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (x : G) :
    0 < normalizedDifferenceConvolution (normalizedIndicator A) (normalizedIndicator B) x ↔
      ∃ y ∈ A, y - x ∈ B := by
  rw [normalizedDifferenceConvolution_indicators_eq_card]
  simp [hA.card_pos, hB.card_pos, Nat.cast_pos, inv_pos, Finset.card_pos]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩
  · rintro ⟨y, hyA, hyB⟩
    exact ⟨y, mem_filter.mpr ⟨hyA, hyB⟩⟩

/-- A one-variable representation fiber is in bijection with the pairs counted
by Mathlib's additive convolution. -/
theorem card_filter_sub_mem_eq_addConvolution (A B : Finset G) (x : G) :
    #(A.filter fun y ↦ x - y ∈ B) = A.addConvolution B x := by
  unfold Finset.addConvolution
  refine Finset.card_nbij' (fun y ↦ (y, x - y)) (fun ab ↦ ab.1) ?_ ?_ ?_ ?_
  · intro y hy
    change y ∈ A.filter (fun y ↦ x - y ∈ B) at hy
    change (y, x - y) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x)
    rw [mem_filter] at hy ⊢
    exact ⟨mem_product.mpr hy, by simp⟩
  · rintro ⟨a, b⟩ hab
    change (a, b) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x) at hab
    change a ∈ A.filter (fun y ↦ x - y ∈ B)
    simp only [mem_filter, mem_product] at hab ⊢
    rcases hab with ⟨⟨ha, hb⟩, hsum⟩
    refine ⟨ha, ?_⟩
    have hxb : x - a = b := by
      rw [← hsum]
      simp [add_comm]
    simpa [hxb] using hb
  · intro y _
    rfl
  · rintro ⟨a, b⟩ hab
    change (a, b) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x) at hab
    simp only [mem_filter, mem_product] at hab
    rcases hab with ⟨-, hsum⟩
    have hxb : x - a = b := by
      rw [← hsum]
      simp [add_comm]
    simp [hxb]

theorem normalizedConvolution_indicators_eq_addConvolution (A B : Finset G) (x : G) :
    normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (A.addConvolution B x : ℝ) * (#A : ℝ)⁻¹ * (#B : ℝ)⁻¹ := by
  rw [normalizedConvolution_indicators_eq_card, card_filter_sub_mem_eq_addConvolution]

end Definitions

section Algebra

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Total mass is invariant under translation. -/
theorem sum_translate_real (a : G) (f : G → ℝ) :
    ∑ x : G, translate a f x = ∑ x : G, f x :=
  sum_translate a f

/-- Convolution is commutative on an additive commutative group. -/
theorem normalizedConvolution_comm (f g : G → ℝ) :
    normalizedConvolution f g = normalizedConvolution g f := by
  funext x
  rw [normalizedConvolution, normalizedConvolution]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ ?_
  simp [mul_comm]

/-- Translating the left input translates the convolution output. -/
theorem normalizedConvolution_translate_left (a : G) (f g : G → ℝ) :
    normalizedConvolution (translate a f) g = translate a (normalizedConvolution f g) := by
  funext x
  simp only [translate_apply]
  unfold normalizedConvolution
  refine Fintype.sum_equiv (Equiv.subRight a) _ _ fun y ↦ ?_
  simp only [Equiv.subRight_apply]
  congr 1
  apply congrArg g
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
  calc
    x + -y = (a + -a) + (x + -y) := by simp
    _ = x + -a + (a + -y) := by ac_rfl

/-- Translating the right input translates the convolution output. -/
theorem normalizedConvolution_translate_right (a : G) (f g : G → ℝ) :
    normalizedConvolution f (translate a g) = translate a (normalizedConvolution f g) := by
  calc
    normalizedConvolution f (translate a g) = normalizedConvolution (translate a g) f :=
      normalizedConvolution_comm _ _
    _ = translate a (normalizedConvolution g f) :=
      normalizedConvolution_translate_left _ _ _
    _ = translate a (normalizedConvolution f g) := by
      rw [normalizedConvolution_comm]

/-- Difference convolution is convolution against the reflected second input. -/
theorem normalizedDifferenceConvolution_eq_convolution (f g : G → ℝ) :
    ∀ x, normalizedDifferenceConvolution f g x =
      normalizedConvolution f (fun y ↦ g (-y)) x := by
  intro x
  simp [normalizedDifferenceConvolution, normalizedConvolution, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

/-- Difference convolution reverses its argument when its two inputs are swapped. -/
theorem normalizedDifferenceConvolution_swap (f g : G → ℝ) (x : G) :
    normalizedDifferenceConvolution f g x =
      normalizedDifferenceConvolution g f (-x) := by
  rw [normalizedDifferenceConvolution, normalizedDifferenceConvolution]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ ?_
  simp [mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The total mass of a convolution is the product of the two total masses. -/
theorem sum_normalizedConvolution (f g : G → ℝ) :
    ∑ x : G, normalizedConvolution f g x = (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [normalizedConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by simp

/-- The total mass of a difference convolution is likewise multiplicative. -/
theorem sum_normalizedDifferenceConvolution (f g : G → ℝ) :
    ∑ x : G, normalizedDifferenceConvolution f g x =
      (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [normalizedDifferenceConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft y) _ _ fun x ↦ by simp

theorem sum_convolution_normalizedIndicators {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∑ x : G, normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x = 1 := by
  rw [sum_normalizedConvolution, sum_normalizedIndicator hA, sum_normalizedIndicator hB, one_mul]

theorem sum_differenceConvolution_normalizedIndicators {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∑ x : G,
        normalizedDifferenceConvolution (normalizedIndicator A) (normalizedIndicator B) x = 1 := by
  rw [sum_normalizedDifferenceConvolution, sum_normalizedIndicator hA,
    sum_normalizedIndicator hB, one_mul]

end Algebra

section APCounting

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The number of ordered solutions `a₁ + a₂ = c + c` with both endpoints in
`A` and the middle term in `C`. -/
def mixedThreeAPCount (A C : Finset G) : ℕ :=
  #(((A ×ˢ A) ×ˢ C).filter fun x ↦ x.1.1 + x.1.2 = x.2 + x.2)

/-- The mixed count is the sum of endpoint representation counts over its
allowed middle terms. -/
theorem mixedThreeAPCount_eq_sum_addConvolution (A C : Finset G) :
    mixedThreeAPCount A C = ∑ c ∈ C, A.addConvolution A (c + c) := by
  unfold mixedThreeAPCount Finset.addConvolution
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  calc
    (∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ C, if a + b = c + c then 1 else 0) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ A, if a + b = c + c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ A, if a + b = c + c then 1 else 0 := by
      rw [Finset.sum_comm]

/-- Ordered three-term progressions can be counted by summing the additive
convolution fiber at `b+b` over all possible middle terms `b`. -/
theorem threeAPCount_eq_sum_addConvolution (A : Finset G) :
    threeAPCount A = ∑ b ∈ A, A.addConvolution A (b + b) := by
  unfold threeAPCount Finset.addConvolution
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  conv_lhs => rw [Finset.sum_comm]

/-- If doubling is injective, the normalized convolution/indicator inner
product is exactly the ordered three-term-progression count divided by `|A|³`. -/
theorem finiteInner_convolution_doubleIndicator {A : Finset G}
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    finiteInner (normalizedConvolution (normalizedIndicator A) (normalizedIndicator A))
        (normalizedIndicator (A.image fun x ↦ x + x)) =
      (threeAPCount A : ℝ) * (#A : ℝ)⁻¹ ^ 3 := by
  let D : Finset G := A.image fun x ↦ x + x
  have hcardD : #D = #A := by
    dsimp [D]
    exact card_image_of_injective _ hdouble
  have hrestrict (F : G → ℝ) :
      (∑ z : G, F z * normalizedIndicator D z) =
        ∑ z ∈ D, F z * (#D : ℝ)⁻¹ := by
    change (∑ z : G, F z * (if z ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun z : G ↦ z ∈ D) = D := by ext; simp
    rw [hfilter]
  have hsumNat : ∑ z ∈ D, A.addConvolution A z = threeAPCount A := by
    rw [threeAPCount_eq_sum_addConvolution]
    dsimp [D]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hdouble hab
  have hsumReal : ∑ z ∈ D, (A.addConvolution A z : ℝ) = (threeAPCount A : ℝ) := by
    exact_mod_cast hsumNat
  rw [finiteInner, hrestrict]
  simp_rw [normalizedConvolution_indicators_eq_addConvolution]
  rw [hcardD]
  calc
    (∑ z ∈ D,
        ((A.addConvolution A z : ℝ) * (#A : ℝ)⁻¹ * (#A : ℝ)⁻¹) * (#A : ℝ)⁻¹) =
        (∑ z ∈ D, (A.addConvolution A z : ℝ)) * (#A : ℝ)⁻¹ ^ 3 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z _
          simp only [pow_succ, pow_two]
          ac_rfl
    _ = (threeAPCount A : ℝ) * (#A : ℝ)⁻¹ ^ 3 := by
      rw [hsumReal]

/-- Mixed form of `finiteInner_convolution_doubleIndicator`: endpoints lie in
`A`, while the doubled middle term comes from `C`. -/
theorem finiteInner_convolution_mixedDoubleIndicator {A C : Finset G}
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    finiteInner (normalizedConvolution (normalizedIndicator A) (normalizedIndicator A))
        (normalizedIndicator (C.image fun x ↦ x + x)) =
      (mixedThreeAPCount A C : ℝ) * (#A : ℝ)⁻¹ ^ 2 * (#C : ℝ)⁻¹ := by
  let D : Finset G := C.image fun x ↦ x + x
  have hcardD : #D = #C := by
    dsimp [D]
    exact card_image_of_injective _ hdouble
  have hrestrict (F : G → ℝ) :
      (∑ z : G, F z * normalizedIndicator D z) =
        ∑ z ∈ D, F z * (#D : ℝ)⁻¹ := by
    change (∑ z : G, F z * (if z ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun z : G ↦ z ∈ D) = D := by ext; simp
    rw [hfilter]
  have hsumNat : ∑ z ∈ D, A.addConvolution A z = mixedThreeAPCount A C := by
    rw [mixedThreeAPCount_eq_sum_addConvolution]
    dsimp [D]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hdouble hab
  have hsumReal : ∑ z ∈ D, (A.addConvolution A z : ℝ) = (mixedThreeAPCount A C : ℝ) := by
    exact_mod_cast hsumNat
  rw [finiteInner, hrestrict]
  simp_rw [normalizedConvolution_indicators_eq_addConvolution]
  rw [hcardD]
  have hpoint (z : G) :
      ((A.addConvolution A z : ℝ) * (#A : ℝ)⁻¹ * (#A : ℝ)⁻¹) * (#C : ℝ)⁻¹ =
        (A.addConvolution A z : ℝ) *
          ((#A : ℝ)⁻¹ * (#A : ℝ)⁻¹ * (#C : ℝ)⁻¹) := by ac_rfl
  simp_rw [hpoint]
  rw [← Finset.sum_mul, hsumReal]
  simp only [pow_two]
  ac_rfl

/-- Restricting the endpoints and middle terms can only decrease the mixed
progression count. -/
theorem mixedThreeAPCount_mono {A A' C C' : Finset G}
    (hA : A' ⊆ A) (hC : C' ⊆ C) :
    mixedThreeAPCount A' C' ≤ mixedThreeAPCount A C := by
  unfold mixedThreeAPCount
  apply card_le_card
  intro x hx
  rcases x with ⟨⟨a, b⟩, c⟩
  simp only [mem_filter, mem_product] at hx ⊢
  exact ⟨⟨⟨hA hx.1.1.1, hA hx.1.1.2⟩, hC hx.1.2⟩, hx.2⟩

/-- The unmixed count agrees with `threeAPCount`. -/
theorem mixedThreeAPCount_self (A : Finset G) : mixedThreeAPCount A A = threeAPCount A := by
  rw [mixedThreeAPCount_eq_sum_addConvolution, threeAPCount_eq_sum_addConvolution]

/-- In particular, a mixed configuration inside one ambient set is bounded by
the ambient ordered AP count. -/
theorem mixedThreeAPCount_le_threeAPCount {A A' C : Finset G}
    (hA : A' ⊆ A) (hC : C ⊆ A) :
    mixedThreeAPCount A' C ≤ threeAPCount A := by
  rw [← mixedThreeAPCount_self A]
  exact mixedThreeAPCount_mono hA hC

/-- Translation invariance of the AP equation gives the exact lifting used
after a local argument: if both local sets become subsets of `A` after
translation by `-t`, their mixed count is bounded by the AP count of `A`. -/
theorem mixedThreeAPCount_le_threeAPCount_of_sub_translate {A A' C : Finset G} (t : G)
    (hA : ∀ x ∈ A', x - t ∈ A) (hC : ∀ x ∈ C, x - t ∈ A) :
    mixedThreeAPCount A' C ≤ threeAPCount A := by
  unfold mixedThreeAPCount threeAPCount
  let f : ((G × G) × G) → ((G × G) × G) := fun x ↦
    ((x.1.1 - t, x.2 - t), x.1.2 - t)
  apply Finset.card_le_card_of_injOn f
  · rintro ⟨⟨a, c⟩, b⟩ habc
    change ((a, c), b) ∈ (((A' ×ˢ A') ×ˢ C).filter fun x ↦
      x.1.1 + x.1.2 = x.2 + x.2) at habc
    change ((a - t, b - t), c - t) ∈ (((A ×ˢ A) ×ˢ A).filter fun x ↦
      x.1.1 + x.2 = x.1.2 + x.1.2)
    simp only [mem_filter, mem_product] at habc ⊢
    rcases habc with ⟨⟨⟨ha, hc⟩, hb⟩, hrel⟩
    refine ⟨⟨⟨hA a ha, hC b hb⟩, hA c hc⟩, ?_⟩
    calc
      (a - t) + (c - t) = (a + c) - (t + t) := by
        simp only [sub_eq_add_neg, neg_add_rev]
        ac_rfl
      _ = (b + b) - (t + t) := congrArg (fun x ↦ x - (t + t)) hrel
      _ = (b - t) + (b - t) := by
        simp only [sub_eq_add_neg, neg_add_rev]
        ac_rfl
  · rintro ⟨⟨a, c⟩, b⟩ _ ⟨⟨a', c'⟩, b'⟩ _ heq
    have haSub : a - t = a' - t := congrArg (fun x ↦ x.1.1) heq
    have hbSub : b - t = b' - t := congrArg (fun x ↦ x.1.2) heq
    have hcSub : c - t = c' - t := congrArg (fun x ↦ x.2) heq
    have ha : a = a' := calc
      a = (a - t) + t := (sub_add_cancel a t).symm
      _ = (a' - t) + t := congrArg (fun x ↦ x + t) haSub
      _ = a' := sub_add_cancel a' t
    have hb : b = b' := calc
      b = (b - t) + t := (sub_add_cancel b t).symm
      _ = (b' - t) + t := congrArg (fun x ↦ x + t) hbSub
      _ = b' := sub_add_cancel b' t
    have hc : c = c' := calc
      c = (c - t) + t := (sub_add_cancel c t).symm
      _ = (c' - t) + t := congrArg (fun x ↦ x + t) hcSub
      _ = c' := sub_add_cancel c' t
    simp [ha, hb, hc]

end APCounting

end

end Erdos140
