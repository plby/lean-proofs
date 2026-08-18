import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Group.Translate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-group averages for Erdős Problem 140

This file contains the elementary, normalization-sensitive algebra used by the
quantitative Roth argument.  If `G` is a finite additive group, `average f` is
`|G|⁻¹ ∑ x, f x`.  Thus `indicator A` has average `|A| / |G|`, while
`normalizedIndicator A` has average one when `A` is nonempty.

The convolution in this file is normalized as well:

`convolution f g x = ᵓ_y f y * g (x - y)`.

This convention is important: it makes both averaging and convolution
probabilistic and avoids factors of `|G|` in the algebraic identities.
-/

open scoped BigOperators translate
open Finset Function

namespace Erdos140
namespace Core

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The uniform probability average on a finite additive group. -/
noncomputable def average (f : G → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card G

lemma card_pos : 0 < Fintype.card G := Fintype.card_pos

lemma card_cast_pos : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast (card_pos (G := G))

lemma card_cast_ne_zero : (Fintype.card G : ℝ) ≠ 0 :=
  (card_cast_pos (G := G)).ne'

lemma average_eq_inv_mul_sum (f : G → ℝ) :
    average f = (Fintype.card G : ℝ)⁻¹ * ∑ x, f x := by
  simp [average, div_eq_inv_mul]

lemma sum_eq_card_mul_average (f : G → ℝ) :
    ∑ x, f x = Fintype.card G * average f := by
  rw [average]
  field_simp

@[simp] lemma average_zero : average (fun _ : G ↦ 0) = 0 := by simp [average]

@[simp] lemma average_const (c : ℝ) : average (fun _ : G ↦ c) = c := by
  simp [average, card_cast_ne_zero (G := G)]

lemma average_add (f g : G → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, sum_add_distrib, add_div]

lemma average_sub (f g : G → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, sum_sub_distrib, sub_div]

lemma average_neg (f : G → ℝ) : average (fun x ↦ -f x) = -average f := by
  rw [average, average, Finset.sum_neg_distrib]
  ring

lemma average_smul (c : ℝ) (f : G → ℝ) :
    average (fun x ↦ c * f x) = c * average f := by
  rw [average, average]
  have hs : (∑ x, c * f x) = c * ∑ x, f x := by
    simpa only using (Finset.mul_sum (Finset.univ : Finset G) f c).symm
  rw [hs]
  ring

lemma average_mul_const (f : G → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  rw [average, average]
  have hs : (∑ x, f x * c) = (∑ x, f x) * c := by
    simpa only using (Finset.sum_mul (Finset.univ : Finset G) f c).symm
  rw [hs]
  ring

lemma average_mono {f g : G → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (sum_le_sum fun x _ ↦ h x) (by positivity)

lemma average_nonneg {f : G → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact div_nonneg (sum_nonneg fun x _ ↦ h x) (by positivity)

lemma abs_average_le_average_abs (f : G → ℝ) :
    |average f| ≤ average fun x ↦ |f x| := by
  rw [average, average, abs_div]
  rw [abs_of_pos (card_cast_pos (G := G))]
  exact div_le_div_of_nonneg_right
    (by simpa only using Finset.abs_sum_le_sum_abs f (Finset.univ : Finset G)) (by positivity)

lemma average_le_of_forall_le {f : G → ℝ} {c : ℝ} (h : ∀ x, f x ≤ c) :
    average f ≤ c := by
  simpa using average_mono (g := fun _ : G ↦ c) h

lemma le_average_of_forall_le {f : G → ℝ} {c : ℝ} (h : ∀ x, c ≤ f x) :
    c ≤ average f := by
  simpa using average_mono (f := fun _ : G ↦ c) h

@[simp] lemma average_translate (t : G) (f : G → ℝ) : average (τ t f) = average f := by
  unfold average
  rw [sum_translate]

/-- The `{0,1}`-valued indicator of a finite set. -/
noncomputable def indicator (A : Finset G) (x : G) : ℝ :=
  open scoped Classical in
  if x ∈ A then 1 else 0

@[simp] lemma indicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    indicator A x = 1 := by simp [indicator, hx]

@[simp] lemma indicator_apply_notMem {A : Finset G} {x : G} (hx : x ∉ A) :
    indicator A x = 0 := by simp [indicator, hx]

lemma indicator_nonneg (A : Finset G) (x : G) : 0 ≤ indicator A x := by
  simp only [indicator]
  split <;> positivity

lemma indicator_le_one (A : Finset G) (x : G) : indicator A x ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

lemma indicator_pos_iff {A : Finset G} {x : G} : 0 < indicator A x ↔ x ∈ A := by
  classical
  by_cases hx : x ∈ A <;> simp [indicator, hx]

lemma indicator_ne_zero_iff {A : Finset G} {x : G} : indicator A x ≠ 0 ↔ x ∈ A := by
  simp [indicator]

@[simp] lemma sum_indicator (A : Finset G) : ∑ x, indicator A x = A.card := by
  classical
  simp [indicator]

@[simp] lemma average_indicator (A : Finset G) :
    average (indicator A) = (A.card : ℝ) / Fintype.card G := by
  simp [average]

/-- The density of a finite set in the ambient finite group. -/
noncomputable def density (A : Finset G) : ℝ :=
  (A.card : ℝ) / Fintype.card G

@[simp] lemma average_indicator_eq_density (A : Finset G) :
    average (indicator A) = density A := by simp [density]

lemma density_nonneg (A : Finset G) : 0 ≤ density A := by
  exact div_nonneg (by positivity) (by positivity)

lemma density_le_one (A : Finset G) : density A ≤ 1 := by
  rw [density, div_le_one (card_cast_pos (G := G))]
  exact_mod_cast A.card_le_univ

lemma density_pos_iff {A : Finset G} : 0 < density A ↔ A.Nonempty := by
  rw [density, div_pos_iff]
  simp [card_cast_pos (G := G), Finset.card_pos]

/-- The probability-density normalization `|G| / |A| · 1_A`.

For the empty set this is defined to be zero. -/
noncomputable def normalizedIndicator (A : Finset G) (x : G) : ℝ :=
  (Fintype.card G : ℝ) / A.card * indicator A x

lemma normalizedIndicator_apply [DecidableEq G] (A : Finset G) (x : G) :
    normalizedIndicator A x =
      if x ∈ A then (Fintype.card G : ℝ) / A.card else 0 := by
  classical
  simp [normalizedIndicator, indicator]

lemma normalizedIndicator_nonneg (A : Finset G) (x : G) :
    0 ≤ normalizedIndicator A x := by
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (indicator_nonneg A x)

lemma normalizedIndicator_eq_zero_of_notMem {A : Finset G} {x : G} (hx : x ∉ A) :
    normalizedIndicator A x = 0 := by simp [normalizedIndicator, hx]

lemma normalizedIndicator_pos_iff {A : Finset G} (hA : A.Nonempty) {x : G} :
    0 < normalizedIndicator A x ↔ x ∈ A := by
  classical
  rw [normalizedIndicator]
  constructor
  · intro h
    by_contra hx
    simp [hx] at h
  · intro hx
    exact mul_pos (div_pos (card_cast_pos (G := G)) (by exact_mod_cast hA.card_pos))
      (indicator_pos_iff.mpr hx)

lemma support_normalizedIndicator {A : Finset G} (hA : A.Nonempty) :
    Function.support (normalizedIndicator A) = (A : Set G) := by
  ext x
  change normalizedIndicator A x ≠ 0 ↔ x ∈ A
  constructor
  · intro hx
    exact (normalizedIndicator_pos_iff hA).mp
      (lt_of_le_of_ne (normalizedIndicator_nonneg A x) (Ne.symm hx))
  · intro hx
    exact ((normalizedIndicator_pos_iff hA).mpr hx).ne'

@[simp] lemma sum_normalizedIndicator (A : Finset G) :
    ∑ x, normalizedIndicator A x = if A.Nonempty then Fintype.card G else 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    unfold normalizedIndicator
    have hs : (∑ x, (Fintype.card G : ℝ) / A.card * indicator A x) =
        (Fintype.card G : ℝ) / A.card * ∑ x, indicator A x := by
      simpa only using
        (Finset.mul_sum (Finset.univ : Finset G) (indicator A)
          ((Fintype.card G : ℝ) / A.card)).symm
    rw [hs, sum_indicator]
    field_simp [hA.card_ne_zero]
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    simp [hAe, normalizedIndicator]

@[simp] lemma average_normalizedIndicator {A : Finset G} (hA : A.Nonempty) :
    average (normalizedIndicator A) = 1 := by
  rw [average, sum_normalizedIndicator, if_pos hA]
  exact div_self (card_cast_ne_zero (G := G))

/-- Reflection in the origin. -/
def reflect (f : G → ℝ) (x : G) : ℝ := f (-x)

@[simp] lemma reflect_apply (f : G → ℝ) (x : G) : reflect f x = f (-x) := rfl
@[simp] lemma reflect_reflect (f : G → ℝ) : reflect (reflect f) = f := by ext; simp [reflect]
@[simp] lemma average_reflect (f : G → ℝ) : average (reflect f) = average f := by
  unfold average reflect
  congr 1
  exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ ↦ rfl)

/-- Normalized additive convolution. -/
noncomputable def convolution (f g : G → ℝ) (x : G) : ℝ :=
  average fun y ↦ f y * g (x - y)

/-- Normalized difference convolution (also called correlation). -/
noncomputable def diffConvolution (f g : G → ℝ) (x : G) : ℝ :=
  average fun y ↦ f y * g (y - x)

@[simp] lemma convolution_apply (f g : G → ℝ) (x : G) :
    convolution f g x = (∑ y, f y * g (x - y)) / Fintype.card G := rfl

@[simp] lemma diffConvolution_apply (f g : G → ℝ) (x : G) :
    diffConvolution f g x = (∑ y, f y * g (y - x)) / Fintype.card G := rfl

lemma diffConvolution_eq_convolution_reflect (f g : G → ℝ) :
    diffConvolution f g = convolution f (reflect g) := by
  ext x
  simp only [diffConvolution_apply, convolution_apply, reflect_apply]
  congr 2 with y
  rw [neg_sub]

lemma convolution_nonneg {f g : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (x : G) : 0 ≤ convolution f g x := by
  exact average_nonneg fun y ↦ mul_nonneg (hf y) (hg (x - y))

lemma diffConvolution_nonneg {f g : G → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (x : G) : 0 ≤ diffConvolution f g x := by
  exact average_nonneg fun y ↦ mul_nonneg (hf y) (hg (y - x))

@[simp] lemma convolution_zero_left (g : G → ℝ) :
    convolution (fun _ ↦ 0) g = fun _ ↦ 0 := by ext; simp [convolution, average]

@[simp] lemma convolution_zero_right (f : G → ℝ) :
    convolution f (fun _ ↦ 0) = fun _ ↦ 0 := by ext; simp [convolution, average]

lemma convolution_add_left (f₁ f₂ g : G → ℝ) :
    convolution (fun x ↦ f₁ x + f₂ x) g =
      fun x ↦ convolution f₁ g x + convolution f₂ g x := by
  ext x
  simp only [convolution]
  rw [← average_add]
  congr 1
  funext y
  ring

lemma convolution_add_right (f g₁ g₂ : G → ℝ) :
    convolution f (fun x ↦ g₁ x + g₂ x) =
      fun x ↦ convolution f g₁ x + convolution f g₂ x := by
  ext x
  simp only [convolution]
  rw [← average_add]
  congr 1
  funext y
  ring

lemma convolution_smul_left (c : ℝ) (f g : G → ℝ) :
    convolution (fun x ↦ c * f x) g = fun x ↦ c * convolution f g x := by
  ext x
  simp only [convolution]
  rw [← average_smul]
  congr 1
  funext y
  ring

lemma convolution_smul_right (c : ℝ) (f g : G → ℝ) :
    convolution f (fun x ↦ c * g x) = fun x ↦ c * convolution f g x := by
  ext x
  simp only [convolution]
  rw [← average_smul]
  congr 1
  funext y
  ring

lemma convolution_comm (f g : G → ℝ) : convolution f g = convolution g f := by
  ext x
  simp only [convolution_apply]
  apply congrArg (fun z : ℝ ↦ z / Fintype.card G)
  calc
    ∑ y, f y * g (x - y) =
        ∑ y, f ((Equiv.subLeft x) y) * g (x - (Equiv.subLeft x) y) :=
      ((Equiv.subLeft x).sum_comp (fun y ↦ f y * g (x - y))).symm
    _ = ∑ y, g y * f (x - y) := by
      apply Fintype.sum_congr _ _
      intro y
      simp [mul_comm]

/-- Associativity of normalized convolution. -/
lemma convolution_assoc (f g h : G → ℝ) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  ext x
  unfold convolution average
  field_simp [card_cast_ne_zero (G := G)]
  have hldiv :
      (∑ y, ((∑ z, f z * g (y - z)) * h (x - y)) / (Fintype.card G : ℝ)) =
        (∑ y, (∑ z, f z * g (y - z)) * h (x - y)) / Fintype.card G := by
    simpa only using
      (Finset.sum_div (Finset.univ : Finset G)
        (fun y ↦ (∑ z, f z * g (y - z)) * h (x - y))
        (Fintype.card G : ℝ)).symm
  have hrdiv :
      (∑ z, (f z * ∑ y, g y * h (x - z - y)) / (Fintype.card G : ℝ)) =
        (∑ z, f z * ∑ y, g y * h (x - z - y)) / Fintype.card G := by
    simpa only using
      (Finset.sum_div (Finset.univ : Finset G)
        (fun z ↦ f z * ∑ y, g y * h (x - z - y))
        (Fintype.card G : ℝ)).symm
  rw [hldiv, hrdiv]
  apply congrArg (fun u : ℝ ↦ u / Fintype.card G)
  have hlexpand :
      (∑ y, (∑ z, f z * g (y - z)) * h (x - y)) =
        ∑ y, ∑ z, (f z * g (y - z)) * h (x - y) := by
    apply Fintype.sum_congr _ _
    intro y
    simpa only using
      Finset.sum_mul (Finset.univ : Finset G) (fun z ↦ f z * g (y - z)) (h (x - y))
  have hrexpand :
      (∑ z, f z * ∑ y, g y * h (x - z - y)) =
        ∑ z, ∑ y, f z * (g y * h (x - z - y)) := by
    apply Fintype.sum_congr _ _
    intro z
    simpa only using
      Finset.mul_sum (Finset.univ : Finset G) (fun y ↦ g y * h (x - z - y)) (f z)
  rw [hlexpand, hrexpand]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr _ _
  intro z
  calc
    ∑ y, (f z * g (y - z)) * h (x - y) =
        ∑ y, (fun u ↦ (f z * g (u - z)) * h (x - u)) ((Equiv.addRight z) y) :=
      (Equiv.sum_comp (Equiv.addRight z)
        (fun u ↦ (f z * g (u - z)) * h (x - u))).symm
    _ = ∑ y, f z * (g y * h (x - z - y)) := by
      apply Fintype.sum_congr _ _
      intro y
      simp
      ring_nf
      congr 2 <;> abel

lemma diffConvolution_zero (f g : G → ℝ) :
    diffConvolution f g 0 = average fun y ↦ f y * g y := by
  simp [diffConvolution]

lemma diffConvolution_swap (f g : G → ℝ) (x : G) :
    diffConvolution f g x = diffConvolution g f (-x) := by
  simp only [diffConvolution_apply]
  apply congrArg (fun z : ℝ ↦ z / Fintype.card G)
  calc
    ∑ y, f y * g (y - x) =
        ∑ y, (fun z ↦ g z * f (z + x)) ((Equiv.subRight x) y) := by
      apply Fintype.sum_congr _ _
      intro y
      simp [mul_comm]
    _ = ∑ y, g y * f (y + x) :=
      (Equiv.subRight x).sum_comp (fun z ↦ g z * f (z + x))
    _ = _ := by apply Fintype.sum_congr _ _; intro y; congr 2; abel

lemma average_convolution (f g : G → ℝ) :
    average (convolution f g) = average f * average g := by
  unfold convolution
  simp_rw [average]
  have hdiv : (∑ x, (∑ y, f y * g (x - y)) / (Fintype.card G : ℝ)) =
      (∑ x, ∑ y, f y * g (x - y)) / Fintype.card G := by
    simpa only using
      (Finset.sum_div (Finset.univ : Finset G)
        (fun x ↦ ∑ y, f y * g (x - y)) (Fintype.card G : ℝ)).symm
  rw [hdiv]
  field_simp [card_cast_ne_zero (G := G)]
  rw [Finset.sum_comm]
  calc
    ∑ y, ∑ x, f y * g (x - y) = ∑ y, f y * ∑ x, g (x - y) := by
      apply Fintype.sum_congr _ _
      intro y
      simpa only using
        (Finset.mul_sum (Finset.univ : Finset G) (fun x ↦ g (x - y)) (f y)).symm
    _ = ∑ y, f y * ∑ x, g x := by
      apply Fintype.sum_congr _ _
      intro y
      congr 1
      simpa only [translate_apply] using sum_translate y g
    _ = (∑ y, f y) * ∑ x, g x := by
      simpa only using
        (Finset.sum_mul (Finset.univ : Finset G) f (∑ x, g x)).symm

lemma average_diffConvolution (f g : G → ℝ) :
    average (diffConvolution f g) = average f * average g := by
  rw [diffConvolution_eq_convolution_reflect, average_convolution, average_reflect]

lemma convolution_translate_right (t : G) (f g : G → ℝ) :
    convolution f (τ t g) = τ t (convolution f g) := by
  ext x
  apply congrArg average
  funext y
  simp only [translate_apply]
  congr 2
  abel

lemma convolution_translate_left (t : G) (f g : G → ℝ) :
    convolution (τ t f) g = τ t (convolution f g) := by
  rw [convolution_comm, convolution_translate_right, convolution_comm]

lemma diffConvolution_translate_left (t : G) (f g : G → ℝ) :
    diffConvolution (τ t f) g = τ t (diffConvolution f g) := by
  ext x
  change average (fun y ↦ f (y - t) * g (y - x)) =
    average (fun y ↦ f y * g (y - (x - t)))
  have heq : (fun y ↦ f (y - t) * g (y - x)) =
      τ t (fun y ↦ f y * g (y - (x - t))) := by
    funext y
    simp only [translate_apply]
    congr 2
    abel
  rw [heq, average_translate]

lemma diffConvolution_translate_right (t : G) (f g : G → ℝ) :
    diffConvolution f (τ t g) = τ (-t) (diffConvolution f g) := by
  ext x
  apply congrArg average
  funext y
  simp only [translate_apply]
  congr 2
  abel

lemma convolution_indicator [DecidableEq G] (A B : Finset G) (x : G) :
    convolution (indicator A) (indicator B) x =
      ((Finset.univ.filter fun y : G ↦ y ∈ A ∧ x - y ∈ B).card : ℝ) / Fintype.card G := by
  classical
  rw [convolution_apply]
  congr 1
  calc
    ∑ y, indicator A y * indicator B (x - y) =
        ∑ y, if y ∈ A ∧ x - y ∈ B then (1 : ℝ) else 0 := by
      apply Fintype.sum_congr _ _
      intro y
      by_cases hyA : y ∈ A <;> by_cases hyB : x - y ∈ B <;>
        simp [indicator, hyA, hyB]
    _ = _ := by
      simpa only using
        (Finset.sum_boole (R := ℝ) (fun y : G ↦ y ∈ A ∧ x - y ∈ B) Finset.univ)

lemma diffConvolution_indicator [DecidableEq G] (A B : Finset G) (x : G) :
    diffConvolution (indicator A) (indicator B) x =
      ((Finset.univ.filter fun y : G ↦ y ∈ A ∧ y - x ∈ B).card : ℝ) / Fintype.card G := by
  classical
  rw [diffConvolution_apply]
  congr 1
  calc
    ∑ y, indicator A y * indicator B (y - x) =
        ∑ y, if y ∈ A ∧ y - x ∈ B then (1 : ℝ) else 0 := by
      apply Fintype.sum_congr _ _
      intro y
      by_cases hyA : y ∈ A <;> by_cases hyB : y - x ∈ B <;>
        simp [indicator, hyA, hyB]
    _ = _ := by
      simpa only using
        (Finset.sum_boole (R := ℝ) (fun y : G ↦ y ∈ A ∧ y - x ∈ B) Finset.univ)

lemma convolution_indicator_pos_iff [DecidableEq G] {A B : Finset G} {x : G} :
    0 < convolution (indicator A) (indicator B) x ↔
      ∃ a ∈ A, ∃ b ∈ B, a + b = x := by
  classical
  rw [convolution_indicator, div_pos_iff_of_pos_right (card_cast_pos (G := G)),
    Nat.cast_pos, Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hxa⟩
    refine ⟨a, ha, x - a, hxa, ?_⟩
    abel
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ha, ?_⟩
    rw [← hab]
    simpa

lemma diffConvolution_indicator_pos_iff [DecidableEq G] {A B : Finset G} {x : G} :
    0 < diffConvolution (indicator A) (indicator B) x ↔
      ∃ a ∈ A, ∃ b ∈ B, a - b = x := by
  classical
  rw [diffConvolution_indicator, div_pos_iff_of_pos_right (card_cast_pos (G := G)),
    Nat.cast_pos, Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, ha, a - x, hax, ?_⟩
    abel
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ha, ?_⟩
    rw [← hab]
    simpa

lemma mem_support_convolution_indicator_iff [DecidableEq G] {A B : Finset G} {x : G} :
    x ∈ Function.support (convolution (indicator A) (indicator B)) ↔
      ∃ a ∈ A, ∃ b ∈ B, a + b = x := by
  change convolution (indicator A) (indicator B) x ≠ 0 ↔ _
  rw [← convolution_indicator_pos_iff]
  constructor
  · intro hx
    exact lt_of_le_of_ne
      (convolution_nonneg (indicator_nonneg A) (indicator_nonneg B) x) (Ne.symm hx)
  · exact fun hx ↦ hx.ne'

lemma mem_support_diffConvolution_indicator_iff [DecidableEq G]
    {A B : Finset G} {x : G} :
    x ∈ Function.support (diffConvolution (indicator A) (indicator B)) ↔
      ∃ a ∈ A, ∃ b ∈ B, a - b = x := by
  change diffConvolution (indicator A) (indicator B) x ≠ 0 ↔ _
  rw [← diffConvolution_indicator_pos_iff]
  constructor
  · intro hx
    exact lt_of_le_of_ne
      (diffConvolution_nonneg (indicator_nonneg A) (indicator_nonneg B) x) (Ne.symm hx)
  · exact fun hx ↦ hx.ne'

lemma convolution_normalizedIndicator [DecidableEq G] (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (x : G) :
    convolution (normalizedIndicator A) (normalizedIndicator B) x =
      (Fintype.card G : ℝ) / (A.card * B.card) *
        (Finset.univ.filter fun y : G ↦ y ∈ A ∧ x - y ∈ B).card := by
  change convolution (fun z ↦ (Fintype.card G : ℝ) / A.card * indicator A z)
    (fun z ↦ (Fintype.card G : ℝ) / B.card * indicator B z) x = _
  calc
    _ = ((Fintype.card G : ℝ) / A.card) * ((Fintype.card G : ℝ) / B.card) *
        convolution (indicator A) (indicator B) x := by
      unfold convolution
      rw [← average_smul]
      congr 1
      funext y
      ring
    _ = _ := by
      rw [convolution_indicator]
      field_simp [card_cast_ne_zero (G := G), hA.card_ne_zero, hB.card_ne_zero]

lemma diffConvolution_normalizedIndicator [DecidableEq G] (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (x : G) :
    diffConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (Fintype.card G : ℝ) / (A.card * B.card) *
        (Finset.univ.filter fun y : G ↦ y ∈ A ∧ y - x ∈ B).card := by
  change diffConvolution (fun z ↦ (Fintype.card G : ℝ) / A.card * indicator A z)
    (fun z ↦ (Fintype.card G : ℝ) / B.card * indicator B z) x = _
  calc
    _ = ((Fintype.card G : ℝ) / A.card) * ((Fintype.card G : ℝ) / B.card) *
        diffConvolution (indicator A) (indicator B) x := by
      unfold diffConvolution
      rw [← average_smul]
      congr 1
      funext y
      ring
    _ = _ := by
      rw [diffConvolution_indicator]
      field_simp [card_cast_ne_zero (G := G), hA.card_ne_zero, hB.card_ne_zero]

/-- The normalized `p`-th absolute moment for a natural exponent. -/
noncomputable def moment (p : ℕ) (f : G → ℝ) : ℝ :=
  average fun x ↦ |f x| ^ p

/-- The natural-exponent `L^p` seminorm, expressed with real powers.
The useful API assumes `0 < p`; at `p = 0` this definition has no intended norm meaning. -/
noncomputable def lpNormNat (p : ℕ) (f : G → ℝ) : ℝ :=
  (moment p f) ^ (1 / (p : ℝ))

lemma moment_nonneg (p : ℕ) (f : G → ℝ) : 0 ≤ moment p f := by
  exact average_nonneg fun x ↦ by positivity

@[simp] lemma moment_zero (f : G → ℝ) : moment 0 f = 1 := by
  simp [moment]

@[simp] lemma moment_one (f : G → ℝ) : moment 1 f = average fun x ↦ |f x| := by
  simp [moment]

lemma moment_two (f : G → ℝ) : moment 2 f = average fun x ↦ f x ^ 2 := by
  apply congrArg average
  funext x
  exact sq_abs (f x)

@[simp] lemma moment_neg (p : ℕ) (f : G → ℝ) :
    moment p (fun x ↦ -f x) = moment p f := by simp [moment]

@[simp] lemma moment_abs (p : ℕ) (f : G → ℝ) :
    moment p (fun x ↦ |f x|) = moment p f := by simp [moment]

@[simp] lemma moment_translate (p : ℕ) (t : G) (f : G → ℝ) :
    moment p (τ t f) = moment p f := by
  change average (fun x ↦ |f (x - t)| ^ p) = average (fun x ↦ |f x| ^ p)
  change average (τ t (fun x ↦ |f x| ^ p)) = average (fun x ↦ |f x| ^ p)
  rw [average_translate]

lemma moment_mono (p : ℕ) {f g : G → ℝ} (h : ∀ x, |f x| ≤ |g x|) :
    moment p f ≤ moment p g := by
  exact average_mono fun x ↦ pow_le_pow_left₀ (abs_nonneg _) (h x) p

lemma lpNormNat_nonneg (p : ℕ) (f : G → ℝ) : 0 ≤ lpNormNat p f := by
  exact Real.rpow_nonneg (moment_nonneg p f) _

lemma lpNormNat_pow (p : ℕ) (hp : 0 < p) (f : G → ℝ) :
    (lpNormNat p f) ^ (p : ℝ) = moment p f := by
  rw [lpNormNat, ← Real.rpow_mul (moment_nonneg p f)]
  field_simp
  simp

private lemma natPow_rpow_div (a : ℝ) (p q : ℕ) (hp : 0 < p) :
    (|a| ^ p) ^ ((q : ℝ) / p) = |a| ^ q := by
  rw [← Real.rpow_natCast |a| p, ← Real.rpow_natCast |a| q]
  rw [← Real.rpow_mul (abs_nonneg a)]
  congr 1
  field_simp

/-- Monotonicity of `L^p` norms on the uniform probability space. -/
lemma lpNormNat_mono_exponent {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) (f : G → ℝ) :
    lpNormNat p f ≤ lpNormNat q f := by
  classical
  have hq : 0 < q := hp.trans_le hpq
  let w : G → ℝ := fun _ ↦ (Fintype.card G : ℝ)⁻¹
  have hw : ∀ i ∈ (Finset.univ : Finset G), 0 ≤ w i := by
    intro i hi
    exact inv_nonneg.mpr (card_cast_pos (G := G)).le
  have hws : ∑ i ∈ (Finset.univ : Finset G), w i = 1 := by
    simp [w, card_cast_ne_zero (G := G)]
  have hz : ∀ i ∈ (Finset.univ : Finset G), 0 ≤ |f i| ^ p := by
    intro i hi
    positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (1 : ℝ) ≤ (q : ℝ) / p := by
    rw [le_div_iff₀ hpR]
    simpa only [one_mul] using (show (p : ℝ) ≤ q by exact_mod_cast hpq)
  have hmean := Real.arith_mean_le_rpow_mean (Finset.univ : Finset G) w
    (fun x ↦ |f x| ^ p) hw hws hz hr
  simp_rw [natPow_rpow_div (p := p) (q := q) (hp := hp)] at hmean
  have hmoment : moment p f ≤ (moment q f) ^ ((p : ℝ) / q) := by
    convert hmean using 1 <;>
      simp [moment, average, w, div_eq_inv_mul, Finset.mul_sum]
  unfold lpNormNat
  calc
    (moment p f) ^ (1 / (p : ℝ)) ≤
        ((moment q f) ^ ((p : ℝ) / q)) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow (moment_nonneg p f) hmoment (by positivity)
    _ = (moment q f) ^ (1 / (q : ℝ)) := by
      rw [← Real.rpow_mul (moment_nonneg q f)]
      congr 1
      field_simp

lemma average_abs_le_lpNormNat (p : ℕ) (hp : 0 < p) (f : G → ℝ) :
    average (fun x ↦ |f x|) ≤ lpNormNat p f := by
  classical
  unfold lpNormNat moment average
  let w : G → ℝ := fun _ ↦ (Fintype.card G : ℝ)⁻¹
  have hw : ∀ i ∈ (Finset.univ : Finset G), 0 ≤ w i := by
    intro i hi
    exact inv_nonneg.mpr (le_of_lt (card_cast_pos (G := G)))
  have hws : ∑ i ∈ (Finset.univ : Finset G), w i = 1 := by
    simp [w, card_cast_ne_zero (G := G)]
  have hz : ∀ i ∈ (Finset.univ : Finset G), 0 ≤ |f i| := by
    intro i hi
    positivity
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := Real.arith_mean_le_rpow_mean (Finset.univ : Finset G) w (fun x ↦ |f x|)
    hw hws hz hpR
  simpa [w, div_eq_inv_mul, Finset.mul_sum, Real.rpow_natCast] using h

lemma cauchySchwarz_average (f g : G → ℝ) :
    |average fun x ↦ f x * g x| ^ 2 ≤ moment 2 f * moment 2 g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G) f g
  rw [average, moment, moment, average, average, abs_div,
    abs_of_pos (card_cast_pos (G := G))]
  rw [div_pow, div_mul_div_comm]
  rw [show (Fintype.card G : ℝ) * Fintype.card G = (Fintype.card G : ℝ) ^ 2 by ring]
  exact div_le_div_of_nonneg_right (by simpa [sq_abs] using h)
    (pow_pos (card_cast_pos (G := G)) 2).le

lemma cauchySchwarz_average_sqrt (f g : G → ℝ) :
    |average fun x ↦ f x * g x| ≤ Real.sqrt (moment 2 f) * Real.sqrt (moment 2 g) := by
  rw [← Real.sqrt_sq_eq_abs (average fun x ↦ f x * g x)]
  rw [← Real.sqrt_mul (moment_nonneg 2 f)]
  exact Real.sqrt_le_sqrt (by simpa [sq_abs] using cauchySchwarz_average f g)

/-- Finite Hölder, with the average on the left and raw sums on the right. -/
lemma holder_average_unnormalized {p q : ℝ} (hpq : p.HolderConjugate q) (f g : G → ℝ) :
    average (fun x ↦ f x * g x) ≤
      ((∑ x, |f x| ^ p) ^ (1 / p) * (∑ x, |g x| ^ q) ^ (1 / q)) /
        Fintype.card G := by
  have h := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset G) f g hpq
  unfold average
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Hölder's inequality on the uniform probability space. -/
lemma holder_average {p q : ℝ} (hpq : p.HolderConjugate q) (f g : G → ℝ) :
    average (fun x ↦ f x * g x) ≤
      (average fun x ↦ |f x| ^ p) ^ (1 / p) *
        (average fun x ↦ |g x| ^ q) ^ (1 / q) := by
  have h := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset G) f g hpq
  have hf : 0 ≤ ∑ x, |f x| ^ p :=
    sum_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hg : 0 ≤ ∑ x, |g x| ^ q :=
    sum_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hd : (0 : ℝ) < Fintype.card G := card_cast_pos (G := G)
  unfold average
  calc
    (∑ x, f x * g x) / Fintype.card G ≤
        ((∑ x, |f x| ^ p) ^ (1 / p) * (∑ x, |g x| ^ q) ^ (1 / q)) /
          Fintype.card G := div_le_div_of_nonneg_right h hd.le
    _ = ((∑ x, |f x| ^ p) / Fintype.card G) ^ (1 / p) *
          ((∑ x, |g x| ^ q) / Fintype.card G) ^ (1 / q) := by
      rw [Real.div_rpow hf hd.le, Real.div_rpow hg hd.le, div_mul_div_comm]
      congr 1
      rw [← Real.rpow_add hd]
      rw [show 1 / p + 1 / q = 1 by simpa [one_div] using hpq.inv_add_inv_eq_one]
      simp

end Core
end Erdos140
