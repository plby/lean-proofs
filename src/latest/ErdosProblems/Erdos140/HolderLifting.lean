import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The finite Hölder-lifting step for Erdős Problem 140

This file isolates the normalization-sensitive, but otherwise elementary, last
step of the Kelley--Meka/Bloom--Sisask counting argument.  We use natural
moments rather than real powers of a norm.  For `C ⊆ B` the main inequality is

`relativeDensity C B * |<f, μ_C>| ^ p ≤ localMoment B p f`.

It is just the triangle inequality followed by Jensen's inequality on the
finite probability space `C`.  The final theorem records the constants used in
the application: the good alternative gives one half of the normalized main
term, while the bad alternative gives a one-quarter lower bound and therefore
contradicts a one-eighth balanced bound.
-/

open scoped BigOperators
open Finset

namespace Erdos140
namespace HolderLifting

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The uniform probability average on the ambient finite type. -/
noncomputable def ambientAverage (f : G → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card G

/-- The `{0,1}`-valued indicator. -/
noncomputable def indicator (C : Finset G) (x : G) : ℝ :=
  open scoped Classical in
  if x ∈ C then 1 else 0

/-- The probability-density normalization `|G| / |C| · 1_C`. -/
noncomputable def normalizedIndicator (C : Finset G) (x : G) : ℝ :=
  (Fintype.card G : ℝ) / C.card * indicator C x

/-- The uniform average on a nonempty finite set.  It is set to zero on the
empty set; all substantive lemmas below assume nonemptiness. -/
noncomputable def localAverage (B : Finset G) (f : G → ℝ) : ℝ :=
  (∑ x ∈ B, f x) / B.card

/-- The relative density `|C| / |B|`. -/
noncomputable def relativeDensity (C B : Finset G) : ℝ :=
  C.card / B.card

/-- The normalized `p`-th absolute moment on `B`. -/
noncomputable def localMoment (B : Finset G) (p : ℕ) (f : G → ℝ) : ℝ :=
  localAverage B fun x ↦ |f x| ^ p

/-- Pairing against the normalized indicator of `C`, using the ambient
probability average from `Core`. -/
noncomputable def pairing (f : G → ℝ) (C : Finset G) : ℝ :=
  ambientAverage fun x ↦ f x * normalizedIndicator C x

lemma localAverage_nonneg {B : Finset G} {f : G → ℝ}
    (hf : ∀ x ∈ B, 0 ≤ f x) : 0 ≤ localAverage B f := by
  unfold localAverage
  exact div_nonneg (sum_nonneg fun x hx ↦ hf x hx) (by positivity)

lemma localMoment_nonneg (B : Finset G) (p : ℕ) (f : G → ℝ) :
    0 ≤ localMoment B p f := by
  exact localAverage_nonneg fun _ _ ↦ by positivity

lemma pairing_eq_localAverage {C : Finset G} (hC : C.Nonempty) (f : G → ℝ) :
    pairing f C = localAverage C f := by
  classical
  unfold pairing localAverage ambientAverage normalizedIndicator indicator
  rw [show (∑ x : G, f x *
      ((Fintype.card G : ℝ) / (C.card : ℝ) * if x ∈ C then 1 else 0)) =
      (Fintype.card G : ℝ) / (C.card : ℝ) * ∑ x ∈ C, f x by
    simp_rw [mul_ite, mul_one, mul_zero]
    simp only [← Finset.sum_filter]
    simp only [subset_univ, filter_mem_eq_of_subset]
    rw [← Finset.sum_mul]
    exact mul_comm _ _]
  have hcardC : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
  have hcardG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp

lemma abs_localAverage_le_localAverage_abs {C : Finset G} (f : G → ℝ) :
    |localAverage C f| ≤ localAverage C fun x ↦ |f x| := by
  unfold localAverage
  calc
    |(∑ x ∈ C, f x) / (C.card : ℝ)| =
        |(∑ x ∈ C, f x)| / (C.card : ℝ) := by
      rw [abs_div]
      congr 1
      exact abs_of_nonneg (Nat.cast_nonneg C.card)
    _ ≤ (∑ x ∈ C, |f x|) / (C.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs f C) (by positivity)

/-- Jensen's inequality for the uniform probability measure on a nonempty
finite set, stated with a natural exponent. -/
lemma localAverage_abs_pow_le_localMoment {C : Finset G} (hC : C.Nonempty)
    (p : ℕ) (f : G → ℝ) :
    (localAverage C fun x ↦ |f x|) ^ p ≤ localMoment C p f := by
  let w : G → ℝ := fun _ ↦ (C.card : ℝ)⁻¹
  have hw : ∀ x ∈ C, 0 ≤ w x := by
    intro x hx
    exact inv_nonneg.mpr (by positivity)
  have hws : ∑ x ∈ C, w x = 1 := by
    simp [w, hC.card_ne_zero]
  have hz : ∀ x ∈ C, 0 ≤ |f x| := by
    intro x hx
    positivity
  have h := Real.pow_arith_mean_le_arith_mean_pow C w (fun x ↦ |f x|)
    hw hws hz p
  simpa [localAverage, localMoment, w, div_eq_inv_mul, Finset.mul_sum] using h

/-- Finite Hölder in the precise weighted form needed for lifting from `C` to
the ambient local set `B`.  No roots occur: this is the `p`-th-power form of
`|<f,μ_C>| ≤ γ⁻¹ᵖ ‖f‖_{Lᵖ(B)}`. -/
theorem weighted_holder_lifting {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (f : G → ℝ) :
    relativeDensity C B * |pairing f C| ^ p ≤ localMoment B p f := by
  have hB : B.Nonempty := hC.mono hCB
  have hpair : |pairing f C| ^ p ≤ localMoment C p f := by
    rw [pairing_eq_localAverage hC]
    calc
      |localAverage C f| ^ p
          ≤ (localAverage C fun x ↦ |f x|) ^ p :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_localAverage_le_localAverage_abs f) p
      _ ≤ localMoment C p f := localAverage_abs_pow_le_localMoment hC p f
  have hrel : 0 ≤ relativeDensity C B := by
    unfold relativeDensity
    positivity
  calc
    relativeDensity C B * |pairing f C| ^ p
        ≤ relativeDensity C B * localMoment C p f := mul_le_mul_of_nonneg_left hpair hrel
    _ = (∑ x ∈ C, |f x| ^ p) / B.card := by
      unfold relativeDensity localMoment localAverage
      field_simp [hC.card_ne_zero, hB.card_ne_zero]
    _ ≤ (∑ x ∈ B, |f x| ^ p) / B.card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hCB fun _ _ _ ↦ by positivity
    _ = localMoment B p f := rfl

/-- The abstract localized Hölder dichotomy, with the constants from the
paper.  The approximation hypothesis says that all cross terms contribute at
most one quarter of the requested error.  The density hypothesis is the
root-free form of `γ⁻¹ᵖ ≤ 3/2`. -/
theorem localized_holder_dichotomy {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (_hp : 0 < p) (f : G → ℝ)
    (progression mainTerm ε : ℝ) (hmain : 0 ≤ mainTerm) (hε : 0 ≤ ε)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ ε * mainTerm / 4) :
    |progression - mainTerm| ≤ ε * mainTerm ∨
      (ε * mainTerm / 2) ^ p ≤ localMoment B p f := by
  by_cases hgood : |progression - mainTerm| ≤ ε * mainTerm
  · exact Or.inl hgood
  right
  have htri : |progression - mainTerm| ≤
      |(progression - mainTerm) - pairing f C| + |pairing f C| := by
    calc
      |progression - mainTerm| =
          |((progression - mainTerm) - pairing f C) + pairing f C| := by ring_nf
      _ ≤ |(progression - mainTerm) - pairing f C| + |pairing f C| := abs_add_le _ _
  have hpair : 3 * (ε * mainTerm) / 4 < |pairing f C| := by
    have hlarge : ε * mainTerm < |progression - mainTerm| := lt_of_not_ge hgood
    nlinarith
  have hrel : 0 ≤ relativeDensity C B := by
    unfold relativeDensity
    positivity
  have hpairpow : (3 * (ε * mainTerm) / 4) ^ p ≤ |pairing f C| ^ p :=
    pow_le_pow_left₀ (by positivity) hpair.le p
  have hproduct :
      (2 / 3 : ℝ) ^ p * (3 * (ε * mainTerm) / 4) ^ p ≤
        relativeDensity C B * |pairing f C| ^ p := by
    exact mul_le_mul hdensity hpairpow (by positivity) hrel
  calc
    (ε * mainTerm / 2) ^ p =
        (2 / 3 : ℝ) ^ p * (3 * (ε * mainTerm) / 4) ^ p := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ relativeDensity C B * |pairing f C| ^ p := hproduct
    _ ≤ localMoment B p f := weighted_holder_lifting hC hCB p f

/-- The counting specialization of `localized_holder_dichotomy`.  With error
parameter `1/2`, either the normalized progression count is at least half the
main term or the local `p`-th moment is at least the `p`-th power of one quarter
of the main term. -/
theorem half_main_term_or_quarter_moment {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (hp : 0 < p) (f : G → ℝ)
    (progression mainTerm : ℝ) (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ mainTerm / 8) :
    mainTerm / 2 ≤ progression ∨
      (mainTerm / 4) ^ p ≤ localMoment B p f := by
  have happ : |(progression - mainTerm) - pairing f C| ≤
      (1 / 2 : ℝ) * mainTerm / 4 := by
    convert happrox using 1 <;> ring
  have hdich := localized_holder_dichotomy hC hCB p hp f progression mainTerm
    (1 / 2 : ℝ) hmain.le (by norm_num) hdensity happ
  rcases hdich with hgood | hbad
  · left
    have hlower := (abs_le.mp hgood).1
    linarith
  · right
    convert hbad using 1 <;> ring

/-- Specialized endgame used in progression counting.  Under the balanced
`1/8` moment bound the bad Hölder alternative is impossible, so the normalized
progression count is at least `1/2` of its main term. -/
theorem half_main_term_of_balanced_eighth {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (hp : 0 < p) (f : G → ℝ)
    (progression mainTerm : ℝ) (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ mainTerm / 8)
    (hbalanced : localMoment B p f ≤ (mainTerm / 8) ^ p) :
    mainTerm / 2 ≤ progression := by
  rcases half_main_term_or_quarter_moment hC hCB p hp f progression mainTerm hmain
    hdensity happrox with hgood | hbad
  · exact hgood
  · have hpne : p ≠ 0 := Nat.ne_of_gt hp
    have hstrict : (mainTerm / 8) ^ p < (mainTerm / 4) ^ p := by
      apply pow_lt_pow_left₀
      · nlinarith
      · positivity
      · exact hpne
    have : (mainTerm / 4) ^ p ≤ (mainTerm / 8) ^ p := hbad.trans hbalanced
    exact (not_lt_of_ge this hstrict).elim

end HolderLifting
end Erdos140
