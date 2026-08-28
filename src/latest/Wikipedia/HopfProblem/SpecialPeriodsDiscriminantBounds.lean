import Wikipedia.HopfProblem.PeriodDomain
import Mathlib.Topology.Order.Compact

/-!
# The discriminant bound and constant imaginary shifts

This file proves the compactness and asymptotic arguments in Proposition 3.15.
A continuous real function on a compact base punctured at one point is bounded
above if it tends to `-∞` at that puncture.  For the actual period discriminant,
an upper bound on `Im (β + τ)` and `Im τ → +∞` imply this negative divergence;
no estimate on `μ` is necessary.  Adding a sufficiently negative imaginary
constant to `β` then makes every period point admissible, without changing any
of the three generator transformation laws.

The final statements take continuous descended period data and their cusp
asymptotics as explicit input.  They establish the uniform shift rather than
assuming its existence or assuming the discriminant is already negative.
Construction of the global equivariant functions and their compactified base
is not asserted here.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem

namespace PeriodPoint

/-- The nonpositive correction in the discriminant can only lower `Im β`. -/
theorem discriminant_le_im_beta (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ p.β.im := by
  exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le)

/-- The form of the discriminant bound used at the cusp. -/
theorem discriminant_le_im_beta_add_tau_sub (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ (p.β + p.τ).im - p.τ.im := by
  simpa only [Complex.add_im, add_sub_cancel_right] using p.discriminant_le_im_beta hτ

/-- Cusp divergence of the discriminant follows from bounded `Im (β + τ)`
and divergent `Im τ`; the middle period `μ` needs no bound. -/
theorem tendsto_discriminant_atBot {X : Type*} {l : Filter X} (P : X → PeriodPoint)
    (hτ : ∀ᶠ z in l, 0 < (P z).τ.im)
    (hτinf : Tendsto (fun z => (P z).τ.im) l atTop)
    (hb : ∃ C : ℝ, ∀ᶠ z in l, ((P z).β + (P z).τ).im ≤ C) :
    Tendsto (fun z => (P z).discriminant) l atBot := by
  obtain ⟨C, hC⟩ := hb
  refine tendsto_atBot.mpr fun R => ?_
  filter_upwards [hτ, hC, hτinf.eventually_ge_atTop (C - R)] with z hzτ hzC hzR
  have hD := (P z).discriminant_le_im_beta_add_tau_sub hzτ
  linarith

/-- Continuity of the actual discriminant follows from that of its three
period functions wherever `Im τ` is nonzero. -/
theorem continuousOn_discriminant {X : Type*} [TopologicalSpace X]
    (P : X → PeriodPoint) {s : Set X}
    (hτ : ContinuousOn (fun z => (P z).τ) s)
    (hμ : ContinuousOn (fun z => (P z).μ) s)
    (hβ : ContinuousOn (fun z => (P z).β) s)
    (hτ₀ : ∀ z ∈ s, (P z).τ.im ≠ 0) :
    ContinuousOn (fun z => (P z).discriminant) s := by
  exact (Complex.continuous_im.comp_continuousOn hβ).sub
    ((continuousOn_const.mul ((Complex.continuous_im.comp_continuousOn hμ).pow 2)).div
      (Complex.continuous_im.comp_continuousOn hτ) hτ₀)

/-- Change only the third period by a complex additive constant. -/
def shiftBeta (p : PeriodPoint) (c : ℂ) : PeriodPoint := ⟨p.τ, p.μ, p.β + c⟩

@[simp] theorem shiftBeta_tau (p : PeriodPoint) (c : ℂ) : (p.shiftBeta c).τ = p.τ := rfl

@[simp] theorem shiftBeta_mu (p : PeriodPoint) (c : ℂ) : (p.shiftBeta c).μ = p.μ := rfl

@[simp] theorem shiftBeta_beta (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).β = p.β + c := rfl

@[simp] theorem shiftBeta_zero (p : PeriodPoint) : p.shiftBeta 0 = p := by
  cases p
  simp [shiftBeta]

@[simp] theorem shiftBeta_shiftBeta (p : PeriodPoint) (c d : ℂ) :
    (p.shiftBeta c).shiftBeta d = p.shiftBeta (c + d) := by
  simp [shiftBeta, add_assoc]

/-- The discriminant changes by precisely the imaginary part of the constant. -/
@[simp] theorem shiftBeta_discriminant (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).discriminant = p.discriminant + c.im := by
  simp only [discriminant, shiftBeta, Complex.add_im]
  ring

theorem shiftBeta_admissible_iff (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).Admissible ↔ 0 < p.τ.im ∧ p.discriminant < -c.im := by
  simp only [Admissible, shiftBeta_tau, shiftBeta_discriminant]
  constructor <;> rintro ⟨hτ, hD⟩ <;> exact ⟨hτ, by linarith⟩

/-- Constant shifts preserve the cusp transformation equation. -/
@[simp] theorem shiftBeta_step₀ (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).step₀ = p.step₀.shiftBeta c := by
  apply PeriodPoint.ext <;> simp [step₀, shiftBeta]
  ring

/-- Constant shifts preserve the order-three transformation equation. -/
@[simp] theorem shiftBeta_step₁ (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).step₁ = p.step₁.shiftBeta c := by
  apply PeriodPoint.ext <;> simp [step₁, shiftBeta]
  ring

/-- Constant shifts preserve the order-four transformation equation. -/
@[simp] theorem shiftBeta_step₂ (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).step₂ = p.step₂.shiftBeta c := by
  apply PeriodPoint.ext <;> simp [step₂, shiftBeta]
  ring

/-- An upper bound on the discriminants gives one threshold that works for
every point and for every constant below that threshold. -/
theorem exists_uniform_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im)
    (hD : BddAbove (range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z, ((P z).shiftBeta c).Admissible := by
  obtain ⟨C, hC⟩ := hD
  refine ⟨max C 0, le_max_right _ _, fun c hc z => ⟨hτ z, ?_⟩⟩
  rw [shiftBeta_discriminant]
  have hDz : (P z).discriminant ≤ C := hC (mem_range_self z)
  have hCM : C ≤ max C 0 := le_max_left _ _
  linarith

/-- In particular a purely imaginary, negative constant can always be chosen. -/
theorem exists_negative_imaginary_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im)
    (hD : BddAbove (range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 < M ∧ ∀ z, ((P z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible := by
  obtain ⟨M, hM, hshift⟩ := exists_uniform_shift_of_bddAbove P hτ hD
  refine ⟨M + 1, by linarith, hshift _ ?_⟩
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
  linarith

end PeriodPoint

namespace SpecialPeriods

/-- Negative divergence at a puncture puts the nonnegative part of a function
inside a compact set disjoint from that puncture. -/
theorem exists_compact_cutoff_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ) (hf : Tendsto f (𝓝[≠] p) atBot) :
    ∃ K : Set B, IsCompact K ∧ K ⊆ ({p} : Set B)ᶜ ∧
      ∀ x : B, x ∈ ({p} : Set B)ᶜ → x ∉ K → f x < 0 := by
  obtain ⟨U, hU, hpU, hUf⟩ := mem_nhdsWithin.mp (hf.eventually_lt_atBot 0)
  refine ⟨Uᶜ, hU.isClosed_compl.isCompact, ?_, ?_⟩
  · intro x hx hp
    have hxp : x = p := by simpa only [mem_singleton_iff] using hp
    exact hx (hxp ▸ hpU)
  · intro x hxp hx
    exact hUf ⟨not_not.mp hx, hxp⟩

/-- Compactness away from the puncture and the negative cusp limit give a
global upper bound; boundedness is a conclusion, not an assumption. -/
theorem bddAbove_image_punctured_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ)
    (hc : ContinuousOn f ({p} : Set B)ᶜ) (hf : Tendsto f (𝓝[≠] p) atBot) :
    BddAbove (f '' ({p} : Set B)ᶜ) := by
  obtain ⟨K, hK, hKp, hneg⟩ := exists_compact_cutoff_of_tendsto_atBot p f hf
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.mono hKp)
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxK : x ∈ K
  · exact (hC (mem_image_of_mem f hxK)).trans (le_max_left _ _)
  · exact (hneg x hx hxK).le.trans (le_max_right _ _)

/-- Transfer the cusp estimate through an actual parametrization whose image
contains a punctured neighbourhood.  Surjectivity onto the whole base is not
needed, so the parametrization may be a single distinguished cusp component. -/
theorem tendsto_descended_discriminant_atBot {B X : Type*} [TopologicalSpace B]
    (p : B) (π : X → B) (P : X → PeriodPoint) (d : B → ℝ)
    (hπ : range π ∈ 𝓝[≠] p)
    (hd : ∀ z, d (π z) = (P z).discriminant)
    (hτ : ∀ᶠ z in comap π (𝓝[≠] p), 0 < (P z).τ.im)
    (hτinf : Tendsto (fun z => (P z).τ.im) (comap π (𝓝[≠] p)) atTop)
    (hb : ∃ C : ℝ, ∀ᶠ z in comap π (𝓝[≠] p), ((P z).β + (P z).τ).im ≤ C) :
    Tendsto d (𝓝[≠] p) atBot := by
  apply (tendsto_comap'_iff hπ).mp
  simpa only [Function.comp_def, hd] using PeriodPoint.tendsto_discriminant_atBot P hτ hτinf hb

/-- The bounded discriminant conclusion of Proposition 3.15, for continuous
data genuinely descended to a compactified base. -/
theorem bddAbove_discriminant_of_compact_descent {B X : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (π : X → B) (P : X → PeriodPoint) (d : B → ℝ)
    (hπ : ∀ z, π z ≠ p) (hd : ∀ z, d (π z) = (P z).discriminant)
    (hc : ContinuousOn d ({p} : Set B)ᶜ) (hlim : Tendsto d (𝓝[≠] p) atBot) :
    BddAbove (range fun z => (P z).discriminant) := by
  apply (bddAbove_image_punctured_of_tendsto_atBot p d hc hlim).mono
  rintro _ ⟨z, rfl⟩
  exact ⟨π z, hπ z, hd z⟩

/-- A single imaginary threshold makes all periods over the punctured compact
base admissible.  The negative cusp limit is the only asymptotic input. -/
theorem exists_uniform_admissible_shift_of_compact_descent {B X : Type*}
    [TopologicalSpace B] [CompactSpace B]
    (p : B) (π : X → B) (P : X → PeriodPoint) (d : B → ℝ)
    (hπ : ∀ z, π z ≠ p) (hd : ∀ z, d (π z) = (P z).discriminant)
    (hc : ContinuousOn d ({p} : Set B)ᶜ) (hlim : Tendsto d (𝓝[≠] p) atBot)
    (hτ : ∀ z, 0 < (P z).τ.im) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z, ((P z).shiftBeta c).Admissible :=
  PeriodPoint.exists_uniform_shift_of_bddAbove P hτ
    (bddAbove_discriminant_of_compact_descent p π P d hπ hd hc hlim)

/-- Combine the cusp bound with compact descent.  The cusp parametrization
need only cover a punctured neighbourhood, and may be a distinguished
component upstairs; no global upper bound or negative discriminant is assumed. -/
theorem exists_uniform_admissible_shift_of_cusp {B X U : Type*}
    [TopologicalSpace B] [CompactSpace B]
    (p : B) (π : X → B) (P : X → PeriodPoint) (d : B → ℝ) (cusp : U → X)
    (hπ : ∀ z, π z ≠ p) (hd : ∀ z, d (π z) = (P z).discriminant)
    (hc : ContinuousOn d ({p} : Set B)ᶜ) (hτ : ∀ z, 0 < (P z).τ.im)
    (hcover : range (π ∘ cusp) ∈ 𝓝[≠] p)
    (hτinf : Tendsto (fun z => (P (cusp z)).τ.im) (comap (π ∘ cusp) (𝓝[≠] p)) atTop)
    (hb : ∃ C : ℝ, ∀ᶠ z in comap (π ∘ cusp) (𝓝[≠] p),
      ((P (cusp z)).β + (P (cusp z)).τ).im ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z, ((P z).shiftBeta c).Admissible := by
  apply exists_uniform_admissible_shift_of_compact_descent p π P d hπ hd hc _ hτ
  exact tendsto_descended_discriminant_atBot p (π ∘ cusp) (P ∘ cusp) d hcover
    (fun z => hd (cusp z)) (Eventually.of_forall fun z => hτ (cusp z)) hτinf hb

end SpecialPeriods

end Wikipedia.HopfProblem
