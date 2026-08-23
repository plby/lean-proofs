/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.BakerIntegralExtrapolation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational-grid extrapolation in van der Poorten--Loxton Lemma 5

This file isolates the arithmetic and logical core of Lemma 5 on pp. 48--50
of van der Poorten and Loxton.  The interpolation nodes are the integers
`1, ..., R`, whereas the new evaluation points are `l / q`.

There are two genuinely different cases.  If `q ∣ l`, then `l / q` is one
of the already controlled integral nodes.  If `q ∤ l`, every distance from
`l / q` to an integral node is at least `1 / q`; this gives the exact
denominator/product bound used in the rational interpolation formula.  Once
the interpolation estimate makes the auxiliary value strictly smaller than
its Liouville lower bound, the latter case also forces vanishing.

The quantitative analytic estimate itself is deliberately an input to
`vdpl_lemma5_of_interpolation_lt_lower`: it is supplied by the Hermite
interpolation and product-estimate layer, while this theorem performs the
source's `q ∣ l` split without any loss in the derivative budget.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerRationalExtrapolation

open Finset

/-- Quantitative Hermite-interpolation data at one nonintegral rational
target.  Every field is one of the explicit estimates verified in the proof
of source Lemma 5: boundary control, containment of the interpolation nodes,
control of the Newton--Hermite polynomial at the target, and the final strict
budget against the Liouville lower bound. -/
structure RationalInterpolationCertificate
    (f : ℂ → ℂ) (z : ℂ) (lower : ℝ) where
  nodes : List ℂ
  center : ℂ
  radius : ℝ
  boundaryBound : ℝ
  polynomialBound : ℝ
  differentiable : Differentiable ℂ f
  radius_pos : 0 < radius
  target_mem : z ∈ Metric.ball center radius
  boundaryBound_nonneg : 0 ≤ boundaryBound
  nodes_mem : ∀ a ∈ nodes, a ∈ Metric.ball center radius
  boundary : ∀ w ∈ Metric.sphere center radius,
    ‖f w - (HermiteInterpolation.polynomial f nodes).eval w‖ /
        HermiteInterpolation.nodeProductNorm nodes w ≤ boundaryBound
  polynomial_target :
    ‖(HermiteInterpolation.polynomial f nodes).eval z‖ ≤ polynomialBound
  strict_budget :
    polynomialBound + HermiteInterpolation.nodeProductNorm nodes z *
      (radius * (boundaryBound / (radius - dist z center))) < lower

namespace RationalInterpolationCertificate

/-- A completed rational interpolation estimate contradicts the nonzero
branch of the Liouville alternative. -/
theorem force_zero {f g : ℂ → ℂ} {z : ℂ} {lower : ℝ}
    (D : RationalInterpolationCertificate f z lower)
    (hliouville : g z = 0 ∨ lower ≤ ‖f z‖) :
    g z = 0 := by
  exact BakerIntegralExtrapolation.vdpl_integral_extrapolation_step
    D.differentiable D.nodes D.radius_pos D.target_mem
    D.boundaryBound_nonneg D.nodes_mem D.boundary D.polynomial_target
    D.strict_budget hliouville

end RationalInterpolationCertificate

/-- The product over the integral interpolation nodes `1, ..., R`. -/
def integerNodeProduct (R : ℕ) (z : ℂ) : ℂ :=
  ∏ r ∈ Finset.range R, (z - (r + 1 : ℕ))

@[simp] theorem integerNodeProduct_zero (z : ℂ) :
    integerNodeProduct 0 z = 1 := by
  simp [integerNodeProduct]

theorem integerNodeProduct_succ (R : ℕ) (z : ℂ) :
    integerNodeProduct (R + 1) z =
      integerNodeProduct R z * (z - (R + 1 : ℕ)) := by
  simp [integerNodeProduct, Finset.prod_range_succ]

/-- Exact simultaneous denominator clearing at the rational point `l/q`.
The right side is visibly the cast of an integer product. -/
theorem pow_mul_integerNodeProduct_div_eq_product
    (R q l : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ R * integerNodeProduct R ((l : ℂ) / (q : ℂ)) =
      ∏ r ∈ Finset.range R,
        ((l : ℂ) - (q : ℂ) * ((r + 1 : ℕ) : ℂ)) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [integerNodeProduct]
  calc
    (q : ℂ) ^ R *
          ∏ r ∈ Finset.range R,
            ((l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)) =
        (∏ _r ∈ Finset.range R, (q : ℂ)) *
          ∏ r ∈ Finset.range R,
            ((l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)) := by simp
    _ = ∏ r ∈ Finset.range R,
        (q : ℂ) *
          ((l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro r hr
      field_simp [hqC]

/-- A nonintegral point `l / q` is separated from every integral node by at
least `1 / q`.  This is the elementary denominator estimate behind the
rational interpolation in source Lemma 5. -/
theorem one_div_le_norm_rational_sub_nat
    {q l r : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l) :
    1 / (q : ℝ) ≤
      ‖(l : ℂ) / (q : ℂ) - (r : ℂ)‖ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  let a : ℤ := (l : ℤ) - (q : ℤ) * (r : ℤ)
  have ha : a ≠ 0 := by
    intro ha0
    apply hnmid
    have hz : (l : ℤ) = (q : ℤ) * (r : ℤ) := by
      dsimp [a] at ha0
      omega
    exact ⟨r, by exact_mod_cast hz⟩
  have haone : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha
  have hfrac :
      (l : ℂ) / (q : ℂ) - (r : ℂ) = (a : ℂ) / (q : ℂ) := by
    dsimp [a]
    push_cast
    field_simp [hqC]
  have hrewrite :
      ‖(l : ℂ) / (q : ℂ) - (r : ℂ)‖ =
        |(a : ℝ)| / (q : ℝ) := by
    rw [hfrac, norm_div]
    simp only [Complex.norm_intCast, Complex.norm_natCast]
  rw [hrewrite]
  exact (div_le_div_iff_of_pos_right hqR).2 haone

/-- If `0 ≤ l/q ≤ R`, its distance from each of the nodes `1, ..., R`
is at most `R`. -/
theorem norm_rational_sub_node_le
    {q l R r : ℕ} (hq : 0 < q) (hlR : l ≤ q * R) (hr : r < R) :
    ‖(l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)‖ ≤ (R : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : (0 : ℝ) ≤ (l : ℝ) / (q : ℝ) := by positivity
  have hxR : (l : ℝ) / (q : ℝ) ≤ R := by
    rw [div_le_iff₀ hqR]
    exact_mod_cast (by simpa [mul_comm] using hlR)
  have hr0 : (0 : ℝ) ≤ (r + 1 : ℕ) := by positivity
  have hrR : ((r + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hr
  have habs :
      |(l : ℝ) / (q : ℝ) - ((r + 1 : ℕ) : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hcast :
      (l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ) =
        (((l : ℝ) / (q : ℝ) - ((r + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real]
  exact habs

/-- On the source's outer circle `‖z‖ ≥ 3R`, every integral node is at
distance at least `2R`. -/
theorem two_mul_le_norm_sub_node_of_three_mul_le_norm
    {R r : ℕ} {z : ℂ} (hr : r < R) (hz : 3 * (R : ℝ) ≤ ‖z‖) :
    2 * (R : ℝ) ≤ ‖z - ((r + 1 : ℕ) : ℂ)‖ := by
  have hrR : ((r + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hr
  have hrev :
      ‖z‖ - ‖((r + 1 : ℕ) : ℂ)‖ ≤
        ‖z - ((r + 1 : ℕ) : ℂ)‖ := norm_sub_norm_le z _
  simp only [Complex.norm_natCast] at hrev
  linarith

/-- Outer-circle nodal-product estimate from Lemma 5.  Factorwise the target
distance is at most `R`, whereas the boundary distance is at least `2R`.
Thus the complete quotient decays as `2^{-R}`. -/
theorem norm_integerNodeProduct_div_le_two_inv_pow
    {q l R : ℕ} (hq : 0 < q) (hR : 0 < R) (hlR : l ≤ q * R)
    {z : ℂ} (hz : 3 * (R : ℝ) ≤ ‖z‖) :
    ‖integerNodeProduct R ((l : ℂ) / (q : ℂ)) /
        integerNodeProduct R z‖ ≤ (1 / 2 : ℝ) ^ R := by
  simp only [integerNodeProduct, ← Finset.prod_div_distrib, norm_prod, norm_div]
  have hprod :
      (∏ r ∈ Finset.range R,
          ‖(l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)‖ /
            ‖z - ((r + 1 : ℕ) : ℂ)‖) ≤
        ∏ _r ∈ Finset.range R, (1 / 2 : ℝ) := by
    apply Finset.prod_le_prod
      (fun _ _ ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))
    intro r hrmem
    have hr : r < R := Finset.mem_range.mp hrmem
    have hnum := norm_rational_sub_node_le hq hlR hr
    have hden := two_mul_le_norm_sub_node_of_three_mul_le_norm hr hz
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
    have hdenpos : 0 < ‖z - ((r + 1 : ℕ) : ℂ)‖ :=
      (mul_pos (by norm_num) hR0).trans_le hden
    rw [div_le_iff₀ hdenpos]
    nlinarith
  simpa using hprod

/-- Hermite-multiplicity form of the outer-circle product estimate. -/
theorem norm_integerNodeProduct_div_pow_le_two_inv_pow_mul
    {q l R T : ℕ} (hq : 0 < q) (hR : 0 < R) (hlR : l ≤ q * R)
    {z : ℂ} (hz : 3 * (R : ℝ) ≤ ‖z‖) :
    ‖(integerNodeProduct R ((l : ℂ) / (q : ℂ)) /
        integerNodeProduct R z) ^ T‖ ≤ (1 / 2 : ℝ) ^ (R * T) := by
  rw [norm_pow, pow_mul]
  exact pow_le_pow_left₀ (by positivity)
    (norm_integerNodeProduct_div_le_two_inv_pow hq hR hlR hz) T

/-- The complete nodal product has denominator at most `q^R` at a
nonintegral rational point.  Unlike a crude factorial estimate, this bound
does not introduce an extra `log R` in the Baker exponent. -/
theorem one_div_pow_le_norm_integerNodeProduct
    {q l R : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l) :
    (1 / (q : ℝ)) ^ R ≤
      ‖integerNodeProduct R ((l : ℂ) / (q : ℂ))‖ := by
  rw [integerNodeProduct, norm_prod]
  have hprod :
      ∏ _r ∈ Finset.range R, (1 / (q : ℝ)) ≤
        ∏ r ∈ Finset.range R,
          ‖(l : ℂ) / (q : ℂ) - ((r + 1 : ℕ) : ℂ)‖ := by
    exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun r _ ↦
      one_div_le_norm_rational_sub_nat hq hnmid
  simpa using hprod

/-- Powered form of the rational denominator bound.  Repetition of every
node `T` times is how Hermite multiplicities are encoded in Lemma 5. -/
theorem one_div_pow_mul_le_norm_integerNodeProduct_pow
    {q l R T : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l) :
    (1 / (q : ℝ)) ^ (R * T) ≤
      ‖(integerNodeProduct R ((l : ℂ) / (q : ℂ))) ^ T‖ := by
  rw [norm_pow, pow_mul]
  exact pow_le_pow_left₀ (by positivity)
    (one_div_pow_le_norm_integerNodeProduct hq hnmid) T

/-- In particular, the rational nodal product does not vanish unless `l/q`
is an integer. -/
theorem integerNodeProduct_ne_zero
    {q l R : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l) :
    integerNodeProduct R ((l : ℂ) / (q : ℂ)) ≠ 0 := by
  intro hzero
  have hlower := one_div_pow_le_norm_integerNodeProduct
    (R := R) hq hnmid
  rw [hzero, norm_zero] at hlower
  have : 0 < (1 / (q : ℝ)) ^ R := by positivity
  linarith

/-- Arithmetic part of the `q ∣ l` branch: a rational grid point whose
numerator is divisible by `q` is exactly an integral grid point, still
inside the same radius. -/
theorem integral_grid_of_dvd
    {n q R S l : ℕ} {G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hl : 1 ≤ l) (hlR : l ≤ R) (hdiv : q ∣ l)
    (hint : VanishesOn G 1 R S) :
    ∀ m, VDPLMultiIndex.weight m ≤ S →
      G ((l : ℂ) / (q : ℂ)) m = 0 := by
  intro m hm
  have hqle : q ≤ l := Nat.le_of_dvd (Nat.zero_lt_of_lt hl) hdiv
  have hquotPos : 0 < l / q := Nat.div_pos hqle hq
  have hquotR : l / q ≤ R := (Nat.div_le_self l q).trans hlR
  have hz := hint (l / q) hquotPos hquotR m hm
  simp only [Nat.cast_one, div_one] at hz
  rwa [Nat.cast_div hdiv (by exact_mod_cast hq.ne')] at hz

/-- Abstract, checked form of source Lemma 5.

For the nondivisible rational nodes, `hupper` is precisely the strict upper
bound delivered by Hermite interpolation and the nodal-product estimates;
`hlower` is the rational Liouville alternative of source Lemma 3.  At
divisible nodes the conclusion follows directly from the integral
extrapolation, as in the last sentence of the source proof. -/
theorem vdpl_lemma5_of_interpolation_lt_lower
    {n q R S : ℕ} {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (lower : ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 R S)
    (hupper : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ‖F ((l : ℂ) / (q : ℂ)) m‖ < lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q R S := by
  intro l hl hlR m hm
  by_cases hdiv : q ∣ l
  · exact integral_grid_of_dvd hq hl hlR hdiv hint m hm
  · rcases hlower l hl hlR m hm with hzero | hlow
    · exact hzero
    · exact False.elim ((not_lt_of_ge hlow) (hupper l hl hlR hdiv m hm))

/-- Source Lemma 5 with the Hermite interpolation step exposed in full.
For every nonintegral target the caller supplies the concrete contours and
bounds in a `RationalInterpolationCertificate`; this theorem combines those
analytic estimates with the integral-node case and the rational Liouville
alternative. -/
theorem vdpl_lemma5_of_interpolation_certificates
    {n q R S : ℕ} {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (lower : ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 R S)
    (hcertificate : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        RationalInterpolationCertificate (fun z ↦ F z m)
          ((l : ℂ) / (q : ℂ)) (lower l m))
    (hliouville : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q R S := by
  intro l hl hlR m hm
  by_cases hdiv : q ∣ l
  · exact integral_grid_of_dvd hq hl hlR hdiv hint m hm
  · exact RationalInterpolationCertificate.force_zero
      (g := fun z ↦ G z m) (hcertificate l hl hlR hdiv m hm)
      (hliouville l hl hlR m hm)

/-- Parameterized source-shaped interface for Lemma 5.  The level condition
is used earlier to establish `hupper`; once that quantitative estimate is in
hand, this implication needs only positivity of the fixed auxiliary prime. -/
theorem vdpl_lemma5
    {ι : Type*} [Fintype ι]
    (P : VDPLParameters ι) (N : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hint : VanishesOn G 1 (P.R (N + 1)) (P.Sstep N))
    (hupper : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖F ((l : ℂ) / (P.q : ℂ)) m‖ < lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        G ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (P.q : ℂ)) m‖) :
    VanishesOn G P.q (P.R (N + 1)) (P.Sstep N) := by
  exact vdpl_lemma5_of_interpolation_lt_lower
    (Nat.zero_lt_of_lt P.one_lt_q) lower hint hupper hlower

/-- The source ultimately keeps the smaller next-level derivative budget.
This wrapper combines Lemma 5 with the checked parameter inequality
`Slevel (N+1) ≤ Sstep N`. -/
theorem vdpl_lemma5_nextLevel
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) (N : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hint : VanishesOn G 1 (P.R (N + 1)) (P.Sstep N))
    (hupper : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖F ((l : ℂ) / (P.q : ℂ)) m‖ < lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        G ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (P.q : ℂ)) m‖) :
    VanishesOn G P.q (P.R (N + 1)) (P.Slevel (N + 1)) := by
  have hall : VanishesOn G P.q (P.R (N + 1)) (P.Sstep N) :=
    vdpl_lemma5 P N lower hint hupper hlower
  exact hall.mono le_rfl (P.Slevel_succ_le_Sstep N)

end Erdos240.BakerRationalExtrapolation

#print axioms Erdos240.BakerRationalExtrapolation.norm_integerNodeProduct_div_pow_le_two_inv_pow_mul
#print axioms Erdos240.BakerRationalExtrapolation.vdpl_lemma5_of_interpolation_certificates
#print axioms Erdos240.BakerRationalExtrapolation.vdpl_lemma5_nextLevel
