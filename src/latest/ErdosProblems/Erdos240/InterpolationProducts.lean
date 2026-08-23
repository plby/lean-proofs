import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import ErdosProblems.Erdos240.HermiteInterpolation

/-!
# Product estimates for the van der Poorten--Loxton interpolation steps

The Hermite interpolation arguments in Lemmas 4 and 5 of van der
Poorten--Loxton use the polynomial

`((z - 1) * ... * (z - R)) ^ S`.

This file records its list of repeated nodes, its exact finite-product form,
and the numerator/denominator estimates which are independent of the
analytic interpolation formula.  The estimates are deliberately stated over
an arbitrary normed field whenever no specifically complex fact is needed.
-/

open scoped BigOperators

open Finset

noncomputable section

namespace Erdos240.InterpolationProducts

/-- The integral nodes `1, ..., R`, each repeated `S` times. -/
def integralNodes (R S : ℕ) : List ℂ :=
  (List.range R).flatMap fun i => List.replicate S (i + 1 : ℕ)

/-- The nodal product for the integral nodes `1, ..., R`, each with multiplicity `S`. -/
def integralNodalProduct (R S : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ range R, (z - (i + 1 : ℕ)) ^ S

@[simp] theorem length_integralNodes (R S : ℕ) :
    (integralNodes R S).length = R * S := by
  simp [integralNodes]

theorem map_sub_prod_integralNodes (R S : ℕ) (z : ℂ) :
    ((integralNodes R S).map fun a => z - a).prod = integralNodalProduct R S z := by
  induction R with
  | zero => simp [integralNodes, integralNodalProduct]
  | succ R ih =>
      rw [integralNodes, List.range_succ, List.flatMap_append, List.map_append,
        List.prod_append, integralNodalProduct, prod_range_succ]
      simp only [List.flatMap_singleton, List.map_replicate, List.prod_replicate,
        Nat.cast_add, Nat.cast_one]
      convert congrArg (fun w : ℂ => w * (z - (R + 1 : ℕ)) ^ S) ih using 1 <;>
        simp only [integralNodes, integralNodalProduct, Nat.cast_add, Nat.cast_one]

/-- Bridge from the repeated-node list to the nodal product used by the
finite Hermite interpolation formula. -/
theorem hermite_nodeProduct_integralNodes (R S : ℕ) (z : ℂ) :
    HermiteInterpolation.nodeProduct (integralNodes R S) z =
      integralNodalProduct R S z := by
  exact map_sub_prod_integralNodes R S z

@[simp] theorem integralNodalProduct_zero_left (S : ℕ) (z : ℂ) :
    integralNodalProduct 0 S z = 1 := by
  simp [integralNodalProduct]

@[simp] theorem integralNodalProduct_zero_multiplicity (R : ℕ) (z : ℂ) :
    integralNodalProduct R 0 z = 1 := by
  simp [integralNodalProduct]

theorem integralNodalProduct_eq_base_pow (R S : ℕ) (z : ℂ) :
    integralNodalProduct R S z =
      (∏ i ∈ range R, (z - (i + 1 : ℕ))) ^ S := by
  simp [integralNodalProduct, prod_pow]

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- A uniform upper bound for each factor bounds the whole repeated nodal product. -/
theorem norm_prod_pow_le_pow {s : Finset ℕ} {f : ℕ → 𝕜} {A : ℝ} (S : ℕ)
    (_hA : 0 ≤ A) (hf : ∀ i ∈ s, ‖f i‖ ≤ A) :
    ‖∏ i ∈ s, (f i) ^ S‖ ≤ A ^ (s.card * S) := by
  rw [norm_prod]
  calc
    ∏ i ∈ s, ‖f i ^ S‖ ≤ ∏ _i ∈ s, A ^ S := by
      apply prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hf i hi) S
    _ = A ^ (s.card * S) := by simp [← pow_mul, mul_comm]

/-- A uniform positive lower bound for each factor bounds the whole repeated nodal product below. -/
theorem pow_card_le_norm_prod_pow {s : Finset ℕ} {f : ℕ → 𝕜} {B : ℝ} (S : ℕ)
    (hB : 0 ≤ B) (hf : ∀ i ∈ s, B ≤ ‖f i‖) :
    B ^ (s.card * S) ≤ ‖∏ i ∈ s, (f i) ^ S‖ := by
  rw [norm_prod]
  calc
    B ^ (s.card * S) = ∏ _i ∈ s, B ^ S := by simp [← pow_mul, mul_comm]
    _ ≤ ∏ i ∈ s, ‖f i ^ S‖ := by
      apply prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        simpa only [norm_pow] using pow_le_pow_left₀ hB (hf i hi) S

/-- The basic interpolation quotient estimate.  It is the finite-product
form used both at integral target points and at the rational points `l/q`. -/
theorem norm_prod_pow_div_prod_pow_le {s : Finset ℕ} {f g : ℕ → 𝕜}
    {A B : ℝ} (S : ℕ) (hA : 0 ≤ A) (hB : 0 < B)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ A) (hg : ∀ i ∈ s, B ≤ ‖g i‖) :
    ‖(∏ i ∈ s, (f i) ^ S) / ∏ i ∈ s, (g i) ^ S‖
      ≤ (A / B) ^ (s.card * S) := by
  rw [norm_div]
  have hnum := norm_prod_pow_le_pow S hA hf
  have hden := pow_card_le_norm_prod_pow S hB.le hg
  have hBpow : 0 < B ^ (s.card * S) := pow_pos hB _
  calc
    ‖∏ i ∈ s, f i ^ S‖ / ‖∏ i ∈ s, g i ^ S‖
        ≤ A ^ (s.card * S) / B ^ (s.card * S) := by
          exact div_le_div₀ (pow_nonneg hA _) hnum hBpow hden
    _ = (A / B) ^ (s.card * S) := by rw [div_pow]

end NormedField

/-- Uniform quotient estimate specialized to the consecutive integral nodes. -/
theorem norm_integralNodalProduct_div_le {R S : ℕ} {x z : ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B)
    (hx : ∀ i < R, ‖x - (i + 1 : ℕ)‖ ≤ A)
    (hz : ∀ i < R, B ≤ ‖z - (i + 1 : ℕ)‖) :
    ‖integralNodalProduct R S x / integralNodalProduct R S z‖
      ≤ (A / B) ^ (R * S) := by
  simpa only [integralNodalProduct, card_range] using
    norm_prod_pow_div_prod_pow_le (𝕜 := ℂ) (s := range R)
      (f := fun i => x - (i + 1 : ℕ)) (g := fun i => z - (i + 1 : ℕ))
      S hA hB (by simpa using hx) (by simpa using hz)

/-- Every integer node lies in the closed real interval `[1,R]`. -/
theorem norm_natCast_sub_natCast_le {l r R : ℕ} (hl : l ≤ R) (hr : r ≤ R) :
    ‖(l : ℂ) - (r : ℂ)‖ ≤ R := by
  have hl' : (l : ℝ) ≤ R := by exact_mod_cast hl
  have hr' : (r : ℝ) ≤ R := by exact_mod_cast hr
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  change ‖((l : ℝ) : ℂ) - ((r : ℝ) : ℂ)‖ ≤ (R : ℝ)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A rational point `l/q` in `[0,R]` is at distance at most `R` from every
integral node in `[1,R]`. -/
theorem norm_ratCast_sub_natCast_le {l q R r : ℕ} (hq : 0 < q)
    (hl : l ≤ q * R) (hr : r ≤ R) :
    ‖((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) - (r : ℂ)‖ ≤ R := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hl' : (l : ℝ) ≤ q * R := by exact_mod_cast hl
  have hr' : (r : ℝ) ≤ R := by exact_mod_cast hr
  have hx0 : (0 : ℝ) ≤ (l : ℝ) / q := div_nonneg (by positivity) hq'.le
  have hxR : (l : ℝ) / q ≤ R := (div_le_iff₀ hq').2 (by simpa [mul_comm] using hl')
  have hr0 : (0 : ℝ) ≤ r := by positivity
  rw [show ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) = (((l : ℝ) / q : ℝ) : ℂ) by
      norm_num,
    show (r : ℂ) = ((r : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The decreasing product `m * (m-1) * ... * 1`, cast to `ℝ`, is `m!`. -/
theorem prod_range_cast_sub_eq_factorial (m : ℕ) :
    (∏ i ∈ range m, ((m - i : ℕ) : ℝ)) = (m.factorial : ℝ) := by
  norm_cast
  simpa [Nat.descFactorial_eq_prod_range] using Nat.descFactorial_self m

/-- The increasing product `1 * ... * m`, cast to `ℝ`, is `m!`. -/
theorem prod_range_cast_add_one_eq_factorial (m : ℕ) :
    (∏ i ∈ range m, ((i + 1 : ℕ) : ℝ)) = (m.factorial : ℝ) := by
  exact_mod_cast prod_range_add_one_eq_factorial m

/-- Splitting at an integer `m` gives the factorial estimate for the
consecutive-node product.  This is the elementary product estimate behind
the factorial gain in both interpolation arguments. -/
theorem abs_prod_range_sub_le_factorial_mul_factorial {x : ℝ} {m R : ℕ}
    (hm : (m : ℝ) ≤ x) (hx : x ≤ m + 1) (hmR : m ≤ R) :
    (∏ i ∈ range R, |x - (i + 1 : ℕ)|)
      ≤ (m.factorial : ℝ) * ((R - m).factorial : ℝ) := by
  conv_lhs => rw [show R = m + (R - m) by omega]
  rw [prod_range_add]
  apply mul_le_mul
  · calc
      (∏ i ∈ range m, |x - (i + 1 : ℕ)|)
          ≤ ∏ i ∈ range m, ((m - i : ℕ) : ℝ) := by
            apply prod_le_prod
            · intro i hi
              positivity
            · intro i hi
              have hi' : i < m := mem_range.mp hi
              have hir : ((i + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hi')
              rw [abs_of_nonneg (sub_nonneg.mpr (hir.trans hm))]
              rw [Nat.cast_sub hi'.le]
              push_cast
              linarith
      _ = (m.factorial : ℝ) := prod_range_cast_sub_eq_factorial m
  · calc
      (∏ i ∈ range (R - m), |x - ((m + i) + 1 : ℕ)|)
          ≤ ∏ i ∈ range (R - m), ((i + 1 : ℕ) : ℝ) := by
            apply prod_le_prod
            · intro i hi
              positivity
            · intro i hi
              have hnode : x ≤ (((m + i) + 1 : ℕ) : ℝ) := by
                push_cast
                linarith
              rw [abs_of_nonpos (sub_nonpos.mpr hnode)]
              push_cast
              linarith
      _ = ((R - m).factorial : ℝ) := prod_range_cast_add_one_eq_factorial (R - m)
  · positivity
  · positivity

/-- The two factorial pieces obtained by splitting the nodes never exceed
the full factorial. -/
theorem factorial_mul_factorial_sub_le_factorial {m R : ℕ} (hmR : m ≤ R) :
    (m.factorial : ℝ) * ((R - m).factorial : ℝ) ≤ (R.factorial : ℝ) := by
  exact_mod_cast Nat.le_of_dvd R.factorial_pos ⟨R.choose m, by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.choose_mul_factorial_mul_factorial hmR).symm⟩

/-- On the whole real interval `[0,R]`, the absolute nodal product is at
most `R!`.  An explicit integer `m` locating `x` in `[m,m+1]` is retained so
the lemma applies directly to `m = l / q` in Lemma 5. -/
theorem abs_prod_range_sub_le_factorial {x : ℝ} {m R : ℕ}
    (hm : (m : ℝ) ≤ x) (hx : x ≤ m + 1) (hmR : m ≤ R) :
    (∏ i ∈ range R, |x - (i + 1 : ℕ)|) ≤ (R.factorial : ℝ) :=
  (abs_prod_range_sub_le_factorial_mul_factorial hm hx hmR).trans
    (factorial_mul_factorial_sub_le_factorial hmR)

/-- The unpowered complex nodal product inherits the real factorial bound. -/
theorem norm_integralNodalProduct_one_ofReal_le_factorial {x : ℝ} {m R : ℕ}
    (hm : (m : ℝ) ≤ x) (hx : x ≤ m + 1) (hmR : m ≤ R) :
    ‖integralNodalProduct R 1 (x : ℂ)‖ ≤ (R.factorial : ℝ) := by
  rw [integralNodalProduct, norm_prod]
  simpa only [pow_one, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using
    abs_prod_range_sub_le_factorial hm hx hmR

/-- Factorial numerator bound with arbitrary Hermite multiplicity. -/
theorem norm_integralNodalProduct_ofReal_le_factorial_pow {x : ℝ} {m R S : ℕ}
    (hm : (m : ℝ) ≤ x) (hx : x ≤ m + 1) (hmR : m ≤ R) :
    ‖integralNodalProduct R S (x : ℂ)‖ ≤ (R.factorial : ℝ) ^ S := by
  calc
    ‖integralNodalProduct R S (x : ℂ)‖ =
        ‖integralNodalProduct R 1 (x : ℂ)‖ ^ S := by
          rw [integralNodalProduct_eq_base_pow, integralNodalProduct_eq_base_pow, norm_pow]
          simp
    _ ≤ (R.factorial : ℝ) ^ S := pow_le_pow_left₀ (norm_nonneg _)
      (norm_integralNodalProduct_one_ofReal_le_factorial hm hx hmR) S

/-- For the rational point `l/q` in `[0,R]`, choose the locating integer
`m = l / q` and obtain the source's factorial numerator estimate. -/
theorem norm_integralNodalProduct_ratCast_le_factorial_pow
    {l q R S : ℕ} (hq : 0 < q) (hl : l ≤ q * R) :
    ‖integralNodalProduct R S ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ)‖
      ≤ (R.factorial : ℝ) ^ S := by
  let m := l / q
  have hmR : m ≤ R := Nat.div_le_of_le_mul (by simpa [mul_comm] using hl)
  have hml : (m : ℝ) ≤ (l : ℝ) / q := by
    rw [le_div_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq)]
    exact_mod_cast Nat.div_mul_le_self l q
  have hlm : (l : ℝ) / q ≤ m + 1 := by
    rw [div_le_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq)]
    have hn : l ≤ (m + 1) * q := by
      have h := Nat.lt_div_mul_add (a := l) hq
      dsimp [m]
      calc
        l ≤ l / q * q + q := h.le
        _ = (l / q + 1) * q := by simp [add_mul]
    exact_mod_cast hn
  rw [show ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) = (((l : ℝ) / q : ℝ) : ℂ) by
    norm_num]
  exact norm_integralNodalProduct_ofReal_le_factorial_pow hml hlm hmR

/-- On the circle `‖z‖ = 3R`, every factor belonging to a node in
`[1,R]` has norm at least `2R`. -/
theorem two_mul_le_norm_sub_natCast_of_norm_eq_three_mul {R r : ℕ} {z : ℂ}
    (hr : r ≤ R) (hz : ‖z‖ = 3 * R) :
    2 * R ≤ ‖z - (r : ℂ)‖ := by
  have hr' : (r : ℝ) ≤ R := by exact_mod_cast hr
  calc
    2 * (R : ℝ) ≤ 3 * (R : ℝ) - (r : ℝ) := by linarith
    _ = ‖z‖ - ‖(r : ℂ)‖ := by simp [hz]
    _ ≤ ‖z - (r : ℂ)‖ := norm_sub_norm_le _ _

/-- Source-style outer-circle estimate for an integral target in `[1,R]`.
The exponent `R*S` is exactly the degree of the nodal product. -/
theorem norm_integralNodalProduct_natCast_div_outerCircle_le {R S l : ℕ} {z : ℂ}
    (hR : 0 < R) (hl : l ≤ R) (hz : ‖z‖ = 3 * R) :
    ‖integralNodalProduct R S (l : ℂ) / integralNodalProduct R S z‖
      ≤ (1 / 2 : ℝ) ^ (R * S) := by
  have hquot := norm_integralNodalProduct_div_le (R := R) (S := S)
    (x := (l : ℂ)) (z := z) (A := R) (B := 2 * R)
    (by positivity) (by positivity)
    (fun i hi => norm_natCast_sub_natCast_le hl (by omega))
    (fun i hi => two_mul_le_norm_sub_natCast_of_norm_eq_three_mul (by omega) hz)
  convert hquot using 1
  field_simp

/-- Source-style outer-circle estimate for a rational target `l/q` in
`[0,R]`.  It is the product estimate required in Lemma 5 before the
factorial sharpening of the base. -/
theorem norm_integralNodalProduct_ratCast_div_outerCircle_le
    {R S l q : ℕ} {z : ℂ} (hR : 0 < R) (hq : 0 < q)
    (hl : l ≤ q * R) (hz : ‖z‖ = 3 * R) :
    ‖integralNodalProduct R S (((l : ℚ) / q : ℚ) : ℂ) /
        integralNodalProduct R S z‖
      ≤ (1 / 2 : ℝ) ^ (R * S) := by
  have hquot := norm_integralNodalProduct_div_le (R := R) (S := S)
    (x := (((l : ℚ) / q : ℚ) : ℂ)) (z := z) (A := R) (B := 2 * R)
    (by positivity) (by positivity)
    (fun i hi => by
      simpa only using
        norm_ratCast_sub_natCast_le hq hl (show i + 1 ≤ R by omega))
    (fun i hi => two_mul_le_norm_sub_natCast_of_norm_eq_three_mul (by omega) hz)
  convert hquot using 1
  field_simp

end Erdos240.InterpolationProducts
