import ErdosProblems.Erdos520.HarperFixedFractionalMoment

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# The fractional-moment recursion used in Harper's good--bad split

The fair-measure good event has exponentially small, but not polynomially
small, complement when the barrier height is fixed.  Consequently the
fixed `2/3` split is not by itself enough at the sharp scale.  The published
argument applies Holder between exponents `q < r`; this file isolates that
measure-theoretic step from the later Euler-product estimates.
-/

/-- Holder on a restricted event, written directly in fractional-moment
coordinates.  In applications `r = (1+q)/2`. -/
theorem integralOn_rpow_le_measure_rpow_mul_integral_rpow
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsFiniteMeasure nu]
    {Z : alpha -> Real} {G : Set alpha} {q r : Real}
    (hG : MeasurableSet G) (hq : 0 < q) (hqr : q < r)
    (hZnonneg : forall omega, 0 <= Z omega)
    (hZq : MemLp (fun omega => Z omega ^ q)
      (ENNReal.ofReal (r / q)) nu) :
    (integral (nu.restrict G) (fun omega => Z omega ^ q)) <=
      (nu.real G) ^ (1 - q / r) *
        (integral nu (fun omega => Z omega ^ r)) ^ (q / r) := by
  let p : Real := r / (r - q)
  let s : Real := r / q
  let f : alpha -> Real := G.indicator (fun _ => (1 : Real))
  let g : alpha -> Real := fun omega => Z omega ^ q
  have hr : 0 < r := hq.trans hqr
  have hrq : 0 < r - q := sub_pos.mpr hqr
  have hp : 0 < p := by positivity
  have hs : 0 < s := by positivity
  have hp1 : 1 < p := by
    dsimp only [p]
    rw [one_lt_div hrq]
    linarith
  have hps : p.HolderConjugate s := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hp1
    · dsimp only [p, s]
      field_simp
      ring
  have hf_nonneg : 0 ≤ᵐ[nu] f := by
    exact Filter.Eventually.of_forall fun omega => Set.indicator_nonneg
      (fun _ _ => by positivity) omega
  have hg_nonneg : 0 ≤ᵐ[nu] g := by
    exact Filter.Eventually.of_forall fun omega =>
      Real.rpow_nonneg (hZnonneg omega) _
  have hf : MemLp f (ENNReal.ofReal p) nu := by
    exact memLp_indicator_const _ hG (1 : Real)
      (Or.inr (measure_ne_top nu _))
  have hg : MemLp g (ENNReal.ofReal s) nu := by
    simpa only [g, s] using! hZq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := nu) hps hf_nonneg hg_nonneg hf hg
  have hleft :
      (integral (nu.restrict G) (fun omega => Z omega ^ q)) =
        integral nu (fun omega => f omega * g omega) := by
    rw [<- integral_indicator hG]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      by_cases homega : omega ∈ G
      · simp [f, g, homega]
      · simp [f, g, homega]
  have hfint : (integral nu (fun omega => f omega ^ p)) =
      nu.real G := by
    rw [show (fun omega => f omega ^ p) =
        G.indicator (fun _ => (1 : Real)) by
      funext omega
      by_cases homega : omega ∈ G
      · simp [f, homega]
      · simp [f, homega, hp.ne']]
    simp [hG]
  have hgint : (integral nu (fun omega => g omega ^ s)) =
      integral nu (fun omega => Z omega ^ r) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      simp only [g]
      rw [<- Real.rpow_mul (hZnonneg omega)]
      congr 1
      dsimp only [s]
      field_simp
  have hpExp : 1 / p = 1 - q / r := by
    dsimp only [p]
    field_simp
  have hsExp : 1 / s = q / r := by
    dsimp only [s]
    field_simp
  rw [<- hleft, hfint, hgint, hpExp, hsExp] at hholder
  exact hholder

/-- Good--bad decomposition at arbitrary exponents `0 < q < r`.  This is
the one-step recurrence in Harper's dyadic iteration toward exponent one. -/
theorem integral_rpow_le_of_good_bad_at_larger_exponent
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsFiniteMeasure nu]
    {Z : alpha -> Real} {G : Set alpha} {q r A epsilon : Real}
    (hG : MeasurableSet G) (hq : 0 < q) (hqr : q < r)
    (hZnonneg : forall omega, 0 <= Z omega)
    (hZq : Integrable (fun omega => Z omega ^ q) nu)
    (hZqLp : MemLp (fun omega => Z omega ^ q)
      (ENNReal.ofReal (r / q)) nu)
    (hgood : integral (nu.restrict G) (fun omega => Z omega ^ q) <= A)
    (hbad : nu.real Gᶜ <= epsilon) :
    integral nu (fun omega => Z omega ^ q) <=
      A + epsilon ^ (1 - q / r) *
        (integral nu (fun omega => Z omega ^ r)) ^ (q / r) := by
  have hsplit : integral nu (fun omega => Z omega ^ q) =
      integral (nu.restrict G) (fun omega => Z omega ^ q) +
        integral (nu.restrict Gᶜ) (fun omega => Z omega ^ q) := by
    have hmeasure : nu.restrict G + nu.restrict Gᶜ = nu :=
      Measure.restrict_add_restrict_compl hG
    calc
      integral nu (fun omega => Z omega ^ q) =
          integral (nu.restrict G + nu.restrict Gᶜ)
            (fun omega => Z omega ^ q) := by rw [hmeasure]
      _ = _ := integral_add_measure hZq.integrableOn hZq.integrableOn
  have hcompl := integralOn_rpow_le_measure_rpow_mul_integral_rpow
    hG.compl hq hqr hZnonneg hZqLp
  have hexp : 0 <= 1 - q / r := by
    have hr : 0 < r := hq.trans hqr
    have hdiv : q / r <= 1 := (div_le_one hr).mpr hqr.le
    linarith
  have hintNonneg : 0 ≤ integral nu (fun omega => Z omega ^ r) :=
    integral_nonneg fun omega => Real.rpow_nonneg (hZnonneg omega) r
  have hmoment : 0 ≤
      (integral nu (fun omega => Z omega ^ r)) ^ (q / r) :=
    Real.rpow_nonneg hintNonneg _
  rw [hsplit]
  apply add_le_add hgood
  exact hcompl.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow measureReal_nonneg hbad hexp)
    hmoment)

/-- A fractional power between zero and one is bounded by `1 + x`. -/
theorem rpow_le_one_add_self {x theta : Real}
    (hx : 0 <= x) (htheta0 : 0 <= theta) (htheta1 : theta <= 1) :
    x ^ theta <= 1 + x := by
  by_cases hx1 : x <= 1
  · exact (Real.rpow_le_one hx hx1 htheta0).trans (le_add_of_nonneg_right hx)
  · have h1x : 1 <= x := le_of_not_ge hx1
    exact (Real.rpow_le_self_of_one_le h1x htheta1).trans
      (le_add_of_nonneg_left (by norm_num : (0 : Real) <= 1))

/-- Linearized form of one fractional-moment recursion step. -/
theorem integral_rpow_le_of_good_bad_linearized
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsFiniteMeasure nu]
    {Z : alpha -> Real} {G : Set alpha} {q r A epsilon : Real}
    (hG : MeasurableSet G) (hq : 0 < q) (hqr : q < r)
    (hZnonneg : forall omega, 0 <= Z omega)
    (hZq : Integrable (fun omega => Z omega ^ q) nu)
    (hZqLp : MemLp (fun omega => Z omega ^ q)
      (ENNReal.ofReal (r / q)) nu)
    (hgood : integral (nu.restrict G) (fun omega => Z omega ^ q) <= A)
    (hbad : nu.real Gᶜ <= epsilon) :
    integral nu (fun omega => Z omega ^ q) <=
      A + epsilon ^ (1 - q / r) *
        (1 + integral nu (fun omega => Z omega ^ r)) := by
  have hrec := integral_rpow_le_of_good_bad_at_larger_exponent
    hG hq hqr hZnonneg hZq hZqLp hgood hbad
  have hr : 0 < r := hq.trans hqr
  have hratio0 : 0 <= q / r := div_nonneg hq.le hr.le
  have hratio1 : q / r <= 1 := (div_le_one hr).mpr hqr.le
  have hint0 : 0 <= integral nu (fun omega => Z omega ^ r) :=
    integral_nonneg fun omega => Real.rpow_nonneg (hZnonneg omega) r
  have hpower := rpow_le_one_add_self hint0 hratio0 hratio1
  have hepsilon : 0 <= epsilon := measureReal_nonneg.trans hbad
  have hepsPower : 0 <= epsilon ^ (1 - q / r) :=
    Real.rpow_nonneg hepsilon _
  have hadd := add_le_add_left
    (mul_le_mul_of_nonneg_left hpower hepsPower) A
  exact hrec.trans (by simpa [add_comm] using! hadd)

/-- The dyadic exponents in Harper's iteration, beginning at `2/3` and
moving halfway toward one at each step. -/
noncomputable def harperDyadicMomentExponent (m : Nat) : Real :=
  1 - 1 / (3 * (2 : Real) ^ m)

@[simp] theorem harperDyadicMomentExponent_zero :
    harperDyadicMomentExponent 0 = harperTwoThird := by
  norm_num [harperDyadicMomentExponent, harperTwoThird]

theorem harperDyadicMomentExponent_succ (m : Nat) :
    harperDyadicMomentExponent (m + 1) =
      (1 + harperDyadicMomentExponent m) / 2 := by
  unfold harperDyadicMomentExponent
  rw [pow_succ]
  field_simp
  ring

theorem harperDyadicMomentExponent_pos (m : Nat) :
    0 < harperDyadicMomentExponent m := by
  have hpow : (1 : Real) <= (2 : Real) ^ m :=
    one_le_pow₀ (by norm_num)
  have hden : (3 : Real) <= 3 * (2 : Real) ^ m := by nlinarith
  have hdiv : 1 / (3 * (2 : Real) ^ m) <= 1 / 3 := by
    exact one_div_le_one_div_of_le (by positivity) hden
  unfold harperDyadicMomentExponent
  linarith

theorem harperDyadicMomentExponent_lt_one (m : Nat) :
    harperDyadicMomentExponent m < 1 := by
  unfold harperDyadicMomentExponent
  have hdiv : 0 < 1 / ((3 : Real) * (2 : Real) ^ m) := by positivity
  linarith

theorem harperDyadicMomentExponent_strictMono :
    StrictMono harperDyadicMomentExponent := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [harperDyadicMomentExponent_succ]
  have hm := harperDyadicMomentExponent_lt_one m
  linarith

/-- A finite linear recurrence with contraction at most one half stays
uniformly bounded, independently of the number of dyadic exponent steps. -/
theorem finite_half_contraction_recursion
    (M : Nat -> Real) {L : Nat} {A rho B : Real}
    (hA : 0 <= A) (hrho0 : 0 <= rho) (hrhoHalf : rho <= 1 / 2)
    (hrec : forall m, m < L -> M m <= A + rho * (1 + M (m + 1)))
    (hbase : M L <= B) (hB : 0 <= B) :
    M 0 <= 2 * (A + rho) + B := by
  let D : Real := 2 * (A + rho) + B
  have hD0 : 0 <= D := by dsimp [D]; positivity
  have hbaseD : M L <= D := by
    calc
      M L <= B := hbase
      _ <= D := by dsimp [D]; nlinarith
  have hstep {m : Nat} (hm : m < L) (hnext : M (m + 1) <= D) :
      M m <= D := by
    have hmrec := hrec m hm
    have hadd : 1 + M (m + 1) <= 1 + D := by linarith
    have hmul := mul_le_mul_of_nonneg_left
      hadd hrho0
    calc
      M m <= A + rho * (1 + M (m + 1)) := hmrec
      _ <= A + rho * (1 + D) := by
        simpa [add_comm] using! add_le_add_left hmul A
      _ <= D := by
        dsimp only [D]
        nlinarith
  have hback : forall d : Nat, d <= L -> M (L - d) <= D := by
    intro d hd
    induction d with
    | zero => simpa using! hbaseD
    | succ d ih =>
        have hdL : d < L := by omega
        have hindex : L - (d + 1) + 1 = L - d := by omega
        apply hstep (m := L - (d + 1)) (by omega)
        rw [hindex]
        exact ih (by omega)
  simpa using! hback L le_rfl

end Problem520
end Erdos
