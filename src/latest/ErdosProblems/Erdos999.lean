/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdos Problem 999 is the Duffin--Schaeffer theorem.

The exact statement is formalized below on the unit additive circle.  The
circle is the standard probability-space version of "almost every alpha",
and `n + 1` indexes the positive denominator q.

Primary reference:
D. Koukoulopoulos and J. Maynard, On the Duffin--Schaeffer conjecture,
Annals of Mathematics 192 (2020), 251--307.

The detailed mathematical proof and Leanization dependency map are in
`tex/999.tex`.
-/

import Mathlib.NumberTheory.WellApproximable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import ErdosProblems.Erdos999.External.Erdos1165.SecondMoment
import ErdosProblems.Erdos220
import ErdosProblems.Erdos999.LayerLower
import ErdosProblems.Erdos999.PairGeometry
import ErdosProblems.Erdos999.PairOverlap

open Filter Metric Set MeasureTheory
open scoped ENNReal MeasureTheory Topology

namespace Erdos999

noncomputable section

/-- A reduced numerator for the positive denominator `q`. -/
abbrev ReducedNumerator (q : ℕ) :=
  {p : ℕ // p < q ∧ q.Coprime p}

/-- The radius in the inequality of Problem 999. -/
def approximationRadius (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  (f q : ℝ) / q

/-- The set of points admitting a reduced approximation with denominator
`n + 1`. -/
def approximationLayer (f : ℕ → ℕ) (n : ℕ) : Set UnitAddCircle :=
  ⋃ p : ReducedNumerator (n + 1),
    ball (↑(((p.1 : ℕ) : ℝ) / (n + 1)) : UnitAddCircle)
      (approximationRadius f (n + 1))

/-- The literal "infinitely many solutions" predicate, with positive
denominators indexed by `n + 1`. -/
def InfinitelyOftenApproximable (f : ℕ → ℕ) (x : UnitAddCircle) : Prop :=
  {n : ℕ | x ∈ approximationLayer f n}.Infinite

/-- The almost-everywhere approximation property in Problem 999. -/
def AlmostEverywhereApproximable (f : ℕ → ℕ) : Prop :=
  ∀ᵐ x : UnitAddCircle, InfinitelyOftenApproximable f x

/-- The nonnegative extended-real series from Problem 999.  Index `n`
corresponds to the positive denominator `q = n + 1`. -/
def duffinSchaefferSum (f : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ,
    (Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) / (n + 1 : ℝ≥0∞)

/-- Exact formal statement of the `ℕ → ℕ` specialization recorded as
Erdos Problem 999. -/
def Erdos999Statement : Prop :=
  ∀ f : ℕ → ℕ,
    AlmostEverywhereApproximable f ↔ duffinSchaefferSum f = ∞

lemma mem_approximationLayer_iff (f : ℕ → ℕ) (n : ℕ) (x : UnitAddCircle) :
    x ∈ approximationLayer f n ↔
      ∃ p < n + 1, (n + 1).Coprime p ∧
        ‖x - ↑((p : ℝ) / (n + 1))‖ < approximationRadius f (n + 1) := by
  simp only [approximationLayer, mem_iUnion, mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.property.1, p.property.2, hp⟩
  · rintro ⟨p, hpq, hcop, hp⟩
    exact ⟨⟨p, hpq, hcop⟩, hp⟩

/-- The custom denominator layer is exactly Mathlib's neighborhood of the
points of exact additive order `n + 1`. -/
lemma approximationLayer_eq_approxAddOrderOf (f : ℕ → ℕ) (n : ℕ) :
    approximationLayer f n =
      approxAddOrderOf UnitAddCircle (n + 1) (approximationRadius f (n + 1)) := by
  ext x
  rw [mem_approximationLayer_iff,
    UnitAddCircle.mem_approxAddOrderOf_iff (by omega : 0 < n + 1)]
  simp only [Nat.lt_succ_iff, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨p, hp, hcop, hx⟩
    exact ⟨p, hp, hcop.symm.gcd_eq_one, hx⟩
  · rintro ⟨p, hp, hcop, hx⟩
    exact ⟨p, hp, (show p.Coprime (n + 1) from hcop).symm, hx⟩

/-- Removing the unused zero denominator and reindexing positive denominators
by `Nat.succ` preserves infinitude. -/
lemma infinite_preimage_succ_iff {S : Set ℕ} (h0 : 0 ∉ S) :
    (Nat.succ ⁻¹' S).Infinite ↔ S.Infinite := by
  constructor
  · intro h
    exact (h.image Nat.succ_injective.injOn).mono (image_preimage_subset _ _)
  · intro h
    apply h.preimage
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (fun hzero ↦ h0 (hzero ▸ hn))
    exact ⟨m, rfl⟩

/-- Pointwise identification of the literal predicate in Problem 999 with
Mathlib's reduced well-approximability set. -/
lemma infinitelyOftenApproximable_iff_mem_addWellApproximable (f : ℕ → ℕ)
    (x : UnitAddCircle) :
    InfinitelyOftenApproximable f x ↔
      x ∈ addWellApproximable UnitAddCircle (approximationRadius f) := by
  rw [UnitAddCircle.mem_addWellApproximable_iff]
  let S : Set ℕ :=
    {q : ℕ | ∃ p < q, Nat.gcd p q = 1 ∧
      ‖x - ↑((p : ℝ) / q)‖ < approximationRadius f q}
  have hzero : 0 ∉ S := by simp [S]
  change InfinitelyOftenApproximable f x ↔ S.Infinite
  rw [← infinite_preimage_succ_iff hzero]
  change {n : ℕ | x ∈ approximationLayer f n}.Infinite ↔
    (Nat.succ ⁻¹' S).Infinite
  apply iff_of_eq
  apply congrArg Set.Infinite
  ext n
  simp only [mem_ofPred_eq, mem_preimage, S]
  rw [mem_approximationLayer_iff]
  simp only [Nat.succ_eq_add_one, Nat.Coprime, Nat.gcd_comm,
    Nat.cast_add, Nat.cast_one]

/-- Almost-everywhere form of
`infinitelyOftenApproximable_iff_mem_addWellApproximable`. -/
lemma almostEverywhereApproximable_iff (f : ℕ → ℕ) :
    AlmostEverywhereApproximable f ↔
      ∀ᵐ x : UnitAddCircle,
        x ∈ addWellApproximable UnitAddCircle (approximationRadius f) := by
  apply eventually_congr
  exact Filter.Eventually.of_forall
    (infinitelyOftenApproximable_iff_mem_addWellApproximable f)

/-- Gallagher's zero--one law upgrades non-nullity of the limsup to the
almost-everywhere conclusion, once the radii tend to zero. -/
lemma almostEverywhereApproximable_of_not_ae_not_mem
    (f : ℕ → ℕ)
    (hradius : Tendsto (approximationRadius f) atTop (𝓝 0))
    (hnonnull : ¬ ∀ᵐ x : UnitAddCircle,
      x ∉ addWellApproximable UnitAddCircle (approximationRadius f)) :
    AlmostEverywhereApproximable f := by
  rw [almostEverywhereApproximable_iff]
  rcases AddCircle.addWellApproximable_ae_empty_or_univ
      (T := (1 : ℝ)) (approximationRadius f) hradius with hempty | hfull
  · exact False.elim (hnonnull hempty)
  · exact hfull

/-!
The convergent half (equivalently, the implication from the a.e. property to
divergence) is elementary Borel--Cantelli.  Its proof is developed below.
The reverse implication is precisely the 2020 Koukoulopoulos--Maynard
theorem; Mathlib's `NumberTheory.WellApproximable` module explicitly notes
that this theorem is not yet formalized there.
-/

lemma natCard_reducedNumerator (q : ℕ) :
    Nat.card (ReducedNumerator q) = Nat.totient q := by
  change Nat.card {p : ℕ // p < q ∧ q.Coprime p} = Nat.totient q
  exact (Nat.totient_eq_card_lt_and_coprime q).symm

lemma volume_ball_unitAddCircle_le (x : UnitAddCircle) (r : ℝ) :
    volume (ball x r) ≤ ENNReal.ofReal (2 * r) := by
  calc
    volume (ball x r) = volume (closedBall x r) :=
      (measure_congr AddCircle.closedBall_ae_eq_ball).symm
    _ = ENNReal.ofReal (min 1 (2 * r)) := AddCircle.volume_closedBall 1 r
    _ ≤ ENNReal.ofReal (2 * r) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

lemma volume_approximationLayer_le (f : ℕ → ℕ) (n : ℕ) :
    volume (approximationLayer f n) ≤
      2 * ((Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) /
        (n + 1 : ℝ≥0∞)) := by
  let q := n + 1
  let r := approximationRadius f q
  have hfinite : ({p : ℕ | p < q ∧ q.Coprime p} : Set ℕ).Finite :=
    (Set.finite_Iio q).subset fun p hp ↦ hp.1
  let _ : Fintype (ReducedNumerator q) := hfinite.fintype
  calc
    volume (approximationLayer f n) ≤
        ∑' p : ReducedNumerator q,
          volume (ball (↑(((p.1 : ℕ) : ℝ) / q) : UnitAddCircle) r) := by
      simpa [approximationLayer, q, r] using
        (measure_iUnion_le (fun p : ReducedNumerator q ↦
          ball (↑(((p.1 : ℕ) : ℝ) / q) : UnitAddCircle) r))
    _ ≤ ∑' _p : ReducedNumerator q, ENNReal.ofReal (2 * r) :=
      ENNReal.tsum_le_tsum fun p ↦ volume_ball_unitAddCircle_le _ _
    _ = (Nat.totient q : ℕ) • ENNReal.ofReal (2 * r) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_eq_nat_card, natCard_reducedNumerator]
    _ = 2 * ((Nat.totient q : ℝ≥0∞) * (f q : ℝ≥0∞) / (q : ℝ≥0∞)) := by
      have hq : (0 : ℝ) < q := by positivity
      simp only [r, approximationRadius, ENNReal.ofReal_mul zero_le_two,
        ENNReal.ofReal_ofNat, ENNReal.ofReal_div_of_pos hq,
        ENNReal.ofReal_natCast, nsmul_eq_mul]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = 2 * ((Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) /
        (n + 1 : ℝ≥0∞)) := by simp [q]

lemma tsum_volume_approximationLayer_ne_top (f : ℕ → ℕ)
    (hsum : duffinSchaefferSum f ≠ ∞) :
    (∑' n : ℕ, volume (approximationLayer f n)) ≠ ∞ := by
  have hle : (∑' n : ℕ, volume (approximationLayer f n)) ≤
      2 * duffinSchaefferSum f := by
    calc
      (∑' n : ℕ, volume (approximationLayer f n)) ≤
          ∑' n : ℕ,
            2 * ((Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) /
              (n + 1 : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum (volume_approximationLayer_le f)
      _ = 2 * duffinSchaefferSum f := by
        rw [duffinSchaefferSum, ENNReal.tsum_mul_left]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hsum) hle

/-- The elementary implication in Problem 999: if almost every point has
infinitely many reduced approximations, then the Duffin--Schaeffer series
diverges. -/
theorem divergence_of_almostEverywhereApproximable (f : ℕ → ℕ)
    (h : AlmostEverywhereApproximable f) :
    duffinSchaefferSum f = ∞ := by
  by_contra hsum
  have hfinite :
      ∀ᵐ x : UnitAddCircle, {n : ℕ | x ∈ approximationLayer f n}.Finite :=
    ae_finite_setOfPred_mem (tsum_volume_approximationLayer_ne_top f hsum)
  have hinfinite :
      ∀ᵐ x : UnitAddCircle, {n : ℕ | x ∈ approximationLayer f n}.Infinite := by
    simpa [AlmostEverywhereApproximable, InfinitelyOftenApproximable] using h
  have hfalse : ∀ᵐ _x : UnitAddCircle, False :=
    (hinfinite.and hfinite).mono fun _x hx ↦ hx.1 hx.2
  exact hfalse.exists.choose_spec

/-!
## The large-values normalization

For the literal natural-valued problem, every nonzero value of `f` is at
least one.  We shall apply the Pollington--Vaughan large-values argument to
the smaller real-valued function

`min (f(q) / 2) (q / (2 * φ(q)))`.

The second term makes every normalized Duffin--Schaeffer weight at most
`1 / 2`, while the first preserves divergence after truncation.  The next
elementary totient estimate is also what makes the normalized physical
radii tend to zero, as required by the version of Gallagher's theorem in
Mathlib.
-/

private lemma totient_sq_ge_odd_prime_pow (p k : ℕ) (hp : p.Prime)
    (hp_odd : Odd p) (hk : 0 < k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [Nat.totient_prime_pow_succ hp]
  have hp3 : 3 ≤ p := by
    rcases hp_odd with ⟨t, ht⟩
    have h2 := hp.two_le
    omega
  have hp_minus_one_sq_ge : p ≤ (p - 1) ^ 2 := by
    set u := p - 1
    have hu2 : 2 ≤ u := by omega
    have hpu : p = u + 1 := by omega
    rw [hpu]
    nlinarith [Nat.mul_self_le_mul_self (by omega : 2 ≤ u)]
  have hpj_pos : 0 < p ^ j := pow_pos hp.pos _
  calc
    p ^ (j + 1) = p ^ j * p := by ring
    _ ≤ p ^ j * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hp_minus_one_sq_ge
    _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) :=
      Nat.le_mul_of_pos_left _ hpj_pos
    _ = (p ^ j * (p - 1)) ^ 2 := by ring

private lemma totient_sq_ge_half_pow_two (k : ℕ) (hk : 0 < k) :
    2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  change 2 ^ (j + 1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2
  rw [show 2 * (2 ^ j * (2 - 1 : ℕ)) ^ 2 = 2 ^ (2 * j + 1) by
    rw [show (2 - 1 : ℕ) = 1 by omega, mul_one, pow_succ]
    ring]
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)

/-- The elementary uniform lower bound `q ≤ 2 φ(q)²`. -/
theorem le_two_mul_totient_sq (q : ℕ) :
    q ≤ 2 * (Nat.totient q) ^ 2 := by
  suffices h : ∀ n : ℕ,
      n ≤ 2 * (Nat.totient n) ^ 2 ∧
        (Odd n → n ≤ (Nat.totient n) ^ 2) by
    exact (h q).1
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      by_cases hp2 : p = 2
      · subst p
        refine ⟨totient_sq_ge_half_pow_two k hk, ?_⟩
        intro hodd
        exfalso
        have heven : Even (2 ^ k) := by
          rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
          exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
        exact (Nat.not_odd_iff_even.mpr heven) hodd
      · have hp_odd : Odd p := hp.odd_of_ne_two hp2
        have hge : p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 :=
          totient_sq_ge_odd_prime_pow p k hp hp_odd hk
        exact ⟨hge.trans (Nat.le_mul_of_pos_left _ (by norm_num)), fun _ ↦ hge⟩
  | zero =>
      exact ⟨Nat.zero_le _, fun hodd ↦
        (Nat.not_odd_iff_even.mpr Even.zero hodd).elim⟩
  | one => simp
  | coprime a b ha hb hcop iha ihb =>
      obtain ⟨iha1, iha2⟩ := iha
      obtain ⟨ihb1, ihb2⟩ := ihb
      have hφmul : Nat.totient (a * b) =
          Nat.totient a * Nat.totient b := Nat.totient_mul hcop
      have hsq : (Nat.totient a * Nat.totient b) ^ 2 =
          (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := by ring
      constructor
      · by_cases ha_odd : Odd a
        · rw [hφmul, hsq]
          calc
            a * b ≤ (Nat.totient a) ^ 2 *
                (2 * (Nat.totient b) ^ 2) := Nat.mul_le_mul (iha2 ha_odd) ihb1
            _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
        · have ha_even : Even a := Nat.not_odd_iff_even.mp ha_odd
          have hb_odd : Odd b := by
            rw [Nat.odd_iff]
            by_contra hbe
            push Not at hbe
            have h2b : 2 ∣ b := by omega
            have h2gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd ha_even.two_dvd h2b
            rw [hcop] at h2gcd
            omega
          rw [hφmul, hsq]
          calc
            a * b ≤ (2 * (Nat.totient a) ^ 2) *
                (Nat.totient b) ^ 2 := Nat.mul_le_mul iha1 (ihb2 hb_odd)
            _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
      · intro hab_odd
        rw [hφmul, hsq]
        exact Nat.mul_le_mul (iha2 (Nat.odd_mul.mp hab_odd).1)
          (ihb2 (Nat.odd_mul.mp hab_odd).2)

/-- Euler's totient tends to infinity.  The proof is deliberately elementary
and uses only `q ≤ 2 φ(q)²`. -/
lemma tendsto_totient_atTop : Tendsto Nat.totient atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨2 * B ^ 2 + 1, fun q hq ↦ ?_⟩
  by_contra hφ
  have hφlt : Nat.totient q < B := Nat.lt_of_not_ge hφ
  have hbound := le_two_mul_totient_sq q
  nlinarith [sq_nonneg (B - Nat.totient q)]

lemma tendsto_inv_totient_zero :
    Tendsto (fun q : ℕ ↦ ((Nat.totient q : ℝ))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp tendsto_totient_atTop)

/-- The normalized real-valued approximating numerator.  Its physical
radius is `largeValueNumerator f q / q`. -/
def largeValueNumerator (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  if q = 0 then 0 else
    min ((f q : ℝ) / 2) ((q : ℝ) / (2 * Nat.totient q))

def largeValueRadius (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  largeValueNumerator f q / q

lemma largeValueNumerator_nonneg (f : ℕ → ℕ) (q : ℕ) :
    0 ≤ largeValueNumerator f q := by
  simp only [largeValueNumerator]
  split_ifs
  · exact le_rfl
  · exact le_min (by positivity) (by positivity)

lemma largeValueNumerator_le (f : ℕ → ℕ) (q : ℕ) :
    largeValueNumerator f q ≤ f q := by
  simp only [largeValueNumerator]
  split_ifs
  · exact_mod_cast Nat.zero_le (f q)
  · have hf : (0 : ℝ) ≤ f q := by positivity
    exact (min_le_left _ _).trans (by linarith)

lemma largeValueRadius_le (f : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    largeValueRadius f q ≤ ((Nat.totient q : ℝ))⁻¹ / 2 := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  rw [largeValueRadius, largeValueNumerator, if_neg hq.ne']
  calc
    min ((f q : ℝ) / 2) ((q : ℝ) / (2 * Nat.totient q)) / q ≤
        ((q : ℝ) / (2 * Nat.totient q)) / q :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = ((Nat.totient q : ℝ))⁻¹ / 2 := by
      field_simp
      <;> norm_num [hq.ne', hφ.ne']

lemma tendsto_largeValueRadius_zero (f : ℕ → ℕ) :
    Tendsto (largeValueRadius f) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun q ↦ by
      exact div_nonneg (largeValueNumerator_nonneg f q) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with q hq
    exact largeValueRadius_le f hq
  · simpa using tendsto_inv_totient_zero.div_const 2

/-- Truncating a divergent nonnegative extended-real series at a fixed
positive height preserves divergence.  This is the precise form needed for
the large-values normalization. -/
lemma tsum_min_half_eq_top_of_tsum_eq_top
    (a : ℕ → ℝ≥0∞) (ha : ∀ n, a n ≠ ∞)
    (hsum : ∑' n, a n = ∞) :
    ∑' n, min (a n / 2) (1 / 2) = ∞ := by
  by_contra hcap
  let g : ℕ → ℝ≥0∞ := fun n ↦ min (a n / 2) (1 / 2)
  have hg_tendsto : Tendsto g atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hcap
  obtain ⟨N, hN⟩ :=
    (ENNReal.tendsto_atTop_zero.mp hg_tendsto) (1 / 4) (by norm_num)
  have htail : ∀ n, N ≤ n → a n = 2 * g n := by
    intro n hn
    have hg_le : g n ≤ 1 / 4 := hN n hn
    have ha_half_le : a n / 2 ≤ 1 / 4 := by
      by_contra hnot
      have hlt : 1 / 4 < a n / 2 := lt_of_not_ge hnot
      have hmin : 1 / 4 < min (a n / 2) (1 / 2) :=
        lt_min hlt (by norm_num)
      exact (not_lt_of_ge hg_le) (by simpa [g] using hmin)
    have ha_half_le_half : a n / 2 ≤ 1 / 2 :=
      ha_half_le.trans (by norm_num)
    have hg : g n = a n / 2 := min_eq_left ha_half_le_half
    rw [hg, mul_comm,
      ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  have hpoint : ∀ n,
      a n ≤ (if n < N then a n else 0) + 2 * g n := by
    intro n
    by_cases hn : n < N
    · simp [hn]
    · rw [if_neg hn, zero_add, htail n (Nat.le_of_not_gt hn)]
  have hprefix : (∑' n, if n < N then a n else 0) ≠ ∞ := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · exact ENNReal.sum_ne_top.mpr fun n hn ↦ by
        simp only [Finset.mem_range] at hn
        simp [hn, ha n]
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp [hn]
  have hupper :
      tsum (fun n : ℕ ↦ (if n < N then a n else 0) + 2 * g n) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    exact ENNReal.add_ne_top.mpr
      ⟨hprefix, ENNReal.mul_ne_top (by norm_num) hcap⟩
  have horig : (∑' n, a n) ≠ ∞ :=
    ne_top_of_le_ne_top hupper (ENNReal.tsum_le_tsum hpoint)
  exact horig hsum

/-- The normalized Duffin--Schaeffer weight.  It is the original weight,
halved and capped at `1 / 2`. -/
def normalizedWeight (f : ℕ → ℕ) (q : ℕ) : ℝ≥0∞ :=
  min (((Nat.totient q : ℝ≥0∞) * (f q : ℝ≥0∞) / q) / 2) (1 / 2)

lemma normalizedWeight_ne_top (f : ℕ → ℕ) (q : ℕ) :
    normalizedWeight f q ≠ ∞ := by
  exact ne_top_of_le_ne_top (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞)
    (min_le_right _ _)

/-- The extended-real normalized weight is exactly the mass attached to
`largeValueNumerator`. -/
lemma normalizedWeight_eq_ofReal_largeValueNumerator
    (f : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    normalizedWeight f q = ENNReal.ofReal
      ((Nat.totient q : ℝ) * largeValueNumerator f q / q) := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  rw [largeValueNumerator, if_neg hq.ne']
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφR : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφ
  have hreal :
      (Nat.totient q : ℝ) *
          min ((f q : ℝ) / 2) ((q : ℝ) / (2 * Nat.totient q)) / q =
        min (((Nat.totient q : ℝ) * (f q : ℝ) / q) / 2) (1 / 2) := by
    rw [mul_min_of_nonneg _ _ hφR.le, ← min_div_div_right hqR.le]
    congr 1 <;> field_simp [hqR.ne', hφR.ne'] <;> ring
  rw [hreal]
  simp only [normalizedWeight, ENNReal.ofReal_min,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Nat.totient q),
    ENNReal.ofReal_div_of_pos hqR,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_one]

/-- Divergence survives the large-values normalization. -/
lemma tsum_normalizedWeight_succ_eq_top (f : ℕ → ℕ)
    (hsum : duffinSchaefferSum f = ∞) :
    ∑' n : ℕ, normalizedWeight f (n + 1) = ∞ := by
  apply tsum_min_half_eq_top_of_tsum_eq_top
  · intro n
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.natCast_ne_top _))
      (by simp)
  · simpa [duffinSchaefferSum, normalizedWeight] using hsum

/-- The ordinary real form of the normalized weight. -/
def normalizedRealWeight (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  (Nat.totient q : ℝ) * largeValueNumerator f q / q

lemma normalizedRealWeight_nonneg (f : ℕ → ℕ) (q : ℕ) :
    0 ≤ normalizedRealWeight f q := by
  exact div_nonneg (mul_nonneg (by positivity)
    (largeValueNumerator_nonneg f q)) (by positivity)

lemma normalizedRealWeight_le_half (f : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    normalizedRealWeight f q ≤ 1 / 2 := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφR : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφ
  rw [normalizedRealWeight, largeValueNumerator, if_neg hq.ne']
  calc
    (Nat.totient q : ℝ) *
          min ((f q : ℝ) / 2) ((q : ℝ) / (2 * Nat.totient q)) / q
        ≤ (Nat.totient q : ℝ) *
            ((q : ℝ) / (2 * Nat.totient q)) / q := by
          gcongr
          exact min_le_right _ _
    _ = 1 / 2 := by field_simp [hqR.ne', hφR.ne']

lemma largeValueNumerator_eq_zero_iff (f : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    largeValueNumerator f q = 0 ↔ f q = 0 := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  rw [largeValueNumerator, if_neg hq.ne']
  constructor
  · intro h
    by_contra hf
    have hfpos : (0 : ℝ) < f q := by
      exact_mod_cast (Nat.pos_of_ne_zero hf)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hφR : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφ
    have hpos : 0 < min ((f q : ℝ) / 2)
        ((q : ℝ) / (2 * Nat.totient q)) :=
      lt_min (div_pos hfpos (by norm_num))
        (div_pos hqR (mul_pos (by norm_num) hφR))
    linarith
  · intro hf
    rw [hf]
    simp
    positivity

lemma one_half_le_largeValueNumerator (f : ℕ → ℕ) {q : ℕ}
    (hq : 0 < q) (hf : f q ≠ 0) :
    1 / 2 ≤ largeValueNumerator f q := by
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hf_one : 1 ≤ f q := Nat.one_le_iff_ne_zero.mpr hf
  have hφ_le_q : Nat.totient q ≤ q := Nat.totient_le q
  rw [largeValueNumerator, if_neg hq.ne', le_min_iff]
  constructor
  · exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast hf_one)
  · have hφR : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφ
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) hφR)).2
    have hφ_le_qR : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast hφ_le_q
    norm_num only [one_mul]
    nlinarith

/-- The normalized denominator layer, indexed by `n` with denominator
`q = n + 1`. -/
def largeValueLayer (f : ℕ → ℕ) (n : ℕ) : Set UnitAddCircle :=
  approxAddOrderOf UnitAddCircle (n + 1) (largeValueRadius f (n + 1))

lemma measurableSet_largeValueLayer (f : ℕ → ℕ) (n : ℕ) :
    MeasurableSet (largeValueLayer f n) := by
  exact isOpen_thickening.measurableSet

private lemma largeValueLayer_eq_iUnion_balls (f : ℕ → ℕ) (n : ℕ) :
    largeValueLayer f n =
      ⋃ p : ReducedNumerator (n + 1),
        ball (↑(((p.1 : ℕ) : ℝ) / (n + 1)) : UnitAddCircle)
          (largeValueRadius f (n + 1)) := by
  ext x
  rw [largeValueLayer, UnitAddCircle.mem_approxAddOrderOf_iff (by omega)]
  simp only [mem_iUnion, mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨p, hp, hcop, hx⟩
    refine ⟨⟨p, hp, (show p.Coprime (n + 1) from hcop).symm⟩, ?_⟩
    simpa [Nat.cast_add, Nat.cast_one] using hx
  · rintro ⟨p, hx⟩
    refine ⟨p.1, p.property.1, p.property.2.symm.gcd_eq_one, ?_⟩
    simpa [Nat.cast_add, Nat.cast_one] using hx

lemma volume_largeValueLayer_le (f : ℕ → ℕ) (n : ℕ) :
    volume (largeValueLayer f n) ≤
      ENNReal.ofReal (2 * normalizedRealWeight f (n + 1)) := by
  let q := n + 1
  let r := largeValueRadius f q
  have hfinite : ({p : ℕ | p < q ∧ q.Coprime p} : Set ℕ).Finite :=
    (Set.finite_Iio q).subset fun p hp ↦ hp.1
  let _ : Fintype (ReducedNumerator q) := hfinite.fintype
  have hr : 0 ≤ r := div_nonneg (largeValueNumerator_nonneg f q) (by positivity)
  calc
    volume (largeValueLayer f n) ≤
        ∑' p : ReducedNumerator q,
          volume (ball (↑(((p.1 : ℕ) : ℝ) / q) : UnitAddCircle) r) := by
      rw [largeValueLayer_eq_iUnion_balls]
      simpa [q, r, Nat.cast_add, Nat.cast_one] using
        (measure_iUnion_le (μ := volume) (fun p : ReducedNumerator q ↦
          ball (↑(((p.1 : ℕ) : ℝ) / q) : UnitAddCircle) r))
    _ ≤ ∑' _p : ReducedNumerator q, ENNReal.ofReal (2 * r) :=
      ENNReal.tsum_le_tsum fun p ↦ volume_ball_unitAddCircle_le _ _
    _ = (Nat.totient q : ℕ) • ENNReal.ofReal (2 * r) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_eq_nat_card, natCard_reducedNumerator]
    _ = ENNReal.ofReal (2 * normalizedRealWeight f q) := by
      rw [← ENNReal.ofReal_nsmul]
      · congr 1
        simp only [nsmul_eq_mul]
        dsimp [r, normalizedRealWeight, largeValueRadius]
        ring
    _ = ENNReal.ofReal (2 * normalizedRealWeight f (n + 1)) := by
      rfl

lemma volumeReal_largeValueLayer_le (f : ℕ → ℕ) (n : ℕ) :
    volume.real (largeValueLayer f n) ≤
      2 * normalizedRealWeight f (n + 1) := by
  rw [measureReal_def]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (volume_largeValueLayer_le f n)
  have hnonneg : 0 ≤ 2 * normalizedRealWeight f (n + 1) :=
    mul_nonneg (by norm_num) (normalizedRealWeight_nonneg f (n + 1))
  rw [ENNReal.toReal_ofReal hnonneg] at h
  exact h

/-- The reduced-residue gap estimate gives a uniform lower bound for every
normalized layer whose denominator is at least four. -/
lemma exists_volumeReal_largeValueLayer_lower_of_three_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℕ → ℕ) (n : ℕ), 3 ≤ n →
      c * normalizedRealWeight f (n + 1) ≤
        volume.real (largeValueLayer f n) := by
  obtain ⟨c, hc, hlower⟩ := exists_largeValueLayer_lower_of_four_le
  refine ⟨c, hc, ?_⟩
  intro f n hn
  let q := n + 1
  have hq : 4 ≤ q := by dsimp [q]; omega
  have hqpos : 0 < q := by omega
  by_cases hf : f q = 0
  · have hLzero : largeValueNumerator f q = 0 :=
      (largeValueNumerator_eq_zero_iff f hqpos).2 hf
    have hLzero' : largeValueNumerator f (n + 1) = 0 := by
      simpa [q] using hLzero
    simp [normalizedRealWeight, hLzero']
  · have hLpos : 0 < largeValueNumerator f q :=
      lt_of_le_of_ne (largeValueNumerator_nonneg f q)
        (Ne.symm ((largeValueNumerator_eq_zero_iff f hqpos).not.mpr hf))
    have hcap : largeValueNumerator f q ≤
        (q : ℝ) / (2 * q.totient) := by
      rw [largeValueNumerator, if_neg hqpos.ne']
      exact min_le_right _ _
    simpa [q, normalizedRealWeight, largeValueLayer, largeValueRadius] using
      hlower q (largeValueNumerator f q) hq hLpos hcap

/-!
## The finite-block second-moment argument

The following lemmas isolate the completely measure-theoretic endgame of
the Pollington--Vaughan large-values proof.  They will be applied with
`w n = normalizedRealWeight f (n + 1)` and `A n = largeValueLayer f n`.
-/

lemma tsum_nat_add_eq_top {w : ℕ → ℝ≥0∞}
    (hw : ∀ n, w n ≠ ∞) (hsum : ∑' n, w n = ∞) (N : ℕ) :
    ∑' k, w (k + N) = ∞ := by
  induction N with
  | zero => simpa using hsum
  | succ N ih =>
      have h := ENNReal.tsum_add_one_eq_top ih (by simpa using hw N)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma exists_real_partial_sum_between_one_three_halves
    {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hwle : ∀ n, w n ≤ 1 / 2)
    (hsum : ∑' n, ENNReal.ofReal (w n) = ∞) (N : ℕ) :
    ∃ k : ℕ, 1 ≤ ∑ i ∈ Finset.range k, w (i + N) ∧
      ∑ i ∈ Finset.range k, w (i + N) ≤ 3 / 2 := by
  let v : ℕ → ℝ := fun i ↦ w (i + N)
  have hvtop : ∑' i, ENNReal.ofReal (v i) = ∞ :=
    tsum_nat_add_eq_top (fun _ ↦ ENNReal.ofReal_ne_top) hsum N
  have hex : ∃ k : ℕ, 1 ≤ ∑ i ∈ Finset.range k, v i := by
    by_contra h
    push Not at h
    have hle : (∑' i, ENNReal.ofReal (v i)) ≤ ENNReal.ofReal 1 := by
      rw [ENNReal.tsum_eq_iSup_sum' Finset.range]
      · apply iSup_le
        intro k
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · exact ENNReal.ofReal_le_ofReal (h k).le
        · exact fun i _ ↦ hw0 (i + N)
      · intro s
        exact s.exists_nat_subset_range
    rw [hvtop] at hle
    simpa using hle
  let k := Nat.find hex
  have hk : 1 ≤ ∑ i ∈ Finset.range k, v i := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hkzero
    have hkzero' : (k : ℕ) = 0 := hkzero
    have hkbad : (1 : ℝ) ≤ 0 := by simpa [k, hkzero'] using hk
    norm_num at hkbad
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hk' : 1 ≤ ∑ i ∈ Finset.range (j + 1), v i := by simpa [hj] using hk
  have hprev : ∑ i ∈ Finset.range j, v i < 1 := by
    apply lt_of_not_ge
    intro h
    have hkj : k ≤ j := Nat.find_min' hex h
    omega
  refine ⟨j + 1, hk', ?_⟩
  rw [Finset.sum_range_succ]
  calc
    (∑ i ∈ Finset.range j, v i) + v j ≤ 1 + 1 / 2 :=
      add_le_add hprev.le (hwle (j + N))
    _ = 3 / 2 := by norm_num

lemma tail_union_measureReal_lower
    (A : ℕ → Set UnitAddCircle) (hA : ∀ n, MeasurableSet (A n))
    (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hwle : ∀ n, w n ≤ 1 / 2)
    (hsum : ∑' n, ENNReal.ofReal (w n) = ∞)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hsingle : ∀ n, c * w n ≤ volume.real (A n))
    (hsingleUpper : ∀ n, volume.real (A n) ≤ 2 * w n)
    (hoverlap : ∀ i j, i ≠ j →
      volume.real (A i ∩ A j) ≤ C * w i * w j) (N : ℕ) :
    c ^ 2 / (3 + 9 * C / 4) ≤
      volume.real (⋃ n, ⋃ (_ : N ≤ n), A n) := by
  obtain ⟨k, hk_lower, hk_upper⟩ :=
    exists_real_partial_sum_between_one_three_halves hw0 hwle hsum N
  let W : ℝ := ∑ i ∈ Finset.range k, w (i + N)
  let B : ℕ → Set UnitAddCircle := fun i ↦ A (i + N)
  have hfirst : c ≤ ∑ i ∈ Finset.range k, volume.real (B i) := by
    calc
      c ≤ c * W := by nlinarith [hk_lower, hc.le]
      _ = ∑ i ∈ Finset.range k, c * w (i + N) := by
        simp only [W, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range k, volume.real (B i) := by
        exact Finset.sum_le_sum fun i _ ↦ hsingle (i + N)
  have hpairpoint : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
      volume.real (B i ∩ B j) ≤
        (if i = j then 2 * w (i + N) else 0) +
          C * w (i + N) * w (j + N) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      simp only [B, inter_self, if_pos]
      exact (hsingleUpper (i + N)).trans
        (le_add_of_nonneg_right (mul_nonneg
          (mul_nonneg hC (hw0 (i + N))) (hw0 (i + N))))
    · simp only [B, if_neg hij, zero_add]
      exact hoverlap (i + N) (j + N) (by omega)
  have hdiag :
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        if i = j then 2 * w (i + N) else 0) = 2 * W := by
    calc
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          if i = j then 2 * w (i + N) else 0) =
          ∑ i ∈ Finset.range k, 2 * w (i + N) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hi]
      _ = 2 * W := by
        simp only [W]
        rw [Finset.mul_sum]
  have hprod :
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        C * w (i + N) * w (j + N)) = C * W ^ 2 := by
    calc
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          C * w (i + N) * w (j + N)) =
          ∑ i ∈ Finset.range k, (C * w (i + N)) * W := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [W]
            rw [Finset.mul_sum]
      _ = C * W ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
  have hsecond :
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          volume.real (B i ∩ B j)) ≤ 3 + 9 * C / 4 := by
    calc
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          volume.real (B i ∩ B j)) ≤
          ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
            ((if i = j then 2 * w (i + N) else 0) +
              C * w (i + N) * w (j + N)) := by
        exact Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦
          hpairpoint i hi j hj
      _ = 2 * W + C * W ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        rw [hdiag, hprod]
      _ ≤ 3 + 9 * C / 4 := by
        have hW0 : 0 ≤ W := by linarith [hk_lower]
        have hWsq : W ^ 2 ≤ (3 / 2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hW0 hk_upper 2
        have hCWsq := mul_le_mul_of_nonneg_left hWsq hC
        nlinarith
  have hU : 0 < 3 + 9 * C / 4 := by nlinarith
  have hunion := Erdos1165.SecondMoment.indicatorCount_union_lower
    (mu := volume) (Finset.range k) B
    (fun i _ ↦ hA (i + N)) hc.le hU hfirst hsecond
  calc
    c ^ 2 / (3 + 9 * C / 4) ≤
        volume.real (⋃ i ∈ Finset.range k, B i) := hunion
    _ ≤ volume.real (⋃ n, ⋃ (_ : N ≤ n), A n) := by
      apply measureReal_mono
      · intro x hx
        rcases mem_iUnion.mp hx with ⟨i, hx⟩
        rcases mem_iUnion.mp hx with ⟨hi, hx⟩
        exact mem_iUnion.mpr ⟨i + N, mem_iUnion.mpr ⟨by omega, hx⟩⟩
      · exact measure_ne_top _ _

lemma measure_limsup_ne_zero_of_tail_lower_bound
    (A : ℕ → Set UnitAddCircle) (hA : ∀ n, MeasurableSet (A n))
    {c : ℝ≥0∞} (hc : c ≠ 0)
    (htail : ∀ N, c ≤ volume (⋃ n, ⋃ (_ : N ≤ n), A n)) :
    volume (limsup A atTop) ≠ 0 := by
  let U : ℕ → Set UnitAddCircle := fun N ↦ ⋃ n, ⋃ (_ : N ≤ n), A n
  have hUmeas : ∀ N, NullMeasurableSet (U N) volume := fun N ↦
    (MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦ hA n).nullMeasurableSet
  have hUanti : Antitone U := by
    intro N M hNM x hx
    rcases mem_iUnion.mp hx with ⟨n, hx⟩
    rcases mem_iUnion.mp hx with ⟨hMn, hx⟩
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hNM.trans hMn, hx⟩⟩
  have hmeasure : volume (⋂ N, U N) = ⨅ N, volume (U N) :=
    hUanti.measure_iInter hUmeas ⟨0, measure_ne_top volume (U 0)⟩
  have hc_inter : c ≤ volume (⋂ N, U N) := by
    rw [hmeasure]
    exact le_iInf fun N ↦ htail N
  have hlimsup : limsup A atTop = ⋂ N, U N := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [iInf_eq_iInter, iSup_eq_iUnion, U]
  rw [hlimsup]
  intro hzero
  have hbot : c ≤ 0 := by simpa [hzero] using hc_inter
  exact hc (bot_unique hbot)

lemma measure_limsup_ne_zero_of_second_moment
    (A : ℕ → Set UnitAddCircle) (hA : ∀ n, MeasurableSet (A n))
    (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hwle : ∀ n, w n ≤ 1 / 2)
    (hsum : ∑' n, ENNReal.ofReal (w n) = ∞)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hsingle : ∀ n, c * w n ≤ volume.real (A n))
    (hsingleUpper : ∀ n, volume.real (A n) ≤ 2 * w n)
    (hoverlap : ∀ i j, i ≠ j →
      volume.real (A i ∩ A j) ≤ C * w i * w j) :
    volume (limsup A atTop) ≠ 0 := by
  have hU : 0 < 3 + 9 * C / 4 := by nlinarith
  let d : ℝ := c ^ 2 / (3 + 9 * C / 4)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  apply measure_limsup_ne_zero_of_tail_lower_bound A hA
    (ENNReal.ofReal_ne_zero_iff.mpr hd)
  intro N
  apply ENNReal.ofReal_le_of_le_toReal
  rw [← measureReal_def]
  exact tail_union_measureReal_lower A hA w hw0 hwle hsum c C hc hC
    hsingle hsingleUpper hoverlap N

/-- Removing finitely many initial sets can only shrink a limsup. -/
lemma limsup_nat_add_subset (A : ℕ → Set UnitAddCircle) (N : ℕ) :
    limsup (fun n ↦ A (n + N)) atTop ⊆ limsup A atTop := by
  rw [limsup_eq_iInf_iSup_of_nat, limsup_eq_iInf_iSup_of_nat]
  simp only [iInf_eq_iInter, iSup_eq_iUnion]
  intro x hx
  rw [mem_iInter] at hx ⊢
  intro n
  have hxn := hx n
  rcases mem_iUnion.mp hxn with ⟨k, hxn⟩
  rcases mem_iUnion.mp hxn with ⟨hnk, hxA⟩
  exact mem_iUnion.mpr
    ⟨k + N, mem_iUnion.mpr ⟨hnk.trans (Nat.le_add_right k N), hxA⟩⟩

lemma tsum_ofReal_normalizedRealWeight_succ_eq_top (f : ℕ → ℕ)
    (hsum : duffinSchaefferSum f = ∞) :
    ∑' n, ENNReal.ofReal (normalizedRealWeight f (n + 1)) = ∞ := by
  calc
    (∑' n, ENNReal.ofReal (normalizedRealWeight f (n + 1))) =
        ∑' n, normalizedWeight f (n + 1) := by
      apply tsum_congr
      intro n
      symm
      simpa [normalizedRealWeight] using
        normalizedWeight_eq_ofReal_largeValueNumerator f (Nat.zero_lt_succ n)
    _ = ∞ := tsum_normalizedWeight_succ_eq_top f hsum

lemma limsup_largeValueLayer_eq_addWellApproximable (f : ℕ → ℕ) :
    limsup (largeValueLayer f) atTop =
      addWellApproximable UnitAddCircle (largeValueRadius f) := by
  unfold addWellApproximable
  rw [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq,
    cofinite.blimsup_set_eq]
  ext x
  simp only [mem_setOf_eq]
  let S : Set ℕ := {q | 0 < q ∧
    x ∈ approxAddOrderOf UnitAddCircle q (largeValueRadius f q)}
  have hzero : 0 ∉ S := by simp [S]
  change {n | x ∈ largeValueLayer f n}.Infinite ↔ S.Infinite
  have hleft : {n | x ∈ largeValueLayer f n} = Nat.succ ⁻¹' S := by
    ext n
    simp [S, largeValueLayer, Nat.succ_eq_add_one]
  rw [hleft]
  exact infinite_preimage_succ_iff hzero

lemma ae_mem_addWellApproximable_of_measure_ne_zero
    (delta : ℕ → ℝ) (hdelta : Tendsto delta atTop (𝓝 0))
    (hpos : volume (addWellApproximable UnitAddCircle delta) ≠ 0) :
    ∀ᵐ x, x ∈ addWellApproximable UnitAddCircle delta := by
  rcases AddCircle.addWellApproximable_ae_empty_or_univ
      (T := (1 : ℝ)) delta hdelta with hnull | hfull
  · exact (hpos (ae_eq_empty.mp (eventuallyEq_empty.mpr hnull))).elim
  · exact hfull

lemma largeValueRadius_le_approximationRadius (f : ℕ → ℕ)
    {q : ℕ} (hq : 0 < q) :
    largeValueRadius f q ≤ approximationRadius f q := by
  exact div_le_div_of_nonneg_right (largeValueNumerator_le f q)
    (by positivity : (0 : ℝ) ≤ q)

lemma addWellApproximable_largeValue_subset (f : ℕ → ℕ) :
    addWellApproximable UnitAddCircle (largeValueRadius f) ⊆
      addWellApproximable UnitAddCircle (approximationRadius f) := by
  intro x hx
  rw [UnitAddCircle.mem_addWellApproximable_iff] at hx ⊢
  apply hx.mono
  intro q hq
  rcases hq with ⟨p, hpq, hcop, hdist⟩
  have hqpos : 0 < q := Nat.zero_lt_of_lt hpq
  exact ⟨p, hpq, hcop,
    hdist.trans_le (largeValueRadius_le_approximationRadius f hqpos)⟩

/-- The remaining arithmetic estimate in the Pollington--Vaughan
large-values argument: distinct normalized denominator layers are uniformly
quasi-independent.  The restriction to indices at least three discards only
the denominators `1,2,3`. -/
def LargeValuePairOverlap : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℕ) (i j : ℕ),
    3 ≤ i → 3 ≤ j → i ≠ j →
      volume.real (largeValueLayer f i ∩ largeValueLayer f j) ≤
        C * normalizedRealWeight f (i + 1) *
          normalizedRealWeight f (j + 1)

/-- Purely finite form of the Pollington--Vaughan arithmetic estimate. -/
def LargeValuePairCountBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℕ → ℕ) (i j : ℕ),
    3 ≤ i → 3 ≤ j → i ≠ j →
      (overlapPairCount (i + 1) (j + 1)
        (largeValueNumerator f (i + 1))
        (largeValueNumerator f (j + 1)) : ℝ) ≤
      K * ((i + 1).totient : ℝ) * ((j + 1).totient : ℝ) *
        max (largeValueRadius f (i + 1)) (largeValueRadius f (j + 1))

/-- The finite pair-count formulation implies the measure overlap
formulation used by the second-moment argument. -/
theorem largeValuePairOverlap_of_pairCountBound
    (hcount : LargeValuePairCountBound) : LargeValuePairOverlap := by
  obtain ⟨K, hK, hcount⟩ := hcount
  refine ⟨2 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro f i j hi hj hij
  have hiq : 0 < i + 1 := by omega
  have hjq : 0 < j + 1 := by omega
  simpa [largeValueLayer, largeValueRadius, normalizedRealWeight] using
    volumeReal_approxAddOrderOf_inter_le_of_pairCount hiq hjq
      (largeValueNumerator_nonneg f (i + 1))
      (largeValueNumerator_nonneg f (j + 1)) hK
      (hcount f i j hi hj hij)

/-- The complete measure-theoretic deduction of the hard direction from the
Pollington--Vaughan pair-overlap estimate. -/
theorem hardDirection_of_largeValuePairOverlap
    (hoverlap : LargeValuePairOverlap) :
    ∀ f : ℕ → ℕ, duffinSchaefferSum f = ∞ →
      AlmostEverywhereApproximable f := by
  obtain ⟨C, hC, hpair⟩ := hoverlap
  obtain ⟨c, hc, hlower⟩ :=
    exists_volumeReal_largeValueLayer_lower_of_three_le
  intro f hsum
  let A : ℕ → Set UnitAddCircle := fun n ↦ largeValueLayer f (n + 3)
  let w : ℕ → ℝ := fun n ↦ normalizedRealWeight f (n + 4)
  have hw0 : ∀ n, 0 ≤ w n := fun n ↦ normalizedRealWeight_nonneg f (n + 4)
  have hwle : ∀ n, w n ≤ 1 / 2 := fun n ↦
    normalizedRealWeight_le_half f (by omega : 0 < n + 4)
  have hsumAll :
      ∑' n, ENNReal.ofReal (normalizedRealWeight f (n + 1)) = ∞ :=
    tsum_ofReal_normalizedRealWeight_succ_eq_top f hsum
  have hsumShift : ∑' n, ENNReal.ofReal (w n) = ∞ := by
    have htail := tsum_nat_add_eq_top
      (w := fun n ↦ ENNReal.ofReal (normalizedRealWeight f (n + 1)))
      (fun _ ↦ ENNReal.ofReal_ne_top) hsumAll 3
    simpa [w, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  have hsingle : ∀ n, c * w n ≤ volume.real (A n) := by
    intro n
    simpa [A, w, Nat.add_assoc] using hlower f (n + 3) (by omega)
  have hsingleUpper : ∀ n, volume.real (A n) ≤ 2 * w n := by
    intro n
    simpa [A, w, Nat.add_assoc] using volumeReal_largeValueLayer_le f (n + 3)
  have hpairShift : ∀ i j, i ≠ j →
      volume.real (A i ∩ A j) ≤ C * w i * w j := by
    intro i j hij
    simpa [A, w, Nat.add_assoc] using
      hpair f (i + 3) (j + 3) (by omega) (by omega) (by omega)
  have hshift : volume (limsup A atTop) ≠ 0 :=
    measure_limsup_ne_zero_of_second_moment A
      (fun n ↦ measurableSet_largeValueLayer f (n + 3)) w hw0 hwle
      hsumShift c C hc hC hsingle hsingleUpper hpairShift
  have hsub : limsup A atTop ⊆ limsup (largeValueLayer f) atTop := by
    simpa [A] using limsup_nat_add_subset (largeValueLayer f) 3
  have hlarge : volume (limsup (largeValueLayer f) atTop) ≠ 0 := by
    intro hzero
    exact hshift (le_zero_iff.mp ((measure_mono hsub).trans_eq hzero))
  have hwell :
      volume (addWellApproximable UnitAddCircle (largeValueRadius f)) ≠ 0 := by
    simpa [limsup_largeValueLayer_eq_addWellApproximable f] using hlarge
  have hfull := ae_mem_addWellApproximable_of_measure_ne_zero
    (largeValueRadius f) (tendsto_largeValueRadius_zero f) hwell
  rw [almostEverywhereApproximable_iff]
  exact hfull.mono fun x hx ↦ addWellApproximable_largeValue_subset f hx


/-- The remaining (deep) direction of the literal `ℕ → ℕ` statement.  Since
every nonzero natural value is at least one, this is the "large values" case
of Duffin--Schaeffer. -/
def DuffinSchaefferHardDirection : Prop :=
  ∀ f : ℕ → ℕ,
    duffinSchaefferSum f = ∞ → AlmostEverywhereApproximable f

/-- Exact reduction of Problem 999 to its hard Duffin--Schaeffer direction.
The reverse implication uses the Borel--Cantelli theorem proved above. -/
theorem erdos999Statement_iff_hardDirection :
    Erdos999Statement ↔ DuffinSchaefferHardDirection := by
  constructor
  · intro h f hsum
    exact (h f).2 hsum
  · intro h f
    exact ⟨divergence_of_almostEverywhereApproximable f, h f⟩

/-- The Pollington--Vaughan sieve estimate supplies the finite pair-count
bound required by the second-moment argument. -/
theorem largeValuePairCountBound : LargeValuePairCountBound := by
  refine ⟨pairOverlapConstant, pairOverlapConstant_nonneg, ?_⟩
  · intro f i j hi hj hij
    have hq : 0 < i + 1 := by omega
    have hr : 0 < j + 1 := by omega
    have hqr : i + 1 ≠ j + 1 := by omega
    simpa only [largeValueRadius] using
      overlapPairCount_le_of_zero_or_half hq hr hqr
        (by
          by_cases hfi : f (i + 1) = 0
          · exact Or.inl ((largeValueNumerator_eq_zero_iff f hq).2 hfi)
          · exact Or.inr (one_half_le_largeValueNumerator f hq hfi))
        (by
          by_cases hfj : f (j + 1) = 0
          · exact Or.inl ((largeValueNumerator_eq_zero_iff f hr).2 hfj)
          · exact Or.inr (one_half_le_largeValueNumerator f hr hfj))

/-- The hard Duffin--Schaeffer implication for the natural-valued function
in Problem 999. -/
theorem duffinSchaefferHardDirection : DuffinSchaefferHardDirection :=
  hardDirection_of_largeValuePairOverlap
    (largeValuePairOverlap_of_pairCountBound largeValuePairCountBound)

/-- Resolution of Erdős Problem 999. -/
theorem erdos_999 : Erdos999Statement :=
  erdos999Statement_iff_hardDirection.mpr duffinSchaefferHardDirection

end

end Erdos999
