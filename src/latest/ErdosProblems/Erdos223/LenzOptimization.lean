import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic

/-!
# The finite optimizations in Swanepoel's theorem

This file contains only the integer optimization layer of the eventual exact
answer to Erdős Problem 223.  Geometry enters the statements below through
explicit hypotheses bounding the cross-carrier and within-carrier diameter
counts.
-/

open Finset

namespace Erdos223

/-- The number of edges in the balanced complete `p`-partite Turán graph. -/
def turanNumber (p n : ℕ) : ℕ :=
  (SimpleGraph.turanGraph n p).edgeFinset.card

/-- The quotient/remainder formula for the Turán number used in the exact answer. -/
theorem turanNumber_eq (p n : ℕ) :
    turanNumber p n =
      (n ^ 2 - (n % p) ^ 2) * (p - 1) / (2 * p) + (n % p).choose 2 := by
  exact SimpleGraph.card_edgeFinset_turanGraph

/-- Division-with-remainder form: if `n = p*q+r`, the balanced parts consist
of `r` parts of size `q+1` and `p-r` parts of size `q`. -/
theorem turanNumber_eq_div_mod (p n : ℕ) :
    turanNumber p n =
      (n % p) * (n / p) * (p - 1) + p.choose 2 * (n / p) ^ 2 +
        (n % p).choose 2 := by
  rw [turanNumber_eq]
  rcases p.eq_zero_or_pos with rfl | hp
  · simp
  · have hmain :
        (n ^ 2 - (n % p) ^ 2) * (p - 1) / (2 * p) =
          n % p * (n / p) * (p - 1) +
            p * (p - 1) * (n / p) ^ 2 / 2 := by
      nth_rw 1 [← Nat.mod_add_div n p, Nat.sq_sub_sq, add_tsub_cancel_left,
        show (n % p + p * (n / p) + n % p) * (p * (n / p)) * (p - 1) =
          (2 * ((n % p) * (n / p) * (p - 1)) +
            p * (p - 1) * (n / p) ^ 2) * p by grind]
      rw [Nat.mul_div_mul_right _ _ hp, Nat.mul_add_div zero_lt_two]
    rw [hmain]
    have hd : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
    rw [← Nat.div_mul_right_comm hd, ← Nat.choose_two_right]

/-- Natural-number ceiling of `n / p`, with value zero when `p = 0`. -/
def ceilQuot (n p : ℕ) : ℕ := (n + p - 1) / p

@[simp] theorem ceilQuot_zero_left (p : ℕ) : ceilQuot 0 p = 0 := by
  rcases p.eq_zero_or_pos with rfl | hp
  · simp [ceilQuot]
  · simp [ceilQuot, hp]

@[simp] theorem ceilQuot_zero_right (n : ℕ) : ceilQuot n 0 = 0 := by
  simp [ceilQuot]

/-- For a positive denominator the ceiling quotient is the successor of the
quotient of the predecessor.  This form is particularly convenient for the
odd-dimensional optimization. -/
theorem ceilQuot_eq_succ_pred_div {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    ceilQuot n p = (n - 1) / p + 1 := by
  unfold ceilQuot
  rw [show n + p - 1 = (n - 1) + p by omega, Nat.add_div_right _ hp]

/-- One-vertex recurrence for Turán numbers. -/
theorem turanNumber_succ_formula {p : ℕ} (hp : 0 < p) (n : ℕ) :
    turanNumber p (n + 1) = turanNumber p n + (n - n / p) := by
  rw [turanNumber_eq_div_mod, turanNumber_eq_div_mod]
  have hnmod : n % p < p := Nat.mod_lt n hp
  have hnEq : n = n % p + p * (n / p) := (Nat.mod_add_div n p).symm
  have hqle : n / p ≤ n := Nat.div_le_self n p
  have hpPred : p - 1 + 1 = p := by omega
  have hsub : n - n / p = n % p + (p - 1) * (n / p) := by
    have hmul_aux (q : ℕ) : p * q = (p - 1) * q + q := by
      calc
        p * q = ((p - 1) + 1) * q := by rw [hpPred]
        _ = (p - 1) * q + q := by ring
    have hmul := hmul_aux (n / p)
    rw [hmul] at hnEq
    omega
  rw [hsub]
  by_cases hwrap : n % p + 1 = p
  · have hn1 : n + 1 = p * (n / p + 1) := by
      calc
        n + 1 = n % p + p * (n / p) + 1 := by omega
        _ = (n % p + 1) + p * (n / p) := by omega
        _ = p + p * (n / p) := by rw [hwrap]
        _ = p * (n / p + 1) := by ring
    have hmod : (n + 1) % p = 0 := by rw [hn1, Nat.mul_mod_right]
    have hdiv : (n + 1) / p = n / p + 1 := by
      rw [hn1, mul_comm, Nat.mul_div_left _ hp]
    rw [hmod, hdiv]
    simp only [zero_mul, Nat.choose_zero_succ, zero_add]
    have hpSub : p - 1 = n % p := by omega
    have hchoose : p.choose 2 = (n % p).choose 2 + n % p := by
      calc
        p.choose 2 = (n % p + 1).choose 2 := congrArg (Nat.choose · 2) hwrap.symm
        _ = (n % p).choose 2 + n % p := by
          rw [Nat.choose_succ_succ]
          simp [add_comm]
    rw [hpSub, hchoose]
    have hdouble : 2 * (n % p).choose 2 = n % p * (n % p - 1) := by
      rw [mul_comm 2, Nat.choose_two_right,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (n % p))]
    by_cases hr0 : n % p = 0
    · simp [hr0]
    · have hrpos : 1 ≤ n % p := Nat.one_le_iff_ne_zero.mpr hr0
      have hdoubleZ :
          (2 : ℤ) * ((n % p).choose 2 : ℤ) =
            ((n % p : ℕ) : ℤ) * (((n % p : ℕ) : ℤ) - 1) := by
        convert congrArg (fun x : ℕ ↦ (x : ℤ)) hdouble using 1 <;>
          simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hrpos]
        all_goals norm_num
      rw [← Int.ofNat_inj]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      linear_combination ((n / p : ℕ) : ℤ) * hdoubleZ
  · have hlt : n % p + 1 < p := by omega
    have hn1 : n + 1 = (n % p + 1) + p * (n / p) := by omega
    have hmod : (n + 1) % p = n % p + 1 := by
      rw [hn1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hdiv : (n + 1) / p = n / p := by
      rw [hn1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, zero_add]
    rw [hmod, hdiv]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]
    ring

/-- The form of the recurrence used by the odd-dimensional Lenz
optimization. -/
theorem turanNumber_pred_add_formula {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    turanNumber p (n - 1) + n = turanNumber p n + ceilQuot n p := by
  have hrec := turanNumber_succ_formula hp (n - 1)
  rw [show n - 1 + 1 = n by omega] at hrec
  rw [hrec, ceilQuot_eq_succ_pred_div hn hp]
  have hqle : (n - 1) / p ≤ n - 1 := Nat.div_le_self _ _
  omega

/-- The familiar product formula for the balanced complete bipartite graph. -/
theorem turanNumber_two (n : ℕ) :
    turanNumber 2 n = (n / 2) * (n - n / 2) := by
  rw [turanNumber_eq]
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with hr | hr <;> rw [hr] <;> norm_num
  · have hn : n = 2 * (n / 2) := by omega
    have hdvd : 4 ∣ n ^ 2 := by
      use (n / 2) ^ 2
      nlinarith
    apply (Nat.div_eq_iff_eq_mul_left (by norm_num) hdvd).2
    have hsub : n - n / 2 = n / 2 := by omega
    rw [hsub]
    nlinarith
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hsquare : n ^ 2 = 4 * ((n / 2) * (n / 2 + 1)) + 1 := by
      nlinarith
    have hdvd : 4 ∣ n ^ 2 - 1 := by
      use (n / 2) * (n / 2 + 1)
      omega
    apply (Nat.div_eq_iff_eq_mul_left (by norm_num) hdvd).2
    have hsub : n - n / 2 = n / 2 + 1 := by omega
    rw [hsub]
    omega

/-- Among two nonnegative part sizes of fixed sum, the cross term is maximized
by the balanced split. -/
theorem mul_le_turanNumber_two {a b n : ℕ} (hsum : a + b = n) :
    a * b ≤ turanNumber 2 n := by
  have hsumz : (a : ℤ) + b = n := by exact_mod_cast hsum
  have hz : 4 * (a : ℤ) * b ≤ (n : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  have hquad : 4 * a * b ≤ n ^ 2 := by exact_mod_cast hz
  rw [turanNumber_two]
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with hr | hr
  · have hn : n = 2 * (n / 2) := by omega
    have hsub : n - n / 2 = n / 2 := by omega
    rw [hsub]
    nlinarith
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hsub : n - n / 2 = n / 2 + 1 := by omega
    rw [hsub]
    nlinarith

/-- Adding one vertex to the balanced bipartite graph creates `ceil (n / 2)`
new cross edges. -/
theorem turanNumber_two_succ (n : ℕ) :
    turanNumber 2 (n + 1) = turanNumber 2 n + ceilQuot n 2 := by
  rw [turanNumber_two, turanNumber_two]
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with hr | hr
  · have hn : n = 2 * (n / 2) := by omega
    have hsdiv : (n + 1) / 2 = n / 2 := by omega
    have hsub : n - n / 2 = n / 2 := by omega
    have hsub' : n + 1 - (n + 1) / 2 = n / 2 + 1 := by omega
    have hceil : ceilQuot n 2 = n / 2 := by
      unfold ceilQuot
      omega
    rw [hsub', hsdiv, hsub, hceil]
    ring
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hsdiv : (n + 1) / 2 = n / 2 + 1 := by omega
    have hsub : n - n / 2 = n / 2 + 1 := by omega
    have hsub' : n + 1 - (n + 1) / 2 = n / 2 + 1 := by omega
    have hceil : ceilQuot n 2 = n / 2 + 1 := by
      unfold ceilQuot
      omega
    rw [hsub', hsdiv, hsub, hceil]
    ring

/-- If `n = 3 (mod 4)` and the first part is odd, the artificially shifted
split `(a, b + 1)` cannot be balanced: its product misses the balanced
maximum by at least one.  This is the parity correction in dimension four. -/
theorem odd_shifted_mul_add_one_le_turanNumber_two
    {a b n : ℕ} (hsum : a + b = n) (ha : a % 2 = 1) (hn : n % 4 = 3) :
    a * (b + 1) + 1 ≤ turanNumber 2 (n + 1) := by
  let q := (n + 1) / 2
  have hnq : n + 1 = 2 * q := by
    dsimp [q]
    omega
  have hqeven : q % 2 = 0 := by
    dsimp [q]
    omega
  have hane : a ≠ q := by omega
  have haneZ : (a : ℤ) - q ≠ 0 := by
    intro h
    apply hane
    have heq : (a : ℤ) = q := sub_eq_zero.mp h
    exact_mod_cast heq
  have hsquare : (1 : ℤ) ≤ ((a : ℤ) - q) ^ 2 := by
    have := sq_pos_of_ne_zero haneZ
    omega
  have hsumz : (a : ℤ) + b = n := by exact_mod_cast hsum
  have hnqz : (n : ℤ) + 1 = 2 * q := by exact_mod_cast hnq
  have hprodZ : (a : ℤ) * (b + 1) + 1 ≤ (q : ℤ) ^ 2 := by
    nlinarith
  have hprod : a * (b + 1) + 1 ≤ q ^ 2 := by exact_mod_cast hprodZ
  rw [turanNumber_two]
  have hdiv : (n + 1) / 2 = q := rfl
  have hsub : n + 1 - (n + 1) / 2 = q := by omega
  rw [hdiv, hsub, ← sq]
  exact hprod

/-- The sharp internal-diameter allowance for the active circle in the
four-dimensional Lenz optimization. -/
def cyclicDiameterAllowance (m : ℕ) : ℕ :=
  if m % 2 = 0 then m - 1 else m

/-- The exceptional correction in dimension four. -/
def fourCorrection (n : ℕ) : ℕ :=
  if n % 4 = 3 then 0 else 1

/-- Ordered cross-pairs belonging to distinct parts.  Every unordered
cross-pair is counted twice. -/
def orderedCrossNumber {p : ℕ} (f : Fin p → ℕ) : ℕ :=
  ∑ i, ∑ j with i ≠ j, f i * f j

/-- Turán's theorem, in the numerical form needed for arbitrary carrier part
sizes.  The proof realizes the sum as twice the number of edges of a complete
multipartite graph and applies Mathlib's exact Turán bound. -/
theorem orderedCrossNumber_le_twice_turanNumber {p : ℕ} (f : Fin p → ℕ) :
    orderedCrossNumber f ≤ 2 * turanNumber p (∑ i, f i) := by
  let H : SimpleGraph (Σ i, Fin (f i)) :=
    ⟨fun x y ↦ x.1 ≠ y.1, by tauto, by tauto⟩
  have cfH : H.CliqueFree (p + 1) := fun s ⟨hs₁, hs₂⟩ ↦ by
    have hc := (s.image (·.1)).card_le_univ
    rw [Fintype.card_fin] at hc
    apply absurd hc
    have hi : (SetLike.coe s).InjOn (·.1) :=
      fun v hv w hw e ↦ not_imp_not.mp (hs₁ hv hw) e
    rw [not_le, card_image_of_injOn hi]
    omega
  have hT := cfH.card_edgeFinset_le
  simp_rw [← SimpleGraph.card_edgeFinset_turanGraph] at hT
  rw [show Fintype.card (Σ i, Fin (f i)) = ∑ i, f i by simp] at hT
  have hH : orderedCrossNumber f = 2 * H.edgeFinset.card := by
    have degree_eq_sum (i : Σ i, Fin (f i)) :
        H.degree i = ∑ j, if H.Adj i j then 1 else 0 :=
      H.degree_eq_sum_if_adj i
    simp_rw [orderedCrossNumber, ← SimpleGraph.sum_degrees_eq_twice_card_edges,
      degree_eq_sum, Fintype.sum_sigma, H]
    have rsum (c₁ c₂ : Fin p) :
        (∑ _x : Fin (f c₁), ∑ _y : Fin (f c₂), if c₁ ≠ c₂ then 1 else 0) =
          if c₁ ≠ c₂ then f c₁ * f c₂ else 0 := by simp
    conv_rhs =>
      enter [2, c₁]
      rw [sum_comm]
      enter [2, c₂]
      rw [rsum]
    simp_rw [sum_filter]
  rwa [hH, mul_le_mul_iff_right₀ zero_lt_two]

/-- The unordered complete-multipartite cross count. -/
def crossNumber {p : ℕ} (f : Fin p → ℕ) : ℕ := orderedCrossNumber f / 2

theorem crossNumber_le_turanNumber {p : ℕ} (f : Fin p → ℕ) :
    crossNumber f ≤ turanNumber p (∑ i, f i) := by
  apply Nat.div_le_of_le_mul
  simpa [mul_comm] using orderedCrossNumber_le_twice_turanNumber f

theorem four_partition_objective_le
    {a b n : ℕ} (hn : 2 ≤ n) (hsum : a + b = n) :
    a * b + cyclicDiameterAllowance a + 1 ≤
      turanNumber 2 n + ceilQuot n 2 + fourCorrection n := by
  have hshift : a + (b + 1) = n + 1 := by omega
  by_cases ha0 : a = 0
  · subst a
    have hqpos : 0 < n / 2 := by omega
    have hrestpos : 0 < n - n / 2 := by omega
    have htpos : 1 ≤ turanNumber 2 n := by
      rw [turanNumber_two]
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hqpos.ne' hrestpos.ne')
    simpa [cyclicDiameterAllowance, add_assoc] using
      htpos.trans (Nat.le_add_right (turanNumber 2 n)
        (ceilQuot n 2 + fourCorrection n))
  · by_cases ha : a % 2 = 0
    · have hprod := mul_le_turanNumber_two hshift
      rw [turanNumber_two_succ] at hprod
      calc
        a * b + cyclicDiameterAllowance a + 1 = a * b + a := by
          simp only [cyclicDiameterAllowance, if_pos ha]
          have hapos : 0 < a := Nat.pos_of_ne_zero ha0
          omega
        _ = a * (b + 1) := by ring
        _ ≤ turanNumber 2 n + ceilQuot n 2 := hprod
        _ ≤ turanNumber 2 n + ceilQuot n 2 + fourCorrection n :=
          Nat.le_add_right _ _
    · have haodd : a % 2 = 1 := by omega
      by_cases hn3 : n % 4 = 3
      · have hprod := odd_shifted_mul_add_one_le_turanNumber_two hsum haodd hn3
        rw [turanNumber_two_succ] at hprod
        simpa [cyclicDiameterAllowance, ha, fourCorrection, hn3, mul_add] using hprod
      · have hprod := mul_le_turanNumber_two hshift
        rw [turanNumber_two_succ] at hprod
        have hprod' := Nat.add_le_add_right hprod 1
        simpa [cyclicDiameterAllowance, ha, fourCorrection, hn3, mul_add] using hprod'

/-! ## Interfaces for the geometric carrier theorems -/

/-- Dimension four: cross diameters are complete bipartite, one circle has
the parity-dependent local allowance, and the other has at most one local
diameter. -/
theorem four_upper_of_carrier
    {a b n localEdges e : ℕ} (hn : 2 ≤ n) (hsum : a + b = n)
    (hlocal : localEdges ≤ cyclicDiameterAllowance a)
    (hedge : e ≤ a * b + localEdges + 1) :
    e ≤ turanNumber 2 n + ceilQuot n 2 + fourCorrection n := by
  exact hedge.trans <| (Nat.add_le_add_right
    (Nat.add_le_add_left hlocal (a * b)) 1).trans <|
      four_partition_objective_le hn hsum

theorem four_eq_of_carrier
    {a b n localEdges e : ℕ} (hn : 2 ≤ n) (hsum : a + b = n)
    (hlocal : localEdges ≤ cyclicDiameterAllowance a)
    (hedge : e ≤ a * b + localEdges + 1)
    (hlower : turanNumber 2 n + ceilQuot n 2 + fourCorrection n ≤ e) :
    e = turanNumber 2 n + ceilQuot n 2 + fourCorrection n :=
  le_antisymm (four_upper_of_carrier hn hsum hlocal hedge) hlower

/-- Dimension five: after the geometric one-step exchange argument, the
total local contribution is at most the number of vertices. -/
theorem five_upper_of_carrier
    {sphere circle n localEdges e : ℕ} (hsum : sphere + circle = n)
    (hlocal : localEdges ≤ n) (hedge : e ≤ sphere * circle + localEdges) :
    e ≤ turanNumber 2 n + n := by
  have hcross := mul_le_turanNumber_two hsum
  omega

theorem five_eq_of_carrier
    {sphere circle n localEdges e : ℕ} (hsum : sphere + circle = n)
    (hlocal : localEdges ≤ n) (hedge : e ≤ sphere * circle + localEdges)
    (hlower : turanNumber 2 n + n ≤ e) :
    e = turanNumber 2 n + n :=
  le_antisymm (five_upper_of_carrier hsum hlocal hedge) hlower

/-- Even dimensions at least six: the carrier theorem supplies part sizes,
all cross pairs, and at most one local diameter per carrier.  The arithmetic
conclusion itself only needs the displayed hypotheses. -/
theorem even_upper_of_carrier
    {p n cross localEdges e : ℕ} {parts : Fin p → ℕ}
    (hsum : ∑ i, parts i = n) (hcross : cross ≤ crossNumber parts)
    (hlocal : localEdges ≤ p) (hedge : e ≤ cross + localEdges) :
    e ≤ turanNumber p n + p := by
  have hT := crossNumber_le_turanNumber parts
  rw [hsum] at hT
  omega

theorem even_eq_of_carrier
    {p n cross localEdges e : ℕ} {parts : Fin p → ℕ}
    (hsum : ∑ i, parts i = n) (hcross : cross ≤ crossNumber parts)
    (hlocal : localEdges ≤ p) (hedge : e ≤ cross + localEdges)
    (hlower : turanNumber p n + p ≤ e) :
    e = turanNumber p n + p :=
  le_antisymm (even_upper_of_carrier hsum hcross hlocal hedge) hlower

/-- Odd dimensions at least seven: `shiftedParts` are obtained by removing
one vertex from the sphere part.  Thus they have total `n-1`, and the sphere
term plus the original cross term is bounded by their cross count plus `n`.
The remaining `p-1` circle parts contribute at most one local diameter each. -/
theorem odd_upper_of_carrier
    {p n cross sphereLocal circleLocal e : ℕ}
    {shiftedParts : Fin p → ℕ} (hp : 0 < p) (hn : 0 < n)
    (hsum : ∑ i, shiftedParts i = n - 1)
    (hshift : cross + sphereLocal ≤ crossNumber shiftedParts + n)
    (hcircle : circleLocal ≤ p - 1)
    (hedge : e ≤ cross + sphereLocal + circleLocal) :
    e ≤ turanNumber p n + ceilQuot n p + (p - 1) := by
  have hT := crossNumber_le_turanNumber shiftedParts
  rw [hsum] at hT
  have hrec := turanNumber_pred_add_formula hp hn
  omega

theorem odd_eq_of_carrier
    {p n cross sphereLocal circleLocal e : ℕ}
    {shiftedParts : Fin p → ℕ} (hp : 0 < p) (hn : 0 < n)
    (hsum : ∑ i, shiftedParts i = n - 1)
    (hshift : cross + sphereLocal ≤ crossNumber shiftedParts + n)
    (hcircle : circleLocal ≤ p - 1)
    (hedge : e ≤ cross + sphereLocal + circleLocal)
    (hlower : turanNumber p n + ceilQuot n p + (p - 1) ≤ e) :
    e = turanNumber p n + ceilQuot n p + (p - 1) :=
  le_antisymm
    (odd_upper_of_carrier hp hn hsum hshift hcircle hedge) hlower

end Erdos223
