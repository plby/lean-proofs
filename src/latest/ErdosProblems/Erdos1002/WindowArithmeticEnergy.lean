import ErdosProblems.Erdos1002.WindowKernelCoefficientBound
import ErdosProblems.Erdos1002.WindowKernelEnvelope
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From the divisor window envelope to the finite arithmetic energy

This module connects `WindowKernelEnvelope` to the exact finite reduction
`windowModeArithmeticEnergy` from `WindowErrorReduction`.  The proof keeps
the summable `d^{-5/2}` factor; replacing it by `d^{-2}` would create a
spurious logarithm after the window envelope contributes a factor `d`.

All rearrangements below are finite.  The only analytic input is an
explicit squared-kernel decay hypothesis, isolated in the statement of the
energy theorem so that it can be discharged by the Fourier calculation.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-! ## Elementary arithmetic factors -/

/-- The reciprocal divisor sum is submultiplicative.  No coprimality is
required: duplicate products of divisors only make the double sum larger. -/
theorem reciprocalDivisorSum_mul_le (a b : ℕ) :
    reciprocalDivisorSum (a * b) ≤
      reciprocalDivisorSum a * reciprocalDivisorSum b := by
  unfold reciprocalDivisorSum
  rw [Nat.divisors_mul, Finset.mul_def]
  calc
    (∑ d ∈ Finset.image (fun z : ℕ × ℕ ↦ z.1 * z.2)
        (a.divisors.product b.divisors), 1 / (d : ℝ)) ≤
      ∑ z ∈ a.divisors.product b.divisors,
        1 / ((z.1 * z.2 : ℕ) : ℝ) := by
      exact Finset.sum_image_le_of_nonneg fun d hd ↦ by positivity
    _ = ∑ x ∈ a.divisors, ∑ y ∈ b.divisors,
        (1 / (x : ℝ)) * (1 / (y : ℝ)) := by
      change (∑ z ∈ a.divisors ×ˢ b.divisors,
        1 / ((z.1 * z.2 : ℕ) : ℝ)) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Nat.cast_mul]
      field_simp
    _ = (∑ x ∈ a.divisors, 1 / (x : ℝ)) *
        ∑ y ∈ b.divisors, 1 / (y : ℝ) := by
      rw [Finset.sum_mul_sum]

/-- The convergent `d^{-3/2}` constant occurring in the first weighted
Cauchy--Schwarz factor. -/
def windowCauchyDConstant : ℝ :=
  ∑' d : ℕ, 1 / Real.sqrt ((d : ℝ) ^ 3)

private theorem sqrt_cube_eq_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast_mul hx 3 (1 / 2 : ℝ)]
  norm_num

theorem summable_windowCauchyDTerm :
    Summable fun d : ℕ ↦ 1 / Real.sqrt ((d : ℝ) ^ 3) := by
  have hp : Summable fun d : ℕ ↦ 1 / (d : ℝ) ^ (3 / 2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  apply hp.congr
  intro d
  rw [sqrt_cube_eq_rpow_three_halves (d : ℝ) (by positivity)]

theorem windowCauchyDConstant_nonneg : 0 ≤ windowCauchyDConstant := by
  exact tsum_nonneg fun d ↦ by positivity

theorem sum_inv_sqrt_cube_le_constant (P : ℕ) :
    (∑ d ∈ Icc 1 P, 1 / Real.sqrt ((d : ℝ) ^ 3)) ≤
      windowCauchyDConstant := by
  exact summable_windowCauchyDTerm.sum_le_tsum (Icc 1 P)
    (fun d hd ↦ by positivity)

/-- The first finite Cauchy--Schwarz mass is bounded by a universal
`d`-constant times `sigma_{-1}(n)`. -/
theorem windowWeightMass_le_reciprocalDivisorSum
    {P n : ℕ} (hn : 0 < n) :
    windowWeightMass P n ≤
      windowCauchyDConstant * reciprocalDivisorSum n := by
  let T : Finset (ℕ × ℕ) := (Icc 1 P).product n.divisors
  have hsub : windowDivisorPairs P n ⊆ T := by
    intro z hz
    rcases mem_windowDivisorPairs_iff.mp hz with
      ⟨hd1, hdP, hr1, hrP, hdr, hrn⟩
    change z ∈ (Icc 1 P).product n.divisors
    exact Finset.mem_product.mpr
      ⟨mem_Icc.mpr ⟨hd1, hdP⟩, Nat.mem_divisors.mpr ⟨hrn, hn.ne'⟩⟩
  have hdrop : windowWeightMass P n ≤
      ∑ z ∈ T, windowCauchyWeight z := by
    unfold windowWeightMass
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro z hzT hznot
    unfold windowCauchyWeight
    positivity
  calc
    windowWeightMass P n ≤ ∑ z ∈ T, windowCauchyWeight z := hdrop
    _ = (∑ d ∈ Icc 1 P, 1 / Real.sqrt ((d : ℝ) ^ 3)) *
        ∑ r ∈ n.divisors, 1 / (r : ℝ) := by
      change (∑ z ∈ (Icc 1 P).product n.divisors,
        windowCauchyWeight z) = _
      calc
        (∑ z ∈ (Icc 1 P).product n.divisors, windowCauchyWeight z) =
            ∑ d ∈ Icc 1 P, ∑ r ∈ n.divisors,
              windowCauchyWeight (d, r) :=
          Finset.sum_product (Icc 1 P) n.divisors windowCauchyWeight
        _ = ∑ d ∈ Icc 1 P, ∑ r ∈ n.divisors,
              (1 / Real.sqrt ((d : ℝ) ^ 3)) * (1 / (r : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro r hr
          unfold windowCauchyWeight
          ring
        _ = (∑ d ∈ Icc 1 P, 1 / Real.sqrt ((d : ℝ) ^ 3)) *
              ∑ r ∈ n.divisors, 1 / (r : ℝ) := by
          rw [Finset.sum_mul_sum]
    _ ≤ windowCauchyDConstant *
        ∑ r ∈ n.divisors, 1 / (r : ℝ) := by
      apply mul_le_mul_of_nonneg_right (sum_inv_sqrt_cube_le_constant P)
      positivity
    _ = windowCauchyDConstant * reciprocalDivisorSum n := by rfl

/-- A second convergent `p`-series constant, used for the average over
the quotient variable `r`. -/
def windowReciprocalSquareConstant : ℝ :=
  ∑' a : ℕ, 1 / (a : ℝ) ^ 2

theorem summable_windowReciprocalSquareTerm :
    Summable fun a : ℕ ↦ 1 / (a : ℝ) ^ 2 :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

theorem windowReciprocalSquareConstant_nonneg :
    0 ≤ windowReciprocalSquareConstant := by
  exact tsum_nonneg fun a ↦ by positivity

theorem sum_reciprocalDivisorSum_div_le
    (P : ℕ) :
    (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) ≤
      windowReciprocalSquareConstant * (harmonic P : ℝ) := by
  have hexpand :
      (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) =
        ∑ a ∈ Icc 1 P, (1 / (a : ℝ)) *
          ∑ r ∈ Icc 1 P,
            if a ∣ r then 1 / (r : ℝ) else 0 := by
    calc
      (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) =
          ∑ r ∈ Icc 1 P, ∑ a ∈ Icc 1 P,
            if a ∣ r then (1 / (a : ℝ)) * (1 / (r : ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [reciprocalDivisorSum, divisors_eq_filter_dvd_Icc hr]
        rw [Finset.sum_filter]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases har : a ∣ r <;> simp [har, div_eq_mul_inv]
      _ = ∑ a ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
          if a ∣ r then (1 / (a : ℝ)) * (1 / (r : ℝ)) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ a ∈ Icc 1 P, (1 / (a : ℝ)) *
          ∑ r ∈ Icc 1 P,
            if a ∣ r then 1 / (r : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        split_ifs <;> simp
  rw [hexpand]
  have hH : 0 ≤ (harmonic P : ℝ) := by
    by_cases hP : P = 0
    · simp [hP]
    · exact_mod_cast (harmonic_pos hP).le
  calc
    (∑ a ∈ Icc 1 P, (1 / (a : ℝ)) *
        ∑ r ∈ Icc 1 P,
          if a ∣ r then 1 / (r : ℝ) else 0) ≤
      ∑ a ∈ Icc 1 P,
        (1 / (a : ℝ) ^ 2) * (harmonic P : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have haPos : 0 < a := (mem_Icc.mp ha).1
      have hmultiple := sum_recip_multiples_Icc_le_harmonic P a haPos
      calc
        (1 / (a : ℝ)) *
            (∑ r ∈ Icc 1 P,
              if a ∣ r then 1 / (r : ℝ) else 0) ≤
          (1 / (a : ℝ)) *
            ((1 / (a : ℝ)) * (harmonic P : ℝ)) :=
          mul_le_mul_of_nonneg_left hmultiple (by positivity)
        _ = (1 / (a : ℝ) ^ 2) * (harmonic P : ℝ) := by ring
    _ = (∑ a ∈ Icc 1 P, 1 / (a : ℝ) ^ 2) *
        (harmonic P : ℝ) := by rw [Finset.sum_mul]
    _ ≤ windowReciprocalSquareConstant * (harmonic P : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact summable_windowReciprocalSquareTerm.sum_le_tsum (Icc 1 P)
          (fun a ha ↦ by positivity)
      · exact hH

/-! ## A signed-carrier form of the coefficient bound -/

/-- The decay profile as a function of distance alone. -/
def windowDistanceDecayWeight (d r : ℕ) : ℝ :=
  if r ≤ d then 1 else (d : ℝ) ^ 2 / (r : ℝ) ^ 2

theorem windowDecayWeight_eq_distance (d m M : ℕ) :
    windowDecayWeight d m M =
      windowDistanceDecayWeight d (Nat.dist m M) := by
  rfl

theorem windowDistanceDecayWeight_nonneg (d r : ℕ) :
    0 ≤ windowDistanceDecayWeight d r := by
  unfold windowDistanceDecayWeight
  split_ifs <;> positivity

theorem windowDistanceDecayWeight_antitone
    {d r s : ℕ} (hrs : r ≤ s) :
    windowDistanceDecayWeight d s ≤ windowDistanceDecayWeight d r := by
  unfold windowDistanceDecayWeight
  by_cases hr : r ≤ d
  · rw [if_pos hr]
    split_ifs
    · exact le_rfl
    · have hds : d < s := Nat.lt_of_not_ge ‹¬s ≤ d›
      have hs0 : (0 : ℝ) < (s : ℝ) := by
        exact_mod_cast lt_of_le_of_lt (Nat.zero_le d) hds
      rw [div_le_one (sq_pos_of_pos hs0)]
      have hdS : (d : ℝ) ≤ (s : ℝ) := by exact_mod_cast hds.le
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hdS
  · have hdr : d < r := Nat.lt_of_not_ge hr
    have hds : ¬d ≥ s := by omega
    rw [if_neg hds, if_neg hr]
    have hr0 : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le d) hdr
    have hs0 : (0 : ℝ) < (s : ℝ) := by
      exact_mod_cast
        (lt_of_le_of_lt (Nat.zero_le d) (lt_of_lt_of_le hdr hrs))
    have hrsR : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
    apply (div_le_div_iff₀ (sq_pos_of_pos hs0) (sq_pos_of_pos hr0)).2
    have hsquare : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 :=
      (sq_le_sq₀ hr0.le hs0.le).2 hrsR
    exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg (d : ℝ))

theorem windowDecayWeight_le_of_dist_le
    {d m₁ M₁ m₂ M₂ : ℕ}
    (h : Nat.dist m₁ M₁ ≤ Nat.dist m₂ M₂) :
    windowDecayWeight d m₂ M₂ ≤ windowDecayWeight d m₁ M₁ := by
  rw [windowDecayWeight_eq_distance, windowDecayWeight_eq_distance]
  exact windowDistanceDecayWeight_antitone h

/-- Natural centre dominating a signed carrier. -/
def windowCarrierCenter (N d : ℕ) (ell : ℤ) : ℕ :=
  ell.natAbs * N * d

/-- The actual coefficient estimate in the coordinates of every signed
carrier.  Negative carriers are no worse than the reflected positive
centre because `|m+M| ≥ |m-M|` for `m,M ≥ 0`. -/
theorem norm_sq_windowKernelCoefficient_carrier_le
    (N d m : ℕ) (ell : ℤ) (hd : 0 < d) :
    ‖windowKernelCoefficient d
        ((m : ℤ) - ell * ((N * d : ℕ) : ℤ))‖ ^ 2 ≤
      144 * windowDecayWeight d m (windowCarrierCenter N d ell) := by
  by_cases hell : 0 ≤ ell
  · have hellEq : ell = (ell.natAbs : ℤ) :=
      (Int.natAbs_of_nonneg hell).symm
    have hcenter :
        ((windowCarrierCenter N d ell : ℕ) : ℤ) =
          ell * ((N * d : ℕ) : ℤ) := by
      unfold windowCarrierCenter
      push_cast
      rw [abs_of_nonneg hell]
      ring
    rw [← hcenter]
    exact norm_sq_windowKernelCoefficient_nat_sub_le
      d m (windowCarrierCenter N d ell) hd
  · have hellNeg : ell < 0 := lt_of_not_ge hell
    let C : ℕ := windowCarrierCenter N d ell
    have hellEq : ell = -(ell.natAbs : ℤ) := by
      have habs : |ell| = -ell := abs_of_neg hellNeg
      rw [← Int.natCast_natAbs] at habs
      omega
    have hcenter :
        ((C : ℕ) : ℤ) =
          (ell.natAbs : ℤ) * ((N * d : ℕ) : ℤ) := by
      dsimp [C, windowCarrierCenter]
      push_cast
      ring
    have harg :
        (m : ℤ) - ell * ((N * d : ℕ) : ℤ) =
          ((m + C : ℕ) : ℤ) - (0 : ℤ) := by
      rw [hellEq, neg_mul, sub_neg_eq_add]
      push_cast
      rw [hcenter]
      rw [← Int.natCast_natAbs]
      push_cast
      ring
    rw [harg]
    have hbase := norm_sq_windowKernelCoefficient_nat_sub_le
      d (m + C) 0 hd
    have hdist : Nat.dist m C ≤ Nat.dist (m + C) 0 := by
      have hright : Nat.dist (m + C) 0 = m + C := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.zero_le (m + C))]
        simp
      rw [hright]
      by_cases hmC : m ≤ C
      · rw [Nat.dist_eq_sub_of_le hmC]
        omega
      · have hCm : C ≤ m := Nat.le_of_not_ge hmC
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hCm]
        omega
    have hweight : windowDecayWeight d (m + C) 0 ≤
        windowDecayWeight d m C :=
      windowDecayWeight_le_of_dist_le hdist
    exact hbase.trans (mul_le_mul_of_nonneg_left hweight (by norm_num))

/-! ## Finite quotient rearrangement -/

theorem sum_divisible_quotient_eq
    (K r : ℕ) (hr : 0 < r) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 K, if r ∣ n then f (n / r) else 0) =
      ∑ m ∈ Icc 1 (K / r), f m := by
  let A : Finset ℕ := positiveMultiplesIcc K r
  let B : Finset ℕ := Icc 1 (K / r)
  let e : {n // n ∈ A} ≃ {m // m ∈ B} :=
    positiveMultiplesIccEquiv K r hr
  have hleft :
      (∑ n ∈ Icc 1 K, if r ∣ n then f (n / r) else 0) =
        ∑ n ∈ A, f (n / r) := by
    symm
    simpa only [A, positiveMultiplesIcc] using!
      Finset.sum_filter (s := Icc 1 K) (p := fun n ↦ r ∣ n)
        (f := fun n ↦ f (n / r))
  rw [hleft]
  calc
    (∑ n ∈ A, f (n / r)) =
        ∑ n : {n // n ∈ A}, f ((n : ℕ) / r) := by
      exact (Finset.sum_attach A (fun n ↦ f (n / r))).symm
    _ = ∑ m : {m // m ∈ B}, f (m : ℕ) := by
      apply Fintype.sum_equiv e
      intro n
      rfl
    _ = ∑ m ∈ B, f m :=
      Finset.sum_attach B f
    _ = ∑ m ∈ Icc 1 (K / r), f m := by rfl

theorem sum_divisible_quotient_le
    (K r : ℕ) (hr : 0 < r) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m) :
    (∑ n ∈ Icc 1 K, if r ∣ n then f (n / r) else 0) ≤
      ∑ m ∈ Icc 1 K, f m := by
  rw [sum_divisible_quotient_eq K r hr f]
  have hsub : Icc 1 (K / r) ⊆ Icc 1 K := by
    intro m hm
    rw [mem_Icc] at hm ⊢
    exact ⟨hm.1, hm.2.trans (Nat.div_le_self K r)⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun m hm hnot ↦ hf m)

/-- The exact `d^{-5/2}r^{-1}` form hidden inside
`windowKernelWeightedEnergy`. -/
def windowSimplifiedKernelEnergy
    (N P : ℕ) (ell : ℤ) (n : ℕ) : ℝ :=
  ∑ z ∈ windowDivisorPairs P n,
    ‖windowKernelCoefficient z.1
      (((n / z.2 : ℕ) : ℤ) -
        ell * ((N * z.1 : ℕ) : ℤ))‖ ^ 2 /
      ((z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ))

theorem windowKernelWeightedEnergy_eq_simplified
    (N P : ℕ) (ell : ℤ) (n : ℕ) :
    windowKernelWeightedEnergy N P ell n =
      windowSimplifiedKernelEnergy N P ell n := by
  unfold windowKernelWeightedEnergy windowSimplifiedKernelEnergy
  apply Finset.sum_congr rfl
  intro z hz
  have hz' := mem_windowDivisorPairs_iff.mp hz
  have hd : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hz'.1
  have hr : (0 : ℝ) < (z.2 : ℝ) := by exact_mod_cast hz'.2.2.1
  have hsqrt : Real.sqrt ((z.1 : ℝ) ^ 3) =
      (z.1 : ℝ) * Real.sqrt (z.1 : ℝ) := by
    rw [show (z.1 : ℝ) ^ 3 = (z.1 : ℝ) ^ 2 * z.1 by ring,
      Real.sqrt_mul (sq_nonneg (z.1 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos hd]
  have hsqrtPos : 0 < Real.sqrt (z.1 : ℝ) := Real.sqrt_pos.2 hd
  unfold windowCauchyWeight
  rw [hsqrt]
  field_simp
  rw [Real.sq_sqrt hd.le]

theorem windowSimplifiedKernelEnergy_le_decay
    (N P : ℕ) (ell : ℤ) (n : ℕ) :
    windowSimplifiedKernelEnergy N P ell n ≤
      ∑ z ∈ windowDivisorPairs P n,
        144 * windowDecayWeight z.1 (n / z.2)
            (windowCarrierCenter N z.1 ell) /
          ((z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ)) := by
  unfold windowSimplifiedKernelEnergy
  apply Finset.sum_le_sum
  intro z hz
  have hz' := mem_windowDivisorPairs_iff.mp hz
  have hden : 0 ≤
      (z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ) := by positivity
  apply div_le_div_of_nonneg_right _ hden
  exact norm_sq_windowKernelCoefficient_carrier_le
    N z.1 (n / z.2) ell (by omega)

theorem sum_divisible_reciprocalDivisor_carrier_le
    (N K d r : ℕ) (ell : ℤ) (hr : 0 < r) :
    (∑ n ∈ Icc 1 K,
        if r ∣ n then
          reciprocalDivisorSum n *
            windowDecayWeight d (n / r) (windowCarrierCenter N d ell)
        else 0) ≤
      reciprocalDivisorSum r *
        finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d := by
  let f : ℕ → ℝ := fun m ↦
    reciprocalDivisorSum m *
      windowDecayWeight d m (windowCarrierCenter N d ell)
  have hf : ∀ m, 0 ≤ f m := by
    intro m
    exact mul_nonneg (reciprocalDivisorSum_nonneg m)
      (windowDecayWeight_nonneg d m (windowCarrierCenter N d ell))
  have hpoint : ∀ n ∈ Icc 1 K,
      (if r ∣ n then
          reciprocalDivisorSum n *
            windowDecayWeight d (n / r) (windowCarrierCenter N d ell)
        else 0) ≤
      (if r ∣ n then reciprocalDivisorSum r * f (n / r) else 0) := by
    intro n hn
    by_cases hrn : r ∣ n
    · simp only [hrn, if_true]
      have hnEq : r * (n / r) = n := Nat.mul_div_cancel' hrn
      have hsigma : reciprocalDivisorSum n ≤
          reciprocalDivisorSum r * reciprocalDivisorSum (n / r) := by
        calc
          reciprocalDivisorSum n =
              reciprocalDivisorSum (r * (n / r)) := by rw [hnEq]
          _ ≤ reciprocalDivisorSum r * reciprocalDivisorSum (n / r) :=
            reciprocalDivisorSum_mul_le r (n / r)
      dsimp [f]
      simpa only [mul_assoc] using!
        (mul_le_mul_of_nonneg_right hsigma
          (windowDecayWeight_nonneg d (n / r) (windowCarrierCenter N d ell)))
    · simp [hrn]
  calc
    (∑ n ∈ Icc 1 K,
        if r ∣ n then
          reciprocalDivisorSum n *
            windowDecayWeight d (n / r) (windowCarrierCenter N d ell)
        else 0) ≤
      ∑ n ∈ Icc 1 K,
        if r ∣ n then reciprocalDivisorSum r * f (n / r) else 0 :=
      Finset.sum_le_sum hpoint
    _ = reciprocalDivisorSum r *
        ∑ n ∈ Icc 1 K, if r ∣ n then f (n / r) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ ≤ reciprocalDivisorSum r * ∑ m ∈ Icc 1 K, f m := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_divisible_quotient_le K r hr f hf
      · exact reciprocalDivisorSum_nonneg r
    _ = reciprocalDivisorSum r *
        finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d := by rfl

/-! ## The separated finite arithmetic energy -/

/-- Energy after the exact kernel coefficient has been replaced by its
proved squared decay majorant. -/
def windowModeDecayEnergy
    (N P K : ℕ) (ell : ℤ) : ℝ :=
  ∑ n ∈ Icc 1 K,
    (windowCauchyDConstant * reciprocalDivisorSum n) *
      ∑ z ∈ windowDivisorPairs P n,
        144 * windowDecayWeight z.1 (n / z.2)
            (windowCarrierCenter N z.1 ell) /
          ((z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ))

theorem windowModeArithmeticEnergy_le_decayEnergy
    (N P K : ℕ) (ell : ℤ) :
    windowModeArithmeticEnergy N P K ell ≤
      windowModeDecayEnergy N P K ell := by
  unfold windowModeArithmeticEnergy windowModeDecayEnergy
  apply Finset.sum_le_sum
  intro n hn
  have hnPos : 0 < n := (mem_Icc.mp hn).1
  have hmass := windowWeightMass_le_reciprocalDivisorSum
    (P := P) (n := n) hnPos
  have hkernel : windowKernelWeightedEnergy N P ell n ≤
      ∑ z ∈ windowDivisorPairs P n,
        144 * windowDecayWeight z.1 (n / z.2)
            (windowCarrierCenter N z.1 ell) /
          ((z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ)) := by
    rw [windowKernelWeightedEnergy_eq_simplified]
    exact windowSimplifiedKernelEnergy_le_decay N P ell n
  calc
    windowWeightMass P n * windowKernelWeightedEnergy N P ell n ≤
        (windowCauchyDConstant * reciprocalDivisorSum n) *
          windowKernelWeightedEnergy N P ell n :=
      mul_le_mul_of_nonneg_right hmass
        (windowKernelWeightedEnergy_nonneg N P ell n)
    _ ≤ (windowCauchyDConstant * reciprocalDivisorSum n) *
        ∑ z ∈ windowDivisorPairs P n,
          144 * windowDecayWeight z.1 (n / z.2)
              (windowCarrierCenter N z.1 ell) /
            ((z.1 : ℝ) ^ 2 * Real.sqrt (z.1 : ℝ) * (z.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hkernel
        (mul_nonneg windowCauchyDConstant_nonneg
          (reciprocalDivisorSum_nonneg n))

/-- The `d`-sum left after the quotient variable has been separated. -/
def windowSeparatedDSum
    (N P K : ℕ) (ell : ℤ) : ℝ :=
  ∑ d ∈ Icc 1 P,
    finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d /
      ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))

theorem windowModeDecayEnergy_le_separated
    (N P K : ℕ) (ell : ℤ) :
    windowModeDecayEnergy N P K ell ≤
      144 * windowCauchyDConstant *
        (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) *
          windowSeparatedDSum N P K ell := by
  let g : ℕ → ℕ → ℕ → ℝ := fun n d r ↦
    144 * windowDecayWeight d (n / r) (windowCarrierCenter N d ell) /
      ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))
  have hdrop : windowModeDecayEnergy N P K ell ≤
      ∑ n ∈ Icc 1 K, ∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
        (windowCauchyDConstant * reciprocalDivisorSum n) *
          (if r ∣ n then g n d r else 0) := by
    unfold windowModeDecayEnergy
    apply Finset.sum_le_sum
    intro n hn
    rw [sum_windowDivisorPairs_eq_nested]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hadm : d * r ≤ P ∧ r ∣ n
    · simp only [hadm, if_true]
      rfl
    · by_cases hrn : r ∣ n
      · have hdnot : ¬ d * r ≤ P := fun hdr ↦ hadm ⟨hdr, hrn⟩
        simp only [mul_ite, mul_zero, ge_iff_le]
        exact mul_nonneg
          (mul_nonneg windowCauchyDConstant_nonneg
            (reciprocalDivisorSum_nonneg n))
          (by
            show 0 ≤ 144 *
              windowDecayWeight d (n / r) (windowCarrierCenter N d ell) /
                ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))
            exact div_nonneg
              (mul_nonneg (by norm_num)
                (windowDecayWeight_nonneg d (n / r)
                  (windowCarrierCenter N d ell)))
              (by positivity))
      · simp [hrn]
  calc
    windowModeDecayEnergy N P K ell ≤
        ∑ n ∈ Icc 1 K, ∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
          (windowCauchyDConstant * reciprocalDivisorSum n) *
            (if r ∣ n then g n d r else 0) := hdrop
    _ = ∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P, ∑ n ∈ Icc 1 K,
          (windowCauchyDConstant * reciprocalDivisorSum n) *
            (if r ∣ n then g n d r else 0) := by
      rw [Finset.sum_comm (s := Icc 1 K) (t := Icc 1 P)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
          (144 * windowCauchyDConstant /
            ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))) *
            ∑ n ∈ Icc 1 K,
              if r ∣ n then
                reciprocalDivisorSum n *
                  windowDecayWeight d (n / r) (windowCarrierCenter N d ell)
              else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [g]
      by_cases hrn : r ∣ n
      · simp [hrn]
        ring
      · simp [hrn]
    _ ≤ ∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
          (144 * windowCauchyDConstant /
            ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))) *
            (reciprocalDivisorSum r *
              finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro r hr
      have hdPos : 0 < d := (mem_Icc.mp hd).1
      have hrPos : 0 < r := (mem_Icc.mp hr).1
      apply mul_le_mul_of_nonneg_left
      · exact sum_divisible_reciprocalDivisor_carrier_le
          N K d r ell hrPos
      · have hD : 0 ≤ 144 * windowCauchyDConstant :=
          mul_nonneg (by norm_num) windowCauchyDConstant_nonneg
        have hden : 0 ≤
            (d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ) := by positivity
        exact div_nonneg hD hden
    _ = 144 * windowCauchyDConstant *
        (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) *
          windowSeparatedDSum N P K ell := by
      unfold windowSeparatedDSum
      calc
        (∑ d ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
            (144 * windowCauchyDConstant /
              ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))) *
              (reciprocalDivisorSum r *
                finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d)) =
          ∑ r ∈ Icc 1 P, ∑ d ∈ Icc 1 P,
            (144 * windowCauchyDConstant /
              ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ) * (r : ℝ))) *
              (reciprocalDivisorSum r *
                finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d) := by
          rw [Finset.sum_comm]
        _ = 144 * windowCauchyDConstant *
            (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) *
              (∑ d ∈ Icc 1 P,
                finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d /
                  ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) := by
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring

/-! ## Uniform control of the separated `d`-sum -/

/-- Common scale dominating every carrier centre with `d ≤ P`. -/
def windowArithmeticScale (N P : ℕ) (ell : ℤ) : ℝ :=
  Real.exp 1 + (ell.natAbs * N + 1) * P

theorem one_le_log_windowArithmeticScale (N P : ℕ) (ell : ℤ) :
    1 ≤ Real.log (windowArithmeticScale N P ell) := by
  have hbase : Real.exp 1 ≤ windowArithmeticScale N P ell := by
    unfold windowArithmeticScale
    have hnonneg : (0 : ℝ) ≤
        ((ell.natAbs : ℝ) * N + 1) * P := by positivity
    linarith
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (windowArithmeticScale N P ell) :=
      Real.log_le_log (Real.exp_pos 1) hbase

theorem log_windowEnvelopeScale_le_arithmeticScale
    {N P d : ℕ} {ell : ℤ} (hdP : d ≤ P) :
    Real.log (windowEnvelopeScale (windowCarrierCenter N d ell) d) ≤
      Real.log (windowArithmeticScale N P ell) := by
  have hnat : windowCarrierCenter N d ell + d ≤
      (ell.natAbs * N + 1) * P := by
    unfold windowCarrierCenter
    calc
      ell.natAbs * N * d + d = (ell.natAbs * N + 1) * d := by ring
      _ ≤ (ell.natAbs * N + 1) * P :=
        Nat.mul_le_mul_left (ell.natAbs * N + 1) hdP
  have hreal : windowEnvelopeScale (windowCarrierCenter N d ell) d ≤
      windowArithmeticScale N P ell := by
    unfold windowEnvelopeScale windowArithmeticScale
    have hnatR :
        (windowCarrierCenter N d ell : ℝ) + (d : ℝ) ≤
          ((ell.natAbs : ℝ) * N + 1) * P := by
      exact_mod_cast hnat
    linarith
  apply Real.log_le_log
  · unfold windowEnvelopeScale
    positivity
  · exact hreal

/-- Convergent `d^{-5/2}` constant. -/
def windowDFiveHalfConstant : ℝ :=
  ∑' d : ℕ, 1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))

/-- Convergent `d^{-3/2}` constant after the window envelope contributes
one power of `d`. -/
def windowDThreeHalfConstant : ℝ :=
  ∑' d : ℕ, 1 / ((d : ℝ) * Real.sqrt (d : ℝ))

private theorem sqrt_fifth_eq_rpow_five_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ 5) = x ^ (5 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast_mul hx 5 (1 / 2 : ℝ)]
  norm_num

private theorem sqrt_fifth_eq_sq_mul_sqrt (x : ℝ) (_hx : 0 ≤ x) :
    Real.sqrt (x ^ 5) = x ^ 2 * Real.sqrt x := by
  rw [show x ^ 5 = x ^ 4 * x by ring,
    Real.sqrt_mul (by positivity : 0 ≤ x ^ 4),
    show x ^ 4 = (x ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg x)]

theorem summable_windowDFiveHalfTerm :
    Summable fun d : ℕ ↦
      1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ)) := by
  have hp : Summable fun d : ℕ ↦ 1 / (d : ℝ) ^ (5 / 2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  apply hp.congr
  intro d
  rw [← sqrt_fifth_eq_rpow_five_halves (d : ℝ) (by positivity),
    sqrt_fifth_eq_sq_mul_sqrt (d : ℝ) (by positivity)]

theorem summable_windowDThreeHalfTerm :
    Summable fun d : ℕ ↦
      1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
  apply summable_windowCauchyDTerm.congr
  intro d
  rw [show (d : ℝ) ^ 3 = (d : ℝ) ^ 2 * d by ring,
    Real.sqrt_mul (sq_nonneg (d : ℝ)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity)]

theorem windowDFiveHalfConstant_nonneg : 0 ≤ windowDFiveHalfConstant := by
  exact tsum_nonneg fun d ↦ by positivity

theorem windowDThreeHalfConstant_nonneg : 0 ≤ windowDThreeHalfConstant := by
  exact tsum_nonneg fun d ↦ by positivity

theorem sum_windowDFiveHalf_le (P : ℕ) :
    (∑ d ∈ Icc 1 P,
      1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) ≤
        windowDFiveHalfConstant :=
  summable_windowDFiveHalfTerm.sum_le_tsum (Icc 1 P)
    (fun d hd ↦ by positivity)

theorem sum_windowDThreeHalf_le (P : ℕ) :
    (∑ d ∈ Icc 1 P,
      1 / ((d : ℝ) * Real.sqrt (d : ℝ))) ≤
        windowDThreeHalfConstant :=
  summable_windowDThreeHalfTerm.sum_le_tsum (Icc 1 P)
    (fun d hd ↦ by positivity)

theorem uniform_windowSeparatedDSum_additive
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (N P K : ℕ) (ell : ℤ),
        windowSeparatedDSum N P K ell ≤
          B + epsilon * Real.log (windowArithmeticScale N P ell) *
            windowDThreeHalfConstant := by
  rcases uniform_finiteDivisorWindowEnergy_additive hepsilon with
    ⟨A, hA, henergy⟩
  refine ⟨A * windowDFiveHalfConstant,
    mul_nonneg hA windowDFiveHalfConstant_nonneg, ?_⟩
  intro N P K ell
  have hpoint : ∀ d ∈ Icc 1 P,
      finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d /
          ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ)) ≤
        A * (1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) +
          (epsilon * Real.log (windowArithmeticScale N P ell)) *
            (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
    intro d hd
    have hdPos : 0 < d := (mem_Icc.mp hd).1
    have hE := henergy K (windowCarrierCenter N d ell) d hdPos
    have hlog := log_windowEnvelopeScale_le_arithmeticScale
      (N := N) (P := P) (ell := ell) (mem_Icc.mp hd).2
    have hupper : finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d ≤
        A + epsilon * d * Real.log (windowArithmeticScale N P ell) := by
      have hcoef : 0 ≤ epsilon * (d : ℝ) :=
        mul_nonneg hepsilon.le (by positivity)
      exact hE.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hlog hcoef))
    have hden : 0 ≤ (d : ℝ) ^ 2 * Real.sqrt (d : ℝ) := by positivity
    calc
      finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d /
          ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ)) ≤
        (A + epsilon * d * Real.log (windowArithmeticScale N P ell)) /
          ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ)) :=
        div_le_div_of_nonneg_right hupper hden
      _ = A * (1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) +
          (epsilon * Real.log (windowArithmeticScale N P ell)) *
            (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
        have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
        field_simp
  unfold windowSeparatedDSum
  calc
    (∑ d ∈ Icc 1 P,
        finiteDivisorWindowEnergy K (windowCarrierCenter N d ell) d /
          ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) ≤
      ∑ d ∈ Icc 1 P,
        (A * (1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) +
          (epsilon * Real.log (windowArithmeticScale N P ell)) *
            (1 / ((d : ℝ) * Real.sqrt (d : ℝ)))) :=
      Finset.sum_le_sum hpoint
    _ = A * (∑ d ∈ Icc 1 P,
          1 / ((d : ℝ) ^ 2 * Real.sqrt (d : ℝ))) +
        (epsilon * Real.log (windowArithmeticScale N P ell)) *
          (∑ d ∈ Icc 1 P,
            1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * windowDFiveHalfConstant +
        (epsilon * Real.log (windowArithmeticScale N P ell)) *
          windowDThreeHalfConstant := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sum_windowDFiveHalf_le P) hA
      · apply mul_le_mul_of_nonneg_left (sum_windowDThreeHalf_le P)
        exact mul_nonneg hepsilon.le
          (le_trans (by norm_num) (one_le_log_windowArithmeticScale N P ell))

/-! ## Uniform `o(log²)` bound for the actual finite arithmetic energy -/

theorem windowSeparatedDSum_nonneg (N P K : ℕ) (ell : ℤ) :
    0 ≤ windowSeparatedDSum N P K ell := by
  unfold windowSeparatedDSum
  apply Finset.sum_nonneg
  intro d hd
  exact div_nonneg
    (by
      unfold finiteDivisorWindowEnergy
      exact Finset.sum_nonneg fun m hm ↦
        mul_nonneg (reciprocalDivisorSum_nonneg m)
          (windowDecayWeight_nonneg d m (windowCarrierCenter N d ell)))
    (by positivity)

/-- Universal prefactor left after the `r`-average. -/
def windowArithmeticPrefactor : ℝ :=
  144 * windowCauchyDConstant * windowReciprocalSquareConstant

theorem windowArithmeticPrefactor_nonneg : 0 ≤ windowArithmeticPrefactor := by
  unfold windowArithmeticPrefactor
  exact mul_nonneg
    (mul_nonneg (by norm_num) windowCauchyDConstant_nonneg)
    windowReciprocalSquareConstant_nonneg

theorem windowModeArithmeticEnergy_le_harmonic_separated
    (N P K : ℕ) (ell : ℤ) :
    windowModeArithmeticEnergy N P K ell ≤
      windowArithmeticPrefactor * (harmonic P : ℝ) *
        windowSeparatedDSum N P K ell := by
  have hfirst := (windowModeArithmeticEnergy_le_decayEnergy N P K ell).trans
    (windowModeDecayEnergy_le_separated N P K ell)
  have hr := sum_reciprocalDivisorSum_div_le P
  have hleft : 0 ≤ 144 * windowCauchyDConstant :=
    mul_nonneg (by norm_num) windowCauchyDConstant_nonneg
  have hD := windowSeparatedDSum_nonneg N P K ell
  calc
    windowModeArithmeticEnergy N P K ell ≤
        144 * windowCauchyDConstant *
          (∑ r ∈ Icc 1 P, reciprocalDivisorSum r / (r : ℝ)) *
            windowSeparatedDSum N P K ell := hfirst
    _ ≤ 144 * windowCauchyDConstant *
          (windowReciprocalSquareConstant * (harmonic P : ℝ)) *
            windowSeparatedDSum N P K ell := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr hleft) hD
    _ = windowArithmeticPrefactor * (harmonic P : ℝ) *
          windowSeparatedDSum N P K ell := by
      unfold windowArithmeticPrefactor
      ring

/-- Additive uniform form for the actual arithmetic energy.  The one
remaining growth factor is the sharp `r`-average `harmonic P`. -/
theorem uniform_windowModeArithmeticEnergy_additive
    {eta : ℝ} (heta : 0 < eta) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (N P K : ℕ) (ell : ℤ),
        windowModeArithmeticEnergy N P K ell ≤
          (harmonic P : ℝ) *
            (A + eta * Real.log (windowArithmeticScale N P ell)) := by
  let C : ℝ := windowArithmeticPrefactor * windowDThreeHalfConstant
  have hC : 0 ≤ C :=
    mul_nonneg windowArithmeticPrefactor_nonneg
      windowDThreeHalfConstant_nonneg
  let epsilon : ℝ := eta / (1 + C)
  have hden : 0 < 1 + C := by linarith
  have hepsilon : 0 < epsilon := div_pos heta hden
  rcases uniform_windowSeparatedDSum_additive hepsilon with ⟨B, hB, hDSum⟩
  refine ⟨windowArithmeticPrefactor * B,
    mul_nonneg windowArithmeticPrefactor_nonneg hB, ?_⟩
  intro N P K ell
  let L : ℝ := Real.log (windowArithmeticScale N P ell)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact le_trans (by norm_num) (one_le_log_windowArithmeticScale N P ell)
  have hharm : 0 ≤ (harmonic P : ℝ) := by
    by_cases hP : P = 0
    · simp [hP]
    · exact_mod_cast (harmonic_pos hP).le
  have hbase := windowModeArithmeticEnergy_le_harmonic_separated N P K ell
  have hsum := hDSum N P K ell
  have hcoef : C * epsilon ≤ eta := by
    dsimp [epsilon]
    rw [show C * (eta / (1 + C)) = (C * eta) / (1 + C) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg heta.le hC]
  have hinside :
      windowArithmeticPrefactor * windowSeparatedDSum N P K ell ≤
        windowArithmeticPrefactor * B + eta * L := by
    calc
      windowArithmeticPrefactor * windowSeparatedDSum N P K ell ≤
          windowArithmeticPrefactor *
            (B + epsilon * L * windowDThreeHalfConstant) :=
        mul_le_mul_of_nonneg_left hsum windowArithmeticPrefactor_nonneg
      _ = windowArithmeticPrefactor * B + (C * epsilon) * L := by
        dsimp [C]
        ring
      _ ≤ windowArithmeticPrefactor * B + eta * L :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hL)
  calc
    windowModeArithmeticEnergy N P K ell ≤
        windowArithmeticPrefactor * (harmonic P : ℝ) *
          windowSeparatedDSum N P K ell := hbase
    _ = (harmonic P : ℝ) *
        (windowArithmeticPrefactor * windowSeparatedDSum N P K ell) := by ring
    _ ≤ (harmonic P : ℝ) *
        (windowArithmeticPrefactor * B + eta * L) :=
      mul_le_mul_of_nonneg_left hinside hharm
    _ = (harmonic P : ℝ) *
        (windowArithmeticPrefactor * B +
          eta * Real.log (windowArithmeticScale N P ell)) := by rfl

theorem harmonic_le_two_log_windowArithmeticScale
    {N P : ℕ} {ell : ℤ} (hP : 0 < P) :
    (harmonic P : ℝ) ≤
      2 * Real.log (windowArithmeticScale N P ell) := by
  have hPReal : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hscale : (P : ℝ) ≤ windowArithmeticScale N P ell := by
    unfold windowArithmeticScale
    have hcoeff : (1 : ℝ) ≤
        (ell.natAbs : ℝ) * (N : ℝ) + 1 := by
      have hprod : 0 ≤ (ell.natAbs : ℝ) * (N : ℝ) := by positivity
      linarith
    have hmul : (P : ℝ) ≤
        ((ell.natAbs : ℝ) * (N : ℝ) + 1) * (P : ℝ) := by
      simpa only [one_mul] using!
        mul_le_mul_of_nonneg_right hcoeff hPReal.le
    have hexp : 0 < Real.exp 1 := Real.exp_pos 1
    exact hmul.trans (by linarith)
  have hlogP : Real.log (P : ℝ) ≤
      Real.log (windowArithmeticScale N P ell) :=
    Real.log_le_log hPReal hscale
  have hLone := one_le_log_windowArithmeticScale N P ell
  calc
    (harmonic P : ℝ) ≤ 1 + Real.log (P : ℝ) :=
      harmonic_le_one_add_log P
    _ ≤ 2 * Real.log (windowArithmeticScale N P ell) := by linarith

/-- Final normalized form: the actual finite arithmetic energy is
uniformly `o(log²(scale))`, independently of the Fourier cutoff `K` and
of the signed carrier. -/
theorem uniform_windowModeArithmeticEnergy_small_above_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ) (ell : ℤ), 0 < P →
        H ≤ Real.log (windowArithmeticScale N P ell) →
          windowModeArithmeticEnergy N P K ell ≤
            eta * (Real.log (windowArithmeticScale N P ell)) ^ 2 := by
  have hetaFour : 0 < eta / 4 := by positivity
  rcases uniform_windowModeArithmeticEnergy_additive hetaFour with
    ⟨A, hA, henergy⟩
  let H : ℝ := 4 * A / eta
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  refine ⟨H, hH, ?_⟩
  intro N P K ell hP hscale
  let L : ℝ := Real.log (windowArithmeticScale N P ell)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact le_trans (by norm_num) (one_le_log_windowArithmeticScale N P ell)
  have hAeq : A = (eta / 4) * H := by
    dsimp [H]
    field_simp [heta.ne']
  have hAtoL : A ≤ (eta / 4) * L := by
    rw [hAeq]
    exact mul_le_mul_of_nonneg_left hscale hetaFour.le
  have hraw := henergy N P K ell
  have hharm := harmonic_le_two_log_windowArithmeticScale
    (N := N) (ell := ell) hP
  change windowModeArithmeticEnergy N P K ell ≤
    (harmonic P : ℝ) * (A + (eta / 4) * L) at hraw
  change windowModeArithmeticEnergy N P K ell ≤ eta * L ^ 2
  calc
    windowModeArithmeticEnergy N P K ell ≤
        (harmonic P : ℝ) * (A + (eta / 4) * L) := hraw
    _ ≤ (2 * L) * ((eta / 4) * L + (eta / 4) * L) := by
      exact mul_le_mul hharm (add_le_add hAtoL le_rfl)
        (by positivity) (by positivity)
    _ = eta * L ^ 2 := by ring

/-- Immediate Hilbert-space corollary through the exact finite Parseval
reduction in `WindowErrorReduction`. -/
theorem uniform_norm_windowModeFourierPolynomial_sq_small_above_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ) (ell : ℤ), 0 < P →
        H ≤ Real.log (windowArithmeticScale N P ell) →
          ‖windowModeFourierPolynomial N P K ell‖ ^ 2 ≤
            eta * (Real.log (windowArithmeticScale N P ell)) ^ 2 := by
  rcases uniform_windowModeArithmeticEnergy_small_above_scale heta with
    ⟨H, hH, henergy⟩
  refine ⟨H, hH, ?_⟩
  intro N P K ell hP hscale
  exact (norm_windowModeFourierPolynomial_sq_le_arithmeticEnergy
    N P K ell).trans (henergy N P K ell hP hscale)

end


end Erdos1002
