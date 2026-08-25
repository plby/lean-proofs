/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos387.FiniteWeylInequality
import ErdosProblems.Erdos587.Analytic

/-!
# A completed quadratic Weyl estimate for Erdős problem 438

This file isolates the analytic estimate used in the Khalfalah--Lodha--
Szemerédi shifting argument.  We use the explicit phase `e(x) = exp(2πix)`
and sums over the half-open interval `[0,L)`.
-/

namespace Erdos438

open Filter
open scoped BigOperators ComplexConjugate
open scoped Topology

namespace QuadraticWeyl

/-- Dirichlet approximation with a reduced numerator and denominator. -/
theorem dirichletApproximationReduced (θ : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (b : ℕ),
      1 ≤ b ∧ b ≤ Q ∧ Nat.Coprime a.natAbs b ∧
        |θ - (a : ℝ) / (b : ℝ)| ≤ 1 / ((b : ℝ) * (Q : ℝ)) := by
  obtain ⟨q, happrox, hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le θ (by omega : 0 < Q)
  refine ⟨q.num, q.den, q.den_pos, hden, q.reduced, ?_⟩
  have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast q.num_div_den.symm
  rw [hcast] at happrox
  refine happrox.trans ?_
  have hb : (0 : ℝ) < q.den := by positivity
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  apply one_div_le_one_div_of_le (mul_pos hb hQr)
  nlinarith

/-- For a nonnegative frequency and a cutoff at least two, the reduced
Dirichlet numerator may be taken to be a natural number. -/
theorem dirichletApproximationReducedNat (θ : ℝ) (Q : ℕ)
    (hθ : 0 ≤ θ) (hQ : 2 ≤ Q) :
    ∃ (a b : ℕ), 1 ≤ b ∧ b ≤ Q ∧ a.Coprime b ∧
      |θ - (a : ℝ) / (b : ℝ)| ≤ 1 / ((b : ℝ) * (Q : ℝ)) := by
  obtain ⟨a, b, hb1, hbQ, hab, happ⟩ :=
    dirichletApproximationReduced θ Q (by omega)
  have ha0 : 0 ≤ a := by
    by_contra hneg
    have ha1 : a ≤ -1 := by omega
    have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb1)
    have hQR : (1 : ℝ) < Q := by exact_mod_cast hQ
    have haR : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
    have hdiff : 1 / (b : ℝ) ≤ θ - (a : ℝ) / b := by
      have : (a : ℝ) / b ≤ -1 / b :=
        (div_le_div_iff_of_pos_right hbR).2 haR
      have hnegdiv : 1 / (b : ℝ) ≤ -((a : ℝ) / b) := by
        calc
          1 / (b : ℝ) = -(-1 / b) := by ring
          _ ≤ -((a : ℝ) / b) := neg_le_neg this
      calc
        1 / (b : ℝ) ≤ θ + 1 / b := le_add_of_nonneg_left hθ
        _ ≤ θ - (a : ℝ) / b := by
          rw [sub_eq_add_neg]
          simpa only [add_comm] using add_le_add_left hnegdiv θ
    have hdiff0 : 0 ≤ θ - (a : ℝ) / b := le_trans (by positivity) hdiff
    have habs : 1 / (b : ℝ) ≤ |θ - (a : ℝ) / b| := by
      rwa [abs_of_nonneg hdiff0]
    have hstrict : 1 / ((b : ℝ) * Q) < 1 / b := by
      rw [one_div_lt_one_div (mul_pos hbR (by positivity)) hbR]
      nlinarith
    exact (not_lt_of_ge (habs.trans happ)) hstrict
  refine ⟨a.natAbs, b, hb1, hbQ, hab, ?_⟩
  have hcast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
    rw [← Int.cast_natCast]
    exact_mod_cast Int.natAbs_of_nonneg ha0
  rwa [hcast]

theorem nearestIntDist_eq_circleNorm (x : ℝ) :
    Erdos587.nearestIntDist x = ‖(x : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq]
  simp [Erdos587.nearestIntDist]

theorem nearestIntDist_neg (x : ℝ) :
    Erdos587.nearestIntDist (-x) = Erdos587.nearestIntDist x := by
  rw [nearestIntDist_eq_circleNorm, nearestIntDist_eq_circleNorm]
  change ‖-(x : AddCircle (1 : ℝ))‖ = ‖(x : AddCircle (1 : ℝ))‖
  exact norm_neg _

/-- Distance to the nearest integer is `1`-Lipschitz. -/
theorem nearestIntDist_le_add_abs_sub (x y : ℝ) :
    Erdos587.nearestIntDist x ≤
      |x - y| + Erdos587.nearestIntDist y := by
  rw [nearestIntDist_eq_circleNorm, nearestIntDist_eq_circleNorm]
  have htri :
      ‖(x : AddCircle (1 : ℝ))‖ ≤
        ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ +
          ‖(y : AddCircle (1 : ℝ))‖ := by
    convert norm_add_le (((x - y : ℝ) : AddCircle (1 : ℝ)))
      ((y : ℝ) : AddCircle (1 : ℝ)) using 1
    all_goals simp
  refine htri.trans (add_le_add ?_ le_rfl)
  rw [AddCircle.norm_eq]
  simpa using (round_le (x - y) 0)

/-- Exact nearest-integer distance of a rational number with natural
numerator and positive denominator. -/
theorem nearestIntDist_nat_div (m b : ℕ) :
    Erdos587.nearestIntDist ((m : ℝ) / b) =
      (min (m % b) (b - m % b) : ℕ) / (b : ℝ) := by
  simpa [Erdos587.nearestIntDist] using
    (abs_sub_round_div_natCast_eq (α := ℝ) (m := m) (n := b))

/-- Group a nonnegative sum over an interval into residue classes.  The
factor `L / b + 1` is the exact elementary bound for the size of a fibre. -/
theorem sum_Icc_comp_mod_le (b L : ℕ) (hb : 0 < b) (f : ℕ → ℝ)
    (hf : ∀ r < b, 0 ≤ f r) :
    (∑ k ∈ Finset.Icc 1 L, f (k % b)) ≤
      (L / b + 1 : ℕ) * ∑ r ∈ Finset.range b, f r := by
  let s := Finset.Icc 1 L
  let g : ℕ → ℕ := fun k => k % b
  have hmaps : ∀ k ∈ s, g k ∈ Finset.range b := by
    intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hb)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => f (g k))]
  simp only [g]
  calc
    (∑ r ∈ Finset.range b,
        ∑ k ∈ s with k % b = r, f (k % b)) =
        ∑ r ∈ Finset.range b,
          ((((s.filter fun k => k % b = r).card : ℕ) : ℝ) * f r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_filter]
      calc
        (∑ x ∈ s, if x % b = r then f (x % b) else 0) =
            ∑ x ∈ s, if x % b = r then f r else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs with h
          · rw [h]
          · rfl
        _ = (((s.filter fun k => k % b = r).card : ℕ) : ℝ) * f r := by
          calc
            (∑ x ∈ s, if x % b = r then f r else 0) =
                (∑ x ∈ s, if x % b = r then (1 : ℝ) else 0) * f r := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro x hx
              split_ifs <;> ring
            _ = (((s.filter fun k => k % b = r).card : ℕ) : ℝ) * f r := by
              rw [Finset.sum_boole]
    _ ≤ ∑ r ∈ Finset.range b, ((L / b + 1 : ℕ) : ℝ) * f r := by
      apply Finset.sum_le_sum
      intro r hr
      have hcard : (s.filter fun k => k % b = r).card ≤ L / b + 1 := by
        apply Erdos587.card_le_div_add_one_of_pairwise_modEq
          (X := L) (h := b)
        · intro k hk
          simpa [s] using (Finset.mem_filter.mp hk).1
        · exact hb
        · intro x hx y hy
          have hx' := (Finset.mem_filter.mp hx).2
          have hy' := (Finset.mem_filter.mp hy).2
          change x % b = y % b
          exact hx'.trans hy'.symm
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (hf r (Finset.mem_range.mp hr))
    _ = ((L / b + 1 : ℕ) : ℝ) * ∑ r ∈ Finset.range b, f r := by
      rw [Finset.mul_sum]

/-- Multiplication by `2a` modulo `b` has fibres of size at most two when
`a` is coprime to `b`.  This weighted form is what the Weyl estimate uses. -/
theorem sum_twice_mul_mod_le_two_sum {a b : ℕ} (hb : 0 < b) (ha : a.Coprime b)
    (f : ℕ → ℝ) (hf : ∀ r < b, 0 ≤ f r) :
    (∑ s ∈ Finset.range b, f ((2 * a * s) % b)) ≤
      2 * ∑ r ∈ Finset.range b, f r := by
  classical
  let low := (Finset.range b).filter fun s => 2 * s < b
  let high := (Finset.range b).filter fun s => ¬ 2 * s < b
  let g : ℕ → ℕ := fun s => (2 * a * s) % b
  have hgmem : ∀ s ∈ Finset.range b, g s ∈ Finset.range b := by
    intro s hs
    exact Finset.mem_range.mpr (Nat.mod_lt _ hb)
  have hinj_piece (u : Finset ℕ)
      (hu : u = low ∨ u = high) : Set.InjOn g u := by
    intro x hx y hy hxy
    have hxb : x < b := by
      rcases hu with rfl | rfl <;>
        exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hyb : y < b := by
      rcases hu with rfl | rfl <;>
        exact Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hmodFull : 2 * a * x ≡ 2 * a * y [MOD b] := by
      change (2 * a * x) % b = (2 * a * y) % b
      exact hxy
    have hmodA : a * (2 * x) ≡ a * (2 * y) [MOD b] := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmodFull
    have hmod : 2 * x ≡ 2 * y [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime
        (by simpa [Nat.gcd_comm] using ha.gcd_eq_one) hmodA
    rcases lt_trichotomy x y with hlt | heq | hgt
    · have hdvd : b ∣ 2 * y - 2 * x :=
        (Nat.modEq_iff_dvd' (by omega : 2 * x ≤ 2 * y)).mp hmod
      have hpos : 0 < 2 * y - 2 * x := by omega
      have hble : b ≤ 2 * y - 2 * x := Nat.le_of_dvd hpos hdvd
      rcases hu with rfl | rfl
      · have hylo := (Finset.mem_filter.mp hy).2
        omega
      · have hxhi := (Finset.mem_filter.mp hx).2
        omega
    · exact heq
    · have hdvd : b ∣ 2 * x - 2 * y :=
        (Nat.modEq_iff_dvd' (by omega : 2 * y ≤ 2 * x)).mp hmod.symm
      have hpos : 0 < 2 * x - 2 * y := by omega
      have hble : b ≤ 2 * x - 2 * y := Nat.le_of_dvd hpos hdvd
      rcases hu with rfl | rfl
      · have hxlo := (Finset.mem_filter.mp hx).2
        omega
      · have hyhi := (Finset.mem_filter.mp hy).2
        omega
  have hpiece (u : Finset ℕ) (hu : u = low ∨ u = high) :
      (∑ s ∈ u, f (g s)) ≤ ∑ r ∈ Finset.range b, f r := by
    rw [← Finset.sum_image (hinj_piece u hu)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      rw [Finset.mem_image] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      have hsrange : s ∈ Finset.range b := by
        rcases hu with rfl | rfl <;> exact (Finset.mem_filter.mp hs).1
      exact hgmem s hsrange
    · intro r hr _
      exact hf r (Finset.mem_range.mp hr)
  have hsplit :
      (∑ s ∈ Finset.range b, f (g s)) =
        (∑ s ∈ low, f (g s)) + ∑ s ∈ high, f (g s) := by
    dsimp only [low, high]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range b)
      (fun s : ℕ => 2 * s < b) (fun s => f (g s))).symm
  change (∑ s ∈ Finset.range b, f (g s)) ≤ _
  rw [hsplit]
  nlinarith [hpiece low (Or.inl rfl), hpiece high (Or.inr rfl)]

/-- The quadratic exponential sum of length `L`. -/
noncomputable def squareExpSum (θ : ℝ) (L : ℕ) : ℂ :=
  Erdos587.quadraticSum θ 0 L

/-- Reversing the sign of the frequency conjugates the quadratic sum, so it
does not change its norm. -/
theorem norm_squareExpSum_neg (θ : ℝ) (L : ℕ) :
    ‖squareExpSum (-θ) L‖ = ‖squareExpSum θ L‖ := by
  have hconj : squareExpSum (-θ) L =
      starRingEnd ℂ (squareExpSum θ L) := by
    simp only [squareExpSum, Erdos587.quadraticSum, neg_mul, zero_mul,
      add_zero, map_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [← Erdos587.phase_neg]
  rw [hconj]
  exact norm_star _

/-- The usual geometric-sum majorant after one Weyl differencing step. -/
noncomputable def correlationMajorant (θ : ℝ) (L h : ℕ) : ℝ :=
  if Erdos587.nearestIntDist (2 * θ * h) = 0 then (L - h : ℕ)
  else min ((L - h : ℕ) : ℝ)
    (1 / (2 * Erdos587.nearestIntDist (2 * θ * h)))

theorem correlationMajorant_nonneg (θ : ℝ) (L h : ℕ) :
    0 ≤ correlationMajorant θ L h := by
  unfold correlationMajorant
  split_ifs with hf
  · positivity
  · apply le_min
    · positivity
    · have hd : 0 < Erdos587.nearestIntDist (2 * θ * h) :=
        (Erdos587.nearestIntDist_nonneg _).lt_of_ne' hf
      positivity

/-- Every quadratic autocorrelation is bounded by `correlationMajorant`. -/
theorem norm_correlation_le_majorant (θ : ℝ) (L h : ℕ) :
    ‖∑ z ∈ Finset.range (L - h),
        Erdos587.phase (θ * (z + h : ℕ) ^ 2) *
          starRingEnd ℂ (Erdos587.phase (θ * (z : ℕ) ^ 2))‖ ≤
      correlationMajorant θ L h := by
  by_cases hf : Erdos587.nearestIntDist (2 * θ * h) = 0
  · rw [correlationMajorant, if_pos hf]
    calc
      ‖∑ z ∈ Finset.range (L - h),
          Erdos587.phase (θ * (z + h : ℕ) ^ 2) *
            starRingEnd ℂ (Erdos587.phase (θ * (z : ℕ) ^ 2))‖
          ≤ ∑ z ∈ Finset.range (L - h),
              ‖Erdos587.phase (θ * (z + h : ℕ) ^ 2) *
                starRingEnd ℂ (Erdos587.phase (θ * (z : ℕ) ^ 2))‖ :=
            norm_sum_le _ _
      _ = (L - h : ℕ) := by
        simp [Erdos587.norm_phase]
  · rw [correlationMajorant, if_neg hf]
    simpa using Erdos587.norm_quadratic_correlation_sum_le θ 0 L h hf

/-- The autocorrelation majorant is unchanged by an arbitrary linear term
in the quadratic phase. -/
theorem norm_quadratic_correlation_le_majorant
    (θ β : ℝ) (L h : ℕ) :
    ‖∑ z ∈ Finset.range (L - h),
        Erdos587.phase (θ * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ
            (Erdos587.phase (θ * (z : ℕ) ^ 2 + β * z))‖ ≤
      correlationMajorant θ L h := by
  by_cases hf : Erdos587.nearestIntDist (2 * θ * h) = 0
  · rw [correlationMajorant, if_pos hf]
    calc
      _ ≤ ∑ z ∈ Finset.range (L - h),
          ‖Erdos587.phase (θ * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
            starRingEnd ℂ
              (Erdos587.phase (θ * (z : ℕ) ^ 2 + β * z))‖ :=
        norm_sum_le _ _
      _ = (L - h : ℕ) := by simp [Erdos587.norm_phase]
  · rw [correlationMajorant, if_neg hf]
    exact Erdos587.norm_quadratic_correlation_sum_le θ β L h hf

/-- One-step Weyl differencing, with all correlation sums replaced by their
explicit geometric majorants. -/
theorem norm_squareExpSum_sq_le (θ : ℝ) (L : ℕ) :
    ‖squareExpSum θ L‖ ^ 2 ≤
      L + 2 * ∑ h ∈ Finset.range L, correlationMajorant θ L (h + 1) := by
  have hweyl := Erdos387.FiniteWeyl.norm_sum_range_sq_le_sum_positiveShift
    (fun z : ℕ => Erdos587.phase (θ * (z : ℝ) ^ 2)) L
    (fun z _hz => Erdos587.norm_phase _)
  change ‖squareExpSum θ L‖ ^ 2 ≤ _
  rw [squareExpSum, Erdos587.quadraticSum]
  simp only [zero_mul, add_zero] at hweyl ⊢
  refine hweyl.trans ?_
  gcongr with h hh
  change
    ‖∑ y ∈ Finset.range (L - h - 1),
        Erdos587.phase (θ * ((y + h + 1 : ℕ) : ℝ) ^ 2) *
          starRingEnd ℂ (Erdos587.phase (θ * (y : ℝ) ^ 2))‖ ≤
      correlationMajorant θ L (h + 1)
  have hsub : L - h - 1 = L - (h + 1) := by omega
  rw [hsub]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
    norm_correlation_le_majorant θ L (h + 1)

/-- One-step Weyl differencing for a quadratic phase with an arbitrary
linear coefficient.  The linear term contributes only a unit-modulus factor
to each autocorrelation, so the same majorant applies. -/
theorem norm_quadraticSum_sq_le (θ β : ℝ) (L : ℕ) :
    ‖Erdos587.quadraticSum θ β L‖ ^ 2 ≤
      L + 2 * ∑ h ∈ Finset.range L, correlationMajorant θ L (h + 1) := by
  have hweyl := Erdos387.FiniteWeyl.norm_sum_range_sq_le_sum_positiveShift
    (fun z : ℕ => Erdos587.phase
      (θ * (z : ℝ) ^ 2 + β * (z : ℝ))) L
    (fun z _hz => Erdos587.norm_phase _)
  change ‖Erdos587.quadraticSum θ β L‖ ^ 2 ≤ _
  rw [Erdos587.quadraticSum]
  refine hweyl.trans ?_
  gcongr with h hh
  change
    ‖∑ y ∈ Finset.range (L - h - 1),
        Erdos587.phase
            (θ * ((y + h + 1 : ℕ) : ℝ) ^ 2 + β * (y + h + 1 : ℕ)) *
          starRingEnd ℂ
            (Erdos587.phase (θ * (y : ℝ) ^ 2 + β * (y : ℝ)))‖ ≤
      correlationMajorant θ L (h + 1)
  have hsub : L - h - 1 = L - (h + 1) := by omega
  rw [hsub]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
    norm_quadratic_correlation_le_majorant θ β L (h + 1)

/-! ## Harmonic aggregation of rationally approximated correlations -/

/-- Integers in `[1,L]` whose twisted doubled residue is `r`. -/
def residueFiber (a b L r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter fun h => (2 * a * h) % b = r

private lemma div_gcd_two_pos {b : ℕ} (hb : 0 < b) :
    0 < b / b.gcd 2 := by
  exact Nat.div_pos (Nat.gcd_le_left 2 hb) (Nat.gcd_pos_of_pos_left 2 hb)

private lemma div_div_gcd_two_add_one_le (L b : ℕ) (hb : 0 < b) :
    L / (b / b.gcd 2) + 1 ≤ 2 * (L / b + 1) := by
  let k := b / b.gcd 2
  have hk : 0 < k := div_gcd_two_pos hb
  have hg : b.gcd 2 ≤ 2 := Nat.gcd_le_right b (by omega)
  have hgdvd : b.gcd 2 ∣ b := Nat.gcd_dvd_left b 2
  have hbk : b ≤ 2 * k := by
    have heq : b.gcd 2 * k = b := by
      dsimp [k]
      exact Nat.mul_div_cancel' hgdvd
    nlinarith
  have hlt : L < (L / b + 1) * b := by
    simpa [mul_comm] using Nat.lt_mul_div_succ L hb
  have hlt' : L < (2 * (L / b + 1)) * k := by
    calc
      L < (L / b + 1) * b := hlt
      _ ≤ (L / b + 1) * (2 * k) := Nat.mul_le_mul_left _ hbk
      _ = (2 * (L / b + 1)) * k := by ring
  have hdiv : L / k < 2 * (L / b + 1) :=
    (Nat.div_lt_iff_lt_mul hk).2 hlt'
  change L / k + 1 ≤ 2 * (L / b + 1)
  omega

theorem card_residueFiber_le (a b L r : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (residueFiber a b L r).card ≤ 2 * (L / b + 1) := by
  let k := b / b.gcd 2
  have hk : 0 < k := div_gcd_two_pos hb
  have hpair : ∀ x ∈ residueFiber a b L r,
      ∀ y ∈ residueFiber a b L r, x ≡ y [MOD k] := by
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hab : 2 * a * x ≡ 2 * a * y [MOD b] := hx'.trans hy'.symm
    have ha' : a * (2 * x) ≡ a * (2 * y) [MOD b] := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hab
    have hba : b.gcd a = 1 := by simpa [Nat.gcd_comm] using ha.gcd_eq_one
    have htwo : 2 * x ≡ 2 * y [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime hba ha'
    exact Nat.ModEq.cancel_left_div_gcd hb htwo
  calc
    (residueFiber a b L r).card ≤ L / k + 1 :=
      Erdos587.card_le_div_add_one_of_pairwise_modEq
        (fun h hh => Finset.filter_subset _ _ hh) hk hpair
    _ ≤ 2 * (L / b + 1) := div_div_gcd_two_add_one_le L b hb

def residueDistance (a b h : ℕ) : ℕ :=
  min ((2 * a * h) % b) (b - (2 * a * h) % b)

def distanceFiber (a b L d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter fun h => residueDistance a b h = d

theorem distanceFiber_zero_subset_residueFiber_zero
    (a b L : ℕ) (hb : 0 < b) :
    distanceFiber a b L 0 ⊆ residueFiber a b L 0 := by
  intro h hh
  have hh' := Finset.mem_filter.mp hh
  apply Finset.mem_filter.mpr
  refine ⟨hh'.1, ?_⟩
  have hrlt : (2 * a * h) % b < b := Nat.mod_lt _ hb
  dsimp [residueDistance] at hh'
  omega

theorem distanceFiber_subset_union (a b L d : ℕ) (hb : 0 < b) :
    distanceFiber a b L d ⊆
      residueFiber a b L d ∪ residueFiber a b L (b - d) := by
  intro h hh
  have hh' := Finset.mem_filter.mp hh
  have hd := hh'.2
  let r := (2 * a * h) % b
  change min r (b - r) = d at hd
  by_cases hle : r ≤ b - r
  · have hre : r = d := by simpa [min_eq_left hle] using hd
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hh'.1, hre⟩
  · have hre : r = b - d := by
      have hd' : b - r = d := by
        simpa [min_eq_right (Nat.le_of_not_ge hle)] using hd
      have hrle : r ≤ b := Nat.le_of_lt (Nat.mod_lt _ hb)
      omega
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hh'.1, hre⟩

theorem card_distanceFiber_zero_le (a b L : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (distanceFiber a b L 0).card ≤ 2 * (L / b + 1) := by
  exact (Finset.card_le_card
    (distanceFiber_zero_subset_residueFiber_zero a b L hb)).trans
      (card_residueFiber_le a b L 0 hb ha)

theorem card_distanceFiber_le (a b L d : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (distanceFiber a b L d).card ≤ 4 * (L / b + 1) := by
  calc
    (distanceFiber a b L d).card ≤
        (residueFiber a b L d ∪ residueFiber a b L (b - d)).card :=
      Finset.card_le_card (distanceFiber_subset_union a b L d hb)
    _ ≤ (residueFiber a b L d).card +
        (residueFiber a b L (b - d)).card := Finset.card_union_le _ _
    _ ≤ 2 * (L / b + 1) + 2 * (L / b + 1) :=
      Nat.add_le_add (card_residueFiber_le a b L d hb ha)
        (card_residueFiber_le a b L (b - d) hb ha)
    _ = 4 * (L / b + 1) := by ring

noncomputable def rationalMajorant (a b L h : ℕ) : ℝ :=
  if residueDistance a b h = 0 then L
  else (b : ℝ) / residueDistance a b h

theorem rationalMajorant_nonneg (a b L h : ℕ) :
    0 ≤ rationalMajorant a b L h := by
  rw [rationalMajorant]
  split_ifs <;> positivity

private theorem residueDistance_le (a b h : ℕ) (hb : 0 < b) :
    residueDistance a b h ≤ b := by
  have hr := Nat.mod_lt (2 * a * h) hb
  simp only [residueDistance]
  omega

theorem sum_rationalMajorant_eq_fibers (a b L : ℕ) (hb : 0 < b) :
    (∑ h ∈ Finset.Icc 1 L, rationalMajorant a b L h) =
      ((distanceFiber a b L 0).card : ℝ) * L +
        ∑ d ∈ Finset.Icc 1 b,
          ((distanceFiber a b L d).card : ℝ) * ((b : ℝ) / d) := by
  let s := Finset.Icc 1 L
  let s0 := s.filter fun h => residueDistance a b h = 0
  let s1 := s.filter fun h => residueDistance a b h ≠ 0
  have hmaps : ∀ h ∈ s1, residueDistance a b h ∈ Finset.Icc 1 b := by
    intro h hh
    have hh' := Finset.mem_filter.mp hh
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hh'.2, residueDistance_le a b h hb⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun h => rationalMajorant a b L h)
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun h => residueDistance a b h = 0)
    (fun h => rationalMajorant a b L h)
  calc
    (∑ h ∈ Finset.Icc 1 L, rationalMajorant a b L h) =
        (∑ h ∈ s0, rationalMajorant a b L h) +
          ∑ h ∈ s1, rationalMajorant a b L h := by
      simpa [s, s0, s1] using hsplit.symm
    _ = ((s0.card : ℕ) : ℝ) * L +
          ∑ h ∈ s1, rationalMajorant a b L h := by
      congr 1
      calc
        (∑ h ∈ s0, rationalMajorant a b L h) =
            ∑ _h ∈ s0, (L : ℝ) := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [rationalMajorant, if_pos (Finset.mem_filter.mp hh).2]
        _ = ((s0.card : ℕ) : ℝ) * L := by simp
    _ = ((s0.card : ℕ) : ℝ) * L +
          ∑ d ∈ Finset.Icc 1 b,
            ∑ h ∈ s1 with residueDistance a b h = d,
              rationalMajorant a b L h := by
      congr 1
      exact hfiber.symm
    _ = ((distanceFiber a b L 0).card : ℝ) * L +
          ∑ d ∈ Finset.Icc 1 b,
            ((distanceFiber a b L d).card : ℝ) * ((b : ℝ) / d) := by
      have hs0 : s0 = distanceFiber a b L 0 := by rfl
      rw [hs0]
      apply congrArg (fun x : ℝ =>
        ((distanceFiber a b L 0).card : ℝ) * L + x)
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hd).1
      have hset : (s1.filter fun h => residueDistance a b h = d) =
          distanceFiber a b L d := by
        ext h
        simp only [s1, s, distanceFiber, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hI, hn0⟩, heq⟩
          exact ⟨hI, heq⟩
        · rintro ⟨hI, heq⟩
          refine ⟨⟨hI, ?_⟩, heq⟩
          intro hz
          apply hd0
          exact heq.symm.trans hz
      rw [hset]
      calc
        (∑ h ∈ distanceFiber a b L d, rationalMajorant a b L h) =
            ∑ _h ∈ distanceFiber a b L d, ((b : ℝ) / d) := by
          apply Finset.sum_congr rfl
          intro h hh
          have heq := (Finset.mem_filter.mp hh).2
          rw [rationalMajorant, if_neg]
          · rw [heq]
          · intro hz
            exact hd0 (heq.symm.trans hz)
        _ = ((distanceFiber a b L d).card : ℝ) * ((b : ℝ) / d) := by
          simp

theorem sum_rationalMajorant_le (a b L : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (∑ h ∈ Finset.Icc 1 L, rationalMajorant a b L h) ≤
      2 * ((L : ℝ) / b + 1) * L +
        4 * (L + b) * (1 + Real.log b) := by
  rw [sum_rationalMajorant_eq_fibers a b L hb]
  have hzero : ((distanceFiber a b L 0).card : ℝ) ≤
      2 * ((L : ℝ) / b + 1) := by
    calc
      ((distanceFiber a b L 0).card : ℝ) ≤
          (2 * (L / b + 1) : ℕ) := by
        exact_mod_cast card_distanceFiber_zero_le a b L hb ha
      _ ≤ 2 * ((L : ℝ) / b + 1) := by
        push_cast
        gcongr
        exact Nat.cast_div_le
  have hnonzero :
      (∑ d ∈ Finset.Icc 1 b,
          ((distanceFiber a b L d).card : ℝ) * ((b : ℝ) / d)) ≤
        4 * (L + b) * (1 + Real.log b) := by
    calc
      (∑ d ∈ Finset.Icc 1 b,
          ((distanceFiber a b L d).card : ℝ) * ((b : ℝ) / d)) ≤
          ∑ d ∈ Finset.Icc 1 b,
            (4 * (L / b + 1) : ℕ) * ((b : ℝ) / d) := by
        apply Finset.sum_le_sum
        intro d hd
        gcongr
        exact_mod_cast card_distanceFiber_le a b L d hb ha
      _ = (4 * (L / b + 1) : ℕ) *
          ∑ d ∈ Finset.Icc 1 b, ((b : ℝ) / d) := by
        rw [Finset.mul_sum]
      _ ≤ (4 * (L / b + 1) : ℕ) *
          (b * (1 + Real.log b)) := by
        gcongr
        exact Erdos587.sum_Icc_natCast_div_le b b
      _ ≤ 4 * (L + b) * (1 + Real.log b) := by
        have hlog : 0 ≤ 1 + Real.log (b : ℝ) := by
          have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
          have := Real.log_nonneg hb1
          linarith
        push_cast
        have hdiv : (L / b) * b ≤ L := Nat.div_mul_le_self L b
        have hdivR : ((L / b : ℕ) : ℝ) * b ≤ L := by exact_mod_cast hdiv
        nlinarith
  exact add_le_add (mul_le_mul_of_nonneg_right hzero (by positivity)) hnonzero

theorem correlationMajorant_le_length (θ : ℝ) (L h : ℕ) :
    correlationMajorant θ L h ≤ L := by
  rw [correlationMajorant]
  split_ifs
  · exact_mod_cast Nat.sub_le L h
  · exact (min_le_left _ _).trans (by exact_mod_cast Nat.sub_le L h)

theorem approximation_error_doubled
    (θ : ℝ) (a b Q L h : ℕ) (hb : 0 < b)
    (hh1 : 1 ≤ h) (hh : h ≤ L) (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    |2 * θ * h - ((2 * a * h : ℕ) : ℝ) / b| ≤ 1 / (2 * b) := by
  have hL : 0 < L := lt_of_lt_of_le hh1 hh
  have hQpos : 0 < Q := lt_of_lt_of_le (by omega : 0 < 4 * L) hQ
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hhR : (h : ℝ) ≤ L := by exact_mod_cast hh
  have hQRle : (4 : ℝ) * L ≤ Q := by exact_mod_cast hQ
  have hid :
      2 * θ * (h : ℝ) - ((2 * a * h : ℕ) : ℝ) / b =
        (2 * h : ℝ) * (θ - (a : ℝ) / b) := by
    push_cast
    field_simp
  rw [hid, abs_mul]
  have h2h : |(2 * h : ℝ)| = 2 * h := by
    rw [abs_of_nonneg]
    positivity
  rw [h2h]
  calc
    (2 : ℝ) * h * |θ - (a : ℝ) / b| ≤
        2 * L * (1 / ((b : ℝ) * Q)) := by
      gcongr
    _ = (2 * L) / ((b : ℝ) * Q) := by ring
    _ ≤ 1 / (2 * b) := by
      rw [div_le_div_iff₀ (mul_pos hbR hQR) (by positivity : (0 : ℝ) < 2 * b)]
      nlinarith

/-- A reduced rational approximation controls every correlation majorant by
the corresponding rational residue-distance weight. -/
theorem correlationMajorant_le_rationalMajorant
    (θ : ℝ) (a b Q L h : ℕ) (hb : 0 < b)
    (hh1 : 1 ≤ h) (hhL : h ≤ L) (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    correlationMajorant θ L h ≤ rationalMajorant a b L h := by
  by_cases hd0 : residueDistance a b h = 0
  · rw [rationalMajorant, if_pos hd0]
    exact correlationMajorant_le_length θ L h
  · rw [rationalMajorant, if_neg hd0]
    let d := residueDistance a b h
    let x : ℝ := 2 * θ * h
    let y : ℝ := ((2 * a * h : ℕ) : ℝ) / b
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have herr : |x - y| ≤ 1 / (2 * b) := by
      exact approximation_error_doubled θ a b Q L h hb hh1 hhL hQ happrox
    have hydist : Erdos587.nearestIntDist y = (d : ℝ) / b := by
      dsimp [y, d, residueDistance]
      exact nearestIntDist_nat_div (2 * a * h) b
    have hlip : Erdos587.nearestIntDist y ≤
        |x - y| + Erdos587.nearestIntDist x := by
      calc
        Erdos587.nearestIntDist y ≤
            |y - x| + Erdos587.nearestIntDist x :=
          nearestIntDist_le_add_abs_sub y x
        _ = |x - y| + Erdos587.nearestIntDist x := by
          rw [abs_sub_comm]
    rw [hydist] at hlip
    have herr' : |x - y| ≤ (d : ℝ) / (2 * b) := by
      calc
        |x - y| ≤ 1 / (2 * b) := herr
        _ ≤ (d : ℝ) / (2 * b) := by
          gcongr
          exact_mod_cast hdpos
    have hdist : (d : ℝ) / (2 * b) ≤
        Erdos587.nearestIntDist x := by
      have hratio : (d : ℝ) / b = 2 * ((d : ℝ) / (2 * b)) := by
        field_simp
      rw [hratio] at hlip
      nlinarith
    have hdistpos : 0 < Erdos587.nearestIntDist x :=
      lt_of_lt_of_le (div_pos hdR (by positivity)) hdist
    have hmul : (d : ℝ) ≤
        2 * b * Erdos587.nearestIntDist x := by
      have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)).mp hdist
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm
    rw [correlationMajorant, if_neg hdistpos.ne']
    refine (min_le_right _ _).trans ?_
    apply (div_le_div_iff₀ (by positivity :
      0 < 2 * Erdos587.nearestIntDist x) hdR).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Harmonic aggregation of all geometric correlation majorants under a
Dirichlet approximation. -/
theorem sum_correlationMajorant_le
    (θ : ℝ) (a b Q L : ℕ) (hb : 0 < b) (ha : a.Coprime b)
    (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    (∑ h ∈ Finset.Icc 1 L, correlationMajorant θ L h) ≤
      2 * ((L : ℝ) / b + 1) * L +
        4 * (L + b) * (1 + Real.log b) := by
  calc
    (∑ h ∈ Finset.Icc 1 L, correlationMajorant θ L h) ≤
        ∑ h ∈ Finset.Icc 1 L, rationalMajorant a b L h := by
      apply Finset.sum_le_sum
      intro h hh
      exact correlationMajorant_le_rationalMajorant θ a b Q L h hb
        (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hh).2 hQ happrox
    _ ≤ _ := sum_rationalMajorant_le a b L hb ha

theorem sum_range_correlationMajorant_succ (θ : ℝ) (L : ℕ) :
    (∑ h ∈ Finset.range L, correlationMajorant θ L (h + 1)) =
      ∑ h ∈ Finset.Icc 1 L, correlationMajorant θ L h := by
  apply Finset.sum_bij (fun h _ => h + 1)
  · intro h hh
    exact Finset.mem_Icc.mpr ⟨by omega, by simpa using Finset.mem_range.mp hh⟩
  · intro h₁ hh₁ h₂ hh₂ heq
    omega
  · intro h hh
    have hI := Finset.mem_Icc.mp hh
    refine ⟨h - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro h hh
    rfl

/-- The fully explicit completed quadratic Weyl inequality. -/
theorem norm_squareExpSum_sq_le_explicit
    (θ : ℝ) (a b Q L : ℕ) (hb : 0 < b) (ha : a.Coprime b)
    (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    ‖squareExpSum θ L‖ ^ 2 ≤
      L + 4 * ((L : ℝ) / b + 1) * L +
        8 * (L + b) * (1 + Real.log b) := by
  calc
    ‖squareExpSum θ L‖ ^ 2 ≤
        L + 2 * ∑ h ∈ Finset.range L,
          correlationMajorant θ L (h + 1) := norm_squareExpSum_sq_le θ L
    _ = L + 2 * ∑ h ∈ Finset.Icc 1 L,
          correlationMajorant θ L h := by
      rw [sum_range_correlationMajorant_succ]
    _ ≤ L + 2 * (2 * ((L : ℝ) / b + 1) * L +
          4 * (L + b) * (1 + Real.log b)) := by
      gcongr
      exact sum_correlationMajorant_le θ a b Q L hb ha hQ happrox
    _ = L + 4 * ((L : ℝ) / b + 1) * L +
          8 * (L + b) * (1 + Real.log b) := by ring

/-- The fully explicit completed quadratic Weyl inequality, allowing an
arbitrary linear coefficient in the phase. -/
theorem norm_quadraticSum_sq_le_explicit
    (θ β : ℝ) (a b Q L : ℕ) (hb : 0 < b) (ha : a.Coprime b)
    (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    ‖Erdos587.quadraticSum θ β L‖ ^ 2 ≤
      L + 4 * ((L : ℝ) / b + 1) * L +
        8 * (L + b) * (1 + Real.log b) := by
  calc
    ‖Erdos587.quadraticSum θ β L‖ ^ 2 ≤
        L + 2 * ∑ h ∈ Finset.range L,
          correlationMajorant θ L (h + 1) :=
      norm_quadraticSum_sq_le θ β L
    _ = L + 2 * ∑ h ∈ Finset.Icc 1 L,
          correlationMajorant θ L h := by
      rw [sum_range_correlationMajorant_succ]
    _ ≤ L + 2 * (2 * ((L : ℝ) / b + 1) * L +
          4 * (L + b) * (1 + Real.log b)) := by
      gcongr
      exact sum_correlationMajorant_le θ a b Q L hb ha hQ happrox
    _ = L + 4 * ((L : ℝ) / b + 1) * L +
          8 * (L + b) * (1 + Real.log b) := by ring

/-- Square-root form of the explicit Weyl inequality. -/
theorem norm_squareExpSum_le_explicit
    (θ : ℝ) (a b Q L : ℕ) (hb : 0 < b) (ha : a.Coprime b)
    (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    ‖squareExpSum θ L‖ ≤ Real.sqrt
      (L + 4 * ((L : ℝ) / b + 1) * L +
        8 * (L + b) * (1 + Real.log b)) := by
  apply Real.le_sqrt_of_sq_le
  exact norm_squareExpSum_sq_le_explicit θ a b Q L hb ha hQ happrox

/-- A pointwise minor-arc consequence with the lower-order growth estimates
separated into two elementary hypotheses.  This is the form consumed by the
KLS shifting argument after choosing its power-sized Dirichlet cutoff. -/
theorem norm_squareExpSum_le_minor_of_growth
    (θ : ℝ) (a b Q L N P : ℕ) (hP : 0 < P) (hPb : P ≤ b)
    (ha : a.Coprime b) (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q))
    (hLsq : (L : ℝ) ^ 2 ≤ 4 * N)
    (hLsmall : (L : ℝ) ≤ (N : ℝ) / P)
    (hlogsmall :
      8 * ((L : ℝ) + b) * (1 + Real.log b) ≤ (N : ℝ) / P) :
    ‖squareExpSum θ L‖ ≤ 5 * Real.sqrt ((N : ℝ) / P) := by
  have hb : 0 < b := lt_of_lt_of_le hP hPb
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hPbR : (P : ℝ) ≤ b := by exact_mod_cast hPb
  have hX : 0 ≤ (N : ℝ) / P := by positivity
  have hquad : ((L : ℝ) / b) * L ≤ 4 * ((N : ℝ) / P) := by
    calc
      ((L : ℝ) / b) * L = (L : ℝ) ^ 2 / b := by ring
      _ ≤ (L : ℝ) ^ 2 / P := by
        exact div_le_div_of_nonneg_left (sq_nonneg _) hPR hPbR
      _ ≤ (4 * (N : ℝ)) / P := by gcongr
      _ = 4 * ((N : ℝ) / P) := by ring
  have hsq := norm_squareExpSum_sq_le_explicit
    θ a b Q L hb ha hQ happrox
  have hsq' : ‖squareExpSum θ L‖ ^ 2 ≤
      22 * ((N : ℝ) / P) := by
    calc
      ‖squareExpSum θ L‖ ^ 2 ≤
          L + 4 * ((L : ℝ) / b + 1) * L +
            8 * (L + b) * (1 + Real.log b) := hsq
      _ ≤ 22 * ((N : ℝ) / P) := by nlinarith
  have hsqrt := Real.sq_sqrt hX
  have hnorm : 0 ≤ ‖squareExpSum θ L‖ := norm_nonneg _
  have hsqrtnonneg : 0 ≤ Real.sqrt ((N : ℝ) / P) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (‖squareExpSum θ L‖ -
    5 * Real.sqrt ((N : ℝ) / P))]

theorem norm_squareExpSum_le_minor_of_growth_six
    (θ : ℝ) (a b Q L N P : ℕ) (hP : 0 < P) (hPb : P ≤ b)
    (ha : a.Coprime b) (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q))
    (hLsq : (L : ℝ) ^ 2 ≤ 5 * N)
    (hLsmall : (L : ℝ) ≤ (N : ℝ) / P)
    (hlogsmall :
      8 * ((L : ℝ) + b) * (1 + Real.log b) ≤ (N : ℝ) / P) :
    ‖squareExpSum θ L‖ ≤ 6 * Real.sqrt ((N : ℝ) / P) := by
  have hb : 0 < b := lt_of_lt_of_le hP hPb
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hPbR : (P : ℝ) ≤ b := by exact_mod_cast hPb
  have hX : 0 ≤ (N : ℝ) / P := by positivity
  have hquad : ((L : ℝ) / b) * L ≤ 5 * ((N : ℝ) / P) := by
    calc
      ((L : ℝ) / b) * L = (L : ℝ) ^ 2 / b := by ring
      _ ≤ (L : ℝ) ^ 2 / P := by
        exact div_le_div_of_nonneg_left (sq_nonneg _) hPR hPbR
      _ ≤ (5 * (N : ℝ)) / P := by gcongr
      _ = 5 * ((N : ℝ) / P) := by ring
  have hsq := norm_squareExpSum_sq_le_explicit
    θ a b Q L hb ha hQ happrox
  have hsq' : ‖squareExpSum θ L‖ ^ 2 ≤
      26 * ((N : ℝ) / P) := by
    calc
      ‖squareExpSum θ L‖ ^ 2 ≤
          L + 4 * ((L : ℝ) / b + 1) * L +
            8 * (L + b) * (1 + Real.log b) := hsq
      _ ≤ 26 * ((N : ℝ) / P) := by nlinarith
  have hsqrt := Real.sq_sqrt hX
  have hnorm : 0 ≤ ‖squareExpSum θ L‖ := norm_nonneg _
  have hsqrtnonneg : 0 ≤ Real.sqrt ((N : ℝ) / P) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (‖squareExpSum θ L‖ -
    6 * Real.sqrt ((N : ℝ) / P))]

/-- Integer-numerator form of `norm_squareExpSum_le_minor_of_growth_six`.
This is convenient for Dirichlet approximation of a frequency of either
sign. -/
theorem norm_squareExpSum_le_minor_of_growth_six_int
    (θ : ℝ) (a : ℤ) (b Q L N P : ℕ) (hP : 0 < P) (hPb : P ≤ b)
    (ha : a.natAbs.Coprime b) (hQ : 4 * L ≤ Q)
    (happrox : |θ - (a : ℝ) / (b : ℝ)| ≤ 1 / ((b : ℝ) * Q))
    (hLsq : (L : ℝ) ^ 2 ≤ 5 * N)
    (hLsmall : (L : ℝ) ≤ (N : ℝ) / P)
    (hlogsmall :
      8 * ((L : ℝ) + b) * (1 + Real.log b) ≤ (N : ℝ) / P) :
    ‖squareExpSum θ L‖ ≤ 6 * Real.sqrt ((N : ℝ) / P) := by
  by_cases hanonneg : 0 ≤ a
  · have hacast : (a.natAbs : ℝ) = (a : ℝ) := by
      have hz : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg hanonneg
      simpa using congrArg (fun z : ℤ => (z : ℝ)) hz
    apply norm_squareExpSum_le_minor_of_growth_six
      θ a.natAbs b Q L N P hP hPb ha hQ
    · simpa only [hacast] using happrox
    · exact hLsq
    · exact hLsmall
    · exact hlogsmall
  · have haneg : a < 0 := lt_of_not_ge hanonneg
    have hacast : (a : ℝ) = -(a.natAbs : ℝ) := by
      have hz : (a.natAbs : ℤ) = -a :=
        Int.ofNat_natAbs_of_nonpos haneg.le
      have hz' : a = -(a.natAbs : ℤ) := by omega
      simpa using congrArg (fun z : ℤ => (z : ℝ)) hz'
    have happrox_neg :
        |-θ - (a.natAbs : ℝ) / b| ≤ 1 / ((b : ℝ) * Q) := by
      rw [show -θ - (a.natAbs : ℝ) / b =
          -(θ - (a : ℝ) / b) by rw [hacast]; ring, abs_neg]
      exact happrox
    have hbound := norm_squareExpSum_le_minor_of_growth_six
      (-θ) a.natAbs b Q L N P hP hPb ha hQ happrox_neg
        hLsq hLsmall hlogsmall
    rw [norm_squareExpSum_neg] at hbound
    exact hbound

/-! ## The power-sized Dirichlet cutoff used in the shifting argument -/

/-- The number of square roots which occur in the no-wrap Fourier model. -/
def squareRootLength (N : ℕ) : ℕ := 2 * Nat.sqrt N + 2

/-- A power-sized Dirichlet cutoff.  The exponent `15/16` leaves enough
room both for the length `O(√N)` and for the logarithmic loss in the
completed Weyl inequality. -/
noncomputable def dirichletCutoff (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ ((15 : ℝ) / 16)⌋₊

private lemma cast_squareRootLength_le (N : ℕ) :
    (squareRootLength N : ℝ) ≤ 2 * √(N : ℝ) + 2 := by
  simp only [squareRootLength, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith [Real.nat_sqrt_le_real_sqrt (a := N)]

private lemma cast_dirichletCutoff_le (N : ℕ) :
    (dirichletCutoff N : ℝ) ≤
      (N : ℝ) ^ ((15 : ℝ) / 16) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

private lemma four_squareRootLength_le_dirichletCutoff_of
    {N : ℕ} (hN : 1 ≤ N)
    (hpow : (16 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 16)) :
    4 * squareRootLength N ≤ dirichletCutoff N := by
  have hx : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrt_one : (1 : ℝ) ≤ √(N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  have hfactor :
      (N : ℝ) ^ ((15 : ℝ) / 16) =
        √(N : ℝ) * (N : ℝ) ^ ((7 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    norm_num
  apply Nat.le_floor
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hfactor]
  have hL := cast_squareRootLength_le N
  have hstep : 4 * (squareRootLength N : ℝ) ≤
      16 * √(N : ℝ) := by
    nlinarith
  calc
    4 * (squareRootLength N : ℝ) ≤ 16 * √(N : ℝ) := hstep
    _ = √(N : ℝ) * 16 := by ring
    _ ≤ √(N : ℝ) * (N : ℝ) ^ ((7 : ℝ) / 16) :=
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)

private lemma squareRootLength_sq_le_of
    {N : ℕ} (hsqrt : (9 : ℝ) ≤ √(N : ℝ)) :
    (squareRootLength N : ℝ) ^ 2 ≤ 5 * (N : ℝ) := by
  have hL := cast_squareRootLength_le N
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg N)
  nlinarith [sq_nonneg ((squareRootLength N : ℝ) -
    (2 * √(N : ℝ) + 2))]

private lemma squareRootLength_le_div_of
    {P N : ℕ} (hP : 0 < P)
    (hsqrt : (3 : ℝ) * P + 2 ≤ √(N : ℝ)) :
    squareRootLength N ≤ N / P := by
  have hL := cast_squareRootLength_le N
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg N)
  have hmulR : (P * squareRootLength N : ℕ) ≤ N := by
    exact_mod_cast (show (P : ℝ) * (squareRootLength N : ℝ) ≤
        (N : ℝ) by nlinarith)
  exact (Nat.le_div_iff_mul_le hP).2
    (by simpa [Nat.mul_comm] using hmulR)

private lemma logarithmic_minor_bound_of
    {P N b : ℕ} (hP : 0 < P) (hN : 1 ≤ N)
    (hfour : 4 * squareRootLength N ≤ dirichletCutoff N)
    (hPb : P ≤ b) (hb : b ≤ dirichletCutoff N)
    (hmaster :
      16 * (P : ℝ) * (1 + Real.log (N : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / 16)) :
    8 * ((squareRootLength N : ℝ) + b) *
        (1 + Real.log (b : ℝ)) ≤ (N : ℝ) / P := by
  have hx : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hxone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hq0 : 0 ≤ (N : ℝ) ^ ((15 : ℝ) / 16) :=
    Real.rpow_nonneg hx.le _
  have hQq := cast_dirichletCutoff_le N
  have hbq : (b : ℝ) ≤ (N : ℝ) ^ ((15 : ℝ) / 16) :=
    (by exact_mod_cast hb : (b : ℝ) ≤ (dirichletCutoff N : ℝ)).trans hQq
  have hLq : (squareRootLength N : ℝ) ≤
      (N : ℝ) ^ ((15 : ℝ) / 16) := by
    have h4R : 4 * (squareRootLength N : ℝ) ≤
        (dirichletCutoff N : ℝ) := by exact_mod_cast hfour
    nlinarith
  have hq_le_x : (N : ℝ) ^ ((15 : ℝ) / 16) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxone
        (by norm_num : (15 : ℝ) / 16 ≤ 1)
  have hbpos : 0 < b := lt_of_lt_of_le hP hPb
  have hbN : (b : ℝ) ≤ (N : ℝ) := hbq.trans hq_le_x
  have hlog : Real.log (b : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hbpos) hbN
  have hlogb0 : 0 ≤ Real.log (b : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hxone
  have hleft :
      8 * ((squareRootLength N : ℝ) + b) * (1 + Real.log (b : ℝ)) ≤
        16 * (N : ℝ) ^ ((15 : ℝ) / 16) *
          (1 + Real.log (N : ℝ)) := by
    have hsum : (squareRootLength N : ℝ) + b ≤
        2 * (N : ℝ) ^ ((15 : ℝ) / 16) := by linarith
    calc
      8 * ((squareRootLength N : ℝ) + b) *
          (1 + Real.log (b : ℝ)) ≤
          8 * (2 * (N : ℝ) ^ ((15 : ℝ) / 16)) *
            (1 + Real.log (b : ℝ)) := by
              gcongr
      _ ≤ 8 * (2 * (N : ℝ) ^ ((15 : ℝ) / 16)) *
            (1 + Real.log (N : ℝ)) := by
              gcongr
      _ = 16 * (N : ℝ) ^ ((15 : ℝ) / 16) *
            (1 + Real.log (N : ℝ)) := by ring
  have hfactor :
      (N : ℝ) ^ ((15 : ℝ) / 16) *
          (N : ℝ) ^ ((1 : ℝ) / 16) = (N : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  have hprod :
      (16 * (N : ℝ) ^ ((15 : ℝ) / 16) *
          (1 + Real.log (N : ℝ))) * (P : ℝ) ≤ (N : ℝ) := by
    calc
      (16 * (N : ℝ) ^ ((15 : ℝ) / 16) *
          (1 + Real.log (N : ℝ))) * (P : ℝ) =
          (N : ℝ) ^ ((15 : ℝ) / 16) *
            (16 * (P : ℝ) * (1 + Real.log (N : ℝ))) := by ring
      _ ≤ (N : ℝ) ^ ((15 : ℝ) / 16) *
            (N : ℝ) ^ ((1 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_left hmaster hq0
      _ = (N : ℝ) := hfactor
  exact hleft.trans ((le_div_iff₀ hp).2 hprod)

/-- All elementary growth estimates needed to specialize the completed Weyl
bound hold simultaneously and uniformly for denominators between `P` and
`dirichletCutoff N`. -/
theorem eventually_squareRootLength_growth (P : ℕ) (hP : 0 < P) :
    ∀ᶠ N : ℕ in atTop,
      4 * squareRootLength N ≤ dirichletCutoff N ∧
      (squareRootLength N : ℝ) ^ 2 ≤ 5 * (N : ℝ) ∧
      squareRootLength N ≤ N / P ∧
      ∀ b : ℕ, P ≤ b → b ≤ dirichletCutoff N →
        8 * ((squareRootLength N : ℝ) + b) *
            (1 + Real.log (b : ℝ)) ≤ (N : ℝ) / P := by
  have hpR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hpow7 : ∀ᶠ N : ℕ in atTop,
      (16 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 16) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (7 : ℝ) / 16)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hsqrt9 : ∀ᶠ N : ℕ in atTop, (9 : ℝ) ≤ √(N : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 9)
  have hsqrtP : ∀ᶠ N : ℕ in atTop,
      (3 : ℝ) * P + 2 ≤ √(N : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((3 : ℝ) * P + 2))
  have hsmallReal :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 16) (by norm_num)).bound
      (show 0 < (1 : ℝ) / (32 * P) by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have hpowLarge : ∀ᶠ N : ℕ in atTop,
      32 * (P : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 16)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (32 * (P : ℝ)))
  filter_upwards [eventually_ge_atTop 1, hpow7, hsqrt9, hsqrtP,
      hsmallNat, hpowLarge] with N hN hpow7N hsqrt9N hsqrtPN hsmallN hpowLargeN
  have hxone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hxone
  have hrpow0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := by positivity
  have hlogsmall : Real.log (N : ℝ) ≤
      ((1 : ℝ) / (32 * P)) * (N : ℝ) ^ ((1 : ℝ) / 16) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hrpow0] using hsmallN
  have honeSmall : (1 : ℝ) ≤
      ((1 : ℝ) / (32 * P)) * (N : ℝ) ^ ((1 : ℝ) / 16) := by
    calc
      (1 : ℝ) = ((1 : ℝ) / (32 * P)) * (32 * P) := by field_simp
      _ ≤ ((1 : ℝ) / (32 * P)) *
          (N : ℝ) ^ ((1 : ℝ) / 16) := by
        gcongr
  have hmaster :
      16 * (P : ℝ) * (1 + Real.log (N : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / 16) := by
    have := add_le_add honeSmall hlogsmall
    field_simp at this ⊢
    nlinarith
  have hfour := four_squareRootLength_le_dirichletCutoff_of hN hpow7N
  refine ⟨hfour, squareRootLength_sq_le_of hsqrt9N,
    squareRootLength_le_div_of hP hsqrtPN, ?_⟩
  intro b _ hbQ
  exact logarithmic_minor_bound_of hP hN hfour (by assumption) hbQ hmaster

/-- Uniform minor-arc Weyl bound at the cutoff used in the KLS shifting
argument.  For every fixed denominator threshold `P`, all reduced rational
approximations with `P ≤ b ≤ ⌊N^(15/16)⌋` satisfy this estimate once
`N` is sufficiently large. -/
theorem eventually_norm_squareExpSum_le_minor (P : ℕ) (hP : 0 < P) :
    ∀ᶠ N : ℕ in atTop, ∀ (θ : ℝ) (a b : ℕ),
      P ≤ b → b ≤ dirichletCutoff N → a.Coprime b →
      |θ - (a : ℝ) / (b : ℝ)| ≤
        1 / ((b : ℝ) * (dirichletCutoff N : ℝ)) →
      ‖squareExpSum θ (squareRootLength N)‖ ≤
        6 * Real.sqrt ((N : ℝ) / P) := by
  filter_upwards [eventually_squareRootLength_growth P hP] with N hN
  rintro θ a b hPb hbQ hab happ
  rcases hN with ⟨hfour, hLsq, hLdiv, hlog⟩
  have hLsmall : (squareRootLength N : ℝ) ≤ (N : ℝ) / P := by
    calc
      (squareRootLength N : ℝ) ≤ (N / P : ℕ) := by exact_mod_cast hLdiv
      _ ≤ (N : ℝ) / P := Nat.cast_div_le
  exact norm_squareExpSum_le_minor_of_growth_six
    θ a b (dirichletCutoff N) (squareRootLength N) N P hP hPb hab
    hfour happ hLsq hLsmall (hlog b hPb hbQ)

/-- Signed-numerator version of `eventually_norm_squareExpSum_le_minor`.
It applies directly to Fourier frequencies of either sign. -/
theorem eventually_norm_squareExpSum_le_minor_int (P : ℕ) (hP : 0 < P) :
    ∀ᶠ N : ℕ in atTop, ∀ (θ : ℝ) (a : ℤ) (b : ℕ),
      P ≤ b → b ≤ dirichletCutoff N → a.natAbs.Coprime b →
      |θ - (a : ℝ) / (b : ℝ)| ≤
        1 / ((b : ℝ) * (dirichletCutoff N : ℝ)) →
      ‖squareExpSum θ (squareRootLength N)‖ ≤
        6 * Real.sqrt ((N : ℝ) / P) := by
  filter_upwards [eventually_squareRootLength_growth P hP] with N hN
  rintro θ a b hPb hbQ hab happ
  rcases hN with ⟨hfour, hLsq, hLdiv, hlog⟩
  have hLsmall : (squareRootLength N : ℝ) ≤ (N : ℝ) / P := by
    calc
      (squareRootLength N : ℝ) ≤ (N / P : ℕ) := by exact_mod_cast hLdiv
      _ ≤ (N : ℝ) / P := Nat.cast_div_le
  exact norm_squareExpSum_le_minor_of_growth_six_int
    θ a b (dirichletCutoff N) (squareRootLength N) N P hP hPb hab
    hfour happ hLsq hLsmall (hlog b hPb hbQ)

/-- Every real frequency has a reduced Dirichlet approximation at the
power-sized cutoff, and whenever its denominator lies on the minor arcs
(`P ≤ b`) the corresponding quadratic sum satisfies the uniform Weyl
bound.  This packages the frequency assignment and estimate used in the
Fourier decomposition. -/
theorem eventually_exists_reduced_approximation_and_minor
    (P : ℕ) (hP : 0 < P) :
    ∀ᶠ N : ℕ in atTop, ∀ θ : ℝ,
      ∃ (a : ℤ) (b : ℕ),
        1 ≤ b ∧ b ≤ dirichletCutoff N ∧ a.natAbs.Coprime b ∧
        |θ - (a : ℝ) / (b : ℝ)| ≤
          1 / ((b : ℝ) * (dirichletCutoff N : ℝ)) ∧
        (P ≤ b → ‖squareExpSum θ (squareRootLength N)‖ ≤
          6 * Real.sqrt ((N : ℝ) / P)) := by
  filter_upwards [eventually_squareRootLength_growth P hP,
      eventually_norm_squareExpSum_le_minor_int P hP] with N hgrowth hminor
  intro θ
  have hQ1 : 1 ≤ dirichletCutoff N := by
    have hLpos : 0 < squareRootLength N := by
      simp [squareRootLength]
    omega
  obtain ⟨a, b, hb1, hbQ, hab, happ⟩ :=
    dirichletApproximationReduced θ (dirichletCutoff N) hQ1
  refine ⟨a, b, hb1, hbQ, hab, happ, ?_⟩
  intro hPb
  exact hminor θ a b hPb hbQ hab happ

end QuadraticWeyl

end Erdos438
