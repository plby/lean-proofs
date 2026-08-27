import ErdosProblems.Erdos587.HooleyReciprocalBlock
import ErdosProblems.Erdos587.HooleyReciprocalParameters
import ErdosProblems.Erdos587.HooleyWeightedGcd

/-! # Summing the reciprocal long-progression denominator range -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_reciprocal_good_denominators_bound (a c r : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q v X D Y : ℕ, 0 < q → q.Coprime v → 2 ≤ X → q ≤ X →
      16 ≤ Y → X ≤ Y ^ r → ∀ (A : ℕ → ℤ) (K R : ℝ),
      1 ≤ K → 0 < R → K ≤ 2 ^ D → (2 : ℝ) ^ D ≤ 2 * K → (a : ℝ) * K < q →
      (a : ℝ) * v * K + 16 * c * q * R ≤ X →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - (a : ℤ) * v) →
      (∀ x ∈ S, |deltaReciprocalFrequencyError c A x| ≤ 2 / ((x.denominator : ℝ) * K)) →
      (∀ x ∈ S, (Y : ℝ) ≤ 2 * c * R * x.denominator / K ^ 2) →
      (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  obtain ⟨C₀, hC₀, hblock⟩ := exists_delta_reciprocal_majorant_block_bound r hr
  obtain ⟨C₁, hC₁, hgcd⟩ := exists_delta_weighted_gcd_multiple_mean_bound
  have hτ : (0 : ℝ) < a.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd a, ha.ne'⟩⟩
  refine ⟨2 * C₀ * C₁ * c * a.divisors.card, by positivity, ?_⟩
  intro q v X D Y hq hcop hX hqX hY hsize A K R hK hR hKD hDK hqa hvalue
    S hlow hupp hden hrel herror hgood
  let L := max 1 (Real.log (Real.log (X : ℝ)))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hKpos : 0 < K := by linarith
  have hmap (x : DeltaApproximant) (hx : x ∈ S) : x.denominator ∈ Finset.Icc 1 (2 ^ D) := by
    refine Finset.mem_Icc.mpr ⟨(hden x hx).1, ?_⟩
    exact_mod_cast (hden x hx).2.trans hKD
  have hlevel (b : ℕ) (hb : b ∈ Finset.Icc 1 (2 ^ D)) :
      (∑ x ∈ S with x.denominator = b, deltaReciprocalMajorant K c A x) ≤
        C₀ * c * R * (q.gcd (a * b)).divisors.card * ((D - Nat.clog 2 b : ℕ) + 3) * L ^ 6 := by
    let T := S.filter (fun x => x.denominator = b)
    have hbpos : 0 < b := (Finset.mem_Icc.mp hb).1
    have hbD : Nat.clog 2 b ≤ D := Nat.clog_le_of_le_pow (Finset.mem_Icc.mp hb).2
    by_cases hT : T.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hT
      have hbK : (b : ℝ) ≤ K := by
        simpa only [(Finset.mem_filter.mp hx₀).2] using (hden x₀ (Finset.mem_filter.mp hx₀).1).2
      have hbase : (Y : ℝ) ≤ 2 * c * R * b / K ^ 2 := by
        simpa only [(Finset.mem_filter.mp hx₀).2] using hgood x₀ (Finset.mem_filter.mp hx₀).1
      have hbase8 : 8 ≤ 2 * c * R * b / K ^ 2 := by
        have hYR : (16 : ℝ) ≤ Y := by exact_mod_cast hY
        linarith
      have hsize' : X ≤ ⌊2 * c * R * b / K ^ 2⌋₊ ^ r :=
        hsize.trans (Nat.pow_le_pow_left (Nat.le_floor hbase) r)
      have hvalues (t : ℤ)
          (ht : |(t : ℝ)| ≤ (2 * c * R * b / K ^ 2) * 2 ^ (D - Nat.clog 2 b + 2)) :
          (b : ℤ) * a * v - q * t ≠ 0 ∧ ((b : ℤ) * a * v - q * t).natAbs ≤ X := by
        have ht' := ht.trans (delta_reciprocal_shell_tolerance_le hK hR.le hDK hbD)
        exact ⟨delta_reciprocal_encoded_ne_zero ha hbpos hK hbK hcop hqa t,
          delta_reciprocal_value_size hbK hvalue t ht'⟩
      have hscale (x : DeltaApproximant) (hx : x ∈ T) :
          K ^ 2 * |deltaReciprocalFrequencyError c A x| ≤ 2 ^ (D - Nat.clog 2 b + 2) := by
        have hxS := (Finset.mem_filter.mp hx).1
        exact delta_reciprocal_dyadic_scale hKpos hKD hbD A (hden x hxS).1
          (congrArg (Nat.clog 2) (Finset.mem_filter.mp hx).2) (herror x hxS)
      have h := hblock c q b X hc hq hbpos hX a v A K R hKpos hR hbase8 hsize'
        (D - Nat.clog 2 b + 2) T
        (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
        (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x hx => hrel x (Finset.mem_filter.mp hx).1) hvalues hscale
      rw [delta_reciprocal_gcd_cancel hcop] at h
      exact h.trans_eq (by dsimp only [L]; push_cast; ring)
    · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      change (∑ x ∈ T, deltaReciprocalMajorant K c A x) ≤ _
      rw [hempty, Finset.sum_empty]
      positivity
  have hg : (∑ b ∈ Finset.Icc 1 (2 ^ D),
      ((q.gcd (a * b)).divisors.card : ℝ) * ((D - Nat.clog 2 b : ℕ) + 3)) ≤
      C₁ * a.divisors.card * 2 ^ D * L := by
    apply (hgcd a q D ha hq).trans
    exact mul_le_mul_of_nonneg_left (delta_loglog_nat_mono hqX) (by positivity)
  calc
    _ = ∑ b ∈ Finset.Icc 1 (2 ^ D),
        ∑ x ∈ S with x.denominator = b, deltaReciprocalMajorant K c A x :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ b ∈ Finset.Icc 1 (2 ^ D),
        C₀ * c * R * (q.gcd (a * b)).divisors.card * ((D - Nat.clog 2 b : ℕ) + 3) * L ^ 6 :=
      Finset.sum_le_sum hlevel
    _ = (C₀ * c * R * L ^ 6) * ∑ b ∈ Finset.Icc 1 (2 ^ D),
        ((q.gcd (a * b)).divisors.card : ℝ) * ((D - Nat.clog 2 b : ℕ) + 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ (C₀ * c * R * L ^ 6) * (C₁ * a.divisors.card * 2 ^ D * L) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (C₀ * C₁ * c * a.divisors.card * R * L ^ 7) * 2 ^ D := by ring
    _ ≤ (C₀ * C₁ * c * a.divisors.card * R * L ^ 7) * (2 * K) :=
      mul_le_mul_of_nonneg_left hDK (by positivity)
    _ = _ := by dsimp only [L]; ring

end Erdos587
