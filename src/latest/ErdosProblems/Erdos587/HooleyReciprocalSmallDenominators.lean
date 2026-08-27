import ErdosProblems.Erdos587.HooleyReciprocalBlock
import ErdosProblems.Erdos587.HooleyReciprocalParameters
import ErdosProblems.Erdos587.HooleyReciprocalDenominatorSum

/-! # Summing the reciprocal short-progression denominator range -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_reciprocal_small_denominators_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a c q v X D Y : ℕ, 0 < a → 0 < c → q.Coprime v →
      ∀ (A : ℕ → ℤ) (K R : ℝ), 1 ≤ K → 0 < R →
      K ≤ 2 ^ D → (2 : ℝ) ^ D ≤ 2 * K → (a : ℝ) * K < q →
      (a : ℝ) * v * K + 16 * c * q * R ≤ X →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - (a : ℤ) * v) →
      (∀ x ∈ S, |deltaReciprocalFrequencyError c A x| ≤ 2 / ((x.denominator : ℝ) * K)) →
      (∀ x ∈ S, 2 * c * R * x.denominator / K ^ 2 < Y) →
      (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
        C * K ^ 2 * (Y + 2) * (D + 3) * (X : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hblock⟩ := exists_delta_reciprocal_majorant_small_block_bound hε
  refine ⟨C, hC, ?_⟩
  intro a c q v X D Y ha hc hcop A K R hK hR hKD hDK hqa hvalue
    S hlow hupp hden hrel herror hsmall
  let H := (Y : ℝ) * K ^ 2 / (2 * c * R)
  let I := (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H)
  have hKpos : 0 < K := by linarith
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hmap (x : DeltaApproximant) (hx : x ∈ S) : x.denominator ∈ I := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hden x hx).1, ?_⟩, ?_⟩
    · exact_mod_cast (hden x hx).2.trans hKD
    · apply le_of_lt
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * c * R)).mpr
      have h := (div_lt_iff₀ (sq_pos_of_pos hKpos)).mp (hsmall x hx)
      nlinarith
  have hlevel (b : ℕ) (hb : b ∈ I) :
      (∑ x ∈ S with x.denominator = b, deltaReciprocalMajorant K c A x) ≤
        C * (2 * c * R * ((D - Nat.clog 2 b : ℕ) + 3) + K ^ 2 / b) * (X : ℝ) ^ ε := by
    let T := S.filter (fun x => x.denominator = b)
    have hbpos : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    have hbD : Nat.clog 2 b ≤ D :=
      Nat.clog_le_of_le_pow (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
    by_cases hT : T.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hT
      have hbK : (b : ℝ) ≤ K := by
        simpa only [(Finset.mem_filter.mp hx₀).2] using (hden x₀ (Finset.mem_filter.mp hx₀).1).2
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
      have h := hblock c q b X hc hbpos a v A K R hKpos hR (D - Nat.clog 2 b + 2) T
        (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
        (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x hx => hrel x (Finset.mem_filter.mp hx).1) hvalues hscale
      exact h.trans_eq (by push_cast; ring)
    · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      change (∑ x ∈ T, deltaReciprocalMajorant K c A x) ≤ _
      rw [hempty, Finset.sum_empty]
      positivity
  have hcost : (∑ b ∈ I, (2 * (c : ℝ) * R * ((D - Nat.clog 2 b : ℕ) + 3) + K ^ 2 / b)) ≤
      K ^ 2 * (Y + 2) * (D + 3) := by
    have h := delta_reciprocal_short_denominator_cost D hH
      (by positivity : (0 : ℝ) ≤ 2 * c * R) (sq_nonneg K)
    have hcancel : (2 : ℝ) * c * R * H = (Y : ℝ) * K ^ 2 := by
      dsimp only [H]
      field_simp
    rw [hcancel] at h
    apply h.trans
    nlinarith [sq_nonneg K]
  calc
    _ = ∑ b ∈ I, ∑ x ∈ S with x.denominator = b, deltaReciprocalMajorant K c A x :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ b ∈ I, C *
        (2 * c * R * ((D - Nat.clog 2 b : ℕ) + 3) + K ^ 2 / b) * (X : ℝ) ^ ε :=
      Finset.sum_le_sum hlevel
    _ = (C * (X : ℝ) ^ ε) *
        ∑ b ∈ I, (2 * c * R * ((D - Nat.clog 2 b : ℕ) + 3) + K ^ 2 / b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ (C * (X : ℝ) ^ ε) * (K ^ 2 * (Y + 2) * (D + 3)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

end Erdos587
