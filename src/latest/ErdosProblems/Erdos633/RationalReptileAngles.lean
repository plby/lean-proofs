import ErdosProblems.Erdos633.QuadraticAngleOrder
import ErdosProblems.Erdos633.SmallTotient

/-!
# The finite angle list for rational-angle nonsquare reptilings

Angles are recorded in units of pi/60. The cyclotomic order bound gives
eleven possible numerators. A sorted scalene triple with sum sixty can
only have numerators ten, twenty, and thirty.
-/

namespace Erdos633

def SmallAngleNumerator (m : ℕ) : Prop :=
  m = 10 ∨ m = 12 ∨ m = 15 ∨ m = 20 ∨ m = 24 ∨ m = 30 ∨
    m = 36 ∨ m = 40 ∨ m = 45 ∨ m = 48 ∨ m = 50

theorem rational_rotation_small_numerator (q : ℚ) (hq0 : 0 < q) (hqhalf : q < 1 / 2)
    (hphi : q.den.totient ≤ 4) :
    ∃ m : ℕ, SmallAngleNumerator m ∧ q = (m : ℚ) / 120 := by
  have hn0 : 0 < q.num := Rat.num_pos.mpr hq0
  have hdpos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hnum : 2 * q.num < (q.den : ℤ) := by
    have h := (div_lt_iff₀ hdpos).mp (show (q.num : ℚ) / q.den < 1 / 2 by
      simpa only [q.num_div_den] using hqhalf)
    exact_mod_cast (show 2 * (q.num : ℚ) < q.den by linarith only [h])
  have hc := q.reduced
  rcases totient_le_four_orders q.den q.den_pos hphi with
    hd | hd | hd | hd | hd | hd | hd | hd | hd
  all_goals rw [hd] at hnum
  all_goals have hnum6 : q.num < 6 := by omega
  all_goals interval_cases hm : q.num <;> norm_num [hm] at hnum <;> norm_num [hd, hm] at hc
  all_goals
    refine ⟨120 * q.num.natAbs / q.den, ?_, ?_⟩
    · norm_num [SmallAngleNumerator, hd, hm]
    · calc
        q = (q.num : ℚ) / q.den := q.num_div_den.symm
        _ = _ := by norm_num [hd, hm]

theorem rational_angle_small_numerator (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hrat : θ / Real.pi ∈ rationalReals)
    (hcos : IsIntegral ℚ (Real.cos θ)) (hdeg : (minpoly ℚ (Real.cos θ)).natDegree ≤ 2) :
    ∃ m : ℕ, SmallAngleNumerator m ∧ θ = (m : ℝ) * Real.pi / 60 := by
  have hrat' : θ / (2 * Real.pi) ∈ rationalReals := by
    simpa only [div_div, Nat.cast_ofNat, mul_comm Real.pi 2] using
      rationalReals.div_mem hrat (rationalReals_nat 2)
  obtain ⟨q, hq⟩ := (mem_rationalReals_iff _).mp hrat'
  have hq0 : 0 < q := by
    exact_mod_cast (show (0 : ℝ) < q by rw [hq]; positivity)
  have hqhalf : q < 1 / 2 := by
    have h : (q : ℝ) < 1 / 2 := by
      rw [hq]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      nlinarith only [hθπ]
    exact (Rat.cast_lt (K := ℝ)).mp (by simpa only [Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using h)
  have hθ : 2 * Real.pi * (q : ℝ) = θ := by
    rw [hq]
    field_simp
  have hphi : q.den.totient ≤ 4 := by
    apply rational_rotation_totient_le_four q
    · simpa only [hθ] using hcos
    · simpa only [hθ] using hdeg
  obtain ⟨m, hm, hqm⟩ := rational_rotation_small_numerator q hq0 hqhalf hphi
  refine ⟨m, hm, ?_⟩
  rw [← hθ, hqm]
  push_cast
  ring

theorem small_angle_numerators_sorted (a b c : ℕ)
    (ha : SmallAngleNumerator a) (hb : SmallAngleNumerator b) (hc : SmallAngleNumerator c)
    (hab : a < b) (hbc : b < c) (hsum : a + b + c = 60) :
    a = 10 ∧ b = 20 ∧ c = 30 := by
  unfold SmallAngleNumerator at ha hb hc
  omega

theorem Triangle.rational_quadratic_cosines_small_numerators (P : Triangle)
    (hrat : P.CommensurableAngles)
    (hcos : ∀ k : Fin 3, IsIntegral ℚ (Real.cos (P.cornerAngle k)) ∧
      (minpoly ℚ (Real.cos (P.cornerAngle k))).natDegree ≤ 2) :
    ∃ m : Fin 3 → ℕ, (∀ k, SmallAngleNumerator (m k)) ∧
      ∀ k, P.cornerAngle k = (m k : ℝ) * Real.pi / 60 := by
  have h (k : Fin 3) := rational_angle_small_numerator (P.cornerAngle k)
    (P.cornerAngle_pos k) (P.cornerAngle_lt_pi k) (hrat k) (hcos k).1 (hcos k).2
  choose m hm heq using h
  exact ⟨m, hm, heq⟩

theorem Triangle.permuted_thirty_of_rational_quadratic_cosines (P : Triangle)
    (hrat : P.CommensurableAngles) (hinj : Function.Injective P.cornerAngle)
    (hcos : ∀ k : Fin 3, IsIntegral ℚ (Real.cos (P.cornerAngle k)) ∧
      (minpoly ℚ (Real.cos (P.cornerAngle k))).natDegree ≤ 2) :
    PermutedTriple P.cornerAngle ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  obtain ⟨m, hm, heq⟩ := P.rational_quadratic_cosines_small_numerators hrat hcos
  have hminj : Function.Injective m := by
    intro i j hij
    apply hinj
    rw [heq i, heq j, hij]
  obtain ⟨e, hmono⟩ := exists_perm_strictMono_nat m hminj
  have hs := P.sum_cornerAngle_permuted e
  rw [heq (e 0), heq (e 1), heq (e 2)] at hs
  have hsumR : (m (e 0) : ℝ) + (m (e 1) : ℝ) + (m (e 2) : ℝ) = 60 := by
    apply mul_right_cancel₀ (ne_of_gt Real.pi_pos)
    nlinarith only [hs]
  have hsum : m (e 0) + m (e 1) + m (e 2) = 60 := by exact_mod_cast hsumR
  obtain ⟨ha, hb, hc⟩ := small_angle_numerators_sorted (m (e 0)) (m (e 1)) (m (e 2))
    (hm (e 0)) (hm (e 1)) (hm (e 2)) (hmono (by decide : (0 : Fin 3) < 1))
    (hmono (by decide : (1 : Fin 3) < 2)) hsum
  have h0 : P.cornerAngle (e 0) = Real.pi / 6 := by rw [heq (e 0), ha]; norm_num; ring
  have h1 : P.cornerAngle (e 1) = Real.pi / 3 := by rw [heq (e 1), hb]; norm_num; ring
  have h2 : P.cornerAngle (e 2) = Real.pi / 2 := by rw [heq (e 2), hc]; norm_num; ring
  exact (permutedTriple_of_at e h0 h1 h2).swap_last

end Erdos633
