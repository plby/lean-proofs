import ErdosProblems.Erdos1148.Elementary

/-!
# Removing the parity restriction from the local existence problem

Two small integral changes of variables preserve the discriminant. Near the
normalized form `(1, -1, -1) / sqrt 5`, they also preserve the strict size
bounds, and one of the two corrects any parity mismatch. Thus an unrestricted
local existence theorem suffices for Erdős 1148. This module does not assert
or assume an equidistribution axiom.
-/

namespace Erdos1148

def discG {R : Type*} [CommRing R] (t : R × R × R) : R × R × R :=
  (t.1 - t.2.1 + t.2.2,
    -2 * t.1 + 3 * t.2.1 - 4 * t.2.2,
    t.1 - 2 * t.2.1 + 4 * t.2.2)

def discH {R : Type*} [CommRing R] (t : R × R × R) : R × R × R :=
  (t.1 + t.2.1 + t.2.2,
    -4 * t.1 - 3 * t.2.1 - 2 * t.2.2,
    4 * t.1 + 2 * t.2.1 + t.2.2)

lemma discG_discriminant {R : Type*} [CommRing R] (t : R × R × R) :
    (discG t).2.1 ^ 2 - 4 * (discG t).1 * (discG t).2.2 =
      t.2.1 ^ 2 - 4 * t.1 * t.2.2 := by
  dsimp [discG]
  ring

lemma discH_discriminant {R : Type*} [CommRing R] (t : R × R × R) :
    (discH t).2.1 ^ 2 - 4 * (discH t).1 * (discH t).2.2 =
      t.2.1 ^ 2 - 4 * t.1 * t.2.2 := by
  dsimp [discH]
  ring

lemma discG_parity (t : ℤ × ℤ × ℤ) (hb : t.2.1 % 2 = 0)
    (hc : t.2.2 % 2 = 0) : (discG t).1 % 2 = (discG t).2.2 % 2 := by
  dsimp [discG]
  omega

lemma discH_parity (t : ℤ × ℤ × ℤ) (hb : t.2.1 % 2 = 0)
    (ha : t.1 % 2 = 0) : (discH t).1 % 2 = (discH t).2.2 % 2 := by
  dsimp [discH]
  omega

def StrictDiscBounds (t : ℝ × ℝ × ℝ) : Prop :=
  |t.1 - t.2.2| < 1 ∧ |t.2.1| < 1 ∧ |t.1 + t.2.2| < 1

def paritySafeRegion : Set (ℝ × ℝ × ℝ) :=
  {t | StrictDiscBounds t ∧ StrictDiscBounds (discG t) ∧ StrictDiscBounds (discH t)}

noncomputable def discCenter : ℝ × ℝ × ℝ :=
  (1 / Real.sqrt 5, -(1 / Real.sqrt 5), -(1 / Real.sqrt 5))

lemma discG_center : discG discCenter = discCenter := by
  dsimp [discG, discCenter]
  ext <;> ring

lemma discH_center : discH discCenter = -discCenter := by
  dsimp [discH, discCenter]
  ext <;> simp <;> ring

lemma strictDiscBounds_neg (t : ℝ × ℝ × ℝ) :
    StrictDiscBounds (-t) ↔ StrictDiscBounds t := by
  dsimp [StrictDiscBounds]
  simp only [neg_sub_neg, abs_sub_comm, abs_neg, ← neg_add]

lemma discCenter_bounds : StrictDiscBounds discCenter := by
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hslt : 2 < Real.sqrt (5 : ℝ) := by nlinarith
  dsimp [StrictDiscBounds, discCenter]
  have hq0 : 0 ≤ 1 / Real.sqrt (5 : ℝ) := by positivity
  have hq : 2 * (1 / Real.sqrt (5 : ℝ)) < 1 := by
    have : (2 : ℝ) / Real.sqrt 5 < 1 := (div_lt_one hs).mpr hslt
    convert this using 1
    ring
  rw [abs_of_nonneg (by linarith), abs_neg, abs_of_nonneg hq0]
  constructor
  · linarith
  · constructor
    · linarith
    · simp

lemma discCenter_discriminant :
    discCenter.2.1 ^ 2 - 4 * discCenter.1 * discCenter.2.2 = 1 := by
  have hs : Real.sqrt (5 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [discCenter]
  field_simp
  nlinarith

lemma discCenter_mem_paritySafeRegion : discCenter ∈ paritySafeRegion := by
  refine ⟨discCenter_bounds, ?_, ?_⟩
  · rw [discG_center]
    exact discCenter_bounds
  · rw [discH_center, strictDiscBounds_neg]
    exact discCenter_bounds

lemma strictDiscBounds_isOpen : IsOpen {t : ℝ × ℝ × ℝ | StrictDiscBounds t} := by
  have h₁ : IsOpen {t : ℝ × ℝ × ℝ | |t.1 - t.2.2| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have h₂ : IsOpen {t : ℝ × ℝ × ℝ | |t.2.1| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have h₃ : IsOpen {t : ℝ × ℝ × ℝ | |t.1 + t.2.2| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h₁.inter (h₂.inter h₃)

lemma paritySafeRegion_isOpen : IsOpen paritySafeRegion := by
  have hg : Continuous (discG : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ) := by
    unfold discG
    fun_prop
  have hh : Continuous (discH : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ) := by
    unfold discH
    fun_prop
  exact strictDiscBounds_isOpen.inter
    ((strictDiscBounds_isOpen.preimage hg).inter (strictDiscBounds_isOpen.preimage hh))

lemma discCenter_small_ball_subset :
    Metric.ball discCenter (1 / 100) ⊆ paritySafeRegion := by
  intro t ht
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hslt : (20 : ℝ) / 9 < Real.sqrt 5 := by nlinarith
  have hq0 : 0 ≤ 1 / Real.sqrt (5 : ℝ) := by positivity
  have hq : (1 : ℝ) / Real.sqrt 5 < 9 / 20 := (div_lt_iff₀ hs).mpr (by nlinarith)
  simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, discCenter] at ht
  obtain ⟨ha, hb, hc⟩ := ht
  obtain ⟨ha₁, ha₂⟩ := abs_lt.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_lt.mp hb
  obtain ⟨hc₁, hc₂⟩ := abs_lt.mp hc
  dsimp [paritySafeRegion, StrictDiscBounds, discG, discH]
  simp only [abs_lt]
  repeat' constructor
  all_goals linarith

lemma exists_paritySafe_ball :
    ∃ ε > 0, Metric.ball discCenter ε ⊆ paritySafeRegion :=
  ⟨1 / 100, by norm_num, discCenter_small_ball_subset⟩

noncomputable def normalizeDisc (n : ℤ) (t : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  ((t.1 : ℝ) / Real.sqrt (4 * (n : ℝ)),
    (t.2.1 : ℝ) / Real.sqrt (4 * (n : ℝ)),
    (t.2.2 : ℝ) / Real.sqrt (4 * (n : ℝ)))

lemma normalizeDisc_g (n : ℤ) (t : ℤ × ℤ × ℤ) :
    normalizeDisc n (discG t) = discG (normalizeDisc n t) := by
  dsimp [normalizeDisc, discG]
  push_cast
  ext <;> ring

lemma normalizeDisc_h (n : ℤ) (t : ℤ × ℤ × ℤ) :
    normalizeDisc n (discH t) = discH (normalizeDisc n t) := by
  dsimp [normalizeDisc, discH]
  push_cast
  ext <;> ring

lemma even_middle_of_discriminant {n a b c : ℤ}
    (hdisc : b ^ 2 - 4 * a * c = 4 * n) : b % 2 = 0 := by
  have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hb2 with hb | hb
  · exact hb
  · have hbmod : (b * b) % 2 = 1 := by rw [Int.mul_emod, hb]; norm_num
    have heq : b * b = 4 * (n + a * c) := by nlinarith
    rw [heq] at hbmod
    omega

lemma half_sq_le_of_normalized_abs_lt {n q w : ℤ} (hn : 0 < n)
    (hqw : q = 2 * w) (hb : |(q : ℝ) / Real.sqrt (4 * (n : ℝ))| < 1) :
    w ^ 2 ≤ n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (4 * (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (4 * (n : ℝ))) ^ 2 = 4 * n := Real.sq_sqrt (by positivity)
  rw [abs_div, abs_of_pos hs, div_lt_one hs] at hb
  have hsq : (q : ℝ) ^ 2 < (Real.sqrt (4 * (n : ℝ))) ^ 2 := by
    apply sq_lt_sq.mpr
    simpa only [abs_of_pos hs] using hb
  have hqw' : (q : ℝ) = 2 * (w : ℝ) := by exact_mod_cast hqw
  rw [hqw'] at hsq
  have hw : (w : ℝ) ^ 2 ≤ n := by nlinarith
  exact_mod_cast hw

lemma boundedRepresentation_of_disc_bounds {n : ℤ} (hn : 0 < n) (t : ℤ × ℤ × ℤ)
    (hdisc : t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n)
    (hpar : t.1 % 2 = t.2.2 % 2) (hbounds : StrictDiscBounds (normalizeDisc n t)) :
    HasBoundedRepresentation n := by
  obtain ⟨a, b, c⟩ := t
  dsimp at hdisc hpar
  have hb := even_middle_of_discriminant hdisc
  have hx : a - c = 2 * ((a - c) / 2) := by omega
  have hy : b = 2 * (b / 2) := by omega
  have hz : a + c = 2 * ((a + c) / 2) := by omega
  have heq : n = ((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2 := by
    have hfour : 4 * (((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2) =
        4 * n := by
      calc
        _ = (2 * ((a - c) / 2)) ^ 2 + (2 * (b / 2)) ^ 2 -
            (2 * ((a + c) / 2)) ^ 2 := by ring
        _ = (a - c) ^ 2 + b ^ 2 - (a + c) ^ 2 := by rw [← hx, ← hy, ← hz]
        _ = 4 * n := by nlinarith [hdisc]
    omega
  have habounds : |((a - c : ℤ) : ℝ) / Real.sqrt (4 * (n : ℝ))| < 1 := by
    simpa only [normalizeDisc, StrictDiscBounds, Int.cast_sub, sub_div] using hbounds.1
  have hbbounds : |(b : ℝ) / Real.sqrt (4 * (n : ℝ))| < 1 := hbounds.2.1
  have hcbounds : |((a + c : ℤ) : ℝ) / Real.sqrt (4 * (n : ℝ))| < 1 := by
    simpa only [normalizeDisc, StrictDiscBounds, Int.cast_add, add_div] using hbounds.2.2
  exact ⟨(a - c) / 2, b / 2, (a + c) / 2, heq,
    max_le (half_sq_le_of_normalized_abs_lt hn hx habounds)
      (max_le (half_sq_le_of_normalized_abs_lt hn hy hbbounds)
        (half_sq_le_of_normalized_abs_lt hn hz hcbounds))⟩

/-- An unrestricted discriminant point in this fixed open set suffices:
neither primitivity nor a parity condition is a hypothesis. -/
theorem boundedRepresentation_of_local_point {n : ℤ} (hn : 0 < n) (t : ℤ × ℤ × ℤ)
    (hdisc : t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n)
    (hlocal : normalizeDisc n t ∈ paritySafeRegion) : HasBoundedRepresentation n := by
  have hb := even_middle_of_discriminant hdisc
  by_cases hpar : t.1 % 2 = t.2.2 % 2
  · exact boundedRepresentation_of_disc_bounds hn t hdisc hpar hlocal.1
  by_cases hc : t.2.2 % 2 = 0
  · apply boundedRepresentation_of_disc_bounds hn (discG t)
    · rwa [discG_discriminant]
    · exact discG_parity t hb hc
    · simpa only [normalizeDisc_g] using hlocal.2.1
  · apply boundedRepresentation_of_disc_bounds hn (discH t)
    · rwa [discH_discriminant]
    · exact discH_parity t hb (by omega)
    · simpa only [normalizeDisc_h] using hlocal.2.2

/-- Local existence only for nonsquares suffices; squares are elementary.
The hypothesis contains no primitivity or parity requirement. -/
theorem erdos_1148_of_unrestricted_local_existence
    (hlocal : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ¬ IsSquare n →
      ∃ t : ℤ × ℤ × ℤ, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n ∧
        normalizeDisc n t ∈ paritySafeRegion) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∃ x y z : ℤ,
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n := by
  obtain ⟨N, hN⟩ := hlocal
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  by_cases hsq : IsSquare n
  · exact boundedRepresentation_of_isSquare hsq
  · obtain ⟨t, hdisc, ht⟩ := hN n (by omega) hsq
    exact boundedRepresentation_of_local_point (by omega) t hdisc ht

/-- The analytic input can be restricted to this explicit ball of radius `1/100`. -/
theorem erdos_1148_of_fixed_ball_existence
    (hball : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ¬ IsSquare n →
      ∃ t : ℤ × ℤ × ℤ, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n ∧
        normalizeDisc n t ∈ Metric.ball discCenter (1 / 100)) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∃ x y z : ℤ,
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n := by
  obtain ⟨N, hN⟩ := hball
  apply erdos_1148_of_unrestricted_local_existence
  refine ⟨N, fun n hn hsq ↦ ?_⟩
  obtain ⟨t, hdisc, ht⟩ := hN n hn hsq
  exact ⟨t, hdisc, discCenter_small_ball_subset ht⟩

/-- A single fixed positive radius is enough; an equidistribution theorem
would supply the hypothesis. This is not an unconditional existence theorem. -/
theorem exists_radius_sufficient_for_erdos_1148 :
    ∃ ε > 0,
      (∃ N : ℤ, ∀ n : ℤ, N ≤ n → ¬ IsSquare n →
        ∃ t : ℤ × ℤ × ℤ, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n ∧
          normalizeDisc n t ∈ Metric.ball discCenter ε) →
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∃ x y z : ℤ,
        n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n := by
  obtain ⟨ε, hε, hsub⟩ := exists_paritySafe_ball
  refine ⟨ε, hε, ?_⟩
  rintro ⟨N, hN⟩
  apply erdos_1148_of_unrestricted_local_existence
  refine ⟨N, fun n hn hsq ↦ ?_⟩
  obtain ⟨t, hdisc, ht⟩ := hN n hn hsq
  exact ⟨t, hdisc, hsub ht⟩

end Erdos1148
