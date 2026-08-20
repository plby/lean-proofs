import ErdosProblems.Erdos525.HighVelocity

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

/-!
## Covariance of a single value away from the real degeneracies

The real two-dimensional value walk loses one direction only at the two real
points of the half-period.  The following explicit estimates quantify that
loss.  Near either endpoint a fixed positive proportion of frequencies gives
a covariance lower bound quadratic in the endpoint distance.  Away from the
endpoints, the reflected Fourier modes have a uniformly bounded cross term.
-/

def endpointPairFrequency (n : ℕ) (r : Fin (n / 100)) : ℕ := n / 100 + r

def endpointPairIndex (n : ℕ) (r : Fin (n / 100)) (b : Bool) :
    Fin (2 * n + 1) := by
  let q := endpointPairFrequency n r
  have hdiv := Nat.div_mul_le_self n 100
  have hq : q < n := by
    dsimp [q, endpointPairFrequency]
    have hr := r.isLt
    omega
  exact if b then ⟨n + q, by omega⟩ else ⟨n - q, by omega⟩

lemma endpointPairFrequency_pos {n : ℕ} (hn : 100 ≤ n)
    (r : Fin (n / 100)) : 0 < endpointPairFrequency n r := by
  unfold endpointPairFrequency
  have : 0 < n / 100 := Nat.div_pos hn (by norm_num)
  omega

lemma endpointPairIndex_injective {n : ℕ} (hn : 100 ≤ n) :
    Function.Injective (fun p : Fin (n / 100) × Bool ↦
      endpointPairIndex n p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨r, b⟩
  rcases q with ⟨s, c⟩
  have hfR := endpointPairFrequency_pos hn r
  have hfS := endpointPairFrequency_pos hn s
  simp only [endpointPairIndex] at hpq
  split at hpq <;> split at hpq
  all_goals simp only [Fin.mk.injEq] at hpq
  · have : r.val = s.val := by
      simp only [endpointPairFrequency] at hpq
      omega
    apply Prod.ext
    · exact Fin.ext this
    · simp_all
  · simp only [endpointPairFrequency] at hpq
    omega
  · simp only [endpointPairFrequency] at hpq
    omega
  · have : r.val = s.val := by
      simp only [endpointPairFrequency] at hpq
      have hfr : endpointPairFrequency n r < n := by
        have hdiv := Nat.div_mul_le_self n 100
        have hr := r.isLt
        simp only [endpointPairFrequency]
        omega
      have hfs : endpointPairFrequency n s < n := by
        have hdiv := Nat.div_mul_le_self n 100
        have hs := s.isLt
        simp only [endpointPairFrequency]
        omega
      omega
    apply Prod.ext
    · exact Fin.ext this
    · simp_all

lemma centeredFrequency_endpointPairIndex_true (n : ℕ)
    (r : Fin (n / 100)) :
    centeredFrequency n (endpointPairIndex n r true) = endpointPairFrequency n r := by
  unfold centeredFrequency endpointPairIndex
  simp

lemma centeredFrequency_endpointPairIndex_false (n : ℕ)
    (r : Fin (n / 100)) :
    centeredFrequency n (endpointPairIndex n r false) = -endpointPairFrequency n r := by
  unfold centeredFrequency endpointPairIndex
  simp
  have hdiv := Nat.div_mul_le_self n 100
  have hr := r.isLt
  have hq : endpointPairFrequency n r ≤ n := by
    simp only [endpointPairFrequency]
    omega
  rw [Nat.cast_sub hq]
  push_cast
  ring

lemma endpoint_trig_pair_lower (a b x t : ℝ)
    (ht0 : 0 ≤ t) (ht10 : t ≤ 10)
    (hxl : t / 200 ≤ x) (hxu : x ≤ 1 / 2) :
    t ^ 2 / 500000 * (a ^ 2 + b ^ 2) ≤
      (a * Real.cos x + b * Real.sin x) ^ 2 +
        (a * Real.cos (-x) + b * Real.sin (-x)) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (div_nonneg ht0 (by norm_num)) hxl
  have hxabs : |x| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg hx0]
    exact hxu.trans (by nlinarith [Real.pi_gt_three])
  have hsinRaw := Real.mul_abs_le_abs_sin hxabs
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hsin : x / 2 ≤ |Real.sin x| := by
    rw [abs_of_nonneg hx0] at hsinRaw
    have hcoef : 1 / 2 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith
    calc
      x / 2 = (1 / 2) * x := by ring
      _ ≤ (2 / Real.pi) * x := mul_le_mul_of_nonneg_right hcoef hx0
      _ ≤ |Real.sin x| := hsinRaw
  have hsinSq : t ^ 2 / 160000 ≤ Real.sin x ^ 2 := by
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ t / 400)
      (abs_nonneg (Real.sin x)) |>.2 (by linarith)
    calc
      t ^ 2 / 160000 = (t / 400) ^ 2 := by ring
      _ ≤ |Real.sin x| ^ 2 := hsq
      _ = Real.sin x ^ 2 := sq_abs _
  have hsinUpper := Real.abs_sin_le_abs (x := x)
  rw [abs_of_nonneg hx0] at hsinUpper
  have hsinSqUpper : Real.sin x ^ 2 ≤ 1 / 4 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg (Real.sin x)) hx0).2 hsinUpper
    calc
      Real.sin x ^ 2 = |Real.sin x| ^ 2 := (sq_abs _).symm
      _ ≤ x ^ 2 := hsquare
      _ ≤ 1 / 4 := by nlinarith
  have hcosSq : 3 / 4 ≤ Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have htSq : t ^ 2 / 500000 ≤ 3 / 2 := by
    nlinarith [sq_nonneg t]
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg b
  rw [Real.cos_neg, Real.sin_neg]
  have hident :
      (a * Real.cos x + b * Real.sin x) ^ 2 +
          (a * Real.cos x + b * -Real.sin x) ^ 2 =
        2 * a ^ 2 * Real.cos x ^ 2 + 2 * b ^ 2 * Real.sin x ^ 2 := by ring
  rw [hident]
  have ha : t ^ 2 / 500000 * a ^ 2 ≤
      2 * a ^ 2 * Real.cos x ^ 2 := by
    have hc : t ^ 2 / 500000 ≤ 2 * Real.cos x ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc ha0]
  have hb : t ^ 2 / 500000 * b ^ 2 ≤
      2 * b ^ 2 * Real.sin x ^ 2 := by
    have hs : t ^ 2 / 500000 ≤ 2 * Real.sin x ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs hb0]
  calc
    t ^ 2 / 500000 * (a ^ 2 + b ^ 2) =
        t ^ 2 / 500000 * a ^ 2 + t ^ 2 / 500000 * b ^ 2 := by ring
    _ ≤ _ := add_le_add ha hb

lemma endpoint_pair_projection_lower
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10)
    (u : PositionCoordinate 1) (r : Fin (n / 100)) :
    t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
      phaseProjection n (fun _ : Fin 1 ↦ t) (positionPhaseEmbedding u)
          (endpointPairIndex n r true) ^ 2 +
        phaseProjection n (fun _ : Fin 1 ↦ t) (positionPhaseEmbedding u)
          (endpointPairIndex n r false) ^ 2 := by
  let q : ℝ := endpointPairFrequency n r
  let x : ℝ := q * t / n
  have hn0 : (0 : ℝ) < n := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hqLower : (n : ℝ) / 200 ≤ q := by
    have hfloor : (n : ℝ) / 100 - 1 < (n / 100 : ℕ) := by
      have h := Nat.sub_one_lt_floor ((n : ℝ) / 100)
      have heq : ⌊(n : ℝ) / 100⌋₊ = n / 100 :=
        Nat.floor_div_eq_div n 100
      rw [heq] at h
      simpa using h
    dsimp [q, endpointPairFrequency]
    push_cast
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hqUpper : q ≤ (n : ℝ) / 50 := by
    dsimp [q, endpointPairFrequency]
    have hr : (r : ℝ) < (n / 100 : ℕ) := by exact_mod_cast r.isLt
    have hdiv : ((n / 100 : ℕ) : ℝ) ≤ (n : ℝ) / 100 :=
      Nat.cast_div_le
    push_cast
    nlinarith
  have hxLower : t / 200 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hn0]
    have := mul_le_mul_of_nonneg_right hqLower ht0
    nlinarith
  have hxUpper : x ≤ 1 / 2 := by
    dsimp [x]
    rw [div_le_iff₀ hn0]
    have := mul_le_mul hqUpper ht10 ht0 (by positivity : 0 ≤ (n : ℝ) / 50)
    nlinarith
  have htrig := endpoint_trig_pair_lower (u 0 0) (u 0 1) x t
    ht0 ht10 hxLower hxUpper
  have hformula : ∀ j : Fin (2 * n + 1),
      phaseProjection n (fun _ : Fin 1 ↦ t) (positionPhaseEmbedding u) j =
        u 0 0 * Real.cos (centeredFrequency n j * (t / n)) +
          u 0 1 * Real.sin (centeredFrequency n j * (t / n)) := by
    intro j
    unfold phaseProjection phaseStep positionPhaseEmbedding
    rw [Fin.sum_univ_one, Fin.sum_univ_four]
    simp
  rw [hformula, hformula, centeredFrequency_endpointPairIndex_true,
    centeredFrequency_endpointPairIndex_false]
  dsimp [x, q] at htrig ⊢
  convert htrig using 1 <;> congr 3 <;> ring

lemma endpoint_position_norm_sq (u : PositionCoordinate 1) :
    ‖positionToEuclidean u‖ ^ 2 = u 0 0 ^ 2 + u 0 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold positionToEuclidean
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]

lemma endpoint_endpoint_energy_lower
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10)
    (u : PositionCoordinate 1) :
    (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
        ‖positionToEuclidean u‖ ^ 2 ≤
      ∑ j : Fin (2 * n + 1),
        phaseProjection n (fun _ : Fin 1 ↦ t)
          (positionPhaseEmbedding u) j ^ 2 := by
  let f : Fin (2 * n + 1) → ℝ := fun j ↦
    phaseProjection n (fun _ : Fin 1 ↦ t)
      (positionPhaseEmbedding u) j ^ 2
  let idx : Fin (n / 100) × Bool → Fin (2 * n + 1) := fun p ↦
    endpointPairIndex n p.1 p.2
  have hinj : Function.Injective idx := by
    exact endpointPairIndex_injective (by omega)
  have hsubset : (∑ p : Fin (n / 100) × Bool, f (idx p)) ≤
      ∑ j : Fin (2 * n + 1), f j := by
    rw [← Finset.sum_image (s := Finset.univ) (g := idx)
      (f := f) (fun _ _ _ _ h ↦ hinj h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro j _hj _hnot
      exact sq_nonneg _
  have hpair : ∀ r : Fin (n / 100),
      t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        f (idx (r, true)) + f (idx (r, false)) := by
    intro r
    exact endpoint_pair_projection_lower n hn t ht0 ht10 u r
  have hselected :
      ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) ≤
        ∑ p : Fin (n / 100) × Bool, f (idx p) := by
    rw [Fintype.sum_prod_type]
    have hs : ∑ _r : Fin (n / 100),
        (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) ≤
          ∑ r : Fin (n / 100),
            (f (idx (r, true)) + f (idx (r, false))) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact hpair r
    simpa [Fintype.univ_bool, add_comm] using hs
  rw [endpoint_position_norm_sq]
  change _ ≤ ∑ j : Fin (2 * n + 1), f j
  apply (show (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
      (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) by
    have hfloor : (n : ℝ) / 100 - 1 < (n / 100 : ℕ) := by
      have h := Nat.sub_one_lt_floor ((n : ℝ) / 100)
      have heq : ⌊(n : ℝ) / 100⌋₊ = n / 100 :=
        Nat.floor_div_eq_div n 100
      rw [heq] at h
      simpa using h
    have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoef : (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) ≤
        (n / 100 : ℕ) * (t ^ 2 / 500000) := by
      have htSq : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith
    have hnorm0 : 0 ≤ u 0 0 ^ 2 + u 0 1 ^ 2 := by positivity
    calc
      (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
          (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        (((n / 100 : ℕ) : ℝ) * (t ^ 2 / 500000)) *
          (u 0 0 ^ 2 + u 0 1 ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef hnorm0
      _ = ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) := by ring).trans
      (hselected.trans hsubset)

lemma endpoint_hasPositionCovarianceLower_near_zero
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10) :
    HasPositionCovarianceLower n (fun _ : Fin 1 ↦ t)
      (t ^ 2 / 1000000000) := by
  intro u
  exact endpoint_endpoint_energy_lower n hn t ht0 ht10 u

lemma endpoint_pair_projection_lower_near_pi
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10)
    (u : PositionCoordinate 1) (r : Fin (n / 100)) :
    t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
      phaseProjection n (fun _ : Fin 1 ↦ Real.pi * n - t)
          (positionPhaseEmbedding u) (endpointPairIndex n r true) ^ 2 +
        phaseProjection n (fun _ : Fin 1 ↦ Real.pi * n - t)
          (positionPhaseEmbedding u) (endpointPairIndex n r false) ^ 2 := by
  let qN : ℕ := endpointPairFrequency n r
  let q : ℝ := qN
  let x : ℝ := q * t / n
  have hn0 : (0 : ℝ) < n := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hqLower : (n : ℝ) / 200 ≤ q := by
    have hfloor : (n : ℝ) / 100 - 1 < (n / 100 : ℕ) := by
      have h := Nat.sub_one_lt_floor ((n : ℝ) / 100)
      have heq : ⌊(n : ℝ) / 100⌋₊ = n / 100 := Nat.floor_div_eq_div n 100
      rw [heq] at h
      simpa using h
    dsimp [q, qN, endpointPairFrequency]
    push_cast
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hqUpper : q ≤ (n : ℝ) / 50 := by
    dsimp [q, qN, endpointPairFrequency]
    have hr : (r : ℝ) < (n / 100 : ℕ) := by exact_mod_cast r.isLt
    have hdiv : ((n / 100 : ℕ) : ℝ) ≤ (n : ℝ) / 100 := Nat.cast_div_le
    push_cast
    nlinarith
  have hxLower : t / 200 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hn0]
    nlinarith [mul_le_mul_of_nonneg_right hqLower ht0]
  have hxUpper : x ≤ 1 / 2 := by
    dsimp [x]
    rw [div_le_iff₀ hn0]
    nlinarith [mul_le_mul hqUpper ht10 ht0
      (by positivity : 0 ≤ (n : ℝ) / 50)]
  have htrig := endpoint_trig_pair_lower (u 0 0) (-u 0 1) x t
    ht0 ht10 hxLower hxUpper
  have hformula : ∀ j : Fin (2 * n + 1),
      phaseProjection n (fun _ : Fin 1 ↦ Real.pi * n - t)
          (positionPhaseEmbedding u) j =
        u 0 0 * Real.cos (centeredFrequency n j *
            ((Real.pi * n - t) / n)) +
          u 0 1 * Real.sin (centeredFrequency n j *
            ((Real.pi * n - t) / n)) := by
    intro j
    unfold phaseProjection phaseStep positionPhaseEmbedding
    rw [Fin.sum_univ_one, Fin.sum_univ_four]
    simp
  rw [hformula, hformula, centeredFrequency_endpointPairIndex_true,
    centeredFrequency_endpointPairIndex_false]
  have harg : q * ((Real.pi * n - t) / n) = (qN : ℝ) * Real.pi - x := by
    dsimp [x, q]
    field_simp [hn0.ne']
  have hargNeg : -q * ((Real.pi * n - t) / n) =
      -((qN : ℝ) * Real.pi - x) := by
    calc
      -q * ((Real.pi * n - t) / n) =
          -(q * ((Real.pi * n - t) / n)) := by ring
      _ = -((qN : ℝ) * Real.pi - x) := congrArg Neg.neg harg
  rw [show (endpointPairFrequency n r : ℝ) = q by rfl,
    show -(endpointPairFrequency n r : ℝ) = -q by rfl,
    harg, hargNeg, Real.cos_neg, Real.sin_neg,
    Real.cos_nat_mul_pi_sub, Real.sin_nat_mul_pi_sub]
  dsimp [x, q] at htrig ⊢
  have hsign : ((-1 : ℝ) ^ (qN * 2)) = 1 := by
    rw [show qN * 2 = 2 * qN by omega, pow_mul]
    norm_num
  convert htrig using 1 <;> try ring
  rw [hsign]
  simp [Real.cos_neg, Real.sin_neg]
  ring

lemma endpoint_endpoint_energy_lower_near_pi
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10)
    (u : PositionCoordinate 1) :
    (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
        ‖positionToEuclidean u‖ ^ 2 ≤
      ∑ j : Fin (2 * n + 1),
        phaseProjection n (fun _ : Fin 1 ↦ Real.pi * n - t)
          (positionPhaseEmbedding u) j ^ 2 := by
  let f : Fin (2 * n + 1) → ℝ := fun j ↦
    phaseProjection n (fun _ : Fin 1 ↦ Real.pi * n - t)
      (positionPhaseEmbedding u) j ^ 2
  let idx : Fin (n / 100) × Bool → Fin (2 * n + 1) := fun p ↦
    endpointPairIndex n p.1 p.2
  have hinj : Function.Injective idx := endpointPairIndex_injective (by omega)
  have hsubset : (∑ p : Fin (n / 100) × Bool, f (idx p)) ≤
      ∑ j : Fin (2 * n + 1), f j := by
    rw [← Finset.sum_image (s := Finset.univ) (g := idx)
      (f := f) (fun _ _ _ _ h ↦ hinj h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro j _hj _hnot
      exact sq_nonneg _
  have hpair : ∀ r : Fin (n / 100),
      t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        f (idx (r, true)) + f (idx (r, false)) := by
    intro r
    exact endpoint_pair_projection_lower_near_pi n hn t ht0 ht10 u r
  have hselected :
      ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) ≤
        ∑ p : Fin (n / 100) × Bool, f (idx p) := by
    rw [Fintype.sum_prod_type]
    have hs : ∑ _r : Fin (n / 100),
        (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) ≤
          ∑ r : Fin (n / 100),
            (f (idx (r, true)) + f (idx (r, false))) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact hpair r
    simpa [Fintype.univ_bool, add_comm] using hs
  rw [endpoint_position_norm_sq]
  change _ ≤ ∑ j : Fin (2 * n + 1), f j
  apply (show (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
      (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) by
    have hfloor : (n : ℝ) / 100 - 1 < (n / 100 : ℕ) := by
      have h := Nat.sub_one_lt_floor ((n : ℝ) / 100)
      have heq : ⌊(n : ℝ) / 100⌋₊ = n / 100 := Nat.floor_div_eq_div n 100
      rw [heq] at h
      simpa using h
    have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoef : (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) ≤
        (n / 100 : ℕ) * (t ^ 2 / 500000) := by
      have htSq : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith
    have hnorm0 : 0 ≤ u 0 0 ^ 2 + u 0 1 ^ 2 := by positivity
    calc
      (t ^ 2 / 1000000000) * (2 * n + 1 : ℝ) *
          (u 0 0 ^ 2 + u 0 1 ^ 2) ≤
        (((n / 100 : ℕ) : ℝ) * (t ^ 2 / 500000)) *
          (u 0 0 ^ 2 + u 0 1 ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef hnorm0
      _ = ((n / 100 : ℕ) : ℝ) *
          (t ^ 2 / 500000 * (u 0 0 ^ 2 + u 0 1 ^ 2)) := by ring).trans
      (hselected.trans hsubset)

lemma endpoint_hasPositionCovarianceLower_near_pi
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht10 : t ≤ 10) :
    HasPositionCovarianceLower n
      (fun _ : Fin 1 ↦ Real.pi * n - t) (t ^ 2 / 1000000000) := by
  intro u
  exact endpoint_endpoint_energy_lower_near_pi n hn t ht0 ht10 u

lemma endpoint_position_energy_reflected_decomposition
    (n : ℕ) (hn : 0 < n) (t : ℝ) (u : PositionCoordinate 1) :
    (∑ j : Fin (2 * n + 1),
        phaseProjection n (fun _ : Fin 1 ↦ t)
          (positionPhaseEmbedding u) j ^ 2) =
      (2 * n + 1 : ℝ) / 2 * ‖positionToEuclidean u‖ ^ 2 +
        (centeredAffineCrossMoment n (-t) t
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re +
        (centeredAffineCrossMoment n t (-t)
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re := by
  rw [phaseProjection_energy_eq_reflectedCross]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [Fintype.univ_bool, reflectedModeTime, reflectedPositionCoeff,
    reflectedVelocityCoeff, phaseVelocityCoeff_positionPhaseEmbedding,
    centeredAffineCrossMoment_self_re n hn, endpoint_position_norm_sq,
    phasePositionCoeff, positionPhaseEmbedding, Complex.normSq_apply]
  ring

lemma endpoint_chord_two_mul_lower (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht0 : 0 ≤ t) (hthalf : t ≤ Real.pi * n / 2) :
    4 * (t / (Real.pi * n)) ≤
      ‖complexWave n (2 * t) 1 - 1‖ := by
  rw [complexWave_eq_circleExp n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio0 : 0 ≤ t / (Real.pi * n) := by positivity
  have hratioHalf : t / (Real.pi * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (mul_pos Real.pi_pos hnR)]
    nlinarith
  have hfour := four_mul_distanceToInteger_le_norm_circleExp_sub_one
    (t / (Real.pi * n))
  rw [distanceToInteger_eq_self_of_nonneg_le_half hratio0 hratioHalf] at hfour
  convert hfour using 1 <;> congr 3 <;> field_simp [hnR.ne', Real.pi_ne_zero] <;> ring

lemma endpoint_phasePositionCoeff_norm_sq (u : PositionCoordinate 1) :
    ‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ ^ 2 =
      ‖positionToEuclidean u‖ ^ 2 := by
  rw [endpoint_position_norm_sq]
  simp [phasePositionCoeff, positionPhaseEmbedding, Complex.normSq_apply,
    Complex.sq_norm]
  ring

lemma endpoint_position_cross_re_abs_le
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hthalf : t ≤ Real.pi * n / 2) (u : PositionCoordinate 1) :
    |(centeredAffineCrossMoment n (-t) t
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re| ≤
      (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
  let delta : ℝ := 4 * (t / (Real.pi * n))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hchord : delta ≤ ‖complexWave n (2 * t) 1 - 1‖ := by
    simpa [delta] using endpoint_chord_two_mul_lower n hn t ht.le hthalf
  have hmom : ∀ k : Fin 3,
      ‖centeredWaveMoment n k (t - -t)‖ ≤ 6 / delta := by
    intro k
    convert norm_centeredWaveMoment_le n k hn (by omega) (2 * t)
      delta hdelta hchord using 1 <;> ring
  have hnorm := norm_centeredAffineCrossMoment_le n (-t) t
    (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
    (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
    (6 / delta) (by positivity) hmom
  have hre := Complex.abs_re_le_norm
    (centeredAffineCrossMoment n (-t) t
      (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
      (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0)
  calc
    _ ≤ ‖centeredAffineCrossMoment n (-t) t
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0‖ := hre
    _ ≤ (6 / delta) *
        (‖phasePositionCoeff (positionPhaseEmbedding u) 0 / 2‖ + ‖0‖) *
        (‖conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2‖ + ‖0‖) := hnorm
    _ = (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
      rw [norm_div, norm_div, Complex.norm_conj]
      simp only [norm_zero, add_zero]
      norm_num [Complex.norm_real]
      rw [show
          (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) =
            (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ ^ 2 / 4) by ring,
        endpoint_phasePositionCoeff_norm_sq]
      dsimp [delta]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [ht.ne', hnR.ne', Real.pi_ne_zero]
      ring

lemma endpoint_position_cross_re_abs_le_reverse
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hthalf : t ≤ Real.pi * n / 2) (u : PositionCoordinate 1) :
    |(centeredAffineCrossMoment n t (-t)
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re| ≤
      (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
  let delta : ℝ := 4 * (t / (Real.pi * n))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hchord : delta ≤ ‖complexWave n (-2 * t) 1 - 1‖ := by
    have hp : delta ≤ ‖complexWave n (2 * t) 1 - 1‖ := by
      simpa [delta] using endpoint_chord_two_mul_lower n hn t ht.le hthalf
    calc
      delta ≤ ‖complexWave n (2 * t) 1 - 1‖ := hp
      _ = ‖conj (complexWave n (2 * t) 1 - 1)‖ :=
        (Complex.norm_conj _).symm
      _ = ‖complexWave n (-2 * t) 1 - 1‖ := by
        congr 2
        simp [map_sub, conj_complexWave]
  have hmom : ∀ k : Fin 3,
      ‖centeredWaveMoment n k (-t - t)‖ ≤ 6 / delta := by
    intro k
    convert norm_centeredWaveMoment_le n k hn (by omega) (-2 * t)
      delta hdelta hchord using 1 <;> ring
  have hnorm := norm_centeredAffineCrossMoment_le n t (-t)
    (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
    (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
    (6 / delta) (by positivity) hmom
  have hre := Complex.abs_re_le_norm
    (centeredAffineCrossMoment n t (-t)
      (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
      (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0)
  calc
    _ ≤ ‖centeredAffineCrossMoment n t (-t)
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0‖ := hre
    _ ≤ (6 / delta) *
        (‖conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2‖ + ‖0‖) *
        (‖phasePositionCoeff (positionPhaseEmbedding u) 0 / 2‖ + ‖0‖) := hnorm
    _ = (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
      rw [norm_div, norm_div, Complex.norm_conj]
      simp only [norm_zero, add_zero]
      norm_num [Complex.norm_real]
      rw [show
          (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) =
            (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ ^ 2 / 4) by ring,
        endpoint_phasePositionCoeff_norm_sq]
      dsimp [delta]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [ht.ne', hnR.ne', Real.pi_ne_zero]
      ring

lemma endpoint_hasPositionCovarianceLower_far_zero
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht : 10 ≤ t)
    (hthalf : t ≤ Real.pi * n / 2) :
    HasPositionCovarianceLower n (fun _ : Fin 1 ↦ t) (1 / 10) := by
  intro u
  have hnpos : 0 < n := by omega
  have htpos : 0 < t := by linarith
  have hforward := endpoint_position_cross_re_abs_le n hnpos t htpos hthalf u
  have hreverse := endpoint_position_cross_re_abs_le_reverse n hnpos t htpos hthalf u
  have hforwardLower :
      -(3 * Real.pi * n / (8 * t) * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (-t) t
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re :=
    neg_le_of_abs_le hforward
  have hreverseLower :
      -(3 * Real.pi * n / (8 * t) * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n t (-t)
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re :=
    neg_le_of_abs_le hreverse
  have hC : 3 * Real.pi * (n : ℝ) / (8 * t) ≤ 3 * n / 20 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * t)]
    have hpi := Real.pi_le_four
    nlinarith
  have hnorm : 0 ≤ ‖positionToEuclidean u‖ ^ 2 := sq_nonneg _
  have hforwardLower' :
      -(3 * (n : ℝ) / 20 * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (-t) t
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re := by
    exact (neg_le_neg (mul_le_mul_of_nonneg_right hC hnorm)).trans hforwardLower
  have hreverseLower' :
      -(3 * (n : ℝ) / 20 * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n t (-t)
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re := by
    exact (neg_le_neg (mul_le_mul_of_nonneg_right hC hnorm)).trans hreverseLower
  rw [endpoint_position_energy_reflected_decomposition n hnpos t u]
  have hnR : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma endpoint_chord_near_pi_forward
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t)
    (hthalf : t ≤ Real.pi * n / 2) :
    4 * (t / (Real.pi * n)) ≤
      ‖complexWave n (2 * (Real.pi * n - t)) 1 - 1‖ := by
  have hbase := endpoint_chord_two_mul_lower n hn t ht0 hthalf
  calc
    4 * (t / (Real.pi * n)) ≤ ‖complexWave n (2 * t) 1 - 1‖ := hbase
    _ = ‖conj (complexWave n (2 * t) 1 - 1)‖ :=
      (Complex.norm_conj _).symm
    _ = ‖complexWave n (-2 * t) 1 - 1‖ := by
      congr 2
      simp [map_sub, conj_complexWave]
    _ = ‖complexWave n (2 * (Real.pi * n - t)) 1 - 1‖ := by
      congr 2
      rw [show 2 * (Real.pi * n - t) = -2 * t + 2 * Real.pi * n by ring,
        complexWave_add_period]

lemma endpoint_chord_near_pi_reverse
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t)
    (hthalf : t ≤ Real.pi * n / 2) :
    4 * (t / (Real.pi * n)) ≤
      ‖complexWave n (-2 * (Real.pi * n - t)) 1 - 1‖ := by
  have hbase := endpoint_chord_two_mul_lower n hn t ht0 hthalf
  calc
    4 * (t / (Real.pi * n)) ≤ ‖complexWave n (2 * t) 1 - 1‖ := hbase
    _ = ‖complexWave n (-2 * (Real.pi * n - t)) 1 - 1‖ := by
      congr 2
      have hperiod := complexWave_add_period n
        (2 * t - 2 * Real.pi * n) (1 : ℤ)
      rw [show (2 * t - 2 * Real.pi * n) + 2 * Real.pi * n = 2 * t by ring]
        at hperiod
      rw [show -2 * (Real.pi * n - t) = 2 * t - 2 * Real.pi * n by ring]
      exact hperiod

lemma endpoint_position_cross_re_abs_le_near_pi
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hthalf : t ≤ Real.pi * n / 2) (u : PositionCoordinate 1) :
    |(centeredAffineCrossMoment n (-(Real.pi * n - t)) (Real.pi * n - t)
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re| ≤
      (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
  let delta : ℝ := 4 * (t / (Real.pi * n))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hchord : delta ≤
      ‖complexWave n (2 * (Real.pi * n - t)) 1 - 1‖ := by
    simpa [delta] using endpoint_chord_near_pi_forward n hn t ht.le hthalf
  have hmom : ∀ k : Fin 3,
      ‖centeredWaveMoment n k
          ((Real.pi * n - t) - -(Real.pi * n - t))‖ ≤ 6 / delta := by
    intro k
    convert norm_centeredWaveMoment_le n k hn (by omega)
      (2 * (Real.pi * n - t)) delta hdelta hchord using 1 <;> ring
  have hnorm := norm_centeredAffineCrossMoment_le n (-(Real.pi * n - t))
    (Real.pi * n - t)
    (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
    (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
    (6 / delta) (by positivity) hmom
  have hre := Complex.abs_re_le_norm
    (centeredAffineCrossMoment n (-(Real.pi * n - t)) (Real.pi * n - t)
      (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
      (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0)
  calc
    _ ≤ ‖centeredAffineCrossMoment n (-(Real.pi * n - t))
        (Real.pi * n - t)
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0‖ := hre
    _ ≤ (6 / delta) *
        (‖phasePositionCoeff (positionPhaseEmbedding u) 0 / 2‖ + ‖0‖) *
        (‖conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2‖ + ‖0‖) := hnorm
    _ = (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
      rw [norm_div, norm_div, Complex.norm_conj]
      simp only [norm_zero, add_zero]
      norm_num [Complex.norm_real]
      rw [show
          (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) =
            (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ ^ 2 / 4) by ring,
        endpoint_phasePositionCoeff_norm_sq]
      dsimp [delta]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [ht.ne', hnR.ne', Real.pi_ne_zero]
      ring

lemma endpoint_position_cross_re_abs_le_reverse_near_pi
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hthalf : t ≤ Real.pi * n / 2) (u : PositionCoordinate 1) :
    |(centeredAffineCrossMoment n (Real.pi * n - t) (-(Real.pi * n - t))
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re| ≤
      (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
  let delta : ℝ := 4 * (t / (Real.pi * n))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hchord : delta ≤
      ‖complexWave n (-2 * (Real.pi * n - t)) 1 - 1‖ := by
    simpa [delta] using endpoint_chord_near_pi_reverse n hn t ht.le hthalf
  have hmom : ∀ k : Fin 3,
      ‖centeredWaveMoment n k
          (-(Real.pi * n - t) - (Real.pi * n - t))‖ ≤ 6 / delta := by
    intro k
    convert norm_centeredWaveMoment_le n k hn (by omega)
      (-2 * (Real.pi * n - t)) delta hdelta hchord using 1 <;> ring
  have hnorm := norm_centeredAffineCrossMoment_le n (Real.pi * n - t)
    (-(Real.pi * n - t))
    (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
    (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
    (6 / delta) (by positivity) hmom
  have hre := Complex.abs_re_le_norm
    (centeredAffineCrossMoment n (Real.pi * n - t) (-(Real.pi * n - t))
      (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
      (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0)
  calc
    _ ≤ ‖centeredAffineCrossMoment n (Real.pi * n - t)
        (-(Real.pi * n - t))
        (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
        (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0‖ := hre
    _ ≤ (6 / delta) *
        (‖conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2‖ + ‖0‖) *
        (‖phasePositionCoeff (positionPhaseEmbedding u) 0 / 2‖ + ‖0‖) := hnorm
    _ = (3 * Real.pi * n / (8 * t)) * ‖positionToEuclidean u‖ ^ 2 := by
      rw [norm_div, norm_div, Complex.norm_conj]
      simp only [norm_zero, add_zero]
      norm_num [Complex.norm_real]
      rw [show
          (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ / 2) =
            (6 / delta) *
              (‖phasePositionCoeff (positionPhaseEmbedding u) 0‖ ^ 2 / 4) by ring,
        endpoint_phasePositionCoeff_norm_sq]
      dsimp [delta]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [ht.ne', hnR.ne', Real.pi_ne_zero]
      ring

lemma endpoint_hasPositionCovarianceLower_far_pi
    (n : ℕ) (hn : 1000 ≤ n) (t : ℝ) (ht : 10 ≤ t)
    (hthalf : t ≤ Real.pi * n / 2) :
    HasPositionCovarianceLower n
      (fun _ : Fin 1 ↦ Real.pi * n - t) (1 / 10) := by
  intro u
  have hnpos : 0 < n := by omega
  have htpos : 0 < t := by linarith
  have hforward := endpoint_position_cross_re_abs_le_near_pi
    n hnpos t htpos hthalf u
  have hreverse := endpoint_position_cross_re_abs_le_reverse_near_pi
    n hnpos t htpos hthalf u
  have hforwardLower :
      -(3 * Real.pi * n / (8 * t) * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (-(Real.pi * n - t))
          (Real.pi * n - t)
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re :=
    neg_le_of_abs_le hforward
  have hreverseLower :
      -(3 * Real.pi * n / (8 * t) * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (Real.pi * n - t)
          (-(Real.pi * n - t))
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re :=
    neg_le_of_abs_le hreverse
  have hC : 3 * Real.pi * (n : ℝ) / (8 * t) ≤ 3 * n / 20 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * t)]
    have hpi := Real.pi_le_four
    nlinarith
  have hnorm : 0 ≤ ‖positionToEuclidean u‖ ^ 2 := sq_nonneg _
  have hforwardLower' :
      -(3 * (n : ℝ) / 20 * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (-(Real.pi * n - t))
          (Real.pi * n - t)
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0).re := by
    exact (neg_le_neg (mul_le_mul_of_nonneg_right hC hnorm)).trans hforwardLower
  have hreverseLower' :
      -(3 * (n : ℝ) / 20 * ‖positionToEuclidean u‖ ^ 2) ≤
        (centeredAffineCrossMoment n (Real.pi * n - t)
          (-(Real.pi * n - t))
          (conj (phasePositionCoeff (positionPhaseEmbedding u) 0) / 2) 0
          (phasePositionCoeff (positionPhaseEmbedding u) 0 / 2) 0).re := by
    exact (neg_le_neg (mul_le_mul_of_nonneg_right hC hnorm)).trans hreverseLower
  rw [endpoint_position_energy_reflected_decomposition n hnpos
    (Real.pi * n - t) u]
  have hnR : (0 : ℝ) ≤ n := by positivity
  nlinarith


end Erdos525

