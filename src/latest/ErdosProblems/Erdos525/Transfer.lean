import ErdosProblems.Erdos525.Position

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory
open Asymptotics

lemma rescaledCenteredEval_neg (n : ℕ) (e : SignVector (2 * n)) (t : ℝ) :
    rescaledCenteredEval n e (-t) = conj (rescaledCenteredEval n e t) := by
  unfold rescaledCenteredEval centeredEval
  rw [map_mul]
  congr 1
  · simp
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    congr 1
    · simp
    · rw [← Complex.exp_conj]
      congr 1
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

@[simp] lemma norm_rescaledCenteredEval_neg
    (n : ℕ) (e : SignVector (2 * n)) (t : ℝ) :
    ‖rescaledCenteredEval n e (-t)‖ = ‖rescaledCenteredEval n e t‖ := by
  rw [rescaledCenteredEval_neg, Complex.norm_conj]

lemma rescaledCenteredEval_nat_mul
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n)) (x : ℝ) :
    rescaledCenteredEval n e (n * x) = centeredEval n e x := by
  unfold rescaledCenteredEval
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 1
  field_simp

lemma exists_halfPeriod_centeredMin
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n)) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
      ‖rescaledCenteredEval n e t‖ = centeredMin n e := by
  rcases centeredMin_mem_range n e with ⟨x, hx, hmin⟩
  let t : ℝ := n * |x|
  refine ⟨t, ?_, ?_⟩
  · constructor
    · exact mul_nonneg (Nat.cast_nonneg n) (abs_nonneg x)
    · have habs : |x| ≤ Real.pi := by
        rw [abs_le]
        exact hx
      dsimp [t]
      nlinarith [show (0 : ℝ) < n by exact_mod_cast hn]
  · rw [show t = n * |x| by rfl, rescaledCenteredEval_nat_mul n hn]
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      exact hmin
    · have hxneg : x < 0 := lt_of_not_ge hx0
      rw [abs_of_neg hxneg]
      have hsym := norm_rescaledCenteredEval_neg n e (n * x)
      rw [rescaledCenteredEval_nat_mul n hn,
        show -(n * x : ℝ) = n * -x by ring,
        rescaledCenteredEval_nat_mul n hn] at hsym
      rw [hsym]
      exact hmin

noncomputable def centeredEnergy
    (n : ℕ) (e : SignVector (2 * n)) (t : ℝ) : ℝ :=
  ‖rescaledCenteredEval n e t‖ ^ 2

lemma hasDerivAt_centeredEnergy
    (n : ℕ) (e : SignVector (2 * n)) (t : ℝ) :
    HasDerivAt (centeredEnergy n e)
      (2 * (rescaledCenteredEval n e t *
        conj (rescaledCenteredVelocity n e t)).re) t := by
  have h := (hasDerivAt_rescaledCenteredEval n e t).norm_sq
  change HasDerivAt (fun s ↦ ‖rescaledCenteredEval n e s‖ ^ 2) _ t
  convert h using 1
  simp [Complex.inner, Complex.mul_re]
  ring

lemma exists_halfPeriod_centeredMin_orthogonal
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n)) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
      ‖rescaledCenteredEval n e t‖ = centeredMin n e ∧
      (rescaledCenteredEval n e t *
        conj (rescaledCenteredVelocity n e t)).re = 0 := by
  rcases exists_halfPeriod_centeredMin n hn e with ⟨t, ht, hmin⟩
  have hlocal : IsLocalMin (centeredEnergy n e) t := by
    change ∀ᶠ s in 𝓝 t, centeredEnergy n e t ≤ centeredEnergy n e s
    exact Eventually.of_forall fun s ↦ by
      have hle := centeredMin_le_rescaledCenteredEval n e s
      have hnonneg : 0 ≤ centeredMin n e := by
        rw [← hmin]
        exact norm_nonneg _
      unfold centeredEnergy
      rw [hmin]
      exact pow_le_pow_left₀ hnonneg hle 2
  have hzero : deriv (centeredEnergy n e) t = 0 :=
    hlocal.deriv_eq_zero
  have hderiv := (hasDerivAt_centeredEnergy n e t).deriv
  refine ⟨t, ht, hmin, ?_⟩
  rw [hzero] at hderiv
  linarith

lemma IsSmooth.halfPeriod_endpoint_separation
    {n : ℕ} (hn : 0 < n) {K t : ℝ}
    (hsmooth : IsSmooth n K t)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    Real.pi * K < t ∧ t < Real.pi * n - Real.pi * K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hdist := hsmooth 1 (by omega) (by omega)
  norm_num only [Nat.cast_one, one_mul] at hdist
  have hzero := distanceToInteger_minimal
    (t / (Real.pi * n)) (0 : ℤ)
  have hone := distanceToInteger_minimal
    (t / (Real.pi * n)) (1 : ℤ)
  have hratio0 : 0 ≤ t / (Real.pi * n) := div_nonneg ht.1 hpiN.le
  have hratio1 : t / (Real.pi * n) ≤ 1 :=
    (div_le_one hpiN).2 ht.2
  constructor
  · have hlt : K / n < t / (Real.pi * n) := by
      exact hdist.trans_le (by simpa [abs_of_nonneg hratio0] using hzero)
    field_simp [hnR.ne', Real.pi_ne_zero] at hlt
    nlinarith [Real.pi_pos]
  · have habs : |t / (Real.pi * n) - 1| =
        1 - t / (Real.pi * n) := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hlt : K / n < 1 - t / (Real.pi * n) := by
      exact hdist.trans_le (by simpa [habs] using hone)
    have hscaled := (mul_lt_mul_of_pos_right hlt hnR)
    have hquot : (1 - t / (Real.pi * n)) * n =
        n - t / Real.pi := by
      field_simp [hnR.ne', Real.pi_ne_zero]
    rw [hquot] at hscaled
    have hpi := mul_lt_mul_of_pos_left hscaled Real.pi_pos
    field_simp [Real.pi_ne_zero] at hpi
    nlinarith

lemma mem_halfLocalMeshSites_iff
    (n : ℕ) (a : Fin (localMeshSize n)) :
    a ∈ halfLocalMeshSites n ↔
      localMeshSize n - halfLocalMeshSize n ≤ a.val := by
  classical
  constructor
  · intro ha
    rw [halfLocalMeshSites] at ha
    rcases Finset.mem_image.mp ha with ⟨b, _hb, rfl⟩
    simp [halfLocalMeshIndex]
  · intro ha
    rw [halfLocalMeshSites]
    let bval := a.val - (localMeshSize n - halfLocalMeshSize n)
    have hhalf : halfLocalMeshSize n ≤ localMeshSize n := Nat.div_le_self _ _
    have hbval : bval < halfLocalMeshSize n := by
      dsimp [bval]
      omega
    let b : Fin (halfLocalMeshSize n) := ⟨bval, hbval⟩
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change localMeshSize n - halfLocalMeshSize n + bval = a.val
    dsimp [bval]
    omega

lemma mem_halfLocalMeshSites_of_point_nonneg
    (n : ℕ) (hn : 0 < n) (a : Fin (localMeshSize n))
    (ha : 0 ≤ localMeshPoint n a) :
    a ∈ halfLocalMeshSites n := by
  rw [mem_halfLocalMeshSites_iff]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < localMeshSize n := by
    exact_mod_cast localMeshSize_pos n
  have hfactor : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hrewrite : localMeshPoint n a =
      Real.pi * n * (2 * (a : ℝ) / localMeshSize n - 1) := by
    unfold localMeshPoint
    ring
  rw [hrewrite] at ha
  have hratio : 0 ≤ 2 * (a : ℝ) / localMeshSize n - 1 := by
    by_contra hnot
    have hneg : 2 * (a : ℝ) / localMeshSize n - 1 < 0 :=
      lt_of_not_ge hnot
    have := mul_neg_of_pos_of_neg hfactor hneg
    linarith
  have hcast : (localMeshSize n : ℝ) ≤ 2 * (a : ℝ) := by
    rw [sub_nonneg, le_div_iff₀ hM] at hratio
    simpa using hratio
  have hnat : localMeshSize n ≤ 2 * a.val := by exact_mod_cast hcast
  unfold halfLocalMeshSize
  omega

lemma exists_halfLocalMeshSite_within_halfWidth
    (n : ℕ) (hn : 0 < n) (K t : ℝ)
    (hKwidth : 2 * localMeshHalfWidth n < Real.pi * K)
    (hsmooth : IsSmooth n K t)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    ∃ a : Fin (localMeshSize n),
      a ∈ halfLocalMeshSites n ∧
      |t - localMeshPoint n a| ≤ localMeshHalfWidth n := by
  have hsep := hsmooth.halfPeriod_endpoint_separation hn ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalfNonneg : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hpiK : 0 < Real.pi * K :=
    (mul_nonneg (by norm_num) hhalfNonneg).trans_lt hKwidth
  have htIco : t ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(by nlinarith [Real.pi_pos]),
      hsep.2.trans_le (sub_le_self _ hpiK.le)⟩
  rcases exists_localMeshPoint_within_step n hn t htIco with
    ⟨a, hdiff0, hdiff⟩
  let x := localMeshPoint n a
  let h := localMeshHalfWidth n
  have hxpos : 0 < x := by
    dsimp [x]
    linarith
  have haHalf : a ∈ halfLocalMeshSites n :=
    mem_halfLocalMeshSites_of_point_nonneg n hn a hxpos.le
  by_cases hnear : t - x ≤ h
  · refine ⟨a, haHalf, ?_⟩
    rw [abs_of_nonneg]
    · exact hnear
    · simpa [x] using hdiff0
  · have hhalfPos : 0 < h := by
      dsimp [h]
      unfold localMeshHalfWidth
      exact div_pos (mul_pos Real.pi_pos hnR)
        (by exact_mod_cast localMeshSize_pos n)
    have hsucc : a.val + 1 < localMeshSize n := by
      by_contra hnot
      have halast : a.val + 1 = localMeshSize n := by omega
      have hxlast : x = Real.pi * n - 2 * h := by
        have halastR : (a.val : ℝ) + 1 = (localMeshSize n : ℝ) := by
          exact_mod_cast halast
        have haR : (a : ℝ) = (localMeshSize n : ℝ) - 1 := by
          change (a.val : ℝ) = (localMeshSize n : ℝ) - 1
          linarith
        dsimp [x, h]
        unfold localMeshPoint localMeshHalfWidth
        have hM0 : (localMeshSize n : ℝ) ≠ 0 := by
          exact_mod_cast (localMeshSize_pos n).ne'
        rw [haR]
        field_simp [hM0]
        ring
      have hupperGap : t < Real.pi * n - 2 * h := by linarith
      linarith
    let b : Fin (localMeshSize n) := ⟨a.val + 1, hsucc⟩
    have hbpoint : localMeshPoint n b = x + 2 * h := by
      have hsub := localMeshPoint_sub_eq_two_halfWidth_of_succ n a b (by
        change a.val + 1 = a.val + 1
        rfl)
      dsimp [x, h]
      linarith
    have hbpos : 0 ≤ localMeshPoint n b := by
      rw [hbpoint]
      exact add_nonneg hxpos.le (mul_nonneg (by norm_num) hhalfPos.le)
    have hbHalf : b ∈ halfLocalMeshSites n :=
      mem_halfLocalMeshSites_of_point_nonneg n hn b hbpos
    refine ⟨b, hbHalf, ?_⟩
    rw [hbpoint]
    have hdpos : 0 ≤ x + 2 * h - t := by
      have : h < t - x := lt_of_not_ge hnear
      linarith
    rw [abs_sub_comm, abs_of_nonneg hdpos]
    linarith

noncomputable def minimumAffineOffsetError
    (n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  globalAccelerationBound n * localMeshHalfWidth n *
      (u / n + localMeshHalfWidth n * velocityUpper) /
    velocityLower ^ 2

lemma localAffineOffset_sub_minimizer_le
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighMeshAcceleration n e)
    (u velocityLower velocityUpper t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hmin : ‖rescaledCenteredEval n e t‖ ≤ u / n)
    (hortho : (rescaledCenteredEval n e t *
      conj (rescaledCenteredVelocity n e t)).re = 0)
    (a : Fin (localMeshSize n))
    (haHalf : a ∈ halfLocalMeshSites n)
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖)
    (haUpper : ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤
      velocityUpper) :
    |localAffineOffset n e a - (t - localMeshPoint n a)| ≤
      minimumAffineOffsetError n u velocityLower velocityUpper := by
  let x := localMeshPoint n a
  let d := t - x
  let A := rescaledCenteredEval n e x
  let B := rescaledCenteredVelocity n e x
  let P := rescaledCenteredEval n e t
  let V := rescaledCenteredVelocity n e t
  let R := P - (A + (d : ℂ) * B)
  let C := globalAccelerationBound n
  let h := localMeshHalfWidth n
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    dsimp [x]
    have hxIco := localMeshPoint_mem_Ico n hn a
    exact ⟨hxIco.1, hxIco.2.le⟩
  have htFull : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans ht.1, ht.2⟩
  have hC0 : 0 ≤ C := by
    dsimp [C, globalAccelerationBound]
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by
        unfold localMeshHalfWidth
        positivity))
  have hh0 : 0 ≤ h := by
    dsimp [h, localMeshHalfWidth]
    positivity
  have hd : |d| ≤ h := by simpa [d, x] using haNear
  have hR : ‖R‖ ≤ C * h ^ 2 := by
    have hraw := norm_rescaledCenteredEval_sub_linear_le_of_not_high
      n hn e hgood x t hx htFull
    have hsq : (t - x) ^ 2 ≤ h ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg d) hd 2
      simpa [d, sq_abs] using this
    calc
      ‖R‖ ≤ C * (t - x) ^ 2 := by simpa [R, P, A, d, B] using hraw
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_left hsq hC0
  have hVB : ‖V - B‖ ≤ C * h := by
    have hraw := norm_rescaledCenteredVelocity_sub_le_of_not_high
      n hn e hgood x t hx htFull
    calc
      ‖V - B‖ = ‖rescaledCenteredVelocity n e t -
          rescaledCenteredVelocity n e x‖ := by rfl
      _ ≤ C * |t - x| := by simpa [C] using hraw
      _ ≤ C * h := mul_le_mul_of_nonneg_left (by simpa [d] using hd) hC0
  have hB0 : B ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le (by simpa [B, x] using haLower)).ne'
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hPB : |(P * conj B).re| ≤ (u / n) * (C * h) := by
    have hid : (P * conj B).re = (P * conj (B - V)).re := by
      have hcomplex : P * conj B =
          P * conj V + P * conj (B - V) := by
        rw [← mul_add, ← map_add]
        congr 2
        ring
      rw [hcomplex, Complex.add_re,
        show (P * conj V).re = 0 by simpa [P, V] using hortho, zero_add]
    rw [hid]
    calc
      |(P * conj (B - V)).re| ≤ ‖P * conj (B - V)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖P‖ * ‖V - B‖ := by
        rw [norm_mul, Complex.norm_conj, norm_sub_rev]
      _ ≤ (u / n) * (C * h) := by
        exact mul_le_mul (by simpa [P] using hmin) hVB
          (norm_nonneg _) (by
            have := (norm_nonneg P).trans (by simpa [P] using hmin)
            exact this)
  have hRB : |(R * conj B).re| ≤ (C * h ^ 2) * velocityUpper := by
    calc
      |(R * conj B).re| ≤ ‖R * conj B‖ := Complex.abs_re_le_norm _
      _ = ‖R‖ * ‖B‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ (C * h ^ 2) * velocityUpper := by
        exact mul_le_mul hR (by simpa [B, x] using haUpper)
          (norm_nonneg _) (mul_nonneg hC0 (sq_nonneg h))
  have hnum : |((A + (d : ℂ) * B) * conj B).re| ≤
      C * h * (u / n + h * velocityUpper) := by
    have hid : ((A + (d : ℂ) * B) * conj B).re =
        (P * conj B).re - (R * conj B).re := by
      have hP : P = A + (d : ℂ) * B + R := by
        dsimp [R]
        ring
      have hcomplex : (A + (d : ℂ) * B) * conj B =
          P * conj B - R * conj B := by
        rw [hP]
        ring
      exact congrArg Complex.re hcomplex
    rw [hid]
    calc
      |(P * conj B).re - (R * conj B).re| ≤
          |(P * conj B).re| + |(R * conj B).re| := abs_sub _ _
      _ ≤ (u / n) * (C * h) + (C * h ^ 2) * velocityUpper :=
        add_le_add hPB hRB
      _ = C * h * (u / n + h * velocityUpper) := by ring
  have hoff : localAffineOffset n e a - d =
      -(((A + (d : ℂ) * B) * conj B).re) / Complex.normSq B := by
    change -(A * conj B).re / Complex.normSq B - d = _
    have hreal : (((d : ℂ) * B) * conj B).re =
        d * Complex.normSq B := by
      rw [mul_assoc, Complex.mul_conj]
      simp
    rw [add_mul, Complex.add_re, hreal]
    have hnormSq0 : Complex.normSq B ≠ 0 := by
      exact fun hz ↦ hB0 (Complex.normSq_eq_zero.mp hz)
    field_simp [hnormSq0]
    ring
  rw [hoff, abs_div, abs_neg,
    abs_of_nonneg (Complex.normSq_nonneg B), Complex.normSq_eq_norm_sq]
  have hden : velocityLower ^ 2 ≤ ‖B‖ ^ 2 := by
    exact pow_le_pow_left₀ hvelocityLower.le (by simpa [B, x] using haLower) 2
  have hdenPos : 0 < ‖B‖ ^ 2 := sq_pos_of_pos hBpos
  calc
    |((A + (d : ℂ) * B) * conj B).re| / ‖B‖ ^ 2 ≤
        (C * h * (u / n + h * velocityUpper)) / ‖B‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (C * h * (u / n + h * velocityUpper)) /
        velocityLower ^ 2 := by
      apply div_le_div_of_nonneg_left
      · exact (abs_nonneg _).trans hnum
      · exact sq_pos_of_pos hvelocityLower
      · exact hden
    _ = minimumAffineOffsetError n u velocityLower velocityUpper := by
      rfl

lemma abs_localSignedHeight_le_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighMeshAcceleration n e)
    (u velocityLower t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hmin : ‖rescaledCenteredEval n e t‖ ≤ u / n)
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖) :
    |localSignedHeight n e a| ≤
      u + n * globalAccelerationBound n * localMeshHalfWidth n ^ 2 := by
  let x := localMeshPoint n a
  let d := t - x
  let A := rescaledCenteredEval n e x
  let B := rescaledCenteredVelocity n e x
  let P := rescaledCenteredEval n e t
  let C := globalAccelerationBound n
  let h := localMeshHalfWidth n
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    dsimp [x]
    have hxIco := localMeshPoint_mem_Ico n hn a
    exact ⟨hxIco.1, hxIco.2.le⟩
  have htFull : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans ht.1, ht.2⟩
  have hC0 : 0 ≤ C := by
    dsimp [C, globalAccelerationBound]
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by
        unfold localMeshHalfWidth
        positivity))
  have hh0 : 0 ≤ h := by
    dsimp [h, localMeshHalfWidth]
    positivity
  have hd : |d| ≤ h := by simpa [d, x] using haNear
  have hsq : d ^ 2 ≤ h ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg d) hd 2
    simpa [sq_abs] using this
  have hB0 : B ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le (by simpa [B, x] using haLower)).ne'
  have htaylor := norm_rescaledCenteredEval_sub_linear_le_of_not_high
    n hn e hgood x t hx htFull
  have hlinear : ‖A + (d : ℂ) * B‖ ≤ u / n + C * h ^ 2 := by
    have htri : ‖A + (d : ℂ) * B‖ ≤
        ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ := by
      have hid : A + (d : ℂ) * B = P - (P - (A + (d : ℂ) * B)) := by
        ring
      calc
        ‖A + (d : ℂ) * B‖ =
            ‖P - (P - (A + (d : ℂ) * B))‖ := congrArg norm hid
        _ ≤ ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ :=
          norm_sub_le P (P - (A + (d : ℂ) * B))
    calc
      ‖A + (d : ℂ) * B‖ ≤
          ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ := htri
      _ ≤ u / n + C * d ^ 2 := by
        exact add_le_add (by simpa [P] using hmin)
          (by simpa [P, A, d, B, C] using htaylor)
      _ ≤ u / n + C * h ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hC0)
  have hclosest := localAffineOffset_min n e a (by simpa [B, x] using hB0) d
  have hheightNorm := norm_localAffineValue n hn e a (by simpa [B, x] using hB0)
  have hdiv : |localSignedHeight n e a| / n ≤ u / n + C * h ^ 2 := by
    rw [← hheightNorm]
    exact hclosest.trans (by simpa [A, B, d, x] using hlinear)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    |localSignedHeight n e a| =
        n * (|localSignedHeight n e a| / n) := by field_simp
    _ ≤ n * (u / n + C * h ^ 2) :=
      mul_le_mul_of_nonneg_left hdiv hnR.le
    _ = u + n * globalAccelerationBound n * localMeshHalfWidth n ^ 2 := by
      dsimp [C, h]
      field_simp [hnR.ne']

noncomputable def minimumTransferWidthFactor
    (n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  1 + minimumAffineOffsetError n u velocityLower velocityUpper /
    localMeshHalfWidth n

noncomputable def minimumTransferHeight (n : ℕ) (u : ℝ) : ℝ :=
  u + n * globalAccelerationBound n * localMeshHalfWidth n ^ 2

lemma isFactoredTruncatedLocalRepresentative_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighMeshAcceleration n e)
    (u velocityLower velocityUpper t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hmin : ‖rescaledCenteredEval n e t‖ ≤ u / n)
    (hortho : (rescaledCenteredEval n e t *
      conj (rescaledCenteredVelocity n e t)).re = 0)
    (a : Fin (localMeshSize n))
    (haHalf : a ∈ halfLocalMeshSites n)
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖)
    (haUpper : ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤
      velocityUpper) :
    IsFactoredTruncatedLocalRepresentative n
      (minimumTransferWidthFactor n u velocityLower velocityUpper)
      (minimumTransferHeight n u) velocityLower velocityUpper e a := by
  let s := localAffineOffset n e a
  let d := t - localMeshPoint n a
  let h := localMeshHalfWidth n
  let err := minimumAffineOffsetError n u velocityLower velocityUpper
  have hhpos : 0 < h := by
    dsimp [h]
    unfold localMeshHalfWidth
    exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)
  have hsminus : |s - d| ≤ err := by
    simpa [s, d, err] using localAffineOffset_sub_minimizer_le
      n hn e hgood u velocityLower velocityUpper t ht hmin hortho a haHalf
        haNear hvelocityLower haLower haUpper
  have hd : |d| ≤ h := by simpa [d, h] using haNear
  have hs : |s| ≤ (1 + err / h) * h := by
    calc
      |s| = |(s - d) + d| := by ring
      _ ≤ |s - d| + |d| := abs_add_le _ _
      _ ≤ err + h := add_le_add hsminus hd
      _ = (1 + err / h) * h := by field_simp [hhpos.ne']; ring
  have hheight := abs_localSignedHeight_le_of_minimizer
    n hn e hgood u velocityLower t ht hmin a haNear hvelocityLower haLower
  refine ⟨?_, ?_, ?_, haLower, haUpper⟩
  · apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le haLower).ne'
  · simpa [minimumTransferWidthFactor, s, h, err] using hs
  · simpa [minimumTransferHeight] using hheight

lemma minimumTransferWidthFactor_tendsto_one
    (u velocityLower velocityUpper : ℝ) (hvelocityLower : velocityLower ≠ 0) :
    Tendsto (fun n : ℕ ↦
      minimumTransferWidthFactor n u velocityLower velocityUpper)
      atTop (𝓝 1) := by
  have hfirst := globalAccelerationBound_div_tendsto_zero.const_mul u
  have hsecond :=
    globalAccelerationBound_mul_halfWidth_tendsto_zero.const_mul velocityUpper
  have hfirst0 : Tendsto (fun n : ℕ ↦
      u * (globalAccelerationBound n / n)) atTop (𝓝 0) := by
    simpa using hfirst
  have hfirst' : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * (u / n)) atTop (𝓝 0) := by
    refine hfirst0.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hsecond0 : Tendsto (fun n : ℕ ↦
      velocityUpper *
        (globalAccelerationBound n * localMeshHalfWidth n))
      atTop (𝓝 0) := by
    simpa using hsecond
  have hsecond' : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * localMeshHalfWidth n * velocityUpper)
      atTop (𝓝 0) := by
    refine hsecond0.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hsum : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * (u / n) +
        globalAccelerationBound n * localMeshHalfWidth n * velocityUpper)
      atTop (𝓝 0) := by
    simpa using hfirst'.add hsecond'
  have hdiv := hsum.div_const (velocityLower ^ 2)
  have hdiv' : Tendsto (fun n : ℕ ↦
      (globalAccelerationBound n * (u / n) +
        globalAccelerationBound n * localMeshHalfWidth n * velocityUpper) /
          velocityLower ^ 2) atTop (𝓝 0) := by
    simpa [hvelocityLower] using hdiv
  have herror : Tendsto (fun n : ℕ ↦
      minimumAffineOffsetError n u velocityLower velocityUpper /
        localMeshHalfWidth n) atTop (𝓝 0) := by
    refine hdiv'.congr' ?_
    filter_upwards [Nat.eventually_pos] with n hn
    have hh : localMeshHalfWidth n ≠ 0 := by
      unfold localMeshHalfWidth
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
        (by exact_mod_cast (localMeshSize_pos n).ne')
    unfold minimumAffineOffsetError
    field_simp [hh]
  simpa [minimumTransferWidthFactor] using
    (tendsto_const_nhds.add herror)

lemma minimumTransferHeight_tendsto
    (u : ℝ) :
    Tendsto (fun n : ℕ ↦ minimumTransferHeight n u) atTop (𝓝 u) := by
  have hprod := scaled_localMeshHalfWidth_tendsto_pi.mul
    globalAccelerationBound_mul_halfWidth_tendsto_zero
  have hprod' : Tendsto (fun n : ℕ ↦
      ((n : ℝ) * localMeshHalfWidth n) *
        (globalAccelerationBound n * localMeshHalfWidth n))
      atTop (𝓝 0) := by
    simpa using hprod
  have hzero : Tendsto (fun n : ℕ ↦
      (n : ℝ) * globalAccelerationBound n * localMeshHalfWidth n ^ 2)
      atTop (𝓝 0) := by
    refine hprod'.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  simpa [minimumTransferHeight] using tendsto_const_nhds.add hzero

lemma eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale :
    ∀ᶠ n : ℕ in atTop,
      2 * localMeshHalfWidth n < Real.pi * (2 * rigiditySmoothScale n) := by
  have hhalf : ∀ᶠ n : ℕ in atTop,
      localMeshHalfWidth n < Real.pi / 2 :=
    localMeshHalfWidth_tendsto_zero.eventually
      (Iio_mem_nhds (half_pos Real.pi_pos))
  have hKtop : Tendsto rigiditySmoothScale atTop atTop := by
    unfold rigiditySmoothScale rigiditySmoothExponent
    exact tendsto_rigidityPower_atTop (by norm_num)
  have hK : ∀ᶠ n : ℕ in atTop, 1 ≤ rigiditySmoothScale n :=
    hKtop.eventually (eventually_ge_atTop 1)
  filter_upwards [hhalf, hK] with n hh hKn
  have hleft : 2 * localMeshHalfWidth n < Real.pi := by linarith
  have hright : Real.pi ≤ Real.pi * (2 * rigiditySmoothScale n) := by
    nlinarith [Real.pi_pos]
  exact hleft.trans_le hright

lemma IsSmooth.of_near
    {n : ℕ} (hn : 0 < n) {K t x h : ℝ}
    (hK : 1 ≤ K) (hh : 0 ≤ h) (hhpi : 2 * h ≤ Real.pi)
    (hsmooth : IsSmooth n (2 * K) t)
    (htx : |t - x| ≤ h) :
    IsSmooth n K x := by
  intro p hp1 hpK
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK0 : 0 ≤ K := hK.trans' (by norm_num)
  have hpFloor : (p : ℝ) ≤ K + 1 := by
    have hpCast : (p : ℝ) ≤ (Nat.floor K + 1 : ℕ) := by
      exact_mod_cast hpK
    have hfloor : (Nat.floor K : ℝ) ≤ K := Nat.floor_le hK0
    push_cast at hpCast
    linarith
  have hpKReal : (p : ℝ) ≤ 2 * K := by linarith
  have hpKFloor : p ≤ Nat.floor (2 * K) + 1 := by
    have hfloor : (p : ℝ) < Nat.floor (2 * K) + 1 := by
      have hfloorTwo : (2 * K : ℝ) < Nat.floor (2 * K) + 1 :=
        Nat.lt_floor_add_one (2 * K)
      exact hpKReal.trans_lt hfloorTwo
    have hfloorNat : p < Nat.floor (2 * K) + 1 := by exact_mod_cast hfloor
    omega
  have hsource := hsmooth p hp1 hpKFloor
  have hperturb :
      distanceToInteger (p * (t - x) / (Real.pi * n)) ≤ K / n := by
    calc
      distanceToInteger (p * (t - x) / (Real.pi * n)) ≤
          |p * (t - x) / (Real.pi * n) - (0 : ℤ)| :=
        distanceToInteger_minimal _ 0
      _ = (p : ℝ) * |t - x| / (Real.pi * n) := by
        rw [Int.cast_zero, sub_zero, abs_div, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg p), abs_mul,
          abs_of_pos Real.pi_pos, abs_of_pos hnR]
      _ ≤ (K + 1) * h / (Real.pi * n) := by
        gcongr
      _ ≤ K / n := by
        have hKh : (K + 1) * h ≤ K * Real.pi := by
          calc
            (K + 1) * h ≤ (K + 1) * (Real.pi / 2) := by
              gcongr
              linarith
            _ ≤ K * Real.pi := by
              nlinarith [Real.pi_pos]
        calc
          (K + 1) * h / (Real.pi * n) ≤
              (K * Real.pi) / (Real.pi * n) :=
            div_le_div_of_nonneg_right hKh
              (mul_pos Real.pi_pos hnR).le
          _ = K / n := by field_simp [Real.pi_ne_zero, hnR.ne']
  have hadd := distanceToInteger_add_le
    (p * x / (Real.pi * n)) (p * (t - x) / (Real.pi * n))
  have hrewrite :
      p * x / (Real.pi * n) + p * (t - x) / (Real.pi * n) =
        p * t / (Real.pi * n) := by ring
  rw [hrewrite] at hadd
  by_contra hnot
  have htarget : distanceToInteger (p * x / (Real.pi * n)) ≤ K / n :=
    le_of_not_gt hnot
  have hupper :
      distanceToInteger (p * t / (Real.pi * n)) ≤ 2 * K / n := by
    calc
      _ ≤ distanceToInteger (p * x / (Real.pi * n)) +
          distanceToInteger (p * (t - x) / (Real.pi * n)) := hadd
      _ ≤ K / n + K / n := add_le_add htarget hperturb
      _ = 2 * K / n := by ring
  exact (not_lt_of_ge hupper) hsource

lemma eventually_nearest_halfLocalMeshSite_smooth :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      IsSmooth n (2 * rigiditySmoothScale n) t →
      ∀ a : Fin (localMeshSize n),
        |t - localMeshPoint n a| ≤ localMeshHalfWidth n →
        IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) := by
  have hKtop : Tendsto rigiditySmoothScale atTop atTop := by
    unfold rigiditySmoothScale rigiditySmoothExponent
    exact tendsto_rigidityPower_atTop (by norm_num)
  have hK : ∀ᶠ n : ℕ in atTop, 1 ≤ rigiditySmoothScale n :=
    hKtop.eventually (eventually_ge_atTop 1)
  have hh : ∀ᶠ n : ℕ in atTop, 2 * localMeshHalfWidth n ≤ Real.pi :=
    (localMeshHalfWidth_tendsto_zero.eventually
      (Iio_mem_nhds (half_pos Real.pi_pos))).mono fun _ hn ↦ by linarith
  filter_upwards [Nat.eventually_pos, hK, hh] with n hn hKn hhn
  intro t ht a hta
  exact ht.of_near hn hKn (by unfold localMeshHalfWidth; positivity) hhn hta

noncomputable def minimumVelocityTransferError (n : ℕ) : ℝ :=
  globalAccelerationBound n * localMeshHalfWidth n

lemma abs_norm_rescaledCenteredVelocity_sub_le_of_near
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighMeshAcceleration n e)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n) :
    |‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ -
        ‖rescaledCenteredVelocity n e t‖| ≤
      minimumVelocityTransferError n := by
  have hx := localMeshPoint_mem_Ico n hn a
  have hxIcc : localMeshPoint n a ∈
      Set.Icc (-(Real.pi * n)) (Real.pi * n) := ⟨hx.1, hx.2.le⟩
  have htIcc : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hpi : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(neg_nonpos.mpr hpi.le).trans ht.1, ht.2⟩
  have hvel := norm_rescaledCenteredVelocity_sub_le_of_not_high
    n hn e hgood t (localMeshPoint n a) htIcc hxIcc
  calc
    |‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ -
        ‖rescaledCenteredVelocity n e t‖| ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a) -
        rescaledCenteredVelocity n e t‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ globalAccelerationBound n *
        |localMeshPoint n a - t| := hvel
    _ ≤ minimumVelocityTransferError n := by
      unfold minimumVelocityTransferError
      rw [abs_sub_comm]
      exact mul_le_mul_of_nonneg_left haNear (by
        unfold globalAccelerationBound
        exact add_nonneg (rigidityPower_nonneg n _)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (by unfold localMeshHalfWidth; positivity)))

lemma minimumVelocityTransferError_tendsto_zero :
    Tendsto minimumVelocityTransferError atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦
    globalAccelerationBound n * localMeshHalfWidth n) atTop (𝓝 0)
  exact globalAccelerationBound_mul_halfWidth_tendsto_zero

lemma exists_smooth_factoredTruncatedLocalRepresentative_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighMeshAcceleration n e)
    (u velocityLower velocityUpper t : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hnearestSmooth : ∀ a : Fin (localMeshSize n),
      |t - localMeshPoint n a| ≤ localMeshHalfWidth n →
      IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a))
    (htSmooth : IsSmooth n (2 * rigiditySmoothScale n) t)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hmin : ‖rescaledCenteredEval n e t‖ ≤ u / n)
    (hortho : (rescaledCenteredEval n e t *
      conj (rescaledCenteredVelocity n e t)).re = 0)
    (hvelocityLower : 0 < velocityLower)
    (htLower : velocityLower + minimumVelocityTransferError n ≤
      ‖rescaledCenteredVelocity n e t‖)
    (htUpper : ‖rescaledCenteredVelocity n e t‖ ≤
      velocityUpper - minimumVelocityTransferError n) :
    ∃ a ∈ halfSmoothLocalMeshSites n,
      IsFactoredTruncatedLocalRepresentative n
        (minimumTransferWidthFactor n u velocityLower velocityUpper)
        (minimumTransferHeight n u) velocityLower velocityUpper e a := by
  rcases exists_halfLocalMeshSite_within_halfWidth n hn
      (2 * rigiditySmoothScale n) t hwidth htSmooth ht with
    ⟨a, haHalf, haNear⟩
  have haSmooth := hnearestSmooth a haNear
  have hvelocityDiff := abs_norm_rescaledCenteredVelocity_sub_le_of_near
    n hn e hgood t ht a haNear
  have hdiffLower :
      ‖rescaledCenteredVelocity n e t‖ -
          minimumVelocityTransferError n ≤
        ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ := by
    rw [abs_le] at hvelocityDiff
    linarith [hvelocityDiff.2]
  have haLower : velocityLower ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ :=
    (by linarith : velocityLower ≤
      ‖rescaledCenteredVelocity n e t‖ - minimumVelocityTransferError n).trans
      hdiffLower
  have hdiffUpper :
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤
        ‖rescaledCenteredVelocity n e t‖ +
          minimumVelocityTransferError n := by
    rw [abs_le] at hvelocityDiff
    linarith [hvelocityDiff.1]
  have haUpper :
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤ velocityUpper :=
    hdiffUpper.trans (by linarith)
  refine ⟨a, ?_, isFactoredTruncatedLocalRepresentative_of_minimizer
    n hn e hgood u velocityLower velocityUpper t ht hmin hortho a haHalf
      haNear hvelocityLower haLower haUpper⟩
  exact Finset.mem_filter.mpr ⟨haHalf, haSmooth⟩

end Erdos525
