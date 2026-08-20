import Mathlib

open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section

private def diskMobius (c z : ℂ) : ℂ :=
  (z - c) / (1 - (starRingEnd ℂ) c * z)

private lemma diskMobius_norm_le_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMobius c z‖ ≤ 1 := by
  have hden : 1 - (starRingEnd ℂ) c * z ≠ 0 := by
    intro h
    have heq : (1 : ℂ) = (starRingEnd ℂ) c * z := sub_eq_zero.mp h
    have : (1 : ℝ) = ‖c‖ * ‖z‖ := by
      simpa using congrArg norm heq
    have hmul : ‖c‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  rw [diskMobius, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_sub, Complex.normSq_sub]
  simp only [Complex.normSq_one, Complex.normSq_mul, Complex.normSq_conj,
    Complex.mul_re, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im, mul_one, zero_mul, sub_zero]
  have hc2 : ‖c‖ ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (add_pos_of_nonneg_of_pos (norm_nonneg c) zero_lt_one)]
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (add_nonneg (norm_nonneg z) zero_le_one)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc2.le) (sub_nonneg.mpr hz2)]

private lemma diskMobius_norm_eq_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskMobius c z‖ = 1 := by
  have hden : 1 - (starRingEnd ℂ) c * z ≠ 0 := by
    intro h
    have heq : (1 : ℂ) = (starRingEnd ℂ) c * z := sub_eq_zero.mp h
    have : (1 : ℝ) = ‖c‖ * ‖z‖ := by simpa using congrArg norm heq
    rw [hz, mul_one] at this
    linarith
  rw [diskMobius, norm_div]
  apply (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)).2
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_one, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, mul_one, zero_mul, sub_zero]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hz]
  ring

private lemma diskMobius_sub (c u v : ℂ)
    (hu : 1 - (starRingEnd ℂ) c * u ≠ 0)
    (hv : 1 - (starRingEnd ℂ) c * v ≠ 0) :
    diskMobius c u - diskMobius c v =
      (1 - (Complex.normSq c : ℂ)) * (u - v) /
        ((1 - (starRingEnd ℂ) c * u) * (1 - (starRingEnd ℂ) c * v)) := by
  have hu' : 1 - u * (starRingEnd ℂ) c ≠ 0 := by simpa [mul_comm] using hu
  have hv' : 1 - v * (starRingEnd ℂ) c ≠ 0 := by simpa [mul_comm] using hv
  rw [diskMobius, diskMobius]
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [hu, hv, hu', hv']
  ring

private lemma norm_le_one_of_schwarz_factor {H J : ℂ → ℂ} {k : ℕ} (hk : 0 < k)
    (hHdiff : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hHmap : MapsTo H (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hH0 : H 0 = 0) (hJcont : ContinuousAt J 0)
    (hfactor : ∀ z ∈ Metric.ball (0 : ℂ) 1, H z = z ^ k * J z) :
    ‖J 0‖ ≤ 1 := by
  have hpred : k - 1 < k := Nat.sub_lt hk zero_lt_one
  have hsmall : (H · - H 0) =o[𝓝 (0 : ℂ)] (fun z ↦ z ^ (k - 1)) := by
    have hpow := Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) hpred
    have hprod := hpow.mul_isBigO hJcont.isBigO
    refine hprod.congr' ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
      rw [hH0, sub_zero, hfactor z hz]
    · exact Eventually.of_forall (fun z ↦ by simp)
  have hbound {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      ‖H z‖ ≤ ‖z‖ ^ k := by
    have hsmall' : (H · - H 0) =o[𝓝 (0 : ℂ)] (fun z ↦ ‖z‖ ^ (k - 1)) := by
      simpa [norm_pow] using hsmall.norm_right
    have hHmap' : MapsTo H (Metric.ball (0 : ℂ) 1) (Metric.closedBall (H 0) 1) := by
      simpa [hH0] using hHmap
    have hsmall'' : (H · - H 0) =o[𝓝 (0 : ℂ)]
        (fun w ↦ ‖w - 0‖ ^ (k - 1)) := by simpa using hsmall'
    have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (n := k - 1) hHdiff hHmap' hsmall'' hz
    simpa [hH0, Nat.sub_add_cancel hk, Complex.dist_eq, norm_pow] using hs
  have htend : Tendsto (fun z ↦ ‖J z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖J 0‖) :=
    hJcont.norm.tendsto.mono_left inf_le_left
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with z hz0 hzball
  have hz_ne : z ≠ 0 := by simpa using hz0
  have hzpos : 0 < ‖z‖ ^ k := pow_pos (norm_pos_iff.mpr hz_ne) _
  have := hbound hzball
  rw [hfactor z hzball, norm_mul, norm_pow] at this
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using this) hzpos

private lemma leading_factor_bound {f g j : ℂ → ℂ} {c : ℂ} {k : ℕ}
    (hc : ‖c‖ < 1) (hk : 0 < k)
    (hfdiff : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hgdiff : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hfmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hgmap : MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hf0 : f 0 = c) (hg0 : g 0 = c) (hjcont : ContinuousAt j 0)
    (hfactor : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - g z = z ^ k * j z) :
    ‖j 0‖ ≤ 2 * (1 - ‖c‖ ^ 2) := by
  let F : ℂ → ℂ := fun z ↦ diskMobius c (f z)
  let G : ℂ → ℂ := fun z ↦ diskMobius c (g z)
  let H : ℂ → ℂ := fun z ↦ (F z - G z) / 2
  let J : ℂ → ℂ := fun z ↦
    ((1 - (Complex.normSq c : ℂ)) * j z) /
      (2 * ((1 - (starRingEnd ℂ) c * f z) * (1 - (starRingEnd ℂ) c * g z)))
  have hden_f {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      1 - (starRingEnd ℂ) c * f z ≠ 0 := by
    intro heq
    have heq' : (1 : ℂ) = (starRingEnd ℂ) c * f z := sub_eq_zero.mp heq
    have hone : (1 : ℝ) = ‖c‖ * ‖f z‖ := by simpa using congrArg norm heq'
    have hfz : ‖f z‖ ≤ 1 := by simpa using hfmap hz
    have : ‖c‖ * ‖f z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hfz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  have hden_g {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      1 - (starRingEnd ℂ) c * g z ≠ 0 := by
    intro heq
    have heq' : (1 : ℂ) = (starRingEnd ℂ) c * g z := sub_eq_zero.mp heq
    have hone : (1 : ℝ) = ‖c‖ * ‖g z‖ := by simpa using congrArg norm heq'
    have hgz : ‖g z‖ ≤ 1 := by simpa using hgmap hz
    have : ‖c‖ * ‖g z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hgz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  have hHdiff : DifferentiableOn ℂ H (Metric.ball 0 1) := by
    intro z hz
    have hfz : DifferentiableAt ℂ f z :=
      (hfdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hgz : DifferentiableAt ℂ g z :=
      (hgdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hFdiff : DifferentiableAt ℂ F z := by
      dsimp only [F, diskMobius]
      exact (hfz.sub (differentiableAt_const c)).div
        ((differentiableAt_const (1 : ℂ)).sub
          ((differentiableAt_const ((starRingEnd ℂ) c)).mul hfz)) (hden_f hz)
    have hGdiff : DifferentiableAt ℂ G z := by
      dsimp only [G, diskMobius]
      exact (hgz.sub (differentiableAt_const c)).div
        ((differentiableAt_const (1 : ℂ)).sub
          ((differentiableAt_const ((starRingEnd ℂ) c)).mul hgz)) (hden_g hz)
    exact (hFdiff.sub hGdiff).div_const 2 |>.differentiableWithinAt
  have hHmap : MapsTo H (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    have hF : ‖F z‖ ≤ 1 := diskMobius_norm_le_one hc (by simpa using hfmap hz)
    have hG : ‖G z‖ ≤ 1 := diskMobius_norm_le_one hc (by simpa using hgmap hz)
    simp only [Metric.mem_closedBall, dist_zero_right, H, norm_div]
    calc
      ‖F z - G z‖ / ‖(2 : ℂ)‖ ≤ (‖F z‖ + ‖G z‖) / 2 := by
        norm_num
        gcongr
        exact norm_sub_le _ _
      _ ≤ 1 := by linarith
  have hH0 : H 0 = 0 := by simp [H, F, G, hf0, hg0]
  have hpos : 0 < 1 - ‖c‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (add_pos_of_nonneg_of_pos (norm_nonneg c) zero_lt_one)]
  have hJcont : ContinuousAt J 0 := by
    have hden0 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have hr : (1 : ℝ) - Complex.normSq c ≠ 0 := by
        rw [Complex.normSq_eq_norm_sq]
        exact ne_of_gt hpos
      exact_mod_cast hr
    have hfcont : ContinuousAt f 0 :=
      ((hfdiff 0 (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
    have hgcont : ContinuousAt g 0 :=
      ((hgdiff 0 (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
    dsimp only [J]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa [hf0, hg0, ← Complex.normSq_eq_conj_mul_self] using
        mul_ne_zero (OfNat.ofNat_ne_zero 2) (mul_ne_zero hden0 hden0)
  have hHJ : ∀ z ∈ Metric.ball (0 : ℂ) 1, H z = z ^ k * J z := by
    intro z hz
    dsimp only [H, F, G]
    rw [diskMobius_sub c (f z) (g z) (hden_f hz) (hden_g hz), hfactor z hz]
    dsimp only [J]
    field_simp
  have hJ := norm_le_one_of_schwarz_factor hk hHdiff hHmap hH0 hJcont hHJ
  have hnormsq : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
  have hJ0 : ‖J 0‖ = ‖j 0‖ / (2 * (1 - ‖c‖ ^ 2)) := by
    dsimp only [J]
    rw [hf0, hg0, ← Complex.normSq_eq_conj_mul_self]
    have hone : (1 : ℂ) - (Complex.normSq c : ℂ) =
        ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
      norm_cast
      rw [hnormsq]
    rw [hone]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    norm_num
    field_simp
  rw [hJ0] at hJ
  exact (div_le_one (mul_pos two_pos hpos)).mp hJ

def IsPisot1096 (θ : ℝ) : Prop :=
  1 < θ ∧ IsIntegral ℤ θ ∧
    ∀ z : ℂ, ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1

private def iterDivX {R : Type*} [Semiring R] (k : ℕ) (p : R[X]) : R[X] :=
  (Polynomial.divX^[k]) p

private lemma coeff_iterDivX {R : Type*} [Semiring R] (k n : ℕ) (p : R[X]) :
    (iterDivX k p).coeff n = p.coeff (n + k) := by
  induction k generalizing n with
  | zero => simp [iterDivX]
  | succ k ih =>
      rw [iterDivX, Function.iterate_succ_apply', Polynomial.coeff_divX]
      change (iterDivX k p).coeff (n + 1) = _
      rw [ih]
      congr 1
      omega

private lemma eq_X_pow_mul_iterDivX {R : Type*} [CommSemiring R] (k : ℕ) (p : R[X])
    (hzero : ∀ n < k, p.coeff n = 0) :
    p = X ^ k * iterDivX k p := by
  ext n
  rw [coeff_X_pow_mul']
  by_cases hnk : k ≤ n
  · rw [if_pos hnk, coeff_iterDivX]
    congr 1
    omega
  · rw [if_neg hnk]
    exact hzero n (lt_of_not_ge hnk)

private lemma map_reverse_of_injective {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    p.reverse.map f = (p.map f).reverse := by
  ext n
  rw [coeff_map, coeff_reverse, coeff_reverse, coeff_map,
    natDegree_map_eq_of_injective hf]

private lemma norm_eval_map_int_conj (r : ℤ[X]) (z : ℂ) :
    ‖(r.map (algebraMap ℤ ℂ)).eval (starRingEnd ℂ z)‖ =
      ‖(r.map (algebraMap ℤ ℂ)).eval z‖ := by
  let rR : ℝ[X] := r.map (algebraMap ℤ ℝ)
  have hcomp : (algebraMap ℤ ℂ) = (algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ) := by
    ext n
    simp
  have hleft : (r.map (algebraMap ℤ ℂ)).eval (starRingEnd ℂ z) =
      aeval (starRingEnd ℂ z) rR := by
    rw [hcomp]
    simp [rR, aeval_def, eval_map, eval₂_map]
  have hright : (r.map (algebraMap ℤ ℂ)).eval z = aeval z rR := by
    rw [hcomp]
    simp [rR, aeval_def, eval_map, eval₂_map]
  rw [hleft, hright, Polynomial.aeval_conj]
  exact RCLike.norm_conj _

private lemma reverse_X_sub_C (a : ℂ) :
    (X - C a).reverse = 1 - C a * X := by
  have hrevX : (X : ℂ[X]).reverse = 1 := by
    rw [← one_mul X, ← C_1, reverse_mul_X, reverse_C, C_1]
  calc
    (X - C a).reverse = (X + C (-a)).reverse := by rw [C_neg, sub_eq_add_neg]
    _ = X.reverse + C (-a) * X ^ X.natDegree := reverse_add_C X (-a)
    _ = 1 + C (-a) * X := by rw [hrevX, natDegree_X, pow_one]
    _ = 1 - C a * X := by rw [C_neg, neg_mul, sub_eq_add_neg]

private lemma reverse_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map (fun a ↦ X - C a)).prod).reverse =
      (s.map (fun a ↦ 1 - C a * X)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      change (1 : ℂ[X]).reverse = 1
      rw [← C_1, reverse_C, C_1]
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [reverse_mul_of_domain, reverse_X_sub_C, ih]

private lemma multiset_prod_le_one {s : Multiset ℝ}
    (h0 : ∀ a ∈ s, 0 ≤ a) (h1 : ∀ a ∈ s, a ≤ 1) : s.prod ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.prod_cons]
      have ha0 : 0 ≤ a := h0 a (by simp)
      have ha1 : a ≤ 1 := h1 a (by simp)
      have hs0 : ∀ b ∈ s, 0 ≤ b := by
        intro b hb
        exact h0 b (by simp [hb])
      have hs1 : ∀ b ∈ s, b ≤ 1 := by
        intro b hb
        exact h1 b (by simp [hb])
      have hsprod := ih hs0 hs1
      have hsprod0 : 0 ≤ s.prod := Multiset.prod_nonneg hs0
      nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hsprod)]

private lemma norm_multiset_prod (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih]

private lemma pisot_minpoly_coeff_zero_abs_eq_one
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (hθint : IsIntegral ℤ θ)
    (hpsep : ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1) :
    |(minpoly ℤ θ).coeff 0| = 1 := by
  let p : ℤ[X] := minpoly ℤ θ
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let roots : Multiset ℂ := P.roots
  have hpmonic : p.Monic := minpoly.monic hθint
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    rw [show roots = P.roots by rfl, mem_roots hPne]
    change (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0
    have hr : (p.map (algebraMap ℤ ℝ)).eval θ = 0 := by
      simpa [p, ← eval_map_algebraMap] using minpoly.aeval ℤ θ
    have hc := congrArg (algebraMap ℝ ℂ) hr
    simpa [eval_map, eval₂_map] using hc
  let others : Multiset ℂ := roots.erase θc
  have hroots : roots = θc ::ₘ others := (Multiset.cons_erase hθroot).symm
  have hnodup : roots.Nodup := by
    apply nodup_roots
    simpa [P, p] using hpsep
  have hother_mem {z : ℂ} (hz : z ∈ others) : ‖z‖ < 1 := by
    apply hother z
    · exact (mem_roots hPne).mp (Multiset.mem_of_mem_erase hz)
    · intro h
      subst z
      exact hnodup.notMem_erase hz
  have hothers_norm : ‖others.prod‖ ≤ 1 := by
    rw [norm_multiset_prod]
    apply multiset_prod_le_one
    · intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨z, -, rfl⟩ := ha
      exact norm_nonneg z
    · intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      exact (hother_mem hz).le
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcoeff := hsplit.coeff_zero_eq_prod_roots_of_monic hPmonic
  have hcoeffnorm := congrArg norm hcoeff
  have hp0lt : |p.coeff 0| < 2 := by
    have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
    rw [show P.coeff 0 = (p.coeff 0 : ℂ) by simp [P]] at hcoeffnorm
    rw [show roots.prod = θc * others.prod by rw [hroots]; simp] at hcoeffnorm
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hcoeffnorm
    have hθnorm : ‖θc‖ = θ := by
      simp [θc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθpos]
    have hp0norm : ‖(p.coeff 0 : ℂ)‖ = |p.coeff 0| := by
      simp [Complex.norm_intCast]
    rw [hθnorm, hp0norm] at hcoeffnorm
    have hp0ltR : ((|p.coeff 0| : ℤ) : ℝ) < 2 := by
      rw [hcoeffnorm]
      have hθ2 : θ < (2 : ℝ) := by nlinarith
      simpa using (mul_le_mul_of_nonneg_left hothers_norm hθpos.le).trans_lt
        (show θ * 1 < (2 : ℝ) by simpa using hθ2)
    exact_mod_cast hp0ltR
  have hp0ne : p.coeff 0 ≠ 0 := by
    have hθintQ : IsIntegral ℚ θ := hθint.tower_top
    have hq0 : (minpoly ℚ θ).coeff 0 ≠ 0 :=
      minpoly.coeff_zero_ne_zero hθintQ (ne_of_gt (lt_trans zero_lt_one hθ1))
    have hpQ : minpoly ℚ θ = p.map (algebraMap ℤ ℚ) := by
      simpa [p] using
        (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hθint)
    rw [hpQ, coeff_map] at hq0
    exact fun hp0 ↦ hq0 (by simp [hp0])
  have hp0pos : (0 : ℤ) < |p.coeff 0| := abs_pos.mpr hp0ne
  have hp0one : |p.coeff 0| = 1 := by omega
  simpa [p] using hp0one

private lemma minpoly_int_map_complex_separable {θ : ℝ} (hθint : IsIntegral ℤ θ) :
    ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).Separable := by
  have hθintQ : IsIntegral ℚ θ := hθint.tower_top
  have hsepQ : (minpoly ℚ θ).Separable := (minpoly.irreducible hθintQ).separable
  have hsepC := hsepQ.map (f := algebraMap ℚ ℂ)
  have hpQ : minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hθint
  rw [hpQ, Polynomial.map_map] at hsepC
  convert hsepC using 1
  ext n
  simp

private lemma reciprocal_pisot_not_lt
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (p : ℤ[X]) (hpmonic : p.Monic)
    (hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0)
    (hpsep : (p.map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, (p.map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1)
    (hp0 : |p.coeff 0| = 1)
    (hrecip : C (p.coeff 0) * p - p.reverse = 0) : False := by
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let c : ℂ := ((θ⁻¹ : ℝ) : ℂ)
  let roots : Multiset ℂ := P.roots
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    rw [show roots = P.roots by rfl, mem_roots hPne]
    exact hproot
  have hnodup : roots.Nodup := nodup_roots hpsep
  have hp0ne : p.coeff 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hp0
    omega
  have hp0neC : (p.coeff 0 : ℂ) ≠ 0 := by exact_mod_cast hp0ne
  have hrecipC : P.reverse = C (p.coeff 0 : ℂ) * P := by
    have hm := congrArg (fun r : ℤ[X] ↦ r.map (algebraMap ℤ ℂ)) hrecip
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, map_zero] at hm
    rw [map_reverse_of_injective (algebraMap ℤ ℂ)
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ))] at hm
    have hm' : C (p.coeff 0 : ℂ) * P - P.reverse = 0 := by
      convert hm using 1 <;> simp [P]
    exact sub_eq_zero.mp hm' |>.symm
  have hroot_ne_zero {z : ℂ} (hz : z ∈ roots) : z ≠ 0 := by
    intro hz0
    subst z
    have hzero : P.eval 0 = 0 := (mem_roots hPne).mp hz
    have : (p.coeff 0 : ℂ) = 0 := by
      simpa [P, ← coeff_zero_eq_eval_zero] using hzero
    exact hp0neC this
  have hinv_root {z : ℂ} (hz : z ∈ roots) : z⁻¹ ∈ roots := by
    have hz0 := hroot_ne_zero hz
    letI : Invertible z := invertibleOfNonzero hz0
    have hzroot : P.eval z = 0 := (mem_roots hPne).mp hz
    have hr : P.reverse.eval z⁻¹ = 0 := by
      have := (eval₂_reverse_eq_zero_iff (RingHom.id ℂ) z P).2 hzroot
      simpa using this
    rw [hrecipC] at hr
    simp only [eval_mul, eval_C] at hr
    have : P.eval z⁻¹ = 0 := (mul_eq_zero.mp hr).resolve_left hp0neC
    exact (mem_roots hPne).2 this
  have hcroot : c ∈ roots := by
    simpa [c, θc] using hinv_root hθroot
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hcne : c ≠ θc := by
    intro h
    have hr : θ⁻¹ = θ := by
      dsimp only [c, θc] at h
      exact_mod_cast h
    have hinvlt : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
    linarith
  have hclass {z : ℂ} (hz : z ∈ roots) : z = θc ∨ z = c := by
    by_cases hzθ : z = θc
    · exact Or.inl hzθ
    · have hznorm : ‖z‖ < 1 := hother z ((mem_roots hPne).mp hz) hzθ
      have hzinvroot := hinv_root hz
      have hzinvnorm : 1 < ‖z⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr (hroot_ne_zero hz))).2 hznorm
      have hzinvθ : z⁻¹ = θc := by
        by_contra hne
        have := hother z⁻¹ ((mem_roots hPne).mp hzinvroot) hne
        linarith
      right
      apply inv_injective
      simpa [θc, c] using hzinvθ
  have hroots_eq : roots = {θc, c} := by
    apply (Multiset.Nodup.ext hnodup (by simp [hcne.symm])).2
    intro z
    constructor
    · intro hz
      rcases hclass hz with rfl | rfl <;> simp
    · intro hz
      have hz' : z = θc ∨ z = c := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hθroot
      · exact hcroot
  have hPprod : P = (roots.map (fun z ↦ X - C z)).prod :=
    (IsAlgClosed.splits P).eq_prod_roots_of_monic hPmonic
  have hPfactor : P = (X - C θc) * (X - C c) := by
    rw [hPprod, hroots_eq]
    simp
  have hcoeff1 := congrArg (fun r : ℂ[X] ↦ r.coeff 1) hPfactor
  have htrace : θ + θ⁻¹ = -(p.coeff 1 : ℝ) := by
    have hpoly : (X - C θc) * (X - C c) =
        X ^ 2 - C (θc + c) * X + C (θc * c) := by
      simp only [map_add, map_mul]
      ring
    rw [hpoly] at hcoeff1
    apply_fun Complex.re at hcoeff1
    have hh : (p.coeff 1 : ℝ) = -θ⁻¹ + -θ := by
      simpa [P, θc, c] using hcoeff1
    linarith
  have hinvpos : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have hmul : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθpos)
  have hlower : 2 < θ + θ⁻¹ := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hθ1)]
  have hinvlt : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
  have hupper : θ + θ⁻¹ < 3 := by nlinarith
  have hlowerZ : (2 : ℤ) < -(p.coeff 1) := by
    exact_mod_cast (htrace ▸ hlower)
  have hupperZ : -(p.coeff 1) < (3 : ℤ) := by
    exact_mod_cast (htrace ▸ hupper)
  omega

private lemma nonreciprocal_pisot_not_lt
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (p : ℤ[X]) (hpmonic : p.Monic)
    (hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0)
    (hpsep : (p.map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, (p.map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1)
    (hp0 : |p.coeff 0| = 1)
    (hrecip : C (p.coeff 0) * p - p.reverse ≠ 0) : False := by
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let c : ℂ := ((θ⁻¹ : ℝ) : ℂ)
  let roots : Multiset ℂ := P.roots
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    change θc ∈ P.roots
    rw [mem_roots hPne]
    exact hproot
  let others : Multiset ℂ := roots.erase θc
  have hroots : roots = θc ::ₘ others := (Multiset.cons_erase hθroot).symm
  have hnodup : roots.Nodup := nodup_roots hpsep
  have hother_mem {z : ℂ} (hz : z ∈ others) : ‖z‖ < 1 := by
    have hzroots : z ∈ roots := Multiset.mem_of_mem_erase hz
    have hzne : z ≠ θc := by
      intro h
      subst z
      exact hnodup.notMem_erase hz
    apply hother z
    · exact (mem_roots hPne).mp hzroots
    · exact hzne
  let RP : ℂ[X] := (others.map (fun z ↦ 1 - C z * X)).prod
  have hPprod : P = (roots.map (fun z ↦ X - C z)).prod :=
    (IsAlgClosed.splits P).eq_prod_roots_of_monic hPmonic
  have hPrev : P.reverse = (roots.map (fun z ↦ 1 - C z * X)).prod := by
    rw [hPprod, reverse_prod_X_sub_C]
  have hPrev_factor : P.reverse = (1 - C θc * X) * RP := by
    rw [hPrev, hroots]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rfl
  have hRP_eval (z : ℂ) : RP.eval z = (others.map (fun w ↦ 1 - w * z)).prod := by
    dsimp only [RP]
    induction others using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simp [ih]
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hθc0 : θc ≠ 0 := by
    change (θ : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hθpos)
  have hc_norm : ‖c‖ = θ⁻¹ := by
    simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθpos]
  have hc_lt : ‖c‖ < 1 := by
    rw [hc_norm]
    exact inv_lt_one_of_one_lt₀ hθ1
  have hRP_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : RP.eval z ≠ 0 := by
    rw [hRP_eval]
    apply Multiset.prod_ne_zero
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨b, hb, heq⟩ := hmem
    have heq : 1 - b * z = 0 := heq
    have hone : (1 : ℂ) = b * z := sub_eq_zero.mp heq
    have hone_norm : (1 : ℝ) = ‖b‖ * ‖z‖ := by simpa using congrArg norm hone
    have hlt : ‖b‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg b)).trans_lt (by simpa using hother_mem hb)
    linarith
  have hcz_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 - c * z ≠ 0 := by
    intro heq
    have hone : (1 : ℂ) = c * z := sub_eq_zero.mp heq
    have hone_norm : (1 : ℝ) = ‖c‖ * ‖z‖ := by simpa using congrArg norm hone
    have hlt : ‖c‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg c)).trans_lt (by simpa using hc_lt)
    linarith
  let D : ℂ → ℂ := fun z ↦ (-θc) * RP.eval z * (1 - c * z)
  have hD_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : D z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθc0) (hRP_ne hz)) (hcz_ne hz)
  have hcθ : θc * c = 1 := by
    dsimp only [θc, c]
    norm_cast
    exact mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one hθ1))
  have hPrev_eval (z : ℂ) : P.reverse.eval z = (-θc) * (z - c) * RP.eval z := by
    rw [hPrev_factor]
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_C_mul]
    rw [show 1 - θc * z = (-θc) * (z - c) by
      calc
        1 - θc * z = θc * c - θc * z := by rw [hcθ]
        _ = (-θc) * (z - c) := by ring]
  have hp0sqZ : p.coeff 0 * p.coeff 0 = 1 := by
    have := congrArg (fun n : ℤ ↦ n * n) hp0
    simpa using this
  have hp0sqC : ((p.coeff 0 : ℂ) * (p.coeff 0 : ℂ)) = 1 := by exact_mod_cast hp0sqZ
  let f : ℂ → ℂ := fun z ↦ ((p.coeff 0 : ℂ) * P.eval z) / D z
  let g : ℂ → ℂ := fun z ↦ diskMobius c z
  let NZ : ℤ[X] := C (p.coeff 0) * p - p.reverse
  let k : ℕ := NZ.natTrailingDegree
  let TZ : ℤ[X] := iterDivX k NZ
  let T : ℂ[X] := TZ.map (algebraMap ℤ ℂ)
  let j : ℂ → ℂ := fun z ↦ T.eval z / D z
  have hNZ : NZ ≠ 0 := by simpa [NZ] using hrecip
  have hNZ0 : NZ.coeff 0 = 0 := by
    simp [NZ, hp0sqZ, hpmonic.leadingCoeff]
  have hk : 0 < k := by
    have hkne : k ≠ 0 := by
      intro hk0
      have hcoeff := (coeff_natTrailingDegree_ne_zero (p := NZ)).mpr hNZ
      change NZ.natTrailingDegree = 0 at hk0
      rw [hk0, hNZ0] at hcoeff
      exact hcoeff rfl
    omega
  have hNZfactor : NZ = X ^ k * TZ := by
    exact eq_X_pow_mul_iterDivX k NZ (fun n hn ↦ coeff_eq_zero_of_lt_natTrailingDegree hn)
  have hmapNZ : NZ.map (algebraMap ℤ ℂ) = C (p.coeff 0 : ℂ) * P - P.reverse := by
    calc
      NZ.map (algebraMap ℤ ℂ) =
          (C (p.coeff 0) * p - p.reverse).map (algebraMap ℤ ℂ) := rfl
      _ = C (p.coeff 0 : ℂ) * p.map (algebraMap ℤ ℂ) -
          (p.reverse.map (algebraMap ℤ ℂ)) := by
            rw [Polynomial.map_sub, Polynomial.map_mul, map_C]
            congr 2
      _ = C (p.coeff 0 : ℂ) * P - P.reverse := by
        rw [map_reverse_of_injective (algebraMap ℤ ℂ)
          (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ))]
  have hfg_factor : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - g z = z ^ k * j z := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hD := hD_ne hzle
    have hden_g : 1 - c * z ≠ 0 := hcz_ne hzle
    have hN_eval : ((C (p.coeff 0 : ℂ) * P - P.reverse).eval z) = z ^ k * T.eval z := by
      rw [← hmapNZ, hNZfactor]
      dsimp only [T]
      simp
    have hN_eval' : (p.coeff 0 : ℂ) * P.eval z - P.reverse.eval z =
        z ^ k * T.eval z := by simpa using hN_eval
    dsimp only [f, g, j, diskMobius]
    rw [show (starRingEnd ℂ) c = c by simp [c]]
    have hg_as_reverse : (z - c) / (1 - c * z) = P.reverse.eval z / D z := by
      apply (div_eq_div_iff hden_g hD).2
      rw [hPrev_eval]
      dsimp only [D]
      ring
    rw [hg_as_reverse]
    calc
      (p.coeff 0 : ℂ) * P.eval z / D z - P.reverse.eval z / D z =
          ((p.coeff 0 : ℂ) * P.eval z - P.reverse.eval z) / D z := by
            rw [sub_div]
      _ = (z ^ k * T.eval z) / D z := by rw [hN_eval']
      _ = z ^ k * (T.eval z / D z) := by ring
  have hP0 : P.eval 0 = (p.coeff 0 : ℂ) := by
    change (p.map (algebraMap ℤ ℂ)).eval 0 = _
    rw [eval_map]
    simp
  have hRP0 : RP.eval 0 = 1 := by rw [hRP_eval]; simp
  have hD0 : D 0 = -θc := by simp [D, hRP0]
  have hf0 : f 0 = -c := by
    dsimp only [f]
    rw [hP0, hD0, hp0sqC]
    dsimp only [c, θc]
    norm_cast
    field_simp
  have hg0 : g 0 = -c := by simp [g, diskMobius]
  have hfdiff_closed : DifferentiableOn ℂ f (Metric.closedBall 0 1) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := by simpa using hz
    dsimp only [f, D]
    apply DifferentiableWithinAt.div
    · exact (differentiableWithinAt_const (c := (p.coeff 0 : ℂ))).mul P.differentiableWithinAt
    · exact ((differentiableWithinAt_const (c := -θc)).mul RP.differentiableWithinAt).mul
        ((differentiableWithinAt_const (c := (1 : ℂ))).sub
          ((differentiableWithinAt_const (c := c)).mul differentiableWithinAt_id))
    · exact hD_ne hzle
  have hgdif : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    dsimp only [g, diskMobius]
    have hcstar : (starRingEnd ℂ) c = c := by simp [c]
    rw [hcstar]
    exact (differentiableWithinAt_id.sub (differentiableWithinAt_const (c := c))).div
      ((differentiableWithinAt_const (c := (1 : ℂ))).sub
        ((differentiableWithinAt_const (c := c)).mul differentiableWithinAt_id)) (hcz_ne hzle)
  have hgmap : MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    simpa [g, Metric.mem_closedBall, dist_zero_right] using
      diskMobius_norm_le_one hc_lt (mem_ball_zero_iff.mp hz).le
  have hboundary (z : ℂ) (hz : z ∈ frontier (Metric.ball (0 : ℂ) 1)) : ‖f z‖ ≤ 1 := by
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 := Metric.frontier_ball_subset_sphere hz
    have hznorm : ‖z‖ = 1 := by simpa using hzsphere
    have hD := hD_ne hznorm.le
    have hzg : 1 - c * z ≠ 0 := hcz_ne hznorm.le
    have hPnorm : ‖P.eval z‖ = ‖P.reverse.eval z‖ := by
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0, norm_zero] at hznorm
        norm_num at hznorm
      letI : Invertible z := invertibleOfNonzero hz0
      have hrev := eval₂_reverse_mul_pow (RingHom.id ℂ) z P
      have hrevnorm : ‖P.reverse.eval z⁻¹‖ = ‖P.eval z‖ := by
        simpa [hznorm] using congrArg norm hrev
      have hPrev_map : P.reverse = p.reverse.map (algebraMap ℤ ℂ) := by
        symm
        exact map_reverse_of_injective (algebraMap ℤ ℂ)
          (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ)) p
      have hconjnorm : ‖P.reverse.eval z⁻¹‖ = ‖P.reverse.eval z‖ := by
        rw [Complex.inv_eq_conj hznorm, hPrev_map]
        exact norm_eval_map_int_conj p.reverse z
      exact hrevnorm.symm.trans hconjnorm
    have hg_norm : ‖g z‖ = 1 := by
      exact diskMobius_norm_eq_one hc_lt hznorm
    have hg_as_reverse : g z = P.reverse.eval z / D z := by
      dsimp only [g, diskMobius]
      rw [show (starRingEnd ℂ) c = c by simp [c]]
      apply (div_eq_div_iff hzg hD).2
      rw [hPrev_eval]
      dsimp only [D]
      ring
    have hDnorm : ‖D z‖ = ‖P.reverse.eval z‖ := by
      rw [hg_as_reverse, norm_div] at hg_norm
      exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hD)).mp hg_norm |>.symm
    dsimp only [f]
    rw [norm_div, norm_mul]
    have hp0norm : ‖(p.coeff 0 : ℂ)‖ = 1 := by
      exact_mod_cast hp0
    rw [hp0norm, one_mul, hPnorm, hDnorm]
    exact div_self_le_one _
  have hfmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (hfdiff_closed.diffContOnCl_ball subset_rfl) hboundary (subset_closure hz)
    simpa using hle
  have hjcont : ContinuousAt j 0 := by
    have hD0ne : D 0 ≠ 0 := hD_ne (by simp)
    dsimp only [j, D]
    fun_prop
  have hlead := leading_factor_bound (c := -c) (by simpa using hc_lt) hk
    (hfdiff_closed.mono Metric.ball_subset_closedBall) hgdif hfmap hgmap hf0 hg0 hjcont hfg_factor
  have hTZ0 : TZ.coeff 0 = NZ.coeff k := by
    change (iterDivX k NZ).coeff 0 = NZ.coeff k
    simpa using coeff_iterDivX k 0 NZ
  have hTZ0ne : TZ.coeff 0 ≠ 0 := by
    rw [hTZ0]
    exact (coeff_natTrailingDegree_ne_zero (p := NZ)).mpr hNZ
  have hT0norm : 1 ≤ ‖T.eval 0‖ := by
    have hz : (1 : ℝ) ≤ |TZ.coeff 0| := by exact_mod_cast Int.one_le_abs hTZ0ne
    rw [← T.coeff_zero_eq_eval_zero, show T.coeff 0 = (TZ.coeff 0 : ℂ) by simp [T]]
    simpa [Complex.norm_intCast] using hz
  have hj0_lower : θ⁻¹ ≤ ‖j 0‖ := by
    dsimp only [j]
    rw [hD0, norm_div, norm_neg, show ‖θc‖ = θ by
      simp [θc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hθ1)]]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hT0norm hθpos.le
  have hineq : θ⁻¹ ≤ 2 * (1 - θ⁻¹ ^ 2) := by
    calc
      θ⁻¹ ≤ ‖j 0‖ := hj0_lower
      _ ≤ 2 * (1 - ‖c‖ ^ 2) := by simpa using hlead
      _ = 2 * (1 - θ⁻¹ ^ 2) := by rw [hc_norm]
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hθinv : θ⁻¹ > 10 / 11 := by
    rw [show (10 / 11 : ℝ) = (11 / 10 : ℝ)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 11 / 10) hθpos).2 hθsmall
  have hθinv_le_one : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
  nlinarith

theorem no_pisot_below_eleven_tenths {θ : ℝ} (hθsmall : θ < 11 / 10) :
    ¬ IsPisot1096 θ := by
  rintro ⟨hθ1, hθint, hother⟩
  let p : ℤ[X] := minpoly ℤ θ
  have hpmonic : p.Monic := minpoly.monic hθint
  have hpsep : (p.map (algebraMap ℤ ℂ)).Separable := by
    simpa [p] using minpoly_int_map_complex_separable hθint
  have hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0 := by
    have hr : (p.map (algebraMap ℤ ℝ)).eval θ = 0 := by
      simpa [p, ← eval_map_algebraMap] using minpoly.aeval ℤ θ
    have hc := congrArg (algebraMap ℝ ℂ) hr
    simpa [eval_map, eval₂_map] using hc
  have hp0 : |p.coeff 0| = 1 := by
    simpa [p] using
      pisot_minpoly_coeff_zero_abs_eq_one hθ1 hθsmall hθint hpsep hother
  by_cases hrecip : C (p.coeff 0) * p - p.reverse = 0
  · exact reciprocal_pisot_not_lt hθ1 hθsmall p hpmonic hproot hpsep hother hp0 hrecip
  · exact nonreciprocal_pisot_not_lt hθ1 hθsmall p hpmonic hproot hpsep hother hp0 hrecip
