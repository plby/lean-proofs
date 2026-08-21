import ErdosProblems.Erdos228.OddSine

/-!
# The reflected-denominator estimate in BBMST Claim 1

The endpoints of every suitable interval lie on the `pi / n` grid.  After
translation by `theta`, the endpoint cosines in integration by parts are
therefore still equal.  The amplitude `1 / sin` is antitone to the left of
`pi / 2` and monotone to its right.  Non-strict separation is enough to
order and telescope the intervals on each side.  At most one interval
crosses the turning point, and shortness bounds that contribution directly.
-/

namespace Erdos228.KernelReflectedClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

/-- The reflected odd-kernel contribution of one base interval. -/
def reflectedIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta)

private def eta (n : ℕ) : ℝ := 100 * Real.pi / n

private def amplitude (theta x : ℝ) : ℝ := (Real.sin (x + theta))⁻¹

private def turningPoint (theta : ℝ) : ℝ := Real.pi / 2 - theta

private noncomputable def leftIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.2 ≤ turningPoint theta

private noncomputable def rightIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ turningPoint theta ≤ I.1

private noncomputable def crossingIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.1 < turningPoint theta ∧ turningPoint theta < I.2

private lemma eta_pos {n : ℕ} (hn : 0 < n) : 0 < eta n := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hn)

private lemma eta_le_pi_div_two {n : ℕ} (hn : 4096 ≤ n) :
    eta n ≤ Real.pi / 2 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  dsimp [eta]
  apply (div_le_iff₀ hnpos).2
  nlinarith [Real.pi_pos]

private lemma shifted_mem_band {n : ℕ} (F : SuitableIntervalFamily n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    eta n ≤ x + theta ∧ x + theta ≤ Real.pi - eta n := by
  have haway := F.away_from_axes I hI
  constructor
  · exact (show eta n ≤ I.1 from haway.1) |>.trans hx.1 |>.trans
      (le_add_of_nonneg_right htheta.1)
  · exact (add_le_add hx.2 htheta.2).trans
      (show I.2 + Real.pi / 2 ≤ Real.pi - eta n by
        dsimp [eta]
        linarith [haway.2])

private lemma sin_shifted_pos {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) : 0 < Real.sin (x + theta) := by
  have hband := shifted_mem_band F htheta hI hx
  have heta := eta_pos hn
  exact Real.sin_pos_of_pos_of_lt_pi (heta.trans_le hband.1)
    (by linarith [hband.2, heta])

private lemma sin_pos_of_mem_shifted_interval {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 + theta) (I.2 + theta)) :
    0 < Real.sin u := by
  have hx : u - theta ∈ Icc I.1 I.2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa only [sub_add_cancel] using
    sin_shifted_pos hn F htheta hI hx

private lemma sin_eta_le_sin_shifted {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    Real.sin (eta n) ≤ Real.sin (x + theta) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have heta0 := (eta_pos hn0).le
  have hetahalf := eta_le_pi_div_two hn
  have hband := shifted_mem_band F htheta hI hx
  by_cases hhalf : x + theta ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [heta0, Real.pi_pos]) hhalf hband.1
  · have hcompHalf : Real.pi - (x + theta) ≤ Real.pi / 2 := by
      linarith
    have hcompLow : eta n ≤ Real.pi - (x + theta) := by
      linarith [hband.2]
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := eta n) (y := Real.pi - (x + theta))
      (by linarith [heta0, Real.pi_pos]) hcompHalf hcompLow
    simpa only [Real.sin_pi_sub] using h

private lemma amplitude_le_inv_sin_eta {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    amplitude theta x ≤ 1 / Real.sin (eta n) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsineta : 0 < Real.sin (eta n) :=
    Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
      ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
  simpa only [amplitude, one_div] using
    one_div_le_one_div_of_le hsineta
      (sin_eta_le_sin_shifted hn F htheta hI hx)

private lemma endpointSeparated {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) := by
    exact div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 := ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 := ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private abbrev Interval := ℝ × ℝ

/-- Endpoint variations of a finite separated family telescope on a
monotone branch. -/
private lemma endpoint_variation_le_of_monotone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Interval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Interval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Interval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Erdos228.KernelClaims.sum_interval_error_le_of_monotone_endpoints
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (Finset.sum_image (s := s)
              (f := fun J : Lex Interval ↦ f (ofLex J).2 - f (ofLex J).1)
              toLex.injective.injOn)
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Interval)).2 -
          f (ofLex (J.1 : Lex Interval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Interval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Interval)).2 -
          f (ofLex ((e i : ↥t) : Lex Interval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Interval)).2 -
                f (ofLex (J.1 : Lex Interval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Interval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

private lemma endpoint_variation_le_of_antitone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpoint_variation_le_of_monotone s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 + theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 + theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  have hphase (k : ℤ) :
      (2 * (n : ℝ)) * ((k : ℝ) * Real.pi / n + theta) =
        (2 * (n : ℝ)) * theta + (k : ℝ) * (2 * Real.pi) := by
    field_simp [hnR]
    ring
  rw [hphase a, hphase b, Real.cos_add_int_mul_two_pi,
    Real.cos_add_int_mul_two_pi]

private lemma shifted_integral_eq {n : ℕ} (I : RealInterval) (theta : ℝ) :
    reflectedIntegral n I theta =
      ∫ u in I.1 + theta..I.2 + theta,
        (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u : ℝ ↦ (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u))
    theta (a := I.1) (b := I.2)
  rw [← hshift]
  unfold reflectedIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  ring

private lemma local_left_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ leftIntervals F theta) :
    |reflectedIntegral n I theta| ≤
      (amplitude theta I.1 - amplitude theta I.2) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : I.2 ≤ turningPoint theta := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonpos : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      -Real.cos u / Real.sin u ^ 2 ≤ 0 := by
    intro u hu
    have huHalf : u ≤ Real.pi / 2 := by
      dsimp [turningPoint] at hside
      linarith [hu.2]
    have huNonneg : -(Real.pi / 2) ≤ u := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := shifted_mem_band F htheta hbase hx
      linarith [hband.1, eta_pos hn0, Real.pi_pos]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc ⟨huNonneg, huHalf⟩))
      (sq_nonneg _)
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonpos
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonpos (endpoint_cos_eq hn0 F hbase)
  rw [shifted_integral_eq]
  have hamp : amplitude theta I.2 ≤ amplitude theta I.1 := by
    have hsinA : 0 < Real.sin (I.1 + theta) :=
      sin_shifted_pos hn0 F htheta hbase ⟨le_rfl, F.ordered I hbase⟩
    have hbandA := shifted_mem_band F htheta hbase
      ⟨le_rfl, F.ordered I hbase⟩
    have hsinmono : Real.sin (I.1 + theta) ≤ Real.sin (I.2 + theta) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hbandA.1, eta_pos hn0, Real.pi_pos])
        (by dsimp [turningPoint] at hside; linarith)
        (by linarith [F.ordered I hbase])
    simpa only [amplitude, one_div] using
      one_div_le_one_div_of_le hsinA hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.2 + theta))⁻¹ ≤
      (Real.sin (I.1 + theta))⁻¹ := by simpa only [amplitude] using hamp
  rw [abs_of_nonpos (sub_nonpos.mpr hamp')] at hosc
  simpa only [amplitude, neg_sub] using hosc

private lemma local_right_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ rightIntervals F theta) :
    |reflectedIntegral n I theta| ≤
      (amplitude theta I.2 - amplitude theta I.1) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : turningPoint theta ≤ I.1 := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonneg : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      0 ≤ -Real.cos u / Real.sin u ^ 2 := by
    intro u hu
    have huHalf : Real.pi / 2 ≤ u := by
      dsimp [turningPoint] at hside
      linarith [hu.1]
    have huTop : u ≤ Real.pi + Real.pi / 2 := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := shifted_mem_band F htheta hbase hx
      linarith [hband.2, eta_pos hn0, Real.pi_pos]
    exact div_nonneg (neg_nonneg.mpr
      (Real.cos_nonpos_of_pi_div_two_le_of_le huHalf huTop)) (sq_nonneg _)
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonneg
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonneg (endpoint_cos_eq hn0 F hbase)
  rw [shifted_integral_eq]
  have hamp : amplitude theta I.1 ≤ amplitude theta I.2 := by
    have hsinB : 0 < Real.sin (I.2 + theta) :=
      sin_shifted_pos hn0 F htheta hbase ⟨F.ordered I hbase, le_rfl⟩
    have hcompOrder : Real.pi - (I.2 + theta) ≤
        Real.pi - (I.1 + theta) := by linarith [F.ordered I hbase]
    have hcompTop : Real.pi - (I.1 + theta) ≤ Real.pi / 2 := by
      dsimp [turningPoint] at hside
      linarith
    have hcompLow : -(Real.pi / 2) ≤ Real.pi - (I.2 + theta) := by
      have hband := shifted_mem_band F htheta hbase
        ⟨F.ordered I hbase, le_rfl⟩
      linarith [hband.2, eta_pos hn0, Real.pi_pos]
    have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      hcompLow hcompTop hcompOrder
    rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
    simpa only [amplitude, one_div] using
      one_div_le_one_div_of_le hsinB hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.1 + theta))⁻¹ ≤
      (Real.sin (I.2 + theta))⁻¹ := by simpa only [amplitude] using hamp
  rw [abs_of_nonneg (sub_nonneg.mpr hamp')] at hosc
  simpa only [amplitude] using hosc

private lemma amplitude_antitone_left {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hbranch : eta n ≤ turningPoint theta) :
    AntitoneOn (amplitude theta) (Icc (eta n) (turningPoint theta)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinX : 0 < Real.sin (x + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1, eta_pos hn0, htheta.1]
    · dsimp [turningPoint] at hy
      linarith [hy.2, Real.pi_pos]
  have hsinmono : Real.sin (x + theta) ≤ Real.sin (y + theta) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1, eta_pos hn0, htheta.1, Real.pi_pos])
      (by dsimp [turningPoint] at hy; linarith [hy.2])
      (by linarith)
  simpa only [amplitude, one_div] using
    one_div_le_one_div_of_le hsinX hsinmono

private lemma amplitude_monotone_right {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hbranch : turningPoint theta ≤ Real.pi / 2 - eta n) :
    MonotoneOn (amplitude theta)
      (Icc (turningPoint theta) (Real.pi / 2 - eta n)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinY : 0 < Real.sin (y + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [turningPoint] at hx
      linarith [hx.1, Real.pi_pos]
    · linarith [hy.2, eta_pos hn0, htheta.2]
  have hcompOrder : Real.pi - (y + theta) ≤ Real.pi - (x + theta) := by
    linarith
  have hcompTop : Real.pi - (x + theta) ≤ Real.pi / 2 := by
    dsimp [turningPoint] at hx
    linarith [hx.1]
  have hcompLow : -(Real.pi / 2) ≤ Real.pi - (y + theta) := by
    linarith [hy.2, eta_pos hn0, htheta.2, Real.pi_pos]
  have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    hcompLow hcompTop hcompOrder
  rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
  simpa only [amplitude, one_div] using
    one_div_le_one_div_of_le hsinY hsinmono

private lemma sum_left_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : eta n ≤ turningPoint theta
  · have hvar := endpoint_variation_le_of_antitone
      (leftIntervals F theta) (amplitude theta) (eta n) (turningPoint theta)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(F.away_from_axes I (Finset.mem_filter.mp hI).1).1,
        (Finset.mem_filter.mp hI).2⟩)
      (fun I hI J hJ hne ↦ endpointSeparated hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (amplitude_antitone_left hn htheta hbranch)
    have hturn : amplitude theta (turningPoint theta) = 1 := by
      simp [amplitude, turningPoint]
    have hampEta : amplitude theta (eta n) ≤ 1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
      have hsinmono : Real.sin (eta n) ≤ Real.sin (eta n + theta) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [eta_pos hn0, Real.pi_pos])
          (by dsimp [turningPoint] at hbranch; linarith)
          (by linarith [htheta.1])
      simpa only [amplitude, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta| ≤
          ∑ I ∈ leftIntervals F theta,
            (amplitude theta I.1 - amplitude theta I.2) / n :=
        Finset.sum_le_sum fun I hI ↦ local_left_bound hn F htheta hI
      _ = (∑ I ∈ leftIntervals F theta,
            (amplitude theta I.1 - amplitude theta I.2)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : leftIntervals F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).1
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turningPoint] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma sum_right_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : turningPoint theta ≤ Real.pi / 2 - eta n
  · have hvar := endpoint_variation_le_of_monotone
      (rightIntervals F theta) (amplitude theta) (turningPoint theta)
        (Real.pi / 2 - eta n)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(Finset.mem_filter.mp hI).2,
        (F.away_from_axes I (Finset.mem_filter.mp hI).1).2⟩)
      (fun I hI J hJ hne ↦ endpointSeparated hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (amplitude_monotone_right hn htheta hbranch)
    have hturn : amplitude theta (turningPoint theta) = 1 := by
      simp [amplitude, turningPoint]
    have hampU : amplitude theta (Real.pi / 2 - eta n) ≤
        1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
      have hcompOrder : eta n ≤
          Real.pi - ((Real.pi / 2 - eta n) + theta) := by
        linarith [htheta.2]
      have hcompTop : Real.pi - ((Real.pi / 2 - eta n) + theta) ≤
          Real.pi / 2 := by
        dsimp [turningPoint] at hbranch
        linarith
      have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := eta n)
        (y := Real.pi - ((Real.pi / 2 - eta n) + theta))
        (by linarith [eta_pos hn0, Real.pi_pos]) hcompTop hcompOrder
      rw [Real.sin_pi_sub] at hsinmono
      simpa only [amplitude, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta| ≤
          ∑ I ∈ rightIntervals F theta,
            (amplitude theta I.2 - amplitude theta I.1) / n :=
        Finset.sum_le_sum fun I hI ↦ local_right_bound hn F htheta hI
      _ = (∑ I ∈ rightIntervals F theta,
            (amplitude theta I.2 - amplitude theta I.1)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : rightIntervals F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).2
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turningPoint] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma crossing_pointwise_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ crossingIntervals F theta) :
    |reflectedIntegral n I theta| ≤ 12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hcross := (Finset.mem_filter.mp hI).2
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := I.1) (b := I.2) (C := (2 : ℝ))
    (f := fun x : ℝ ↦
      Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta))
    (fun x hx ↦ by
      rw [Set.uIoc_of_le (F.ordered I hbase)] at hx
      have hxI : x ∈ Icc I.1 I.2 := ⟨hx.1.le, hx.2⟩
      have hdist : |(x + theta) - Real.pi / 2| ≤ 6 * Real.pi / n := by
        have hwidth := F.short I hbase
        dsimp [turningPoint] at hcross
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2]
      have hsmall : |(x + theta) - Real.pi / 2| ≤ 1 := by
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hfrac : 6 * Real.pi / (n : ℝ) < 1 := by
          apply (div_lt_iff₀ hnRpos).2
          nlinarith
        exact hdist.trans hfrac.le
      have hcos : (1 : ℝ) / 2 ≤ Real.cos ((x + theta) - Real.pi / 2) := by
        have hlow := Real.one_sub_sq_div_two_le_cos
          (x := (x + theta) - Real.pi / 2)
        have hsq : ((x + theta) - Real.pi / 2) ^ 2 ≤ 1 := by
          have habs0 : 0 ≤ |(x + theta) - Real.pi / 2| := abs_nonneg _
          nlinarith [sq_abs ((x + theta) - Real.pi / 2)]
        linarith
      have hsin : (1 : ℝ) / 2 ≤ Real.sin (x + theta) := by
        rw [← Real.cos_sub_pi_div_two]
        exact hcos
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by linarith : 0 ≤ Real.sin (x + theta))]
      apply (div_le_iff₀ (by linarith : 0 < Real.sin (x + theta))).2
      nlinarith [Real.abs_sin_le_one
        (((2 * n : ℕ) : ℝ) * (x + theta))])
  unfold reflectedIntegral
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ x in I.1..I.2,
        Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) /
          Real.sin (x + theta)| ≤ 2 * |I.2 - I.1| := hnorm
    _ = 2 * (I.2 - I.1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (F.ordered I hbase))]
    _ ≤ 2 * (6 * Real.pi / n) := by
      gcongr
      exact F.short I hbase
    _ = 12 * Real.pi / n := by ring

private lemma card_crossing_le_one {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (crossingIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  have hbaseI := (Finset.mem_filter.mp hI).1
  have hbaseJ := (Finset.mem_filter.mp hJ).1
  by_contra hne
  have hcrossI := (Finset.mem_filter.mp hI).2
  have hcrossJ := (Finset.mem_filter.mp hJ).2
  have hsep := F.separated hbaseI hbaseJ hne (turningPoint theta)
    ⟨hcrossI.1.le, hcrossI.2.le⟩ (turningPoint theta)
    ⟨hcrossJ.1.le, hcrossJ.2.le⟩
  have hpi : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
  exact (not_le_of_gt hpi) this

private lemma sum_crossing_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
      12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
        ∑ _I ∈ crossingIntervals F theta, 12 * Real.pi / n :=
      Finset.sum_le_sum fun I hI ↦ crossing_pointwise_bound hn F htheta hI
    _ = ((crossingIntervals F theta).card : ℝ) * (12 * Real.pi / n) := by simp
    _ ≤ 1 * (12 * Real.pi / n) := by
      gcongr
      exact_mod_cast card_crossing_le_one hn0 F theta
    _ = 12 * Real.pi / n := one_mul _

private lemma base_partition {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    F.base = (leftIntervals F theta ∪ rightIntervals F theta) ∪
      crossingIntervals F theta := by
  classical
  ext I
  simp only [leftIntervals, rightIntervals, crossingIntervals, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · intro hI
    by_cases hleft : I.2 ≤ turningPoint theta
    · exact Or.inl (Or.inl ⟨hI, hleft⟩)
    · by_cases hright : turningPoint theta ≤ I.1
      · exact Or.inl (Or.inr ⟨hI, hright⟩)
      · exact Or.inr ⟨hI, lt_of_not_ge hright, lt_of_not_ge hleft⟩
  · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩) <;> exact hI

private lemma disjoint_left_right {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Disjoint (leftIntervals F theta) (rightIntervals F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hleft hright
  have hbase := (Finset.mem_filter.mp hleft).1
  have hstrict := F.nondegenerate I hbase
  linarith [(Finset.mem_filter.mp hleft).2, (Finset.mem_filter.mp hright).2]

private lemma disjoint_sides_crossing {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) :
    Disjoint (leftIntervals F theta ∪ rightIntervals F theta)
      (crossingIntervals F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hsides hcross
  simp only [Finset.mem_union] at hsides
  have hc := (Finset.mem_filter.mp hcross).2
  rcases hsides with hleft | hright
  · linarith [(Finset.mem_filter.mp hleft).2, hc.2]
  · linarith [(Finset.mem_filter.mp hright).2, hc.1]

/-- Concrete BBMST Claim 1 for a suitable interval family.  The two
monotone tails telescope to one reciprocal-sine endpoint each, and the
unique interval crossing `pi / 2 - theta` costs at most `12*pi/n`. -/
theorem sum_abs_reflectedIntegral_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |reflectedIntegral n I.1 theta| ≤
      2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) + 12 * Real.pi / n := by
  classical
  rw [← Finset.sum_subtype F.base (by simp)
    (fun I ↦ |reflectedIntegral n I theta|)]
  rw [base_partition F theta,
    Finset.sum_union (disjoint_sides_crossing F theta),
    Finset.sum_union (disjoint_left_right F theta)]
  have hleft := sum_left_le hn F htheta
  have hright := sum_right_le hn F htheta
  have hcross := sum_crossing_le hn F htheta
  dsimp [eta] at hleft hright
  calc
    (∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta|) +
          (∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta|) +
        ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
        1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by linarith
    _ = 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by ring

end

end Erdos228.KernelReflectedClaim
