import ErdosProblems.Erdos228.OddSine
import ErdosProblems.Erdos228.KernelReplacementMonotone
import ErdosProblems.Erdos228.KernelDistantClaim
import ErdosProblems.Erdos228.KernelReflectedClaim

/-!
# Concrete aggregate kernel estimates for Erdős Problem 228

This file turns the one-interval calculus estimates in `KernelClaims` into
estimates for an actual `OddSine.SuitableIntervalFamily`.  The only
bookkeeping needed for this passage is that a finite separated family of
real intervals can be put in increasing order and its endpoint variations
then telescope.
-/

namespace Erdos228.ConcreteKernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

private abbrev Interval := ℝ × ℝ

/-! ## A finite-family telescope -/

theorem endpoint_variation_le_of_monotone
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
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) = ∑ k ∈ Finset.range m, E k := by
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

theorem endpoint_variation_le_of_antitone
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

/-! ## Claim 2: replacement of `sin u` by `u` -/

/-- The removable denominator-replacement contribution on one base interval. -/
def replacementIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta) *
      Real.sin ((2 * (n : ℝ)) * (x - theta))

private lemma endpointSeparated {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 :=
      ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 :=
      ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private lemma shifted_mem_half {n : ℕ} (F : SuitableIntervalFamily n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 - theta) (I.2 - theta)) :
    u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hquadrant := F.in_first_quadrant I hI
  constructor
  · linarith [hu.1, hquadrant.1, htheta.2]
  · linarith [hu.2, hquadrant.2, htheta.1]

private lemma shifted_endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  calc
    Real.cos ((2 * (n : ℝ)) * ((b : ℝ) * Real.pi / n - theta)) =
        Real.cos ((b : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) := by
          congr 1
          field_simp [hn0]
    _ = Real.cos ((2 * (n : ℝ)) * theta) :=
      Real.cos_int_mul_two_pi_sub _ b
    _ = Real.cos ((a : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) :=
      (Real.cos_int_mul_two_pi_sub _ a).symm
    _ = Real.cos ((2 * (n : ℝ)) * ((a : ℝ) * Real.pi / n - theta)) := by
          congr 1
          field_simp [hn0]

private lemma replacementIntegral_shifted (n : ℕ) (I : RealInterval)
    (theta : ℝ) :
    replacementIntegral n I theta =
      ∫ u in I.1 - theta..I.2 - theta,
        Erdos228.KernelReplacementMonotone.replacementAmplitude u *
          Real.sin ((2 * (n : ℝ)) * u) := by
  exact intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦
      Erdos228.KernelReplacementMonotone.replacementAmplitude u *
        Real.sin ((2 * (n : ℝ)) * u)) theta

private lemma abs_replacementIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) :
    |replacementIntegral n I theta| ≤
      (Erdos228.KernelReplacementMonotone.replacementAmplitude (I.2 - theta) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (I.1 - theta)) / n := by
  rw [replacementIntegral_shifted]
  have hdata :=
    Erdos228.KernelReplacementMonotone.replacementAmplitude_derivative_data
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonneg
    (h := Erdos228.KernelReplacementMonotone.replacementAmplitude)
    (h' := deriv Erdos228.KernelReplacementMonotone.replacementAmplitude)
    hn (sub_le_sub_right (F.ordered I hI) theta)
    (fun u hu ↦ hdata.1 u (shifted_mem_half F htheta hI hu))
    (hdata.2.1.mono (fun u hu ↦ shifted_mem_half F htheta hI hu))
    (fun u hu ↦ hdata.2.2 u (shifted_mem_half F htheta hI hu))
    (shifted_endpoint_cos_eq hn F hI)
  have hmono := Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
    (shifted_mem_half F htheta hI
      ⟨le_rfl, sub_le_sub_right (F.ordered I hI) theta⟩)
    (shifted_mem_half F htheta hI
      ⟨sub_le_sub_right (F.ordered I hI) theta, le_rfl⟩)
    (sub_le_sub_right (F.ordered I hI) theta)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hosc
  exact hosc

/-- Claim 2, aggregated over the concrete suitable interval family. -/
theorem sum_abs_replacementIntegral_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ F.base, |replacementIntegral n I theta| ≤
      (2 - 4 / Real.pi) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let f : ℝ → ℝ := fun x ↦
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta)
  have hfmono : MonotoneOn f (Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
      ⟨by linarith [hx.1, htheta.2], by linarith [hx.2, htheta.1]⟩
      ⟨by linarith [hy.1, htheta.2], by linarith [hy.2, htheta.1]⟩
      (sub_le_sub_right hxy theta)
  have htel := endpoint_variation_le_of_monotone F.base f 0 (Real.pi / 2)
    F.nondegenerate (by positivity) F.in_first_quadrant
    (endpointSeparated hn0 F) hfmono
  have hglobal : f (Real.pi / 2) - f 0 ≤
      Erdos228.KernelReplacementMonotone.replacementAmplitude (Real.pi / 2) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (-(Real.pi / 2)) := by
    apply sub_le_sub
    · exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
        ⟨by linarith [htheta.2, Real.pi_pos], by linarith [htheta.1]⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ (by linarith [htheta.1])
    · exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
        ⟨le_rfl, by linarith [Real.pi_pos]⟩
        ⟨by linarith [htheta.2], by linarith [htheta.1, Real.pi_pos]⟩
        (by linarith [htheta.2])
  calc
    ∑ I ∈ F.base, |replacementIntegral n I theta| ≤
        ∑ I ∈ F.base, (f I.2 - f I.1) / n := by
          apply Finset.sum_le_sum
          intro I hI
          exact abs_replacementIntegral_le hn0 F htheta hI
    _ = (∑ I ∈ F.base, (f I.2 - f I.1)) / n := by
          rw [Finset.sum_div]
    _ ≤ (f (Real.pi / 2) - f 0) / n := by
          exact div_le_div_of_nonneg_right htel (Nat.cast_nonneg n)
    _ ≤ (Erdos228.KernelReplacementMonotone.replacementAmplitude (Real.pi / 2) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (-(Real.pi / 2))) / n := by
          exact div_le_div_of_nonneg_right hglobal (Nat.cast_nonneg n)
    _ = (2 - 4 / Real.pi) / n := by
          rw [Erdos228.KernelReplacementMonotone.replacementAmplitude_endpoint_variation]

/-- Subtype-indexed form of the aggregate Claim 2 estimate. -/
theorem sum_abs_replacementIntegral_subtype_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |replacementIntegral n I.1 theta| ≤
      (2 - 4 / Real.pi) / n := by
  rw [Finset.univ_eq_attach]
  calc
    ∑ I ∈ F.base.attach, |replacementIntegral n I.1 theta| =
        ∑ I ∈ F.base, |replacementIntegral n I theta| :=
      Finset.sum_attach F.base (fun I ↦ |replacementIntegral n I theta|)
    _ ≤ (2 - 4 / Real.pi) / n :=
      sum_abs_replacementIntegral_le hn F htheta

/-! ## Exact per-interval decomposition -/

/-- The quotient form of the odd kernel integrated over one interval. -/
def quotientIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
      Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta))

private lemma quotientFirst_eq_principal_add_replacement {n : ℕ} (hn : 0 < n)
    {u : ℝ} (huHalf : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu : u ≠ 0) :
    Real.sin ((2 * n : ℕ) * u) / Real.sin u =
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) +
        Erdos228.KernelReplacementMonotone.replacementAmplitude u *
          Real.sin (2 * (n : ℝ) * u) := by
  have hsin := Erdos228.KernelReplacementMonotone.sin_ne_zero_of_mem_half
    huHalf hu
  have hscale : (2 * (n : ℝ)) ≠ 0 := by positivity
  have harg : 2 * (n : ℝ) * u ≠ 0 := mul_ne_zero hscale hu
  rw [Real.sinc_of_ne_zero harg,
    Erdos228.KernelReplacementMonotone.replacementAmplitude_eq hu hsin]
  norm_cast
  field_simp [hu, hsin, hscale]
  ring

/-- Exact decomposition of one integrated quotient kernel into its
principal, denominator-replacement, and reflected pieces. -/
theorem quotientIntegral_eq_principal_add_replacement_sub_reflected
    {n : ℕ} (hn : 0 < n) (F : SuitableIntervalFamily n)
    {I : RealInterval} (hI : I ∈ F.base) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    quotientIntegral n I theta =
      Erdos228.KernelDistantClaim.principalIntegral n I theta +
        replacementIntegral n I theta -
          Erdos228.KernelReflectedClaim.reflectedIntegral n I theta := by
  let p : ℝ → ℝ := fun x ↦
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))
  let r : ℝ → ℝ := fun x ↦
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta) *
      Real.sin (2 * (n : ℝ) * (x - theta))
  let q : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta)
  let s : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)
  have hord := F.ordered I hI
  have hpint : IntervalIntegrable p volume I.1 I.2 := by
    apply Continuous.intervalIntegrable
    dsimp [p]
    fun_prop
  have hrcont : ContinuousOn r (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hxHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    have hamp : ContinuousAt
        (fun y : ℝ ↦
          Erdos228.KernelReplacementMonotone.replacementAmplitude (y - theta)) x := by
      have hsub : ContinuousAt (fun y : ℝ ↦ y - theta) x :=
        continuousAt_id.sub continuousAt_const
      simpa only [Function.comp_def] using
        (Erdos228.KernelReplacementMonotone.analyticAt_replacementAmplitude
          hxHalf).continuousAt.comp_of_eq hsub rfl
    exact (hamp.mul (by fun_prop)).continuousWithinAt
  have hrint : IntervalIntegrable r volume I.1 I.2 := hrcont.intervalIntegrable
  have hscont : ContinuousOn s (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
    have haxes := F.away_from_axes I hI
    have hsumPos : 0 < x + theta := by
      linarith [hxI.1, haxes.1, htheta.1]
    have hsumLt : x + theta < Real.pi := by
      linarith [hxI.2, haxes.2, htheta.2]
    have hsin : Real.sin (x + theta) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsumPos hsumLt)
    have hnum : ContinuousAt
        (fun y : ℝ ↦ Real.sin ((2 * n : ℕ) * (y + theta))) x := by
      fun_prop
    have hden : ContinuousAt (fun y : ℝ ↦ Real.sin (y + theta)) x := by
      fun_prop
    exact (hnum.div hden hsin).continuousWithinAt
  have hsint : IntervalIntegrable s volume I.1 I.2 := hscont.intervalIntegrable
  have hqr : ∀ᵐ x ∂volume, x ∈ uIoc I.1 I.2 → q x = p x + r x := by
    filter_upwards [Measure.ae_ne volume theta] with x hxt hx
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact quotientFirst_eq_principal_add_replacement hn huHalf hu
  have hqrRestrict : p + r =ᵐ[volume.restrict (uIoc I.1 I.2)] q := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume theta)] with x hx hxt
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact (quotientFirst_eq_principal_add_replacement hn huHalf hu).symm
  have hqint : IntervalIntegrable q volume I.1 I.2 :=
    (hpint.add hrint).congr_ae hqrRestrict
  have hfirst : (∫ x in I.1..I.2, q x) =
      (∫ x in I.1..I.2, p x) + ∫ x in I.1..I.2, r x := by
    rw [intervalIntegral.integral_congr_ae hqr,
      intervalIntegral.integral_add hpint hrint]
  rw [quotientIntegral, show (fun x : ℝ ↦
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) =
      fun x ↦ q x - s x by rfl,
    intervalIntegral.integral_sub hqint hsint, hfirst]
  rfl

/-! ## Explicit numerical absorption -/

/-- At the concrete threshold used by the odd construction, the sum of the
three sharp error bounds is at most `2 / 3`. -/
theorem total_kernel_error_le_two_thirds {n : ℕ} (hn : 4096 ≤ n) :
    2 / Real.pi + 2 / (n * Real.sin (100 * Real.pi / n)) +
        12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let x : ℝ := 100 * Real.pi / n
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 10 := by
    rw [show x = 100 * Real.pi / n by rfl, div_le_iff₀ hnpos]
    nlinarith [Real.pi_lt_four]
  have hxsq : x ^ 2 ≤ 1 / 100 := by nlinarith [sq_nonneg x]
  have hsin0 := Real.sin_ge_sub_cube hxpos.le
  have hsin : (99 / 100) * x ≤ Real.sin x := by
    nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hxsq)]
  have hden : 300 ≤ (n : ℝ) * Real.sin x := by
    calc
      (300 : ℝ) ≤ 99 * Real.pi := by
        nlinarith [Real.pi_gt_d2]
      _ = (n : ℝ) * ((99 / 100) * x) := by
        dsimp [x]
        field_simp [hn0]
      _ ≤ (n : ℝ) * Real.sin x := mul_le_mul_of_nonneg_left hsin hnpos.le
  have hdenpos : 0 < (n : ℝ) * Real.sin x := lt_of_lt_of_le (by norm_num) hden
  have hreflectedPole : 2 / ((n : ℝ) * Real.sin x) ≤ 1 / 150 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hprincipal : 2 / Real.pi ≤ 100 / 157 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d2]
  have hcrossing : 12 * Real.pi / (n : ℝ) ≤ 189 / 20480 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith [Real.pi_lt_d2]
  have hreplacement : (2 - 4 / Real.pi) / (n : ℝ) ≤ 1 / 2048 := by
    apply (div_le_iff₀ hnpos).2
    have : 0 ≤ 4 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
    nlinarith
  change 2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
      12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3
  calc
    2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
          12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤
        100 / 157 + 1 / 150 + 189 / 20480 + 1 / 2048 := by linarith
    _ ≤ 2 / 3 := by norm_num

/-! ## The combined signed residual -/

/-- Claims 1--3 combined in the exact form used by the normalized odd-kernel
assembly: after retaining the principal kernel only on the strict near set,
the entire signed residual has absolute value at most `2 / 3`. -/
theorem signed_kernel_residual_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |(∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) -
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta)| ≤
      2 / 3 := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let principal : (↑F.base : Type) → ℝ := fun I ↦
    Erdos228.KernelDistantClaim.principalIntegral n I.1 theta
  let replacement : (↑F.base : Type) → ℝ := fun I ↦
    replacementIntegral n I.1 theta
  let reflected : (↑F.base : Type) → ℝ := fun I ↦
    Erdos228.KernelReflectedClaim.reflectedIntegral n I.1 theta
  have halphaAbs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  have hquotient :
      (∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) =
        (∑ I : (↑F.base : Type), alpha I * principal I) +
          (∑ I : (↑F.base : Type), alpha I * replacement I) -
            ∑ I : (↑F.base : Type), alpha I * reflected I := by
    simp_rw [quotientIntegral_eq_principal_add_replacement_sub_reflected
      hn0 F (hI := Subtype.property _) htheta]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rfl
  have hpartition :
      (∑ I : (↑F.base : Type), alpha I * principal I) =
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I) +
        ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I := by
    rw [Erdos228.KernelDistantClaim.distantBaseIntervals_eq_sdiff]
    calc
      (∑ I : (↑F.base : Type), alpha I * principal I) =
          (∑ I ∈ Finset.univ \
              Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I) +
          ∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I :=
        (Finset.sum_sdiff
          (Finset.subset_univ
            (Erdos228.KernelNearGeometry.nearBaseIntervals F theta))).symm
      _ = (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I) +
          ∑ I ∈ Finset.univ \
              Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I := add_comm _ _
  have hresidual :
      (∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) -
          (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta) =
        (∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I := by
    rw [hquotient, hpartition]
    dsimp only [principal]
    ring
  have hprincipal :
      |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| ≤ 2 / Real.pi := by
    calc
      |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| ≤
          ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
            |alpha I * principal I| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
            |principal I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / Real.pi :=
        Erdos228.KernelDistantClaim.sum_abs_principalIntegral_distant_le_two_div_pi
          hn0 F htheta
  have hreplacement :
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
        (2 - 4 / Real.pi) / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
          ∑ I : (↑F.base : Type), |alpha I * replacement I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |replacement I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ (2 - 4 / Real.pi) / n :=
        sum_abs_replacementIntegral_subtype_le hn F htheta
  have hreflected :
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
          ∑ I : (↑F.base : Type), |alpha I * reflected I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |reflected I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n :=
        Erdos228.KernelReflectedClaim.sum_abs_reflectedIntegral_le hn F htheta
  rw [hresidual]
  calc
    |(∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| +
        |∑ I : (↑F.base : Type), alpha I * replacement I| +
        |∑ I : (↑F.base : Type), alpha I * reflected I| := by
          linarith [abs_add_le
            (∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
              alpha I * principal I)
            (∑ I : (↑F.base : Type), alpha I * replacement I),
            abs_sub
              ((∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
                alpha I * principal I) +
                ∑ I : (↑F.base : Type), alpha I * replacement I)
              (∑ I : (↑F.base : Type), alpha I * reflected I)]
    _ ≤ 2 / Real.pi + (2 - 4 / Real.pi) / n +
        (2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n) := by linarith
    _ ≤ 2 / 3 := by
      linarith [total_kernel_error_le_two_thirds hn]

end

end Erdos228.ConcreteKernelClaims
