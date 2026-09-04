import ErdosProblems.Erdos228.KernelNearGeometry
import ErdosProblems.Erdos228.KernelClaims

/-!
# The distant principal-kernel estimate in BBMST Claim 3

This file proves the concrete Claim 3 estimate for a
`OddSine.SuitableIntervalFamily`.  The near collection is the one fixed in
`KernelNearGeometry`; in particular, its complement uses the non-strict
separation `pi / n <= intervalGap theta I`.
-/

namespace Erdos228.KernelDistantClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

/-- The principal (translated sinc) part of the odd kernel on one interval. -/
def principalIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))

/-- Base intervals outside the strict near set.  Thus membership means the
non-strict inequality `pi / n <= intervalGap theta I`. -/
def distantBaseIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type)
    (fun I ↦ ¬Erdos228.KernelNearGeometry.Near n theta I.1)
    (Classical.decPred _) Finset.univ

/-- The distant collection is literally the complement of
`KernelNearGeometry.nearBaseIntervals`. -/
theorem distantBaseIntervals_eq_sdiff {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    distantBaseIntervals F theta =
      Finset.univ \
        Erdos228.KernelNearGeometry.nearBaseIntervals F theta := by
  classical
  ext I
  simp [distantBaseIntervals,
    Erdos228.KernelNearGeometry.nearBaseIntervals]

/-- Endpoint-indexed version of `distantBaseIntervals`. -/
private def distantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval
    (fun I ↦ ¬Erdos228.KernelNearGeometry.Near n theta I)
    (Classical.decPred _) F.base

private lemma sum_distantBaseIntervals_eq_sum_distantIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) (f : RealInterval → ℝ) :
    ∑ I ∈ distantBaseIntervals F theta, f I.1 =
      ∑ I ∈ distantIntervals F theta, f I := by
  classical
  apply Finset.sum_bij (fun I _ ↦ I.1)
  · intro I hI
    simp only [distantBaseIntervals, Finset.mem_filter, Finset.mem_univ,
      true_and] at hI
    simp [distantIntervals, I.property, hI]
  · intro I hI J hJ hIJ
    exact Subtype.ext hIJ
  · intro I hI
    simp only [distantIntervals, Finset.mem_filter] at hI
    refine ⟨⟨I, hI.1⟩, ?_, rfl⟩
    simp [distantBaseIntervals, hI.2]
  · intro I hI
    rfl

private lemma shifted_endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    {I : RealInterval}
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (theta : ℝ) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := hgrid
  rw [ha, hb]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
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

/-- Away from the translated singular point, the sinc presentation is
exactly `sin (2*n*u) / u` after shifting the interval by `theta`. -/
theorem principalIntegral_eq_reciprocal_sine_of_zero_not_mem
    {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ}
    (hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0) :
    principalIntegral n I theta =
      ∫ u in (I.1 - theta)..(I.2 - theta),
        u⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  rw [principalIntegral]
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦ 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u)) theta]
  apply intervalIntegral.integral_congr
  intro u hu
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hu0 := hzero u hu
  change 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) =
    u⁻¹ * Real.sin (2 * (n : ℝ) * u)
  rw [Real.sinc_of_ne_zero (mul_ne_zero hn0 hu0)]
  field_simp [hn0, hu0]

/-- One distant grid interval is controlled by its reciprocal endpoint
variation.  This is the concrete one-interval use of BBMST Lemma 5.9. -/
theorem abs_principalIntegral_le_endpointVariation {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ} (hord : I.1 ≤ I.2)
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (hside : I.2 ≤ theta - Real.pi / n ∨
      theta + Real.pi / n ≤ I.1) :
    |principalIntegral n I theta| ≤
      ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hleftOrRight : I.2 < theta ∨ theta < I.1 := by
    rcases hside with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le (sub_le_sub_right hord theta)] at hu
    rcases hleftOrRight with hleft | hright
    · have : u < 0 := lt_of_le_of_lt hu.2 (sub_neg.mpr hleft)
      exact this.ne
    · have : 0 < u := lt_of_lt_of_le (sub_pos.mpr hright) hu.1
      exact this.ne'
  rw [principalIntegral_eq_reciprocal_sine_of_zero_not_mem hn hzero]
  have hlocal :=
    Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonpos
      (h := fun u : ℝ ↦ u⁻¹) (h' := fun u : ℝ ↦ -(u ^ 2)⁻¹)
      hn (sub_le_sub_right hord theta)
      (fun u hu ↦ hasDerivAt_inv (hzero u (by
        simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (by fun_prop)
        intro u hu
        exact pow_ne_zero 2 (hzero u (by
          simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (fun u hu ↦ neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u)))
      (shifted_endpoint_cos_eq hn hgrid theta)
  have hanti : (I.2 - theta)⁻¹ ≤ (I.1 - theta)⁻¹ := by
    rcases hleftOrRight with hleft | hright
    · exact inv_antitoneOn_Iio
        (show I.1 - theta ∈ Iio 0 by exact sub_neg.mpr (hord.trans_lt hleft))
        (show I.2 - theta ∈ Iio 0 by exact sub_neg.mpr hleft)
        (sub_le_sub_right hord theta)
    · exact inv_antitoneOn_Ioi
        (show I.1 - theta ∈ Ioi 0 by exact sub_pos.mpr hright)
        (show I.2 - theta ∈ Ioi 0 by exact sub_pos.mpr (hright.trans_le hord))
        (sub_le_sub_right hord theta)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti)] at hlocal
  convert hlocal using 1
  ring

/-! ## The finite endpoint telescope -/

private lemma endpoint_variation_le_of_monotone
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex RealInterval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↑t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↑t) : Lex RealInterval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↑t) : Lex RealInterval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).2 else f U
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
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval) := by
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
              (f := fun J : Lex RealInterval ↦
                f (ofLex J).2 - f (ofLex J).1) toLex.injective.injOn)
      _ = ∑ J : ↑t, (f (ofLex (J.1 : Lex RealInterval)).2 -
          f (ofLex (J.1 : Lex RealInterval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex RealInterval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↑t) : Lex RealInterval)).2 -
          f (ofLex ((e i : ↑t) : Lex RealInterval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↑t ↦
              f (ofLex (J.1 : Lex RealInterval)).2 -
                f (ofLex (J.1 : Lex RealInterval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr
      (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 =
        f (ofLex ((e ⟨0, hmpos⟩ : ↑t) : Lex RealInterval)).1 := by
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
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpoint_variation_le_of_monotone s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma pairwise_disjoint_base {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases le_total I.1 J.1 with hle | hle
  · left
    by_contra hnot
    have hJlt : J.1 < I.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne J.1
      ⟨hle, hJlt.le⟩ J.1 ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this
  · right
    by_contra hnot
    have hIlt : I.1 < J.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 ⟨hle, hIlt.le⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this

private def leftDistantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ I.2 ≤ theta)
    (Classical.decPred _) (distantIntervals F theta)

private def rightDistantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ ¬I.2 ≤ theta)
    (Classical.decPred _) (distantIntervals F theta)

private lemma leftDistant_upper {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ leftDistantIntervals F theta) :
    I.2 ≤ theta - Real.pi / n := by
  simp only [leftDistantIntervals, distantIntervals, Finset.mem_filter] at hI
  have hgap : Real.pi / (n : ℝ) ≤
      Erdos228.KernelNearGeometry.intervalGap theta I := by
    exact le_of_not_gt hI.1.2
  rw [Erdos228.KernelNearGeometry.intervalGap_eq_right
    (F.ordered I hI.1.1) hI.2] at hgap
  linarith

private lemma rightDistant_lower {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ rightDistantIntervals F theta) :
    theta + Real.pi / n ≤ I.1 := by
  simp only [rightDistantIntervals, distantIntervals, Finset.mem_filter] at hI
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hright : theta ≤ I.1 := by
    by_contra hnot
    have hleft : I.1 < theta := lt_of_not_ge hnot
    have hright : theta < I.2 := lt_of_not_ge hI.2
    apply hI.1.2
    rw [Erdos228.KernelNearGeometry.Near,
      Erdos228.KernelNearGeometry.intervalGap_eq_zero_of_mem]
    · exact hpiN
    · exact ⟨hleft.le, hright.le⟩
  have hgap : Real.pi / (n : ℝ) ≤
      Erdos228.KernelNearGeometry.intervalGap theta I := by
    exact le_of_not_gt hI.1.2
  rw [Erdos228.KernelNearGeometry.intervalGap_eq_left
    (F.ordered I hI.1.1) hright] at hgap
  linarith

private lemma side_pairwise_disjoint {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (s : Finset RealInterval)
    (hs : s ⊆ F.base) :
    Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  exact pairwise_disjoint_base hn F (hs hI) (hs hJ) hne

private lemma sum_left_endpointVariation_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftDistantIntervals F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := leftDistantIntervals F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta J) ∧ J.2 ≤ theta := by
        simpa only [s, leftDistantIntervals, distantIntervals,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        (0 : ℝ) ≤ J.1 ∧ J.2 ≤ theta - Real.pi / n := by
      intro J hJ
      exact ⟨(F.in_first_quadrant J (hbase J hJ)).1,
        leftDistant_upper hn F (by simpa [s] using hJ)⟩
    have hLU : (0 : ℝ) ≤ theta - Real.pi / n :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpoint_variation_le_of_antitone s
      (fun x : ℝ ↦ (x - theta)⁻¹) 0 (theta - Real.pi / n)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_left (by linarith))
    have hzeroEndpoint : (0 - theta)⁻¹ ≤ 0 :=
      inv_nonpos.mpr (sub_nonpos.mpr htheta.1)
    have hfarEndpoint :
        (theta - Real.pi / (n : ℝ) - theta)⁻¹ =
          -(n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hfarEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ leftDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (0 - theta)⁻¹ - (-(n : ℝ) / Real.pi) := htel
      _ ≤ 0 - (-(n : ℝ) / Real.pi) :=
        sub_le_sub_right hzeroEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : leftDistantIntervals F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp only [Finset.sum_sub_distrib, Finset.sum_empty, sub_self, ge_iff_le]
    positivity

private lemma sum_right_endpointVariation_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightDistantIntervals F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := rightDistantIntervals F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta J) ∧ ¬J.2 ≤ theta := by
        simpa only [s, rightDistantIntervals, distantIntervals,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        theta + Real.pi / n ≤ J.1 ∧ J.2 ≤ Real.pi / 2 := by
      intro J hJ
      exact ⟨rightDistant_lower hn F (by simpa [s] using hJ),
        (F.in_first_quadrant J (hbase J hJ)).2⟩
    have hLU : theta + Real.pi / n ≤ Real.pi / 2 :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpoint_variation_le_of_antitone s
      (fun x : ℝ ↦ (x - theta)⁻¹)
      (theta + Real.pi / n) (Real.pi / 2)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_right (by linarith))
    have hlastEndpoint : 0 ≤ (Real.pi / 2 - theta)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr htheta.2)
    have hnearEndpoint :
        (theta + Real.pi / (n : ℝ) - theta)⁻¹ =
          (n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hnearEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ rightDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (n : ℝ) / Real.pi - (Real.pi / 2 - theta)⁻¹ := htel
      _ ≤ (n : ℝ) / Real.pi - 0 :=
        sub_le_sub_left hlastEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : rightDistantIntervals F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp only [Finset.sum_sub_distrib, Finset.sum_empty, sub_self, ge_iff_le]
    positivity

private lemma sum_left_abs_principalIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta| ≤
        ∑ I ∈ leftDistantIntervals F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta I) ∧ I.2 ≤ theta := by
        simpa only [leftDistantIntervals, distantIntervals,
          Finset.mem_filter] using hI
      exact abs_principalIntegral_le_endpointVariation hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inl (leftDistant_upper hn F hI))
    _ = (∑ I ∈ leftDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (sum_left_endpointVariation_le hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]

private lemma sum_right_abs_principalIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightDistantIntervals F theta, |principalIntegral n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ rightDistantIntervals F theta, |principalIntegral n I theta| ≤
        ∑ I ∈ rightDistantIntervals F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta I) ∧ ¬I.2 ≤ theta := by
        simpa only [rightDistantIntervals, distantIntervals,
          Finset.mem_filter] using hI
      exact abs_principalIntegral_le_endpointVariation hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inr (rightDistant_lower hn F hI))
    _ = (∑ I ∈ rightDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (sum_right_endpointVariation_le hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]

/-- Concrete BBMST Claim 3.  For an evaluation angle in the closed first
quadrant, the total absolute principal-kernel contribution of every base
interval outside the strict near set is at most `2 / pi`. -/
theorem sum_abs_principalIntegral_distant_le_two_div_pi {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ distantBaseIntervals F theta,
        |principalIntegral n I.1 theta| ≤ 2 / Real.pi := by
  classical
  rw [sum_distantBaseIntervals_eq_sum_distantIntervals F theta
    (fun I ↦ |principalIntegral n I theta|)]
  have hsplit :
      (∑ I ∈ distantIntervals F theta, |principalIntegral n I theta|) =
        (∑ I ∈ leftDistantIntervals F theta,
          |principalIntegral n I theta|) +
        ∑ I ∈ rightDistantIntervals F theta,
          |principalIntegral n I theta| := by
    rw [leftDistantIntervals, rightDistantIntervals,
      Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  calc
    (∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta|) +
        ∑ I ∈ rightDistantIntervals F theta,
          |principalIntegral n I theta| ≤
        1 / Real.pi + 1 / Real.pi :=
      add_le_add (sum_left_abs_principalIntegral_le hn F htheta)
        (sum_right_abs_principalIntegral_le hn F htheta)
    _ = 2 / Real.pi := by ring

/-- Short Claim 3 alias. -/
theorem claim3_distant_le_two_div_pi {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ distantBaseIntervals F theta,
        |principalIntegral n I.1 theta| ≤ 2 / Real.pi :=
  sum_abs_principalIntegral_distant_le_two_div_pi hn F htheta

end

end Erdos228.KernelDistantClaim
