import Arxiv.Arxiv2407_19026.BookAsymptotics

/-!
# From the book induction to a graph Ramsey bound

This file formalizes Theorem `t:bookCor`.
-/

noncomputable section

open Finset

namespace Arxiv2407_19026

/-- Red-edge density among all unordered pairs.  Both numerator and
denominator are written in their ordered-pair form. -/
def globalRedDensity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (redEdgesBetween G Finset.univ Finset.univ : ℝ) /
    ((Fintype.card V : ℝ) * (Fintype.card V - 1))

/-- A strict limiting inequality remains true after decreasing the
density parameter slightly. -/
lemma exists_density_slack {x μ p : ℝ}
    (hμ1 : μ < 1) (hp : 0 < p)
    (h :
      x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ)) :
    ∃ q : ℝ, 0 < q ∧ q < p ∧
      x < q ^ ((1 : ℝ) / (1 - μ)) * (1 - μ) := by
  let F : ℝ → ℝ := fun q ↦
    q ^ ((1 : ℝ) / (1 - μ)) * (1 - μ)
  have hcont : ContinuousAt F p := by
    dsimp [F]
    exact (Real.continuousAt_rpow_const p
      ((1 : ℝ) / (1 - μ)) (.inl hp.ne')).mul continuousAt_const
  have hevent : ∀ᶠ q : ℝ in nhds p, x < F q :=
    continuousAt_const.eventually_lt hcont (by simpa [F] using h)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hevent
  let d := min (δ / 2) (p / 2)
  let q := p - d
  have hd : 0 < d := lt_min (half_pos hδ) (half_pos hp)
  have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
  have hdp : d < p := (min_le_right _ _).trans_lt (by linarith)
  have hq : 0 < q := by dsimp [q]; linarith
  have hqp : q < p := by dsimp [q]; linarith
  have hqball : q ∈ Metric.ball p δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [q]
    rw [show |p - d - p| = d by
      rw [show p - d - p = -d by ring, abs_neg, abs_of_pos hd]]
    exact hdδ
  exact ⟨q, hq, hqp, hball hqball⟩

/-- An interior Ramsey-region point can be moved slightly upward in its
second coordinate while remaining in the interior. -/
lemma exists_right_slack_interior {x y : ℝ}
    (hy : 0 < y) (hy1 : y < 1)
    (hxy : (x, y) ∈ ramseyRegionInterior) :
    ∃ y₀ : ℝ, y < y₀ ∧ y₀ < 1 ∧
      (x, y₀) ∈ ramseyRegionInterior := by
  have hopen : IsOpen ramseyRegionInterior := isOpen_interior
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhds_iff.1 (hopen.mem_nhds hxy)
  let d := min (δ / 2) ((1 - y) / 2)
  let y₀ := y + d
  have hd : 0 < d :=
    lt_min (half_pos hδ) (half_pos (sub_pos.mpr hy1))
  have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
  have hdy : d < 1 - y :=
    (min_le_right _ _).trans_lt (by linarith)
  have hy₀ball : (x, y₀) ∈ Metric.ball (x, y) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · simpa using hδ
    · rw [Real.dist_eq]
      dsimp [y₀]
      rw [show |y + d - y| = d by
        rw [show y + d - y = d by ring, abs_of_pos hd]]
      exact hdδ
  exact ⟨y₀, by dsimp [y₀]; linarith,
    by dsimp [y₀]; linarith, hball hy₀ball⟩

/-- A fixed target is eventually dominated by powers of a base greater
than one. -/
lemma exists_pow_ge {b A : ℝ} (hb : 1 < b) :
    ∃ L : ℕ, ∀ l : ℕ, L ≤ l → A ≤ b ^ l := by
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt hb).eventually
      (Filter.eventually_ge_atTop A))
  exact ⟨L, hL⟩

set_option maxHeartbeats 1000000 in
-- The max-cut arithmetic and the two nested asymptotic choices produce
-- several large nonlinear real-arithmetic goals.
/-- The max-cut supplied by `exists_partition_redEdgesBetween_le_four_mul`
has enough density and enough vertices for the book theorem. -/
theorem graph_good_of_bookMain
    {x y μ p : ℝ}
    (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1)
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hlimit :
      x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))
    (hregion : (x, y) ∈ ramseyRegionInterior) :
    ∃ L₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (k l : ℕ),
        1 ≤ k → 1 ≤ l → L₀ ≤ l →
        p ≤ globalRedDensity G →
        bookWeight x y μ k l l ≤ (Fintype.card V : ℝ) ^ 2 →
        (∃ K : Finset V, G.IsNClique k K) ∨
          ∃ K : Finset V, G.IsNIndepSet l K := by
  obtain ⟨q, hq, hqp, hlimitq⟩ :=
    exists_density_slack hμ1 hp hlimit
  obtain ⟨y₀, hyy₀, hy₀1, hregion₀⟩ :=
    exists_right_slack_interior hy hy1 hregion
  have hy₀ : 0 < y₀ := hy.trans hyy₀
  obtain ⟨Lb, hbook⟩ := candidate_good_bookMain
    hx hx1 hy₀ hy₀1 hμ hμ1 hq (hqp.trans hp1)
    hlimitq hregion₀
  have hratio : 1 < y₀ / y := (one_lt_div hy).2 hyy₀
  obtain ⟨Ly, hLy⟩ := exists_pow_ge (A := 8 / p) hratio
  let A : ℝ := max 2 (p / (p - q) + 1)
  have hμy : 0 < μ * y := mul_pos hμ hy
  have hμy1 : μ * y < 1 := by
    nlinarith [mul_pos hμ (sub_pos.mpr hy1),
      mul_pos hy (sub_pos.mpr hμ1)]
  have hbase : 1 < (μ * y)⁻¹ := by
    rw [one_lt_inv₀ hμy]
    exact hμy1
  obtain ⟨Ln, hLn⟩ := exists_pow_ge (A := A ^ 2) hbase
  let L₀ := Lb + Ly + Ln
  refine ⟨L₀, ?_⟩
  intro V instF instD G k l hk hl hl₀ hdensity hsize
  let n : ℕ := Fintype.card V
  have hLb : Lb ≤ l := by dsimp [L₀] at hl₀; omega
  have hLy' : Ly ≤ l := by dsimp [L₀] at hl₀; omega
  have hLn' : Ln ≤ l := by dsimp [L₀] at hl₀; omega
  have hratioPow : 8 / p ≤ (y₀ / y) ^ l := hLy l hLy'
  have hbasePow : A ^ 2 ≤ ((μ * y)⁻¹) ^ l := hLn l hLn'
  have hxInv : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 hx1.le
  have hμyInv : 1 ≤ (μ * y)⁻¹ := (one_le_inv₀ hμy).2 hμy1.le
  have hweightBase :
      ((μ * y)⁻¹) ^ l ≤ bookWeight x y μ k l l := by
    dsimp [bookWeight]
    rw [mul_inv, mul_pow]
    have hxpow : 1 ≤ x⁻¹ ^ k := one_le_pow₀ hxInv
    nlinarith [mul_nonneg (pow_nonneg (inv_nonneg.mpr hy.le) l)
      (pow_nonneg (inv_nonneg.mpr hμ.le) l)]
  have hnSq : A ^ 2 ≤ (n : ℝ) ^ 2 :=
    hbasePow.trans (hweightBase.trans hsize)
  have hA0 : 0 ≤ A := zero_le_two.trans (le_max_left _ _)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnA : A ≤ n := by nlinarith
  have hn2 : (2 : ℝ) ≤ n := (le_max_left _ _).trans hnA
  have hnNat2 : 2 ≤ n := by exact_mod_cast hn2
  obtain ⟨X, Y, hXY, hunion, hcut⟩ :=
    exists_partition_redEdgesBetween_le_four_mul G Finset.univ
  have htotal :
      p * (n : ℝ) * (n - 1) ≤
        (redEdgesBetween G Finset.univ Finset.univ : ℝ) := by
    have hden : 0 < (n : ℝ) * (n - 1) := by
      have : 0 < (n : ℝ) - 1 := by linarith
      positivity
    have hdensity' :
        p ≤ (redEdgesBetween G Finset.univ Finset.univ : ℝ) /
          ((n : ℝ) * (n - 1)) := by
      simpa [globalRedDensity, n] using hdensity
    simpa [mul_assoc] using (le_div_iff₀ hden).1 hdensity'
  have hcutR :
      (redEdgesBetween G Finset.univ Finset.univ : ℝ) ≤
        4 * redEdgesBetween G X Y := by
    exact_mod_cast hcut
  have hcross :
      p / 4 * (n : ℝ) * (n - 1) ≤
        (redEdgesBetween G X Y : ℝ) := by
    nlinarith [htotal, hcutR]
  have hcards :
      X.card + Y.card = n := by
    rw [← card_union_of_disjoint hXY, hunion, card_univ]
  have hcardsR : (X.card : ℝ) + Y.card = n := by
    exact_mod_cast hcards
  have hprodUpper :
      4 * (X.card : ℝ) * Y.card ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((X.card : ℝ) - Y.card)]
  have hcrossPos : 0 < (redEdgesBetween G X Y : ℝ) := by
    have hn1pos : 0 < (n : ℝ) - 1 := by linarith
    have : 0 < p / 4 * (n : ℝ) * (n - 1) := by
      positivity
    exact this.trans_le hcross
  have hXne : X.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst X
    simp [redEdgesBetween] at hcrossPos
  have hYne : Y.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst Y
    simp [redEdgesBetween] at hcrossPos
  let C : Candidate G := ⟨X, Y, hXne, hYne, hXY⟩
  have hqDensity : q ≤ C.density := by
    have hprodPos : 0 < (X.card : ℝ) * Y.card := by
      exact mul_pos (by exact_mod_cast hXne.card_pos)
        (by exact_mod_cast hYne.card_pos)
    rw [Candidate.density, densityBetween]
    apply (le_div_iff₀ hprodPos).2
    have hqGlobal :
        q * (n : ℝ) ^ 2 ≤ p * (n : ℝ) * (n - 1) := by
      have hAq : p / (p - q) + 1 ≤ A := le_max_right _ _
      have hpq : 0 < p - q := sub_pos.mpr hqp
      have hnlarge : p / (p - q) + 1 ≤ n := hAq.trans hnA
      have hnratio : p / (p - q) ≤ (n : ℝ) := by linarith
      have hpMul : p ≤ (p - q) * (n : ℝ) :=
        by simpa [mul_comm] using (div_le_iff₀ hpq).1 hnratio
      have hlinear :
          q * (n : ℝ) ≤ p * ((n : ℝ) - 1) := by
        nlinarith
      have hscaled :=
        mul_le_mul_of_nonneg_right hlinear hn0
      nlinarith
    calc
      q * ((X.card : ℝ) * Y.card) ≤
          q * ((n : ℝ) ^ 2 / 4) := by
        have hq0 : 0 ≤ q := hq.le
        apply mul_le_mul_of_nonneg_left _ hq0
        linarith [hprodUpper]
      _ ≤ p / 4 * (n : ℝ) * (n - 1) := by
        nlinarith
      _ ≤ redEdgesBetween G X Y := hcross
  have hweightChange :
      bookWeight x y₀ μ k l l * (y₀ / y) ^ l =
        bookWeight x y μ k l l := by
    dsimp [bookWeight]
    rw [div_pow]
    calc
      (x⁻¹ ^ k * y₀⁻¹ ^ l * μ⁻¹ ^ l) *
          (y₀ ^ l / y ^ l) =
          x⁻¹ ^ k * μ⁻¹ ^ l *
            ((y₀⁻¹ * y₀) ^ l * y⁻¹ ^ l) := by
        rw [mul_pow, inv_pow]
        field_simp [ne_of_gt hy]
        simp [← mul_pow, hy.ne', hy₀.ne']
      _ = x⁻¹ ^ k * μ⁻¹ ^ l * y⁻¹ ^ l := by
        rw [inv_mul_cancel₀ (ne_of_gt hy₀), one_pow, one_mul]
      _ = x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ l := by ring
  have hsizeC :
      bookWeight x y₀ μ k l l ≤
        (C.X.card : ℝ) * C.Y.card := by
    have hpn :
        p / 8 * (n : ℝ) ^ 2 ≤
          (C.X.card : ℝ) * C.Y.card := by
      have hnminus : (n : ℝ) / 2 ≤ n - 1 := by linarith
      have hcrossLe :
          (redEdgesBetween G X Y : ℝ) ≤
            (X.card : ℝ) * Y.card := by
        exact_mod_cast redEdgesBetween_le_card_mul_card G X Y
      dsimp [C]
      calc
        p / 8 * (n : ℝ) ^ 2 ≤
            p / 4 * (n : ℝ) * (n - 1) := by
          have hfac : 0 ≤ p / 4 * (n : ℝ) := by positivity
          have hmul :
              (p / 4 * (n : ℝ)) * ((n : ℝ) / 2) ≤
                (p / 4 * (n : ℝ)) * ((n : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hnminus hfac
          calc
            p / 8 * (n : ℝ) ^ 2 =
                (p / 4 * (n : ℝ)) * ((n : ℝ) / 2) := by ring
            _ ≤ (p / 4 * (n : ℝ)) * ((n : ℝ) - 1) := hmul
            _ = p / 4 * (n : ℝ) * (n - 1) := by ring
        _ ≤ redEdgesBetween G X Y := hcross
        _ ≤ (X.card : ℝ) * Y.card := hcrossLe
    have hratioScaled :
        1 ≤ p / 8 * (y₀ / y) ^ l := by
      calc
        1 = p / 8 * (8 / p) := by
          field_simp [hp.ne']
        _ ≤ p / 8 * (y₀ / y) ^ l := by
          exact mul_le_mul_of_nonneg_left hratioPow (by positivity)
    have hweight0 :
        0 ≤ bookWeight x y₀ μ k l l :=
      (bookWeight_pos hx hy₀ hμ k l l).le
    calc
      bookWeight x y₀ μ k l l ≤
          p / 8 * (bookWeight x y₀ μ k l l *
            (y₀ / y) ^ l) := by
        nlinarith [mul_nonneg hweight0
          (sub_nonneg.mpr hratioScaled)]
      _ = p / 8 * bookWeight x y μ k l l := by
        rw [hweightChange]
      _ ≤ p / 8 * (n : ℝ) ^ 2 := by
        gcongr
      _ ≤ (C.X.card : ℝ) * C.Y.card := hpn
  have hgood := hbook V G k l l C hk hl hl hLb hqDensity hsizeC
  rcases hgood with hred | hblueX | hblueY
  · rcases hred with ⟨K, _, hK⟩
    exact Or.inl ⟨K, hK⟩
  · rcases hblueX with ⟨K, _, hK⟩
    exact Or.inr ⟨K, hK⟩
  · rcases hblueY with ⟨K, _, hK⟩
    exact Or.inr ⟨K, hK⟩

/-- The vertex threshold in Theorem `t:bookCor`, expressed as the square
root of the exact multiplicative book weight. -/
def bookGraphThreshold (x y μ : ℝ) (k l : ℕ) : ℝ :=
  Real.sqrt (bookWeight x y μ k l l)

/-- Theorem `t:bookCor` in its exact square-root form. -/
theorem graph_good_bookCor
    {x y μ p : ℝ}
    (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1)
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hlimit :
      x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))
    (hregion : (x, y) ∈ ramseyRegionInterior) :
    ∃ L₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (k l : ℕ),
        1 ≤ k → 1 ≤ l → L₀ ≤ l →
        p ≤ globalRedDensity G →
        bookGraphThreshold x y μ k l ≤ Fintype.card V →
        (∃ K : Finset V, G.IsNClique k K) ∨
          ∃ K : Finset V, G.IsNIndepSet l K := by
  obtain ⟨L₀, hL₀⟩ := graph_good_of_bookMain
    hx hx1 hy hy1 hμ hμ1 hp hp1 hlimit hregion
  refine ⟨L₀, ?_⟩
  intro V instF instD G k l hk hl hl₀ hdensity hcard
  apply hL₀ V G k l hk hl hl₀ hdensity
  have hw0 : 0 ≤ bookWeight x y μ k l l :=
    (bookWeight_pos hx hy hμ k l l).le
  have hsqrt := mul_self_le_mul_self
    (Real.sqrt_nonneg _) (by exact_mod_cast hcard)
  rw [Real.mul_self_sqrt hw0] at hsqrt
  simpa [pow_two, bookGraphThreshold] using hsqrt

end Arxiv2407_19026
