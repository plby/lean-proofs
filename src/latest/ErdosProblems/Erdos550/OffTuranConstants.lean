import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constants for the direct off-Turán argument

The regularity parameter also lies below an externally supplied positive cap,
the one returned by the red multipartite blow-up lemma.  Keeping that cap
explicit prevents a circular choice in the reduced-graph independence step.
-/

namespace Erdos550

/-- Quantitative parameter regime used by the direct off-Turán proof. -/
structure OffTuranConstants (q f m₀ : ℕ) (δ εCap : ℝ) where
  η : ℝ
  ε : ℝ
  ε' : ℝ
  eta_pos : 0 < η
  eta_delta_400 : 400 * η ≤ δ
  eta_delta : η < δ / 200
  eta_q : η < ((q - 1 : ℕ) : ℝ) / (200 * q)
  eta_edges : η < 1 / (100 * (f + 1 : ℝ))
  eta_small : η < (1 / 10000 : ℝ)
  eps_pos : 0 < ε
  eps_cap : ε < εCap
  eps_cube : ε < η ^ 3 / 400
  four_eps_cube : 4 * ε < η ^ 3 / 400
  eps_square_q : ε < η ^ 2 / (8 * q)
  eps_square_q_strong : ε < η ^ 2 / (32 * q)
  eps_linear : ε < η / 100
  eps_slice_budget : ε < η ^ 4 / 500
  eps'_eq : ε' = ε / (20 * η)
  cluster_count : max m₀ ⌈4 * q ^ 2 / η⌉₊ ≤ ⌈4 / ε⌉₊
  cluster_count_strong : max m₀ ⌈8 * q ^ 2 / η⌉₊ ≤ ⌈4 / ε⌉₊

/-- Existence of the full parameter package. -/
theorem offTuranConstants_exists (q f m₀ : ℕ) (hq : 2 ≤ q) (hm₀ : 1 ≤ m₀)
    (δ εCap : ℝ) (hδ : 0 < δ) (hcap : 0 < εCap) :
    Nonempty (OffTuranConstants q f m₀ δ εCap) := by
  have hqm1 : 0 < q - 1 := by omega
  let η : ℝ := min (δ / 400)
    (min (((q - 1 : ℕ) : ℝ) / (400 * q))
      (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000)))
  have hη : 0 < η := by dsimp [η]; positivity
  let A : ℕ := max m₀ ⌈8 * q ^ 2 / η⌉₊
  have hA : 0 < A := lt_of_lt_of_le (by omega) (le_max_left m₀ ⌈8 * q ^ 2 / η⌉₊)
  let ε : ℝ := min (εCap / 2)
    (min (η ^ 3 / 3200)
      (min (η ^ 2 / (64 * q))
        (min (η / 200) (min (η ^ 4 / 1000) (2 / A)))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : ε ≤ εCap / 2 := by dsimp [ε]; exact min_le_left _ _
  have h3 : ε ≤ η ^ 3 / 3200 := by
    dsimp [ε]; exact (min_le_right _ _).trans (min_le_left _ _)
  have h2 : ε ≤ η ^ 2 / (64 * q) := by
    dsimp [ε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h1 : ε ≤ η / 200 := by
    dsimp [ε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 : ε ≤ η ^ 4 / 1000 := by
    dsimp [ε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hAε : ε ≤ 2 / (A : ℝ) := by
    dsimp [ε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hreal : (A : ℝ) ≤ 4 / ε := by
    rw [le_div_iff₀ hε]
    have hlt : 2 / (A : ℝ) < 4 / A := by
      rw [div_lt_div_iff₀ hAr hAr]
      nlinarith [hAr]
    have ht := hAε.trans_lt hlt
    have hmul : ε * (A : ℝ) ≤ 4 := ((lt_div_iff₀ hAr).mp ht).le
    rw [mul_comm] at hmul
    exact hmul
  have hcluster : A ≤ ⌈4 / ε⌉₊ := by
    exact_mod_cast hreal.trans (Nat.le_ceil (4 / ε))
  refine ⟨⟨η, ε, ε / (20 * η), hη, ?_, ?_, ?_, ?_, ?_, hε,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩⟩
  · dsimp [η]
    have h := min_le_left (δ / 400) (min (((q - 1 : ℕ) : ℝ) / (400 * q))
      (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000)))
    nlinarith
  · dsimp [η]
    have h := min_le_left (δ / 400) (min (((q - 1 : ℕ) : ℝ) / (400 * q))
      (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000)))
    nlinarith
  · dsimp [η]
    have h : min (δ / 400) (min (((q - 1 : ℕ) : ℝ) / (400 * q))
        (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000)))
        ≤ ((q - 1 : ℕ) : ℝ) / (400 * q) :=
      (min_le_right (δ / 400) _).trans (min_le_left _ _)
    apply h.trans_lt
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 400 * q)
      (by positivity : (0 : ℝ) < 200 * q)]
    have hqr : (0 : ℝ) < q := by positivity
    have hm : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast hqm1
    nlinarith
  · dsimp [η]
    have h : min (δ / 400) (min (((q - 1 : ℕ) : ℝ) / (400 * q))
        (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000)))
        ≤ 1 / (200 * (f + 1 : ℝ)) :=
      (min_le_right (δ / 400) _).trans
        ((min_le_right (((q - 1 : ℕ) : ℝ) / (400 * q)) _).trans (min_le_left _ _))
    apply h.trans_lt
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 200 * (f + 1))
      (by positivity : (0 : ℝ) < 100 * (f + 1))]
    have hf : (0 : ℝ) < f + 1 := by positivity
    nlinarith
  · dsimp [η]
    have h : min (δ / 400) (min (((q - 1 : ℕ) : ℝ) / (400 * q))
        (min (1 / (200 * (f + 1 : ℝ))) (1 / 20000))) ≤ (1 / 20000 : ℝ) :=
      (min_le_right (δ / 400) _).trans
        ((min_le_right (((q - 1 : ℕ) : ℝ) / (400 * q)) _).trans (min_le_right _ _))
    exact h.trans_lt (by norm_num)
  · exact hc.trans_lt (by linarith)
  · apply h3.trans_lt
    have hp : 0 < η ^ 3 := by positivity
    nlinarith
  · apply (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4)).trans_lt
    have hp : 0 < η ^ 3 := by positivity
    nlinarith
  · apply h2.trans_lt
    have hp : 0 < η ^ 2 := by positivity
    have hqR : (0 : ℝ) < q := by positivity
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 64 * q)
      (by positivity : (0 : ℝ) < 8 * q)]
    nlinarith
  · apply h2.trans_lt
    have hp : 0 < η ^ 2 := by positivity
    have hqR : (0 : ℝ) < q := by positivity
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 64 * q)
      (by positivity : (0 : ℝ) < 32 * q)]
    nlinarith
  · exact h1.trans_lt (by nlinarith [hη])
  · apply h4.trans_lt
    have hp : 0 < η ^ 4 := by positivity
    nlinarith
  · have hAold :
        max m₀ ⌈4 * q ^ 2 / η⌉₊ ≤ A := by
      apply max_le
      · exact le_max_left _ _
      · apply (Nat.ceil_mono ?_).trans (le_max_right _ _)
        gcongr
        norm_num
    exact hAold.trans hcluster
  · simpa [A] using! hcluster

/-- The sliced regularity parameter is positive. -/
lemma OffTuranConstants.eps'_pos {q f m₀ : ℕ} {δ εCap : ℝ}
    (c : OffTuranConstants q f m₀ δ εCap) : 0 < c.ε' := by
  rw [c.eps'_eq]
  exact div_pos c.eps_pos (mul_pos (by norm_num) c.eta_pos)

/-- Slicing leaves ample room below the density threshold. -/
lemma OffTuranConstants.eps'_lt_eta_div_100 {q f m₀ : ℕ} {δ εCap : ℝ}
    (c : OffTuranConstants q f m₀ δ εCap) : c.ε' < c.η / 100 := by
  rw [c.eps'_eq]
  have hη1 : c.η < 1 := lt_trans c.eta_small (by norm_num)
  have hη0 := c.eta_pos
  have hsq : c.η ^ 2 ≤ 1 := by nlinarith [mul_nonneg hη0.le (sub_nonneg.mpr hη1.le)]
  have hpow : c.η ^ 4 ≤ c.η ^ 2 := by
    calc
      c.η ^ 4 = c.η ^ 2 * c.η ^ 2 := by ring
      _ ≤ c.η ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg c.η)
      _ = c.η ^ 2 := by ring
  rw [div_lt_iff₀ (mul_pos (by norm_num) c.eta_pos)]
  nlinarith [c.eps_slice_budget]

/-- In particular all downstream `4ε'` losses are below `η/20`. -/
lemma OffTuranConstants.four_eps'_lt_eta_div_20 {q f m₀ : ℕ} {δ εCap : ℝ}
    (c : OffTuranConstants q f m₀ δ εCap) : 4 * c.ε' < c.η / 20 := by
  nlinarith [c.eps'_lt_eta_div_100, c.eta_pos]

end Erdos550
