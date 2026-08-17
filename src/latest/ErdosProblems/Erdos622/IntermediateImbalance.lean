import ErdosProblems.Erdos622.OneSmallSymmetric

/-!
# The intermediate-imbalance, forced-left-cover count

This file strengthens the positive one-small-cover arm from excess
`d ≤ floor(sqrt n / K)` to the full intermediate range `d ≤ floor(sqrt n)`.
The cover-product inequality supplies the extra room: it forces the balanced
left minimum cover to have size at least `(K-1) floor(sqrt n)`, which absorbs
both the original-cut excess and the positive Gaussian window.
-/

open Filter Finset Real
open scoped BigOperators Topology SimpleGraph

namespace Erdos622.AlmostBipartiteRegimeCounts

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A cover above a sufficiently large fixed multiple of `floor (sqrt n)`
automatically satisfies the product arm used by the one-small-cover count.
The factor `4` leaves room for both integer division in
`sqrtCoverThreshold` and the gap between `n` and `floor (sqrt n)^2`. -/
lemma eventually_large_sqrtCover_forces_product
    {K M : ℕ} (hK : 0 < K) (hKM : 4 * K ≤ M) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ C : ℕ,
      M * Nat.sqrt n < C →
        n + 1 ≤ sqrtCoverThreshold K n * (C + 1) := by
  let R := max (2 * K) 3
  filter_upwards [Filter.eventually_ge_atTop (R * R)] with n hn
  intro C hC
  let s := Nat.sqrt n
  have hRs : R ≤ s := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using hn
  have h2Ks : 2 * K ≤ s := (le_max_left _ _).trans hRs
  have h3s : 3 ≤ s := (le_max_right _ _).trans hRs
  have hKs : K ≤ s := by omega
  have hqpos : 0 < s / K := Nat.div_pos hKs hK
  have hsdiv : s ≤ 2 * K * (s / K) := by
    have hdecomp := Nat.div_add_mod s K
    have hmod : s % K < K := Nat.mod_lt s hK
    nlinarith
  have hCs : M * s ≤ C + 1 := by
    have hMC : M * s ≤ C := by
      simpa [s] using (Nat.le_of_lt hC)
    exact hMC.trans (Nat.le_succ C)
  have hlarge : 2 * s * s ≤ (s / K) * (C + 1) := by
    calc
      2 * s * s ≤ (4 * K * (s / K)) * s := by
        nlinarith
      _ ≤ (M * (s / K)) * s := by
        gcongr
      _ = (s / K) * (M * s) := by ring
      _ ≤ (s / K) * (C + 1) := Nat.mul_le_mul_left _ hCs
  have hnlt : n < (s + 1) * (s + 1) := by
    simpa [s] using Nat.lt_succ_sqrt n
  have hsquare : (s + 1) * (s + 1) ≤ 2 * s * s := by
    nlinarith
  unfold sqrtCoverThreshold
  exact (Nat.succ_le_of_lt hnlt).trans (hsquare.trans hlarge)

/-- Choose one auxiliary error scale small enough for transfer
concentration, the compact sampled-forest estimate, and elementary
probability bounds. -/
lemma exists_auxiliary_capacity_shrink
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    ∃ σ : ℝ, 0 < σ ∧ 2 * σ ≤ ρ ∧ σ * M < 1 ∧ σ < 1 := by
  let σ : ℝ := min (ρ / 4) (min (1 / (2 * M)) (1 / 2))
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  have hσρ : σ ≤ ρ / 4 := by
    exact min_le_left _ _
  have hσM : σ ≤ 1 / (2 * M) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hσhalf : σ ≤ 1 / 2 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hmul : σ * M ≤ 1 / 2 := by
    calc
      σ * M ≤ (1 / (2 * M)) * M :=
        mul_le_mul_of_nonneg_right hσM hM.le
      _ = 1 / 2 := by field_simp [hM.ne']
  exact ⟨σ, hσ, by linarith, hmul.trans_lt (by norm_num),
    hσhalf.trans_lt (by norm_num)⟩

/-- Reciprocal reparameterization for the reversed bounded-internal
orientation.  If `beta` is a normalized cover size in the original compact
range, then `4 / beta` lies in the enlarged range used by the common shifted
Gaussian window. -/
lemma reciprocal_four_mem_cover_window
    {K M₀ : ℕ} (hK : 0 < K) (hM₀ : 0 < M₀) {beta : ℝ}
    (hbeta : beta ∈ Set.Icc (1 / (4 * K : ℝ)) (M₀ : ℝ)) :
    4 / beta ∈
      Set.Icc (min (1 / (4 * K : ℝ)) (4 / (M₀ : ℝ)))
        (max (M₀ : ℝ) (16 * K : ℝ)) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hM₀real : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have heta₀ : (0 : ℝ) < 1 / (4 * K : ℝ) := by positivity
  have hbetaPos : 0 < beta := heta₀.trans_le hbeta.1
  constructor
  · apply (min_le_right _ _).trans
    rw [div_le_div_iff₀ hM₀real hbetaPos]
    nlinarith [hbeta.2]
  · apply le_max_of_le_right
    calc
      4 / beta ≤ 4 / (1 / (4 * K : ℝ)) := by
        rw [div_le_div_iff₀ hbetaPos heta₀]
        nlinarith [hbeta.1]
      _ = 16 * K := by field_simp [hKreal.ne'] <;> norm_num

/-- A small integer square-root threshold gives the corresponding normalized
real bound without any asymptotic rounding loss. -/
lemma normalized_le_inv_of_le_sqrtCoverThreshold
    {L n d : ℕ} (hL : 0 < L) (hn : 0 < n)
    (hd : d ≤ sqrtCoverThreshold L n) :
    (d : ℝ) / Real.sqrt n ≤ 1 / (L : ℝ) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hmulNat : d * L ≤ Nat.sqrt n := by
    exact (Nat.le_div_iff_mul_le hL).mp (by
      simpa only [sqrtCoverThreshold] using hd)
  have hmulReal : (d : ℝ) * L ≤ Real.sqrt n := by
    calc
      (d : ℝ) * L = ((d * L : ℕ) : ℝ) := by norm_num
      _ ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hmulNat
      _ ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  rw [div_le_div_iff₀ hsqrt hLreal]
  simpa only [one_mul] using hmulReal

/-- The normalized form used by the small-transfer window.  The scale
condition isolates the only parameter-hierarchy calculation: the reciprocal
threshold must dominate `64 / alpha`. -/
lemma normalized_le_alpha_div_sixtyFour_of_small
    {L n d : ℕ} {alpha : ℝ} (hL : 0 < L) (hn : 0 < n)
    (hd : d ≤ sqrtCoverThreshold L n)
    (hscale : 64 ≤ (L : ℝ) * alpha) :
    (d : ℝ) / Real.sqrt n ≤ alpha / 64 := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  apply (normalized_le_inv_of_le_sqrtCoverThreshold hL hn hd).trans
  rw [div_le_div_iff₀ hLreal (by norm_num : (0 : ℝ) < 64)]
  nlinarith [hscale]

/-- Ready-to-use small-transfer bound for the reversed orientation
`alpha = 4 / beta`.  The threshold scale `L ≥ 16 M₀` exactly pays for
the worst compact value `beta = M₀`. -/
lemma normalized_le_reciprocal_cover_div_sixtyFour
    {L M₀ n d c : ℕ} (hL : 0 < L) (hM₀ : 0 < M₀)
    (hn : 0 < n) (hLM₀ : 16 * M₀ ≤ L)
    (hd : d ≤ sqrtCoverThreshold L n)
    (hbetaPos : 0 < (c : ℝ) / Real.sqrt n)
    (hbetaUpper : (c : ℝ) / Real.sqrt n ≤ M₀) :
    (d : ℝ) / Real.sqrt n ≤
      (4 / ((c : ℝ) / Real.sqrt n)) / 64 := by
  let beta : ℝ := (c : ℝ) / Real.sqrt n
  let alpha : ℝ := 4 / beta
  have hM₀real : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have halphaLower : 4 / (M₀ : ℝ) ≤ alpha := by
    dsimp [alpha, beta]
    rw [div_le_div_iff₀ hM₀real hbetaPos]
    nlinarith
  have hLM₀real : (16 : ℝ) * M₀ ≤ L := by exact_mod_cast hLM₀
  have hscale : 64 ≤ (L : ℝ) * alpha := by
    calc
      (64 : ℝ) = (16 * (M₀ : ℝ)) * (4 / M₀) := by
        field_simp [hM₀real.ne'] <;> norm_num
      _ ≤ (L : ℝ) * alpha :=
        mul_le_mul hLM₀real halphaLower (by positivity) (by positivity)
  simpa only [alpha, beta] using
    normalized_le_alpha_div_sixtyFour_of_small hL hn hd hscale

/-- Real-valued deterministic transport for the shifted intermediate window.

Here `x,y,t` stand for the sampled cardinalities on the balanced left side,
balanced right side, and transfer set, respectively.  The shifted binomial
window is applied in the swapped orientation, so its normalized statistic is
`(y-x)/s`.  Concentration of `2t` about `κs`, together with a shrink
`rho` at least twice the concentration error, makes the two window
inequalities fit either the balanced matching/original-side forest on the
left or the transferred balanced forest on the right. -/
lemma shrunken_capacity_window_real_bounds
    {α κ ρ σ s x y t leftBalanced leftOriginal right : ℝ}
    (_hα : 0 < α) (hκ : 0 ≤ κ) (hs : 0 < s)
    (hσ : 0 ≤ σ) (hσρ : 2 * σ ≤ ρ)
    (htransfer : |2 * t - κ * s| ≤ σ * s)
    (hwindow : (y - x) / s ∈
      Set.Icc
        (-(max (α / 4 - κ) (15 * κ) - ρ))
        (max (1 / α) κ - ρ))
    (hleftBalanced : (α / 4 - σ) * s ≤ leftBalanced)
    (hleftOriginal : 20 * κ * s ≤ leftOriginal)
    (hright : (1 / α - σ) * s ≤ right) :
    x + 2 * t ≤ y + max leftBalanced leftOriginal ∧
      y ≤ x + max (2 * t) right := by
  have hσρ' : σ ≤ ρ := by linarith
  have htransferUpper : 2 * t ≤ (κ + σ) * s := by
    have := (abs_le.mp htransfer).2
    nlinarith
  have htransferLower : (κ - σ) * s ≤ 2 * t := by
    have := (abs_le.mp htransfer).1
    nlinarith
  have hwindowLower :
      x - y ≤ (max (α / 4 - κ) (15 * κ) - ρ) * s := by
    have hw := hwindow.1
    rw [le_div_iff₀ hs] at hw
    nlinarith
  have hwindowUpper :
      y - x ≤ (max (1 / α) κ - ρ) * s := by
    have hw := hwindow.2
    rw [div_le_iff₀ hs] at hw
    exact hw
  constructor
  · rcases max_cases (α / 4 - κ) (15 * κ) with ⟨ha, _⟩ | ⟨ha, _⟩
    · have hcap : x + 2 * t - y ≤ leftBalanced := by
        calc
          x + 2 * t - y ≤
              (max (α / 4 - κ) (15 * κ) - ρ) * s +
                (κ + σ) * s := by linarith
          _ = (α / 4 - ρ + σ) * s := by rw [ha]; ring
          _ ≤ (α / 4 - σ) * s := by
            exact mul_le_mul_of_nonneg_right (by linarith) hs.le
          _ ≤ leftBalanced := hleftBalanced
      have hmax : leftBalanced ≤ max leftBalanced leftOriginal :=
        le_max_left _ _
      linarith
    · have hcap : x + 2 * t - y ≤ leftOriginal := by
        calc
          x + 2 * t - y ≤
              (max (α / 4 - κ) (15 * κ) - ρ) * s +
                (κ + σ) * s := by linarith
          _ = (16 * κ - ρ + σ) * s := by rw [ha]; ring
          _ ≤ 20 * κ * s := by
            have hcoef : 0 ≤ 4 * κ + ρ - σ := by
              nlinarith only [hκ, hσρ']
            have hnonneg : 0 ≤ (4 * κ + ρ - σ) * s :=
              mul_nonneg hcoef hs.le
            nlinarith
          _ ≤ leftOriginal := hleftOriginal
      have hmax : leftOriginal ≤ max leftBalanced leftOriginal :=
        le_max_right _ _
      linarith
  · rcases max_cases (1 / α) κ with ⟨hb, _⟩ | ⟨hb, _⟩
    · have hcap : y - x ≤ right := by
        calc
          y - x ≤ (max (1 / α) κ - ρ) * s := hwindowUpper
          _ = (1 / α - ρ) * s := by rw [hb]
          _ ≤ (1 / α - σ) * s := by
            exact mul_le_mul_of_nonneg_right (by linarith) hs.le
          _ ≤ right := hright
      have hmax : right ≤ max (2 * t) right := le_max_right _ _
      linarith
    · have hcap : y - x ≤ 2 * t := by
        calc
          y - x ≤ (max (1 / α) κ - ρ) * s := hwindowUpper
          _ = (κ - ρ) * s := by rw [hb]
          _ ≤ (κ - σ) * s := by
            exact mul_le_mul_of_nonneg_right (by linarith) hs.le
          _ ≤ 2 * t := htransferLower
      have hmax : 2 * t ≤ max (2 * t) right := le_max_left _ _
      linarith

/-- Small-transfer companion to `shrunken_capacity_window_real_bounds`.
When `κ ≤ α/64`, the balanced matching alone controls the left window;
the extra forest on the original, unbalanced side is not needed. -/
lemma shrunken_capacity_window_small_transfer_real_bounds
    {α κ ρ σ s x y t leftBalanced right : ℝ}
    (_hα : 0 < α) (_hκ : 0 ≤ κ) (hκα : κ ≤ α / 64) (hs : 0 < s)
    (hσ : 0 ≤ σ) (hσρ : 2 * σ ≤ ρ)
    (htransfer : |2 * t - κ * s| ≤ σ * s)
    (hwindow : (y - x) / s ∈
      Set.Icc
        (-(max (α / 4 - κ) (15 * κ) - ρ))
        (max (1 / α) κ - ρ))
    (hleftBalanced : (α / 4 - σ) * s ≤ leftBalanced)
    (hright : (1 / α - σ) * s ≤ right) :
    x + 2 * t ≤ y + leftBalanced ∧
      y ≤ x + max (2 * t) right := by
  have hσρ' : σ ≤ ρ := by linarith
  have htransferUpper : 2 * t ≤ (κ + σ) * s := by
    have := (abs_le.mp htransfer).2
    nlinarith
  have htransferLower : (κ - σ) * s ≤ 2 * t := by
    have := (abs_le.mp htransfer).1
    nlinarith
  have hmaxLeft : max (α / 4 - κ) (15 * κ) = α / 4 - κ := by
    rw [max_eq_left]
    nlinarith
  have hwindowLower :
      x - y ≤ (max (α / 4 - κ) (15 * κ) - ρ) * s := by
    have hw := hwindow.1
    rw [le_div_iff₀ hs] at hw
    nlinarith
  have hwindowUpper :
      y - x ≤ (max (1 / α) κ - ρ) * s := by
    have hw := hwindow.2
    rw [div_le_iff₀ hs] at hw
    exact hw
  constructor
  · calc
      x + 2 * t ≤ y +
          (max (α / 4 - κ) (15 * κ) - ρ) * s +
            (κ + σ) * s := by linarith
      _ = y + (α / 4 - ρ + σ) * s := by rw [hmaxLeft]; ring
      _ ≤ y + (α / 4 - σ) * s := by
        have hcoef : α / 4 - ρ + σ ≤ α / 4 - σ := by linarith
        have hmul := mul_le_mul_of_nonneg_right hcoef hs.le
        linarith
      _ ≤ y + leftBalanced := by
        linarith
  · rcases max_cases (1 / α) κ with ⟨hb, _⟩ | ⟨hb, _⟩
    · have hcap : y - x ≤ right := by
        calc
          y - x ≤ (max (1 / α) κ - ρ) * s := hwindowUpper
          _ = (1 / α - ρ) * s := by rw [hb]
          _ ≤ (1 / α - σ) * s := by
            exact mul_le_mul_of_nonneg_right (by linarith) hs.le
          _ ≤ right := hright
      have hmax : right ≤ max (2 * t) right := le_max_right _ _
      linarith
    · have hcap : y - x ≤ 2 * t := by
        calc
          y - x ≤ (max (1 / α) κ - ρ) * s := hwindowUpper
          _ = (κ - ρ) * s := by rw [hb]
          _ ≤ (κ - σ) * s := by
            exact mul_le_mul_of_nonneg_right (by linarith) hs.le
          _ ≤ 2 * t := htransferLower
      have hmax : 2 * t ≤ max (2 * t) right := le_max_left _ _
      linarith

/-- Natural-number form of the shifted three-capacity window.  This lemma
does all casts and unfolds the standardized balanced-cut statistic, leaving
exactly the two inequalities consumed by
`IsKGoodSample.of_balanced_transfer_three_forests`.  The statistic is in
the swapped orientation: its selected cardinalities are `y` first and `x`
second. -/
lemma shrunken_capacity_window_nat_bounds
    {n x y t d leftBalanced leftOriginal right : ℕ}
    {α κ ρ σ : ℝ}
    (hn : 0 < n) (hx : x ≤ n)
    (hα : 0 < α) (hκ : κ = (d : ℝ) / Real.sqrt n)
    (hσ : 0 ≤ σ) (hσρ : 2 * σ ≤ ρ)
    (htransfer :
      |((2 * t : ℕ) : ℝ) - d| ≤ σ * Real.sqrt n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (y + (n - x)) ∈
      Set.Icc
        (-((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2))
        ((max (1 / α) κ - ρ) * Real.sqrt 2))
    (hleftBalanced :
      (α / 4 - σ) * Real.sqrt n ≤ (leftBalanced : ℝ))
    (hleftOriginal : (20 * d : ℕ) ≤ leftOriginal)
    (hright : (1 / α - σ) * Real.sqrt n ≤ (right : ℝ)) :
    x + 2 * t ≤ y + max leftBalanced leftOriginal ∧
      y ≤ x + max (2 * t) right := by
  have hs : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hnum :
      (2 * (y + (n - x)) : ℝ) - (2 * n : ℝ) =
        2 * ((y : ℝ) - x) := by
    ring
  have hnormalized : ((y : ℝ) - x) / Real.sqrt n ∈
      Set.Icc
        (-(max (α / 4 - κ) (15 * κ) - ρ))
        (max (1 / α) κ - ρ) := by
    constructor
    · have hw := hwindow.1
      unfold BinomialCLT.standardizedBinomialPoint at hw
      norm_num at hw
      rw [Nat.cast_sub hx,
        le_div_iff₀ (mul_pos hsqrt2 hs), hnum] at hw
      rw [le_div_iff₀ hs]
      nlinarith [hsqrt2sq]
    · have hw := hwindow.2
      unfold BinomialCLT.standardizedBinomialPoint at hw
      norm_num at hw
      rw [Nat.cast_sub hx,
        div_le_iff₀ (mul_pos hsqrt2 hs), hnum] at hw
      have hscale :
          (max α⁻¹ κ - ρ) * Real.sqrt 2 *
              (Real.sqrt 2 * Real.sqrt n) =
            2 * (max α⁻¹ κ - ρ) * Real.sqrt n := by
        calc
          _ = (max α⁻¹ κ - ρ) * (Real.sqrt 2) ^ 2 *
                Real.sqrt n := by ring
          _ = _ := by rw [hsqrt2sq]; ring
      have hw' :
          2 * ((y : ℝ) - x) ≤
            2 * (max α⁻¹ κ - ρ) * Real.sqrt n := by
        calc
          _ ≤ (max α⁻¹ κ - ρ) * Real.sqrt 2 *
                (Real.sqrt 2 * Real.sqrt n) := hw
          _ = _ := hscale
      rw [div_le_iff₀ hs]
      have hbound :
          (y : ℝ) - x ≤ (max α⁻¹ κ - ρ) * Real.sqrt n := by
        linarith
      simpa only [one_div] using hbound
  have hκs : κ * Real.sqrt n = d := by
    rw [hκ]
    field_simp [hs.ne']
  have hκnonneg : 0 ≤ κ := by
    rw [hκ]
    positivity
  have htransfer' :
      |2 * (t : ℝ) - κ * Real.sqrt n| ≤
        σ * Real.sqrt n := by
    rw [hκs]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htransfer
  have hleftOriginal' :
      20 * κ * Real.sqrt n ≤ (leftOriginal : ℝ) := by
    rw [mul_assoc, hκs]
    exact_mod_cast hleftOriginal
  have hreal := shrunken_capacity_window_real_bounds
    hα hκnonneg hs hσ hσρ htransfer' hnormalized
    hleftBalanced hleftOriginal' hright
  constructor
  · exact_mod_cast hreal.1
  · exact_mod_cast hreal.2

/-- Natural-number small-transfer companion.  The hypothesis
`κ ≤ α/64` removes the original-side forest from the input and from the
resulting left capacity. -/
lemma shrunken_capacity_window_small_transfer_nat_bounds
    {n x y t d leftBalanced right : ℕ}
    {α κ ρ σ : ℝ}
    (hn : 0 < n) (hx : x ≤ n)
    (hα : 0 < α) (hκ : κ = (d : ℝ) / Real.sqrt n)
    (hκα : κ ≤ α / 64)
    (hσ : 0 ≤ σ) (hσρ : 2 * σ ≤ ρ)
    (htransfer :
      |((2 * t : ℕ) : ℝ) - d| ≤ σ * Real.sqrt n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (y + (n - x)) ∈
      Set.Icc
        (-((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2))
        ((max (1 / α) κ - ρ) * Real.sqrt 2))
    (hleftBalanced :
      (α / 4 - σ) * Real.sqrt n ≤ (leftBalanced : ℝ))
    (hright : (1 / α - σ) * Real.sqrt n ≤ (right : ℝ)) :
    x + 2 * t ≤ y + leftBalanced ∧
      y ≤ x + max (2 * t) right := by
  have hs : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hnum :
      (2 * (y + (n - x)) : ℝ) - (2 * n : ℝ) =
        2 * ((y : ℝ) - x) := by
    ring
  have hnormalized : ((y : ℝ) - x) / Real.sqrt n ∈
      Set.Icc
        (-(max (α / 4 - κ) (15 * κ) - ρ))
        (max (1 / α) κ - ρ) := by
    constructor
    · have hw := hwindow.1
      unfold BinomialCLT.standardizedBinomialPoint at hw
      norm_num at hw
      rw [Nat.cast_sub hx,
        le_div_iff₀ (mul_pos hsqrt2 hs), hnum] at hw
      rw [le_div_iff₀ hs]
      nlinarith [hsqrt2sq]
    · have hw := hwindow.2
      unfold BinomialCLT.standardizedBinomialPoint at hw
      norm_num at hw
      rw [Nat.cast_sub hx,
        div_le_iff₀ (mul_pos hsqrt2 hs), hnum] at hw
      have hscale :
          (max α⁻¹ κ - ρ) * Real.sqrt 2 *
              (Real.sqrt 2 * Real.sqrt n) =
            2 * (max α⁻¹ κ - ρ) * Real.sqrt n := by
        calc
          _ = (max α⁻¹ κ - ρ) * (Real.sqrt 2) ^ 2 *
                Real.sqrt n := by ring
          _ = _ := by rw [hsqrt2sq]; ring
      have hw' :
          2 * ((y : ℝ) - x) ≤
            2 * (max α⁻¹ κ - ρ) * Real.sqrt n := by
        calc
          _ ≤ (max α⁻¹ κ - ρ) * Real.sqrt 2 *
                (Real.sqrt 2 * Real.sqrt n) := hw
          _ = _ := hscale
      rw [div_le_iff₀ hs]
      have hbound :
          (y : ℝ) - x ≤ (max α⁻¹ κ - ρ) * Real.sqrt n := by
        linarith
      simpa only [one_div] using hbound
  have hκs : κ * Real.sqrt n = d := by
    rw [hκ]
    field_simp [hs.ne']
  have hκnonneg : 0 ≤ κ := by
    rw [hκ]
    positivity
  have htransfer' :
      |2 * (t : ℝ) - κ * Real.sqrt n| ≤
        σ * Real.sqrt n := by
    rw [hκs]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htransfer
  have hreal := shrunken_capacity_window_small_transfer_real_bounds
    hα hκnonneg hκα hs hσ hσρ htransfer' hnormalized
    hleftBalanced hright
  constructor
  · exact_mod_cast hreal.1
  · exact_mod_cast hreal.2

/-- In the forced-large balanced-left-cover arm, the usual positive window
still fits when the original cut excess is as large as `floor(sqrt n)`.
The product hypothesis forces `(K-1) floor(sqrt n) ≤ C`. -/
lemma intermediate_positive_window_bounds
    {n K d C x y : ℕ}
    (hK : 16 ≤ K) (hsqrt : K ≤ Nat.sqrt n)
    (hd : d ≤ Nat.sqrt n)
    (hy : y ≤ n - d)
    (hprod : n + 1 ≤ sqrtCoverThreshold K n * (C + 1))
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + ((n - d) - y)) ∈
      Set.Icc 0 ((K : ℝ) * Real.sqrt 2 / 16)) :
    y ≤ x ∧
      (((x - y : ℕ) : ℝ) ≤ (1 / 4 - 1 / 64 : ℝ) * C) := by
  let s := Nat.sqrt n
  have hspos : 0 < s := lt_of_lt_of_le (by omega) hsqrt
  have hsn : s * s ≤ n := by simpa [s] using Nat.sqrt_le n
  have hC : (K - 1) * s ≤ C := by
    have hKm1 : K - 1 < K := by omega
    exact coverProductArm_forces_sqrtCover hKm1 hprod
  have hnpos : 0 < n := by
    have : 0 < s * s := Nat.mul_pos hspos hspos
    omega
  have hdn : d ≤ n :=
    hd.trans (by simpa [s] using Nat.sqrt_le_self n)
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hnum :
      (2 * (x + ((n - d) - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y - d) := by
    ring
  have hlower : (0 : ℝ) ≤ (x : ℝ) - y - d := by
    have hw := hwindow.1
    unfold BinomialCLT.standardizedBinomialPoint at hw
    norm_num at hw
    rw [Nat.cast_sub hy, Nat.cast_sub hdn, hnum] at hw
    have hden : 0 < Real.sqrt 2 * Real.sqrt n := by positivity
    have hw' := (le_div_iff₀ hden).mp hw
    nlinarith
  have hyxReal : (y : ℝ) ≤ x := by linarith
  have hyx : y ≤ x := by exact_mod_cast hyxReal
  refine ⟨hyx, ?_⟩
  have hupper :
      ((x : ℝ) - y - d) ≤ (K : ℝ) / 16 * Real.sqrt n := by
    have hw := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hw
    norm_num at hw
    rw [Nat.cast_sub hy, Nat.cast_sub hdn, hnum] at hw
    have hsqrtmul : Real.sqrt (2 * n : ℝ) = Real.sqrt 2 * Real.sqrt n := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_le_iff₀ (by positivity : 0 < Real.sqrt 2 * Real.sqrt n)] at hw
    nlinarith [hsqrt2sq]
  have hsqrtlt : Real.sqrt n < (s : ℝ) + 1 := by
    have hnlt : n < (s + 1) * (s + 1) := by
      simpa [s] using Nat.lt_succ_sqrt n
    have hnltReal : (n : ℝ) < ((s + 1) * (s + 1) : ℕ) := by
      exact_mod_cast hnlt
    have hsqrtsq : (Real.sqrt n) ^ 2 = n :=
      Real.sq_sqrt (by positivity)
    norm_num at hnltReal
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hdles : (d : ℝ) ≤ s := by exact_mod_cast hd
  have htarget : ((x : ℝ) - y) ≤
      (15 / 64 : ℝ) * (((K - 1) * s : ℕ) : ℝ) := by
    have hKreal : (16 : ℝ) ≤ K := by exact_mod_cast hK
    have hsreal : (K : ℝ) ≤ s := by exact_mod_cast hsqrt
    have hstep : ((x : ℝ) - y) ≤
        (K : ℝ) / 16 * ((s : ℝ) + 1) + s := by
      nlinarith
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
    calc
      ((x : ℝ) - y) ≤
          (K : ℝ) / 16 * ((s : ℝ) + 1) + s := hstep
      _ ≤ (15 / 64 : ℝ) * (((K : ℝ) - 1) * s) := by
        nlinarith
  have hCreal : (((K - 1) * s : ℕ) : ℝ) ≤ C := by exact_mod_cast hC
  have hscale : (15 / 64 : ℝ) * (((K - 1) * s : ℕ) : ℝ) ≤
      (15 / 64 : ℝ) * C :=
    mul_le_mul_of_nonneg_left hCreal (by norm_num)
  have hfinal : ((x : ℝ) - y) ≤ (15 / 64 : ℝ) * C :=
    htarget.trans hscale
  calc
    (((x - y : ℕ) : ℝ)) = (x : ℝ) - y := by
      rw [Nat.cast_sub hyx]
    _ ≤ (15 / 64 : ℝ) * C := hfinal
    _ = (1 / 4 - 1 / 64 : ℝ) * C := by ring

/-- The Gaussian parameters chosen for the negative one-small-cover window
also give the positive window used in the forced-left-cover arm.  This
exposes the comparison needed when one common scale `K` is shared by all
cover-regime branches. -/
lemma positive_gaussianWindow_of_negative
    {ε : ℝ} {K M : ℕ} (hM : 0 < M) (hMK : 16 * M < K)
    (hnegative : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K))) :
    (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16) := by
  have hK : 16 ≤ K := by omega
  have hKpos : 0 < K := by omega
  let u : ℝ := (M : ℝ) * Real.sqrt 2
  let v : ℝ := Real.sqrt 2 / K
  let w : ℝ := (K : ℝ) * Real.sqrt 2 / 16
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvu : v ≤ u := by
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hinv : (1 : ℝ) / K ≤ M :=
      ((div_le_one hKreal).2 hKone).trans hMreal
    have hmul := mul_le_mul_of_nonneg_right hinv hsqrt2.le
    simpa [u, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have huw : u ≤ w := by
    have hMKreal : (16 : ℝ) * M ≤ K := by
      exact_mod_cast (Nat.le_of_lt hMK)
    dsimp [u, w]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    have hmul := mul_le_mul_of_nonneg_right hMKreal hsqrt2.le
    nlinarith
  have hhalfMono : gaussianHalfInterval u ≤ gaussianHalfInterval w :=
    gaussianHalfInterval_mono (by dsimp [u]; positivity) huw
  have hhalfV : 0 ≤ gaussianHalfInterval v := by
    have hmono := gaussianHalfInterval_mono (a := 0) (b := v) (by norm_num) hv
    simpa [gaussianHalfInterval] using hmono
  have hc : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  have hpositiveEq :
      BinomialCLT.gaussianWindowMass 0 w = gaussianWindow 0 w := by
    simpa using gaussianWindowMass_eq_gaussianWindow (u := 0) (v := w)
      (by norm_num) hw
  have hdominates :
      BinomialCLT.gaussianWindowMass (-u) (-v) ≤
        BinomialCLT.gaussianWindowMass 0 w := by
    calc
      BinomialCLT.gaussianWindowMass (-u) (-v) =
          (gaussianHalfInterval u - gaussianHalfInterval v) /
            Real.sqrt (2 * Real.pi) :=
        OneSmallGaussian.gaussianWindowMass_neg_neg hv hvu
      _ ≤ gaussianHalfInterval w / Real.sqrt (2 * Real.pi) := by
        rw [div_le_div_iff_of_pos_right hc]
        linarith
      _ = gaussianWindow 0 w := by
        simp [gaussianWindow, gaussianHalfInterval]
      _ = BinomialCLT.gaussianWindowMass 0 w := hpositiveEq.symm
  dsimp [u, v, w] at hnegative hdominates ⊢
  exact hnegative.trans_le hdominates

/-! ## A product-form Gaussian window for the intermediate two-large arm -/

/-- The elementary central estimate at product `15/32`.  This is the
slightly strengthened numerical core needed after the original-side forest
is combined with the two balanced-cover capacities. -/
lemma central_polynomial_bound_fifteen_thirtyTwo
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u * v = 15 / 32)
    (hu' : u ≤ Real.sqrt 2) (hv' : v ≤ Real.sqrt 2) :
    (251 : ℝ) / 200 ≤
      (u - u ^ 3 / 6) + (v - v ^ 3 / 6) := by
  let s := u + v
  have hspos : 0 < s := add_pos hu hv
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsLower : (34 / 25 : ℝ) ≤ s := by
    have hsq : (15 / 8 : ℝ) ≤ s ^ 2 := by
      dsimp [s]
      nlinarith [sq_nonneg (u - v)]
    by_contra h
    have hslt : s < 34 / 25 := lt_of_not_ge h
    have hsSqLt : s ^ 2 < (34 / 25 : ℝ) ^ 2 := by nlinarith
    norm_num at hsSqLt hsq
    linarith
  have hsUpper : s ≤ (7 / 4 : ℝ) := by
    have hnonneg : 0 ≤ (Real.sqrt 2 - u) * (Real.sqrt 2 - v) :=
      mul_nonneg (sub_nonneg.2 hu') (sub_nonneg.2 hv')
    have hsqrtLower : (79 / 56 : ℝ) < Real.sqrt 2 := by
      nlinarith [hsqrtSq]
    dsimp [s]
    nlinarith
  have hpolyEq :
      (u - u ^ 3 / 6) + (v - v ^ 3 / 6) =
        (79 / 64 : ℝ) * s - s ^ 3 / 6 := by
    dsimp [s]
    nlinarith
  rw [hpolyEq]
  by_cases hs : s ≤ (3 / 2 : ℝ)
  · have hbracket :
        0 ≤ (79 / 64 : ℝ) -
          (s ^ 2 + s * (34 / 25 : ℝ) + (34 / 25 : ℝ) ^ 2) / 6 := by
      have ha : (34 / 25 : ℝ) ≤ 3 / 2 := by norm_num
      have hs0 : 0 ≤ s := hspos.le
      nlinarith [sq_nonneg (s - 34 / 25)]
    have hmono := mul_nonneg (sub_nonneg.2 hsLower) hbracket
    have hbase : (251 / 200 : ℝ) ≤
        (79 / 64 : ℝ) * (34 / 25) - (34 / 25 : ℝ) ^ 3 / 6 := by
      norm_num
    nlinarith
  · have hsa : (3 / 2 : ℝ) ≤ s := le_of_not_ge hs
    have hleft : 0 ≤ s - (3 / 2 : ℝ) := sub_nonneg.2 hsa
    have hright : 0 ≤ (7 / 4 : ℝ) - s := sub_nonneg.2 hsUpper
    have hsumpos : 0 ≤ s + (3 / 2 : ℝ) + 7 / 4 := by positivity
    have hconcave :
        0 ≤ (s - (3 / 2 : ℝ)) * ((7 / 4 : ℝ) - s) *
          (s + (3 / 2 : ℝ) + 7 / 4) :=
      mul_nonneg (mul_nonneg hleft hright) hsumpos
    have hweightLeft : 0 ≤ (7 / 4 : ℝ) - s := hright
    have hweightRight : 0 ≤ s - (3 / 2 : ℝ) := hleft
    have hfa : (251 / 200 : ℝ) ≤
        (79 / 64 : ℝ) * (3 / 2) - (3 / 2 : ℝ) ^ 3 / 6 := by
      norm_num
    have hfb : (251 / 200 : ℝ) ≤
        (79 / 64 : ℝ) * (7 / 4) - (7 / 4 : ℝ) ^ 3 / 6 := by
      norm_num
    have hchord : (251 / 200 : ℝ) ≤
        4 * ((7 / 4 - s) *
          ((79 / 64 : ℝ) * (3 / 2) - (3 / 2 : ℝ) ^ 3 / 6) +
        (s - 3 / 2) *
          ((79 / 64 : ℝ) * (7 / 4) - (7 / 4 : ℝ) ^ 3 / 6)) := by
      nlinarith
    nlinarith

lemma sqrt_two_pi_div_two_lt_twoHundredFiftyOne_div_twoHundred :
    Real.sqrt (2 * Real.pi) / 2 < (251 : ℝ) / 200 := by
  have hc : 0 < (251 / 100 : ℝ) := by norm_num
  have hsqrt : Real.sqrt (2 * Real.pi) < (251 / 100 : ℝ) := by
    rw [Real.sqrt_lt' hc]
    nlinarith [Real.pi_lt_d4]
  linarith

/-- Exact-product form of the Gaussian estimate used in the intermediate
two-large-cover argument. -/
theorem gaussianWindow_gt_half_of_mul_eq_fifteen_thirtyTwo
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u * v = 15 / 32) :
    (1 / 2 : ℝ) < gaussianWindow u v := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2Sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hmass : Real.sqrt (2 * Real.pi) / 2 <
      gaussianHalfInterval u + gaussianHalfInterval v := by
    rcases le_or_gt u (Real.sqrt 2) with huSmall | huLarge
    · rcases le_or_gt v (Real.sqrt 2) with hvSmall | hvLarge
      · have hpoly := central_polynomial_bound_fifteen_thirtyTwo
          hu hv huv huSmall hvSmall
        have huInt := gaussianHalfInterval_lower hu.le
        have hvInt := gaussianHalfInterval_lower hv.le
        have hconst :=
          sqrt_two_pi_div_two_lt_twoHundredFiftyOne_div_twoHundred
        linarith
      · have hult : u < 1 / 3 := by
          have hmul := mul_lt_mul_of_pos_left hvLarge hu
          nlinarith [hsqrt2Sq]
        have hk : gaussianKernel v < 2 / 5 := by
          calc
            gaussianKernel v = Real.exp (-(v ^ 2) / 2) := rfl
            _ < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith)
            _ < 2 / 5 := Real.exp_neg_one_lt_d9.trans (by norm_num)
        have huSq : u ^ 2 < 1 / 9 := by nlinarith
        have hvu3 : v * u ^ 3 = (15 / 32 : ℝ) * u ^ 2 := by
          calc
            v * u ^ 3 = (u * v) * u ^ 2 := by ring
            _ = (15 / 32 : ℝ) * u ^ 2 := by rw [huv]
        have hscaled : 2 / 5 < v * (u - u ^ 3 / 6) := by
          nlinarith
        have htailLt : (∫ t : ℝ in Set.Ioi v, gaussianKernel t) <
            gaussianHalfInterval u := by
          calc
            (∫ t : ℝ in Set.Ioi v, gaussianKernel t) ≤
                gaussianKernel v / v := gaussianKernel_tail_le hv
            _ < u - u ^ 3 / 6 := by
              rw [div_lt_iff₀ hv]
              simpa [mul_comm] using hk.trans hscaled
            _ ≤ gaussianHalfInterval u := gaussianHalfInterval_lower hu.le
        nlinarith [gaussianHalfInterval_add_tail hv.le]
    · have hvlt : v < 1 / 3 := by
        have hmul := mul_lt_mul_of_pos_right huLarge hv
        nlinarith [hsqrt2Sq]
      have hk : gaussianKernel u < 2 / 5 := by
        calc
          gaussianKernel u = Real.exp (-(u ^ 2) / 2) := rfl
          _ < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith)
          _ < 2 / 5 := Real.exp_neg_one_lt_d9.trans (by norm_num)
      have hvSq : v ^ 2 < 1 / 9 := by nlinarith
      have huv3 : u * v ^ 3 = (15 / 32 : ℝ) * v ^ 2 := by
        calc
          u * v ^ 3 = (u * v) * v ^ 2 := by ring
          _ = (15 / 32 : ℝ) * v ^ 2 := by rw [huv]
      have hscaled : 2 / 5 < u * (v - v ^ 3 / 6) := by
        nlinarith
      have htailLt : (∫ t : ℝ in Set.Ioi u, gaussianKernel t) <
          gaussianHalfInterval v := by
        calc
          (∫ t : ℝ in Set.Ioi u, gaussianKernel t) ≤
              gaussianKernel u / u := gaussianKernel_tail_le hu
          _ < v - v ^ 3 / 6 := by
            rw [div_lt_iff₀ hu]
            simpa [mul_comm] using hk.trans hscaled
          _ ≤ gaussianHalfInterval v := gaussianHalfInterval_lower hv.le
      nlinarith [gaussianHalfInterval_add_tail hu.le]
  rw [gaussianWindow, lt_div_iff₀ hsqrt]
  nlinarith

/-- Monotone product form. -/
theorem gaussianWindow_gt_half_of_fifteen_thirtyTwo_le_mul
    {u v : ℝ} (hu : 0 < u) (_hv : 0 < v)
    (huv : (15 / 32 : ℝ) ≤ u * v) :
    (1 / 2 : ℝ) < gaussianWindow u v := by
  let v₀ : ℝ := (15 / 32 : ℝ) / u
  have hv₀ : 0 < v₀ := by dsimp [v₀]; positivity
  have hv₀v : v₀ ≤ v := by
    dsimp [v₀]
    rw [div_le_iff₀ hu]
    simpa [mul_comm] using huv
  have hprod : u * v₀ = (15 / 32 : ℝ) := by
    dsimp [v₀]
    field_simp
  have hbase := gaussianWindow_gt_half_of_mul_eq_fifteen_thirtyTwo
    hu hv₀ hprod
  have hmono : gaussianWindow u v₀ ≤ gaussianWindow u v := by
    unfold gaussianWindow
    have hh := gaussianHalfInterval_mono hv₀.le hv₀v
    have hsqrt : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    gcongr
  exact hbase.trans_le hmono

/-- Uniform counting endpoint for the forced-large balanced-left-cover arm
throughout the whole range `A.card - n ≤ floor(sqrt n)`.  The conclusion is
for the original, unbalanced cut `(A,B)`; the matching found in `A₀ = A \ T`
is enlarged to the original sampled left part. -/
theorem eventually_intermediate_oneSmallCover_left_goodSample_count
    {ε : ℝ} (hε : 0 < ε) {K : ℕ}
    (hK : 16 ≤ K)
    (hgauss : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ C : Finset (Fin (2 * n))),
        IsCut A B → n ≤ A.card →
        A.card - n ≤ Nat.sqrt n →
        A₀ = A \ T →
        IsMinimumVertexCoverOn G A₀ C →
        n + 1 ≤ sqrtCoverThreshold K n * (C.card + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hab : (0 : ℝ) ≤ (K : ℝ) * Real.sqrt 2 / 16 := by positivity
  have hclt :=
    BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio hab hgauss
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hclt
  have hclt2 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) - ε / 2 <
        (BinomialCLT.fairBinomialWindowCount (2 * n) 0
          ((K : ℝ) * Real.sqrt 2 / 16) : ℝ) /
          (2 : ℝ) ^ (2 * n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    exact hN (2 * n) (by omega)
  have hhall := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := 1) (eps := (1 / 64 : ℝ)) (delta := ε / 2)
      (by omega) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [hclt2, hhall,
      Filter.eventually_ge_atTop (K * K)] with n hnWindow hnHall hnlarge
  intro G A B T A₀ C hcut hnA hd hA₀ hC hprod
  have hsqrt : K ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hnlarge)
  have hsum : A.card + B.card = 2 * n := by
    simpa using hcut.card_add_card
  let d := A.card - n
  have hb : B.card = n - d := by omega
  have hCsqrt : sqrtCoverThreshold 1 n ≤ C.card := by
    simp only [sqrtCoverThreshold, Nat.div_one]
    have honeK : 1 < K := by omega
    simpa using (coverProductArm_forces_sqrtCover
      (n := n) (K := K) (H := 1) (D := C.card) honeK hprod)
  let threshold : ℝ := (1 / 4 - 1 / 64 : ℝ) * C.card
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
        Set.Icc 0 ((K : ℝ) * Real.sqrt 2 / 16)
  let Failure : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S threshold
  have hfailure :
      (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        (ε / 2) * (2 : ℝ) ^ (2 * n) := by
    have h := hnHall (Fin (2 * n)) G A₀ C hC hCsqrt
    simpa [Failure, threshold, almostBipartiteCount,
      almostBipartiteEvent] using h
  have hcountEq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P =
        BinomialCLT.fairBinomialWindowCount (2 * n) 0
          ((K : ℝ) * Real.sqrt 2 / 16) := by
    simpa [P] using cut_difference_window_count hcut 0
      ((K : ℝ) * Real.sqrt 2 / 16)
  have hwindowRaw :
      ((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    rw [hcountEq]
    exact le_of_lt ((lt_div_iff₀ (by positivity)).mp hnWindow)
  have hgoodWindow : ∀ S : Finset (Fin (2 * n)), S ⊆ Finset.univ →
      P S → ¬ Failure S → IsKGoodSample G A B S 0 := by
    intro S _hSuniv hSP hnotFailure
    have hy : (S ∩ B).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hbnds := intermediate_positive_window_bounds hK hsqrt
      (d := d) (C := C.card) (x := (S ∩ A).card)
      (y := (S ∩ B).card) (by simpa [d] using hd)
      (by simpa [hb] using hy) hprod (by simpa [P, hb] using hSP)
    have hpartCard :
        (restrictedPart S B).card ≤ (restrictedPart S A).card := by
      simpa only [card_restrictedPart_eq_inter] using hbnds.1
    have hmatching : RandomCover.HasMatchingAtLeast
        (internalGraph G A₀) S threshold := by
      simpa [Failure] using hnotFailure
    obtain ⟨M, hMmatching, hMsupport, hMcard⟩ := hmatching
    have hmatchingTarget : RandomCover.HasMatchingAtLeast
        (internalGraph G A₀) S
          (((restrictedPart S A).card -
            (restrictedPart S B).card : ℕ) : ℝ) := by
      refine ⟨M, hMmatching, hMsupport, ?_⟩
      have hthreshold :
          (((restrictedPart S A).card -
            (restrictedPart S B).card : ℕ) : ℝ) ≤ threshold := by
        simpa only [card_restrictedPart_eq_inter] using hbnds.2
      exact hthreshold.trans hMcard
    have hforest₀ := hmatchingTarget.induce_internalGraph
    have hpartMono : restrictedPart S A₀ ⊆ restrictedPart S A := by
      intro v hv
      apply mem_restrictedPart.mpr
      have hvA₀ := mem_restrictedPart.mp hv
      rw [hA₀] at hvA₀
      exact Finset.sdiff_subset hvA₀
    have hforest : ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
        (restrictedPart S A)
        ((restrictedPart S A).card - (restrictedPart S B).card) :=
      ContainsLinearForestWith.mono_vertexSet hforest₀ hpartMono
    refine ⟨restrictedParts_isCut hcut, Or.inl ⟨hpartCard, ?_⟩⟩
    simpa using hforest
  have hgood := goodSample_count_of_window_failure G P Failure
    (((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n)) (ε / 2)
    hgoodWindow hwindowRaw (by simpa using hfailure)
  convert hgood using 1
  all_goals simp
  all_goals ring

end

end Erdos622.AlmostBipartiteRegimeCounts
