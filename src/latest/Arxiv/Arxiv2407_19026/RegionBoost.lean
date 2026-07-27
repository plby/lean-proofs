import Arxiv.Arxiv2407_19026.Profiles

/-!
# Entropy bounds and the Ramsey-region boost

This file isolates the argument around Lemma `l:y`.  The printed lemma uses
an estimate stated only for `l ≤ k` to assert membership in a symmetric
Ramsey region, whose definition quantifies over every ordered pair `(k,l)`.
The one-sided implication is proved below as
`eventuallyOrderedRamseyBound_leftBoost`.  The exact additional condition
needed to recover membership in the paper's (two-sided) region is expressed
by `twoSidedEntropyCertificate_mem_ramseyRegion`.
-/

noncomputable section

open Finset

namespace Arxiv2407_19026

/-- The entropy exponent improved by `α` times the smaller parameter. -/
def entropyImprovement (α z : ℝ) : ℝ :=
  ramseyEntropy z - α * z

/-- The one-sided eventual bound actually obtained in the first half of the
proof of `l:y`. -/
def EventuallyOrderedRamseyBound (x y : ℝ) : Prop :=
  ∃ N : ℕ, ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k → N ≤ k →
    (ramseyNumber k l : ℝ) * x ^ k * y ^ l ≤ 1

lemma ramseyProperty_swap {k l n : ℕ} :
    RamseyProperty k l n → RamseyProperty l k n := by
  intro h G hbad
  apply h Gᶜ
  constructor
  · simpa [SimpleGraph.cliqueFree_compl] using hbad.2
  · simpa [SimpleGraph.indepSetFree_compl] using hbad.1

lemma ramseyNumber_swap (k l : ℕ) :
    ramseyNumber k l = ramseyNumber l k := by
  apply le_antisymm
  · exact Erdos1014.ramseyNumber_le_of_property
      (ramseyProperty_swap (Erdos1014.ramseyNumber_spec l k))
  · exact Erdos1014.ramseyNumber_le_of_property
      (ramseyProperty_swap (Erdos1014.ramseyNumber_spec k l))

/-- The log-sum inequality in the two-variable form used by the paper. -/
lemma two_mass_entropy_le_cross_entropy
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hx1 : x < 1) :
    (a + b) * Real.log (a + b) -
        a * Real.log a - b * Real.log b ≤
      -a * Real.log x - b * Real.log (1 - x) := by
  have hab : 0 < a + b := add_pos ha hb
  have h1raw := Real.log_le_sub_one_of_pos
    (mul_pos hx (div_pos hab ha))
  have h2raw := Real.log_le_sub_one_of_pos
    (mul_pos (sub_pos.mpr hx1) (div_pos hab hb))
  have h1 :
      a * Real.log (x * ((a + b) / a)) ≤
        a * (x * ((a + b) / a) - 1) :=
    mul_le_mul_of_nonneg_left h1raw ha.le
  have h2 :
      b * Real.log ((1 - x) * ((a + b) / b)) ≤
        b * ((1 - x) * ((a + b) / b) - 1) :=
    mul_le_mul_of_nonneg_left h2raw hb.le
  rw [Real.log_mul hx.ne' (div_ne_zero hab.ne' ha.ne'),
    Real.log_div hab.ne' ha.ne'] at h1
  rw [Real.log_mul (sub_pos.mpr hx1).ne'
      (div_ne_zero hab.ne' hb.ne'),
    Real.log_div hab.ne' hb.ne'] at h2
  have hsum := add_le_add h1 h2
  field_simp [ha.ne', hb.ne'] at hsum
  nlinarith

lemma ramseyEntropy_mul_eq_two_mass_entropy
    {k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    ramseyEntropy (l / k) * k =
      (k + l) * Real.log (k + l) -
        k * Real.log k - l * Real.log l := by
  have hkl : 0 < k + l := add_pos hk hl
  rw [ramseyEntropy, Real.log_div hl.ne' hk.ne']
  have heq : l / k + 1 = (k + l) / k := by
    field_simp
    ring
  rw [heq, Real.log_div hkl.ne' hk.ne']
  field_simp [hk.ne']
  ring

/-- The exponential of a negative integral multiple of a logarithm. -/
lemma exp_neg_nat_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log x) = x⁻¹ ^ n := by
  rw [show -(n : ℝ) * Real.log x =
      (n : ℕ) * (-Real.log x) by norm_num,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]

/-- A two-sided entropy certificate is the missing compatibility condition
between a one-sided exponent estimate and the symmetric Ramsey region. -/
structure TwoSidedEntropyCertificate (α x y : ℝ) : Prop where
  forward :
    ∀ a b : ℝ, 0 < a → 0 < b → b ≤ a →
      ramseyEntropy (b / a) * a - α * b ≤
        -a * Real.log x - b * Real.log y
  backward :
    ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b →
      ramseyEntropy (a / b) * b - α * a ≤
        -a * Real.log x - b * Real.log y

/-- A one-sided exponent estimate plus a two-sided entropy certificate gives
the strict-coordinate estimates required by the definition of `𝓡`. -/
lemma eventuallyRamseyBound_of_twoSidedEntropyCertificate
    {α x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (C : TwoSidedEntropyCertificate α x y)
    (hExp : HasRamseyExponent (entropyImprovement α)) :
    ∀ x₀ y₀ : ℝ, 0 < x₀ → x₀ < x → 0 < y₀ → y₀ < y →
      EventuallyRamseyBound x₀ y₀ := by
  intro x₀ y₀ hx₀ hxx hy₀ hyy
  have hlogx : Real.log x₀ < Real.log x :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hx₀)
      (Set.mem_Ioi.mpr hx) hxx
  have hlogy : Real.log y₀ < Real.log y :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hy₀)
      (Set.mem_Ioi.mpr hy) hyy
  let ε : ℝ := min (Real.log x - Real.log x₀)
    (Real.log y - Real.log y₀) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨K, hK⟩ := hExp ε hε
  refine ⟨2 * K, ?_⟩
  intro k l hk hl hsum
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by omega)
  have hlR : (0 : ℝ) < l := by
    exact_mod_cast (show 0 < l by omega)
  have hεx : ε ≤ Real.log x - Real.log x₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_left _ _)
  have hεy : ε ≤ Real.log y - Real.log y₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_right _ _)
  have finish
      (hbound : (ramseyNumber k l : ℝ) ≤
        Real.exp (-(k : ℝ) * Real.log x₀ -
          (l : ℝ) * Real.log y₀)) :
      (ramseyNumber k l : ℝ) * x₀ ^ k * y₀ ^ l ≤ 1 := by
    calc
      (ramseyNumber k l : ℝ) * x₀ ^ k * y₀ ^ l ≤
          Real.exp (-(k : ℝ) * Real.log x₀ -
            (l : ℝ) * Real.log y₀) * x₀ ^ k * y₀ ^ l := by
        gcongr
      _ = 1 := by
        rw [show -(k : ℝ) * Real.log x₀ -
              (l : ℝ) * Real.log y₀ =
            (-(k : ℝ) * Real.log x₀) +
              (-(l : ℝ) * Real.log y₀) by ring,
          Real.exp_add, exp_neg_nat_mul_log hx₀,
          exp_neg_nat_mul_log hy₀]
        calc
          x₀⁻¹ ^ k * y₀⁻¹ ^ l * x₀ ^ k * y₀ ^ l =
              (x₀⁻¹ * x₀) ^ k * (y₀⁻¹ * y₀) ^ l := by
            rw [mul_pow, mul_pow]
            ring
          _ = 1 := by simp [hx₀.ne', hy₀.ne']
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  by_cases hlk : l ≤ k
  · have hkK : K ≤ k := by omega
    have hraw := hK k l hkK hl hlk
    apply finish
    refine hraw.trans (Real.exp_le_exp_of_le ?_)
    have hcross := C.forward k l hkR hlR
      (by exact_mod_cast hlk)
    dsimp [entropyImprovement] at hraw ⊢
    have hxmul := mul_le_mul_of_nonneg_left hεx hk0
    have hymul :=
      mul_nonneg hl0 (sub_nonneg.mpr hlogy.le)
    have hexpand :
        (ramseyEntropy ((l : ℝ) / k) -
            α * ((l : ℝ) / k) + ε) * k =
          ramseyEntropy ((l : ℝ) / k) * k -
            α * l + ε * k := by
      field_simp [hkR.ne']
    rw [hexpand]
    nlinarith
  · have hkl : k ≤ l := by omega
    have hlK : K ≤ l := by omega
    have hraw := hK l k hlK hk hkl
    rw [← ramseyNumber_swap] at hraw
    apply finish
    refine hraw.trans (Real.exp_le_exp_of_le ?_)
    have hcross := C.backward k l hkR hlR
      (by exact_mod_cast hkl)
    dsimp [entropyImprovement] at hraw ⊢
    have hxmul :=
      mul_nonneg hk0 (sub_nonneg.mpr hlogx.le)
    have hymul := mul_le_mul_of_nonneg_left hεy hl0
    have hexpand :
        (ramseyEntropy ((k : ℝ) / l) -
            α * ((k : ℝ) / l) + ε) * l =
          ramseyEntropy ((k : ℝ) / l) * l -
            α * k + ε * l := by
      field_simp [hlR.ne']
    rw [hexpand]
    nlinarith

/-- Certified version of the Ramsey-region conclusion intended in `l:y`. -/
theorem twoSidedEntropyCertificate_mem_ramseyRegion
    {α x y : ℝ}
    (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1)
    (C : TwoSidedEntropyCertificate α x y)
    (hExp : HasRamseyExponent (entropyImprovement α)) :
    (x, y) ∈ ramseyRegion := by
  apply mem_ramseyRegion_of_strict_eventuallyRamseyBound
    hx hx1 hy hy1
  exact eventuallyRamseyBound_of_twoSidedEntropyCertificate
    hx hy C hExp

/-- The first, genuinely one-sided estimate in the proof of `l:y`.  The
additional hypothesis `eᵅ(1-x)<1` is forced by the definition of the Ramsey
region and is absent from the printed statement. -/
theorem eventuallyOrderedRamseyBound_leftBoost
    {α x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hα : 0 ≤ α)
    (hy1 : Real.exp α * (1 - x) < 1)
    (hExp : HasRamseyExponent (entropyImprovement α)) :
    ∀ x₀ y₀ : ℝ, 0 < x₀ → x₀ < x →
      0 < y₀ → y₀ < Real.exp α * (1 - x) →
      EventuallyOrderedRamseyBound x₀ y₀ := by
  intro x₀ y₀ hx₀ hxx hy₀ hyy
  have hy : 0 < Real.exp α * (1 - x) :=
    mul_pos (Real.exp_pos α) (sub_pos.mpr hx1)
  have hlogx : Real.log x₀ < Real.log x :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hx₀)
      (Set.mem_Ioi.mpr hx) hxx
  have hlogy :
      Real.log y₀ <
        Real.log (Real.exp α * (1 - x)) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hy₀)
      (Set.mem_Ioi.mpr hy) hyy
  let ε : ℝ := min (Real.log x - Real.log x₀)
    (Real.log (Real.exp α * (1 - x)) - Real.log y₀) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨K, hK⟩ := hExp ε hε
  refine ⟨K, ?_⟩
  intro k l hk hl hlk hkK
  have hkR : (0 : ℝ) < k := by positivity
  have hlR : (0 : ℝ) < l := by positivity
  have hraw := hK k l hkK hl hlk
  have hmass := two_mass_entropy_le_cross_entropy
    hkR hlR hx hx1
  have hentropy := ramseyEntropy_mul_eq_two_mass_entropy
    hkR hlR
  have hlogProduct :
      Real.log (Real.exp α * (1 - x)) =
        α + Real.log (1 - x) := by
    rw [Real.log_mul (Real.exp_ne_zero α)
      (sub_pos.mpr hx1).ne', Real.log_exp]
  have hcross :
      ramseyEntropy ((l : ℝ) / k) * k - α * l ≤
        -(k : ℝ) * Real.log x -
          (l : ℝ) * Real.log (Real.exp α * (1 - x)) := by
    rw [hentropy, hlogProduct]
    nlinarith
  have hεx : ε ≤ Real.log x - Real.log x₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_left _ _)
  have hεy :
      ε ≤ Real.log (Real.exp α * (1 - x)) -
        Real.log y₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_right _ _)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hxmul := mul_le_mul_of_nonneg_left hεx hk0
  have hymul :=
    mul_nonneg hl0 (sub_nonneg.mpr hlogy.le)
  have hexpand :
      (entropyImprovement α ((l : ℝ) / k) + ε) * k =
        ramseyEntropy ((l : ℝ) / k) * k -
          α * l + ε * k := by
    dsimp [entropyImprovement]
    field_simp [hkR.ne']
  have hexponent :
      (entropyImprovement α ((l : ℝ) / k) + ε) * k ≤
        -(k : ℝ) * Real.log x₀ - (l : ℝ) * Real.log y₀ := by
    rw [hexpand]
    nlinarith
  have hbound := hraw.trans
    (Real.exp_le_exp_of_le hexponent)
  calc
    (ramseyNumber k l : ℝ) * x₀ ^ k * y₀ ^ l ≤
        Real.exp (-(k : ℝ) * Real.log x₀ -
          (l : ℝ) * Real.log y₀) * x₀ ^ k * y₀ ^ l := by
      gcongr
    _ = 1 := by
      rw [show -(k : ℝ) * Real.log x₀ -
            (l : ℝ) * Real.log y₀ =
          (-(k : ℝ) * Real.log x₀) +
            (-(l : ℝ) * Real.log y₀) by ring,
        Real.exp_add, exp_neg_nat_mul_log hx₀,
        exp_neg_nat_mul_log hy₀]
      calc
        x₀⁻¹ ^ k * y₀⁻¹ ^ l * x₀ ^ k * y₀ ^ l =
            (x₀⁻¹ * x₀) ^ k * (y₀⁻¹ * y₀) ^ l := by
          rw [mul_pow, mul_pow]
          ring
        _ = 1 := by simp [hx₀.ne', hy₀.ne']

end Arxiv2407_19026
