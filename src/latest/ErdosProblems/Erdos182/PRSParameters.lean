/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Numerical parameters in the Pyber--Rödl--Szemerédi argument

This file isolates the (purely ordered-field) choice of the four parameters
appearing in (12) of the mathematical write-up.  Keeping this bookkeeping out
of the graph-theoretic proof makes all strict inequalities, and in particular
the positivity of the two denominators, available as named fields.

The final two lemmas are the precise logarithm/exponent conversion used in
(14).  Notice the extra `+γ` in its hypothesis: it is exactly the unit of
slack needed to pass from a real exponent to its natural floor.
-/

namespace Erdos182

/-- A package of constants satisfying all the inequalities in (12).

`lambda`, `alpha`, and `gamma` are natural because they are degrees or
cardinality parameters.  Only the interpolation base `beta` is genuinely
real. -/
structure PRSParameters (k : ℕ) (η : ℝ) where
  lambda : ℕ
  alpha : ℕ
  beta : ℝ
  gamma : ℕ
  lambda_ge : 4 * k - 3 ≤ lambda
  inv_lambda_lt : 1 / (lambda : ℝ) < η / 4
  alpha_gt_one : 1 < alpha
  alpha_den_pos : 0 < (alpha : ℝ) - 1
  alpha_ratio_lt :
    ((alpha : ℝ) + 1) / ((alpha : ℝ) - 1) < 1 + η / 8
  beta_gt_one : 1 < beta
  beta_ratio_lt :
    beta * (((alpha : ℝ) + 1) / ((alpha : ℝ) - 1)) < 1 + η / 4
  gamma_gt_lambda : lambda < gamma
  gamma_den_pos : 0 < 1 - (lambda : ℝ) / (gamma : ℝ)
  final_ratio_lt :
    (beta * (((alpha : ℝ) + 1) / ((alpha : ℝ) - 1))) /
        (1 - (lambda : ℝ) / (gamma : ℝ)) <
      1 + η / 2

namespace PRSParameters

/-- A natural number can make `q / (1 - l/g)` as close to `q` as desired.
This is the last, and only Archimedean, step in the choice of (12). -/
private lemma exists_gamma {q t : ℝ} (hq : 0 < q) (hqt : q < t) (l : ℕ) :
    ∃ g : ℕ, l < g ∧ 0 < 1 - (l : ℝ) / (g : ℝ) ∧
      q / (1 - (l : ℝ) / (g : ℝ)) < t := by
  have ht : 0 < t := hq.trans hqt
  let ε : ℝ := 1 - q / t
  have hqt' : q / t < 1 := (div_lt_one ht).2 hqt
  have hε : 0 < ε := sub_pos.2 hqt'
  obtain ⟨g, hg⟩ := exists_nat_gt
    (max ((l : ℝ) + 1) ((l : ℝ) / ε))
  have hgl1 : (l : ℝ) + 1 < g :=
    (le_max_left _ _).trans_lt hg
  have hgle : (l : ℝ) / ε < g :=
    (le_max_right _ _).trans_lt hg
  have hgpos : (0 : ℝ) < g := by
    have : (0 : ℝ) ≤ l := by positivity
    linarith
  have hlg : l < g := by exact_mod_cast (lt_trans (lt_add_one (l : ℝ)) hgl1)
  have hfrac : (l : ℝ) / (g : ℝ) < ε := by
    rw [div_lt_iff₀ hgpos]
    have := (div_lt_iff₀ hε).1 hgle
    nlinarith
  have hden : 0 < 1 - (l : ℝ) / (g : ℝ) := by
    have hεle : ε ≤ 1 := by
      dsimp [ε]
      exact sub_le_self _ (div_nonneg hq.le ht.le)
    linarith
  refine ⟨g, hlg, hden, ?_⟩
  have hden_qt : q / t < 1 - (l : ℝ) / (g : ℝ) := by
    dsimp [ε] at hfrac
    linarith
  rw [div_lt_iff₀ hden]
  have := (div_lt_iff₀ ht).1 hden_qt
  nlinarith

/-- For every positive error tolerance the four constants in (12) exist.

The proof makes the middle choices explicit.  After choosing the two natural
numbers `λ` and `α` large enough, it sets

`beta = (1 + 3 * η / 16) / ((α + 1) / (α - 1))`.

Thus the product involving `beta` is exactly `1 + 3η/16`, leaving strict
room on both sides of the required estimate. -/
theorem exists_of_pos (k : ℕ) {η : ℝ} (hη : 0 < η) :
    Nonempty (PRSParameters k η) := by
  obtain ⟨l, hl⟩ := exists_nat_gt
    (max (4 * (k : ℝ)) (4 / η + 1))
  have hlk : 4 * (k : ℝ) < l := (le_max_left _ _).trans_lt hl
  have hlη : 4 / η + 1 < l := (le_max_right _ _).trans_lt hl
  have hlpos : (0 : ℝ) < l := by
    have : 0 < 4 / η + 1 := by positivity
    linarith
  have hlbound : 4 * k - 3 ≤ l := by
    have h4k : 4 * k ≤ l := by exact_mod_cast hlk.le
    exact (Nat.sub_le (4 * k) 3).trans h4k
  have hlinv : 1 / (l : ℝ) < η / 4 := by
    apply (div_lt_div_iff₀ hlpos (by norm_num : (0 : ℝ) < 4)).2
    have hlarge : 4 / η < (l : ℝ) := by linarith
    have := (div_lt_iff₀ hη).1 hlarge
    nlinarith

  obtain ⟨a, ha⟩ := exists_nat_gt
    (max (2 : ℝ) (1 + 16 / η))
  have ha2 : (2 : ℝ) < a := (le_max_left _ _).trans_lt ha
  have haη : 1 + 16 / η < (a : ℝ) :=
    (le_max_right _ _).trans_lt ha
  have ha1 : 1 < a := by exact_mod_cast (lt_trans (by norm_num : (1 : ℝ) < 2) ha2)
  have haden : 0 < (a : ℝ) - 1 := by
    have ha1r : (1 : ℝ) < a := by exact_mod_cast ha1
    linarith
  have haformula :
      ((a : ℝ) + 1) / ((a : ℝ) - 1) =
        1 + 2 / ((a : ℝ) - 1) := by
    field_simp
    ring
  have hafrac : 2 / ((a : ℝ) - 1) < η / 8 := by
    rw [div_lt_iff₀ haden]
    have hlarge : 16 / η < (a : ℝ) - 1 := by linarith
    have := (div_lt_iff₀ hη).1 hlarge
    nlinarith
  have haratio :
      ((a : ℝ) + 1) / ((a : ℝ) - 1) < 1 + η / 8 := by
    rw [haformula]
    linarith
  have haratio_pos : 0 < ((a : ℝ) + 1) / ((a : ℝ) - 1) := by
    positivity

  let b : ℝ :=
    (1 + 3 * η / 16) / (((a : ℝ) + 1) / ((a : ℝ) - 1))
  have hratio_mid :
      ((a : ℝ) + 1) / ((a : ℝ) - 1) < 1 + 3 * η / 16 := by
    nlinarith [haratio]
  have hb1 : 1 < b := by
    dsimp [b]
    rw [lt_div_iff₀ haratio_pos]
    simpa using hratio_mid
  have hbprod :
      b * (((a : ℝ) + 1) / ((a : ℝ) - 1)) = 1 + 3 * η / 16 := by
    dsimp [b]
    exact div_mul_cancel₀ _ haratio_pos.ne'
  have hbquarter :
      b * (((a : ℝ) + 1) / ((a : ℝ) - 1)) < 1 + η / 4 := by
    rw [hbprod]
    nlinarith
  have hqpos : 0 < 1 + 3 * η / 16 := by positivity
  have hqhalf : 1 + 3 * η / 16 < 1 + η / 2 := by nlinarith
  obtain ⟨g, hlg, hgden, hgfinal⟩ :=
    exists_gamma hqpos hqhalf l
  refine ⟨⟨l, a, b, g, hlbound, hlinv, ha1, haden, haratio,
    hb1, hbquarter, hlg, hgden, ?_⟩⟩
  rw [hbprod]
  exact hgfinal

/-- Equation (13), extracted from the two strict estimates in (12). -/
theorem assembled_ratio_lt {k : ℕ} {η : ℝ} (hη : 0 < η)
    (P : PRSParameters k η) :
    1 / (P.lambda : ℝ) +
        (P.beta * (((P.alpha : ℝ) + 1) / ((P.alpha : ℝ) - 1))) /
          (1 - (P.lambda : ℝ) / (P.gamma : ℝ)) <
      1 + η := by
  nlinarith [P.inv_lambda_lt, P.final_ratio_lt]

/-- The exact tolerance used for degree `k` in the PRS proof. -/
noncomputable def eta (k : ℕ) : ℝ := 1 / (4 * (k : ℝ) - 4)

lemma eta_pos {k : ℕ} (hk : 2 ≤ k) : 0 < eta k := by
  dsimp [eta]
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  exact one_div_pos.mpr (by nlinarith)

/-- The specialization of (12) used in the regular-subgraph theorem. -/
theorem exists_for_degree (k : ℕ) (hk : 2 ≤ k) :
    Nonempty (PRSParameters k (eta k)) :=
  exists_of_pos k (eta_pos hk)

end PRSParameters

section Exponent

/-- A discrete replacement for changing logarithm bases.  For every real
base bigger than one, a fixed positive natural `M` makes
`b ^ (M * (log2 Δ + 1))` dominate every natural `Δ`. -/
lemma exists_pow_mul_log2_add_one_bound {b : ℝ} (hb : 1 < b) :
    ∃ M : ℕ, 0 < M ∧ ∀ Δ : ℕ,
      (Δ : ℝ) ≤ b ^ (M * (Nat.log2 Δ + 1)) := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ b ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hb).eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let M := N + 1
  have hMpos : 0 < M := by simp [M]
  have hMtwo : (2 : ℝ) ≤ b ^ M := hN M (by simp [M])
  refine ⟨M, hMpos, ?_⟩
  intro Δ
  let t := Nat.log2 Δ + 1
  have hΔtwoNat : Δ ≤ 2 ^ t := by
    exact (Nat.lt_log2_self (n := Δ)).le
  have hΔtwo : (Δ : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast hΔtwoNat
  calc
    (Δ : ℝ) ≤ (2 : ℝ) ^ t := hΔtwo
    _ ≤ (b ^ M) ^ t := pow_le_pow_left₀ (by norm_num) hMtwo t
    _ = b ^ (M * t) := (pow_mul b M t).symm

/-- Natural-number division bookkeeping for the discrete form of (14). -/
lemma le_floor_div_of_mul_add_one_le {δ γ q : ℕ} (hγ : 2 ≤ γ)
    (hδ : (γ - 1) * q + 1 ≤ δ) :
    q ≤ ⌊((δ : ℝ) - 1) / ((γ : ℝ) - 1)⌋₊ := by
  have hγ1 : 1 ≤ γ := by omega
  have hden : 0 < (γ : ℝ) - 1 := by
    have hγreal : (2 : ℝ) ≤ γ := by exact_mod_cast hγ
    linarith
  have hcast : (((γ : ℝ) - 1) * q + 1) ≤ (δ : ℝ) := by
    exact_mod_cast hδ
  apply Nat.le_floor
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The preceding floor lemma at the exponent used in the PRS proof. -/
lemma mul_log2_add_one_le_floor_of_degree_bound {δ γ M Δ : ℕ}
    (hγ : 2 ≤ γ)
    (hδ : (γ - 1) * (M * (Nat.log2 Δ + 1)) + 1 ≤ δ) :
    M * (Nat.log2 Δ + 1) ≤
      ⌊((δ : ℝ) - 1) / ((γ : ℝ) - 1)⌋₊ :=
  le_floor_div_of_mul_add_one_le hγ hδ

/-- A base-`b` logarithmic bound is equivalent to the corresponding natural
power bound.  This is the last implication in (14), with the exponent already
chosen. -/
lemma le_pow_nat_of_logb_le {b x : ℝ} {q : ℕ}
    (hb : 1 < b) (hx : 0 < x) (hlog : Real.logb b x ≤ q) :
    x ≤ b ^ q := by
  rw [← Real.rpow_natCast]
  exact (Real.logb_le_iff_le_rpow hb hx).1 hlog

/-- Equation (14), including its floor.  The `+γ` in the degree hypothesis
absorbs the loss of less than one when replacing a real exponent by its
natural floor. -/
lemma le_pow_floor_of_parameter_bound {δ γ : ℕ} {b x : ℝ}
    (hγ : 2 ≤ γ) (hb : 1 < b) (hx : 0 < x)
    (hδ : ((γ : ℝ) - 1) * Real.logb b x + γ ≤ δ) :
    x ≤ b ^ ⌊((δ : ℝ) - 1) / ((γ : ℝ) - 1)⌋₊ := by
  have hden : 0 < (γ : ℝ) - 1 := by
    have hγreal : (2 : ℝ) ≤ γ := by exact_mod_cast hγ
    linarith
  let y : ℝ := ((δ : ℝ) - 1) / ((γ : ℝ) - 1)
  have hlog_sub : Real.logb b x ≤ y - 1 := by
    dsimp [y]
    rw [le_sub_iff_add_le]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hlog_floor : Real.logb b x ≤ (⌊y⌋₊ : ℝ) :=
    hlog_sub.trans (Nat.sub_one_lt_floor y).le
  exact le_pow_nat_of_logb_le hb hx hlog_floor

end Exponent

end Erdos182
