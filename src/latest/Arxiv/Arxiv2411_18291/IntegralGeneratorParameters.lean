import Arxiv.Arxiv2411_18291.IntegralGeneratorExistence

/-!
# Sparse integral generators at the paper's density scales

The choices `ρ = (6*choose(q,r))⁻²` and `α = ρ/(2*q)^r`
satisfy the exchange and focusing inequalities. Every fixed output exponent
below `0.7*α` is available; we record `0.6*α` for the flattening input.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem integral_generator_parameters (q r : ℕ) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
    0 < α ∧ α * ((3 * (2 * q) ^ (r + 1) * k ^ 2 : ℕ) : ℝ) ≤ 1 / 12 ∧
      2 * α * k ≤ ρ ∧ ρ < 1 := by
  dsimp only
  let k := q.choose (r + 1)
  let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
  let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
  change 0 < α ∧ α * ((3 * (2 * q) ^ (r + 1) * k ^ 2 : ℕ) : ℝ) ≤ 1 / 12 ∧
    2 * α * k ≤ ρ ∧ ρ < 1
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.choose_pos hqr.le
  have hkp : (0 : ℝ) < k := by linarith only [hk]
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hp : 0 < (2 * q : ℝ) ^ (r + 1) := by positivity
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hα : 0 < α := div_pos hρ hp
  have hcancel : α * (2 * q : ℝ) ^ (r + 1) = ρ := div_mul_cancel₀ ρ hp.ne'
  have hrhok : ρ * (k : ℝ) ^ 2 = 1 / 36 := by
    dsimp only [ρ]
    field_simp
    ring
  have hαO : α * ((3 * (2 * q) ^ (r + 1) * k ^ 2 : ℕ) : ℝ) = 1 / 12 := by
    push_cast
    calc
      _ = 3 * (α * (2 * q : ℝ) ^ (r + 1)) * (k : ℝ) ^ 2 := by ring
      _ = 3 * (ρ * (k : ℝ) ^ 2) := by rw [hcancel]; ring
      _ = _ := by rw [hrhok]; norm_num
  have htwo : 2 ≤ 2 ^ (r + 1) := by
    have hpow : 1 ≤ 2 ^ r := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    rw [pow_succ]
    omega
  have hscale : (2 : ℝ) * k ≤ (2 * q : ℝ) ^ (r + 1) := by
    have hnat : 2 * k ≤ (2 * q) ^ (r + 1) := by
      calc
        _ ≤ 2 * q ^ (r + 1) := Nat.mul_le_mul_left 2 (Nat.choose_le_pow q (r + 1))
        _ ≤ 2 ^ (r + 1) * q ^ (r + 1) := Nat.mul_le_mul_right _ htwo
        _ = _ := (mul_pow 2 q (r + 1)).symm
    exact_mod_cast hnat
  refine ⟨hα, hαO.le, ?_, ?_⟩
  · rw [show 2 * α * k = (2 * k : ℝ) * ρ / (2 * q : ℝ) ^ (r + 1) by
      dsimp only [α]; ring]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hscale hρ.le
  · dsimp only [ρ]
    apply (div_lt_one (by positivity)).mpr
    nlinarith only [hk, sq_nonneg (k : ℝ)]

theorem eventually_exists_sparse_integral_generators_paper_parameters
    (q r : ℕ) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * α / 5))) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          DegreeDivisible q J → GeneratedBy D J := by
  dsimp only
  obtain ⟨hα, hαO, hρ, hρ1⟩ := integral_generator_parameters q r hqr
  exact eventually_exists_sparse_divisible_generators q r hqr hα hαO hρ hρ1
    (by positivity) (by linarith only [hα])

end Arxiv2411_18291
