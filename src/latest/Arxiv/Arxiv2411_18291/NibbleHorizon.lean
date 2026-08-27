import Arxiv.Arxiv2411_18291.RemovalDensity
import Arxiv.Arxiv2411_18291.NibbleComparisonParameters
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Rounding the deterministic stopping time -/

noncomputable section

namespace Arxiv2411_18291

def nibbleHorizon (k : ℕ) (g p₀ : ℝ) : ℕ := ⌊(1 - p₀) * g / (k : ℝ)⌋₊

theorem nibbleHorizon_mul_le {k : ℕ} (hk : 0 < k) {g p₀ : ℝ}
    (hg : 0 ≤ g) (hp₀ : p₀ ≤ 1) :
    (k : ℝ) * nibbleHorizon k g p₀ ≤ (1 - p₀) * g := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 ≤ (1 - p₀) * g / (k : ℝ) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hp₀) hg) hk'.le
  have h := (le_div_iff₀ hk').mp (Nat.floor_le hx)
  simpa only [nibbleHorizon, mul_comm] using h

theorem nibbleHorizon_density_ge {k : ℕ} (hk : 0 < k) {g p₀ : ℝ}
    (hg : 0 < g) (hp₀ : p₀ ≤ 1) :
    p₀ ≤ removalDensity k g (nibbleHorizon k g p₀) :=
  removalDensity_lower_until k hg _ (nibbleHorizon_mul_le hk hg.le hp₀) _ le_rfl

theorem nibbleHorizon_density_lt {k : ℕ} (hk : 0 < k) {g p₀ : ℝ} (hg : 0 < g) :
    removalDensity k g (nibbleHorizon k g p₀) < p₀ + (k : ℝ) / g := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfloor := Nat.lt_floor_add_one ((1 - p₀) * g / (k : ℝ))
  have hnum : (1 - p₀) * g < ((nibbleHorizon k g p₀ : ℝ) + 1) * k :=
    (div_lt_iff₀ hk').mp hfloor
  have hsmall : 1 - p₀ < (k : ℝ) * nibbleHorizon k g p₀ / g + (k : ℝ) / g := by
    calc
      _ = ((1 - p₀) * g) / g := by field_simp
      _ < (((nibbleHorizon k g p₀ : ℝ) + 1) * k) / g :=
        div_lt_div_of_pos_right hnum hg
      _ = _ := by ring
  unfold removalDensity
  linarith only [hsmall]

theorem nibbleHorizon_le_graph {k : ℕ} (hk : 0 < k) {g p₀ : ℝ}
    (hg : 0 ≤ g) (hp₀ : 0 ≤ p₀) (hp₁ : p₀ ≤ 1) : (nibbleHorizon k g p₀ : ℝ) ≤ g := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hk']
  have hfloor : (nibbleHorizon k g p₀ : ℝ) ≤ (1 - p₀) * g / (k : ℝ) :=
    Nat.floor_le (div_nonneg (mul_nonneg (sub_nonneg.mpr hp₁) hg) hk0.le)
  apply hfloor.trans
  apply (div_le_iff₀ hk0).mpr
  have hleft := mul_le_mul_of_nonneg_right (show 1 - p₀ ≤ 1 by linarith only [hp₀]) hg
  have hright := mul_le_mul_of_nonneg_left hk' hg
  nlinarith only [hleft, hright]

theorem NibbleComparisonParameters.horizon_face_density_lt {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) (ha : 128 * (k : ℝ) * a ≤ p₀) :
    removalDensity k g (nibbleHorizon k g p₀) + 128 * (k : ℝ) * a < 3 * p₀ := by
  have hk : 0 < k := by have h := P.rank; omega
  have h := nibbleHorizon_density_lt hk (p₀ := p₀) P.graph_pos
  have hs := P.step_le_floor
  linarith only [h, hs, ha]

end Arxiv2411_18291
