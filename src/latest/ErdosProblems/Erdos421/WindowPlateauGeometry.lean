import ErdosProblems.Erdos421.PrimeLongIntervals
import ErdosProblems.Erdos421.PrimePolynomialSupport
import ErdosProblems.Erdos421.OneSidedWindowPlateau

/-! # Primes in the central exponential interval lie on the window plateau -/

namespace Erdos421

open Complex
open scoped SchwartzMap

theorem exponential_plateau_order {ρ : ℝ} (hρ : 0 ≤ ρ) (y : ℝ) :
    Real.exp (y + ρ / 4) ≤ Real.exp (y + 3 * ρ / 4) :=
  Real.exp_le_exp.mpr (by linarith)

theorem prime_exponential_plateau {ρ y : ℝ} (hρ : 0 < ρ) {p : ℕ}
    (hp : p ∈ primesInRealInterval (Real.exp (y + ρ / 4)) (Real.exp (y + 3 * ρ / 4))) :
    0 < p ∧ (y - Real.log p) / ρ ∈ Set.Icc (-3 / 4 : ℝ) (-1 / 4) := by
  have hmem :=
    (mem_primesInRealInterval (Real.exp_pos _).le (exponential_plateau_order hρ.le y) p).mp hp
  have hpp : (0 : ℝ) < p := Nat.cast_pos.mpr hmem.1.pos
  have hlo : y + ρ / 4 < Real.log p := by
    have h := Real.log_lt_log (Real.exp_pos (y + ρ / 4)) hmem.2.1
    rwa [Real.log_exp] at h
  have hhi : Real.log p ≤ y + 3 * ρ / 4 := by
    have h := Real.log_le_log hpp hmem.2.2
    rwa [Real.log_exp] at h
  refine ⟨hmem.1.pos, ?_, ?_⟩
  · apply (le_div_iff₀ hρ).mpr
    linarith
  · apply (div_le_iff₀ hρ).mpr
    linarith

theorem prime_reference_window_plateau_bound (M N : ℕ) {ρ V y : ℝ} (hρ : 0 < ρ)
    (hV : 0 < V) (hM : (M : ℝ) ≤ Real.exp (y + ρ / 4))
    (hN : Real.exp (y + 3 * ρ / 4) ≤ (M + N : ℕ))
    (hupper : Real.exp (y + 3 * ρ / 4) ≤ V) :
    ((primesInRealInterval (Real.exp (y + ρ / 4)) (Real.exp (y + 3 * ρ / 4))).card : ℝ) *
        oneSidedWindowHeight / (ρ * V) ≤
      (schwartzDirichletWindow (primeBlockSupport M N) (fun _ ↦ 1) 1
        (normalizedSchwartzScale ρ hρ oneSidedSchwartzWindow) y).re := by
  let T := primesInRealInterval (Real.exp (y + ρ / 4)) (Real.exp (y + 3 * ρ / 4))
  have hmem : ∀ p ∈ T, p.Prime ∧ Real.exp (y + ρ / 4) < p ∧
      (p : ℝ) ≤ Real.exp (y + 3 * ρ / 4) := fun p hp ↦
    (mem_primesInRealInterval (Real.exp_pos _).le (exponential_plateau_order hρ.le y) p).mp hp
  have hsub : T ⊆ primeBlockSupport M N := by
    intro p hp
    have hm := hmem p hp
    have hMp : M < p := by exact_mod_cast hM.trans_lt hm.2.1
    have hpN : p ≤ M + N := by exact_mod_cast hm.2.2.trans hN
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hMp, hpN⟩, hm.1⟩
  apply oneSided_unit_window_re_lower_bound _ T hsub hρ hV
  intro p hp
  have hplateau := prime_exponential_plateau hρ hp
  exact ⟨hplateau.1, (hmem p hp).2.2.trans hupper, hplateau.2⟩

theorem exponential_plateau_span {ρ : ℝ} (hρ : 0 ≤ ρ) (y : ℝ) :
    Real.exp y * (ρ / 2) ≤ Real.exp (y + 3 * ρ / 4) - Real.exp (y + ρ / 4) := by
  have hy : 0 < Real.exp y := Real.exp_pos y
  have hstep : ρ / 2 ≤ Real.exp (ρ / 2) - 1 := by linarith [Real.add_one_le_exp (ρ / 2)]
  have hbase : Real.exp y ≤ Real.exp (y + ρ / 4) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul hbase hstep (by positivity : 0 ≤ ρ / 2) (Real.exp_pos _).le
  have he : Real.exp (y + ρ / 4) * (Real.exp (ρ / 2) - 1) =
      Real.exp (y + 3 * ρ / 4) - Real.exp (y + ρ / 4) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    congr 2
    ring
  exact hm.trans_eq he

theorem exponential_plateau_bounds {X ρ y : ℝ} (hX : 0 ≤ X) (hρ : 0 ≤ ρ)
    (hlo : X ≤ Real.exp y) (hhi : Real.exp y ≤ 3 * X / 2) (hexp : Real.exp ρ ≤ 4 / 3) :
    X ≤ Real.exp (y + ρ / 4) ∧ Real.exp (y + 3 * ρ / 4) ≤ 2 * X ∧
      X * ρ / 2 ≤ Real.exp (y + 3 * ρ / 4) - Real.exp (y + ρ / 4) := by
  refine ⟨hlo.trans (Real.exp_le_exp.mpr (by linarith)), ?_, ?_⟩
  · have hsmall : Real.exp (3 * ρ / 4) ≤ 4 / 3 :=
      (Real.exp_le_exp.mpr (by linarith : 3 * ρ / 4 ≤ ρ)).trans hexp
    rw [Real.exp_add]
    have hm := mul_le_mul hhi hsmall (Real.exp_pos _).le (by positivity : 0 ≤ 3 * X / 2)
    exact hm.trans_eq (by ring)
  · have hm := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ ρ / 2)
    calc
      _ = X * (ρ / 2) := by ring
      _ ≤ Real.exp y * (ρ / 2) := hm
      _ ≤ _ := exponential_plateau_span hρ y

end Erdos421
