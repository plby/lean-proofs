/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure oscillation control for all distinct roots in the closed unit interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.BulkStability
import ErdosProblems.Erdos521.InteriorDecomposition

namespace Erdos521

open MeasureTheory Filter

theorem ae_positiveRootCount_dyadic_oscillation {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
        |(intervalRootCount ε m 0 1 : ℝ) - (intervalRootCount ε (2 ^ j) 0 1 : ℝ)| ≤
          η * Real.log (2 ^ j : ℕ) := by
  obtain ⟨C, hC, hbulk⟩ := ae_bulk_stability
  let K := Real.log ((1 - (19 / 20 : ℝ))⁻¹) / Real.log ((19 / 20 : ℝ) / (9 / 10))
  have hpow : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp hpow
  have hconst := (hlog.const_mul_atTop (by positivity : 0 < η / 2)).eventually_ge_atTop (2 + K)
  filter_upwards [hbulk, ae_endpoint_dyadic_bound C (by positivity : 0 < η / 2),
    ae_sequence_signs] with ε hεbulk hεend hεsign
  have hε : ∀ k, |ε k| = 1 := by
    intro k
    rcases hεsign k with h | h <;> simp [h]
  have hsmall (m : ℕ) : (smallRootCount ε m (9 / 10) : ℝ) ≤ K :=
    smallRootCount_le ε hε m (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hpow.eventually hεbulk, hεend, hconst,
    hpow.eventually (eventually_endpointCenter_bounds hC)] with j hjbulk hjend hjconst hjcenter
  intro m hnm hmn
  have hnn : (2 : ℕ) ^ j ≤ 2 * 2 ^ j := by omega
  have h := positiveRootCount_comparison ε (2 ^ j) m (by norm_num : (0 : ℝ) ≤ 9 / 10)
    hjcenter.2.le (hjbulk m hnm hmn) (hsmall (2 ^ j)) (hsmall m)
    (hjend (2 ^ j) le_rfl hnn) (hjend m hnm hmn)
  apply h.trans
  dsimp only [Function.comp_apply] at hjconst
  linarith

theorem ae_interiorRootCount_dyadic_oscillation {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
        |(interiorRootCount ε m : ℝ) - (interiorRootCount ε (2 ^ j) : ℝ)| ≤
          η * Real.log (2 ^ j : ℕ) := by
  have hpos := ae_positiveRootCount_dyadic_oscillation (by positivity : 0 < η / 2)
  have hneg := measurePreserving_alternateSigns.quasiMeasurePreserving.ae hpos
  filter_upwards [hpos, hneg, ae_sequence_signs] with ε hεpos hεneg hεsign
  have hε₀ : ε 0 ≠ 0 := by rcases hεsign 0 with h | h <;> simp [h]
  filter_upwards [hεpos, hεneg] with j hjpos hjneg
  intro m hnm hmn
  rw [interiorRootCount_eq_positive_add_alternate ε m hε₀,
    interiorRootCount_eq_positive_add_alternate ε (2 ^ j) hε₀, Nat.cast_add, Nat.cast_add]
  calc
    |((intervalRootCount ε m 0 1 : ℝ) + (intervalRootCount (alternateSigns ε) m 0 1 : ℝ)) -
        ((intervalRootCount ε (2 ^ j) 0 1 : ℝ) +
          (intervalRootCount (alternateSigns ε) (2 ^ j) 0 1 : ℝ))| =
        |((intervalRootCount ε m 0 1 : ℝ) - (intervalRootCount ε (2 ^ j) 0 1 : ℝ)) +
          ((intervalRootCount (alternateSigns ε) m 0 1 : ℝ) -
            (intervalRootCount (alternateSigns ε) (2 ^ j) 0 1 : ℝ))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      have h := add_le_add (hjpos m hnm hmn) (hjneg m hnm hmn)
      linarith)

end Erdos521
