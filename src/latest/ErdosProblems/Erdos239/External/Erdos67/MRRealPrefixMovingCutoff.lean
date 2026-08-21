import ErdosProblems.Erdos239.External.Erdos67.MRRealPrefixMinimizerDichotomy
import ErdosProblems.Erdos239.External.Erdos67.MRHalaszDistanceTail

/-!
# Moving the real-prefix nonpretentious cutoff

The real minimizer dichotomy supplies Archimedean nonpretentiousness at
`3X`, whereas an ordinary sharp-prefix estimate at `Z ∈ [X,3X]` naturally
uses cutoff `Z`.  The proved prime-tail estimate transfers the hypothesis
uniformly, at the cost of only one unit of the moving distance threshold.
-/

open Filter

namespace Erdos67

noncomputable section

/-- Eventually the moving threshold is at least one. -/
theorem eventually_one_le_realPrefixMovingThreshold :
    ∀ᶠ X : ℕ in atTop, 1 ≤ realPrefixMovingThreshold X := by
  have hloglogTop : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglogTop.eventually (eventually_ge_atTop 16)]
    with X hloglog
  have hloglog0 : 0 ≤ Real.log (Real.log (X : ℝ)) := by linarith
  unfold realPrefixMovingThreshold
  rw [max_eq_right (mul_nonneg (by norm_num) hloglog0)]
  apply Nat.le_floor
  norm_num
  linarith

/-- Uniform lower-cutoff transfer for the exact moving threshold appearing
in the real minimizer dichotomy.  The loss is one natural unit, not a fixed
proportion of `log log X`. -/
theorem eventually_realPrefixMovingThreshold_sub_one_archimedean_at_prefix :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        MRArchimedeanNonpretentious f
          (realPrefixMovingThreshold X - 1) Z := by
  obtain ⟨C, hC, htail⟩ :=
    MRHalaszDistanceTail.exists_uniform_pretentiousDistSq_ge_at_lower_cutoff
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [eventually_one_le_realPrefixMovingThreshold,
        hlogTop.eventually
          (eventually_ge_atTop (2 * (Real.log 3 + C))),
        eventually_ge_atTop 3]
      with X hthreshold hlogX hX
  intro f hbound hnonpret Z hXZ hZupper t ht
  have hZtwo : 2 ≤ Z := by omega
  have htUpper : |t| ≤ (3 * X : ℕ) := by
    exact ht.trans (by exact_mod_cast hZupper)
  have hglobal := hnonpret t htUpper
  by_cases hZX : Z = 3 * X
  · subst Z
    have hsub : ((realPrefixMovingThreshold X - 1 : ℕ) : ℝ) ≤
        (realPrefixMovingThreshold X : ℝ) := by
      exact_mod_cast (Nat.sub_le (realPrefixMovingThreshold X) 1)
    exact hsub.trans hglobal
  · have hZstrict : Z < 3 * X := lt_of_le_of_ne hZupper hZX
    have hlocal := htail (x := Z) (y := 3 * X)
      (A := (realPrefixMovingThreshold X : ℝ)) hZtwo hZstrict
      (fun p _hp ↦ hbound p)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le) hglobal
    have hXpos : (0 : ℝ) < X := by
      exact_mod_cast (show 0 < X by omega)
    have hZsuccPos : (0 : ℝ) < (Z : ℝ) + 1 := by positivity
    have hratioPos :
        0 < ((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1) := by positivity
    have hratio :
        ((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1) ≤ 3 := by
      apply (div_le_iff₀ hZsuccPos).2
      have hcast : (X : ℝ) ≤ Z := by exact_mod_cast hXZ
      push_cast
      linarith
    have hlogRatio :
        Real.log (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) ≤ Real.log 3 :=
      Real.strictMonoOn_log.monotoneOn hratioPos (by norm_num) hratio
    have hlogMono :
        Real.log (X : ℝ) ≤ Real.log ((Z : ℝ) + 1) := by
      apply Real.strictMonoOn_log.monotoneOn hXpos hZsuccPos
      exact_mod_cast (show X ≤ Z + 1 by omega)
    have hdenPos : 0 < Real.log ((Z : ℝ) + 1) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < Z + 1 by omega))
    have htailOne :
        2 * (Real.log (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) + C) /
            Real.log ((Z : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hdenPos).2
      calc
        2 * (Real.log
              (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) + C) ≤
            2 * (Real.log 3 + C) := by linarith
        _ ≤ Real.log (X : ℝ) := hlogX
        _ ≤ Real.log ((Z : ℝ) + 1) := hlogMono
        _ = 1 * Real.log ((Z : ℝ) + 1) := by ring
    have hcastSub :
        ((realPrefixMovingThreshold X - 1 : ℕ) : ℝ) =
          (realPrefixMovingThreshold X : ℝ) - 1 := by
      rw [Nat.cast_sub hthreshold]
      norm_num
    rw [hcastSub]
    exact (sub_le_sub_left htailOne
      (realPrefixMovingThreshold X : ℝ)).trans hlocal

end

end Erdos67
