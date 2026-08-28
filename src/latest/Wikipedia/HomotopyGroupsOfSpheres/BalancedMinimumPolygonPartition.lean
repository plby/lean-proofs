import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygonRetraction

/-!
# Uniform partitions supporting the minimum polygon retraction

The squared Frobenius norm of every balanced minimum generator is the same.
A uniform energy mesh bound therefore makes all minimum increments small
and simultaneously makes every lower energy sublevel compact.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices
open NoExoticSixSphere.UniformTimePartition

theorem norm_sq_minimumGenerator {n : ℕ} (J : BalancedRealInvolutions.Space n) :
    ‖imaginaryDirection (minimumGenerator J)‖ ^ 2 = (2 * n : ℝ) * Real.pi ^ 2 := by
  change ‖ImaginarySymmetricMatrices.imaginary (minimumGenerator J).val‖ ^ 2 = _
  rw [ComplexMatrixRealRepresentation.frobenius_norm_sq,
    ImaginarySymmetricMatrices.squareNorm_imaginary, minimumGenerator_squareNorm]

theorem exists_minimum_partition (n : ℕ) (E : ℝ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧
      (∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
        ‖(time m i.succ - time m i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
          CompatibleLog.radius (Index n)) ∧
      ∀ C : ℝ, C ≤ max E ((4 * n : ℝ) * Real.pi ^ 2) →
        IsCompact (energySublevel specialIdentity (antipode n) (time m) C) := by
  let cap := max E ((4 * n : ℝ) * Real.pi ^ 2)
  let r := CompatibleLog.radius (Index n) / 2
  have hr : 0 < r := half_pos (CompatibleLog.radius_pos (N := Index n))
  have hrsmall : r < CompatibleLog.radius (Index n) :=
    half_lt_self (CompatibleLog.radius_pos (N := Index n))
  obtain ⟨m, hlower, hmesh⟩ := exists_small_energy_steps_above cap hr lower
  have hτ := strictMono_time m
  have hδpos (i : Fin (m + 1)) : 0 < time m i.succ - time m i.castSucc :=
    sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))
  have hQ : 0 ≤ (2 * n : ℝ) * Real.pi ^ 2 := by positivity
  have hQcap : (2 * n : ℝ) * Real.pi ^ 2 ≤ cap := by
    apply le_trans _ (le_max_right E ((4 * n : ℝ) * Real.pi ^ 2))
    nlinarith only [hQ]
  refine ⟨m, hlower, ?_, ?_⟩
  · intro J i
    have hδone : time m i.succ - time m i.castSucc ≤ 1 := by
      have hl := hτ.monotone (Fin.zero_le i.castSucc)
      have hu := hτ.monotone (Fin.le_last i.succ)
      rw [time_zero] at hl
      rw [time_last] at hu
      linarith
    have hδsq : (time m i.succ - time m i.castSucc) ^ 2 ≤
        time m i.succ - time m i.castSucc := by nlinarith [hδpos i]
    have hs : ‖(time m i.succ - time m i.castSucc) •
        imaginaryDirection (minimumGenerator J)‖ ^ 2 =
        (time m i.succ - time m i.castSucc) ^ 2 * ((2 * n : ℝ) * Real.pi ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_minimumGenerator]
    have hbound : ‖(time m i.succ - time m i.castSucc) •
        imaginaryDirection (minimumGenerator J)‖ ^ 2 < r ^ 2 := by
      rw [hs]
      exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_right hδsq hQ).trans
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hQcap (hδpos i).le))
        (hmesh i)
    exact ((sq_lt_sq₀ (norm_nonneg _) hr.le).mp hbound).trans hrsmall
  · intro C hC
    apply isCompact_energySublevel specialIdentity (antipode n) (time m) hτ hr.le hrsmall
    intro i
    exact (mul_le_mul_of_nonneg_right hC (hδpos i).le).trans (hmesh i).le

theorem exists_minimum_retraction_partition (n : ℕ) (E : ℝ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧
      IsOpen (minimumRetractionDomain n (time m)) ∧
      minimumSet n (time m) ⊆ minimumRetractionDomain n (time m) ∧
      ∃ R : C(minimumRetractionDomain n (time m), minimumSet n (time m)),
        (∀ v : minimumSet n (time m), ∀ hv : v.val ∈ minimumRetractionDomain n (time m),
          R ⟨v.val, hv⟩ = v) ∧
        ∀ C : ℝ, C ≤ E →
          IsCompact (energySublevel specialIdentity (antipode n) (time m) C) := by
  obtain ⟨m, hm, hsmall, hcompact⟩ := exists_minimum_partition n E lower
  have hminimum := hcompact ((4 * n : ℝ) * Real.pi ^ 2) (le_max_right _ _)
  let R := minimumNeighborhoodRetraction n (time m) (strictMono_time m)
    (time_zero m) (time_last m) hsmall
  refine ⟨m, hm, isOpen_minimumRetractionDomain n (time m),
    minimumSet_subset_retractionDomain n (time m) (strictMono_time m)
      (time_zero m) (time_last m) hsmall hminimum, R, ?_, ?_⟩
  · intro v hv
    exact minimumNeighborhoodRetraction_eq_self n (time m) (strictMono_time m)
      (time_zero m) (time_last m) hsmall hminimum v
  · intro C hC
    exact hcompact C (hC.trans (le_max_left _ _))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
