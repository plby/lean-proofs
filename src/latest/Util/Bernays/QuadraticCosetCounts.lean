import Util.Bernays.QuadraticIdealCovolume
import Util.Bernays.QuadraticNormBalls

/-!
# A square-root error for quadratic-ideal coset counts
-/

open scoped Classical

namespace Bernays

noncomputable def quadraticIdealLatticeEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) : I ≃ quadraticIdealLattice d b I :=
  Equiv.ofBijective (fun z : I => ⟨quadraticComplexMap d b z,
    (mem_quadraticIdealLattice d b I _).mpr ⟨z, z.2, rfl⟩⟩) (by
      constructor
      · intro z w hzw
        exact Subtype.ext (quadraticComplexMap_injective hD (congrArg Subtype.val hzw))
      · intro w
        obtain ⟨z, hz, hzw⟩ := (mem_quadraticIdealLattice d b I w).mp w.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩)

theorem quadraticNorm_natAbs_le_iff_complex {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) (N : ℕ) :
    z.norm.natAbs ≤ N ↔ ‖quadraticComplexMap d b z‖ ≤ 2 * Real.sqrt (N : ℝ) := by
  have hn := quadraticComplexMap_norm_sq hD z
  have hcast : (z.norm.natAbs : ℝ) = (z.norm : ℝ) := by
    have hZ : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg (quadraticNorm_nonneg hD z)
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℝ)) hZ
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hs₀ := Real.sqrt_nonneg (N : ℝ)
  have hz₀ := norm_nonneg (quadraticComplexMap d b z)
  constructor
  · intro h
    have hR : (z.norm.natAbs : ℝ) ≤ N := by exact_mod_cast h
    rw [hcast] at hR
    nlinarith
  · intro h
    have hR : (z.norm.natAbs : ℝ) ≤ N := by rw [hcast]; nlinarith
    exact_mod_cast hR

def quadraticIdealCosetBall {d b : ℤ} (I : Ideal (QuadraticAlgebra ℤ d b))
    (a : QuadraticAlgebra ℤ d b) (N : ℕ) :=
  {z : I // (a + (z : QuadraticAlgebra ℤ d b)).norm.natAbs ≤ N}

theorem finite_quadraticIdealCosetBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (a : QuadraticAlgebra ℤ d b) (N : ℕ) :
    Finite (quadraticIdealCosetBall I a N) := by
  letI := finite_quadraticNormBall hD N
  let e : quadraticIdealCosetBall I a N → QuadraticNormBall d b N := fun z => ⟨a + z.1, z.2⟩
  apply Finite.of_injective e
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  exact add_left_cancel (congrArg (fun t : QuadraticNormBall d b N => t.1) hzw)

theorem quadraticIdealCosetBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (a : QuadraticAlgebra ℤ d b) (N : ℕ) :
    Nat.card (quadraticIdealCosetBall I a N) =
      Nat.card (latticeCosetBall (quadraticIdealLattice d b I)
        (quadraticComplexMap d b a) (2 * Real.sqrt (N : ℝ))) := by
  apply Nat.card_congr
  apply (quadraticIdealLatticeEquiv hD I).subtypeEquiv
  intro z
  rw [quadraticNorm_natAbs_le_iff_complex hD, map_add]
  rfl

theorem quadraticIdealCosetBall_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : QuadraticAlgebra ℤ d b, ∀ N : ℕ,
      |(Nat.card (quadraticIdealCosetBall I a N) : ℝ) -
        (4 * Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) * N| ≤
          K * (Real.sqrt (N : ℝ) + 1) := by
  letI := quadraticIdealLattice_discrete hD I
  letI := quadraticIdealLattice_full hD I hI
  obtain ⟨K, hK, hbound⟩ := latticeCosetBall_error (quadraticIdealLattice d b I)
  refine ⟨2 * K, by positivity, ?_⟩
  intro a N
  have h := hbound (quadraticComplexMap d b a) (2 * Real.sqrt (N : ℝ)) (by positivity)
  rw [← quadraticIdealCosetBall_card hD, quadraticIdealLattice_covolume hD I hI] at h
  have hmain : Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤)) *
      (2 * Real.sqrt (N : ℝ)) ^ 2 =
      (4 * Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) * N := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  rw [hmain] at h
  exact h.trans (by nlinarith [Real.sqrt_nonneg (N : ℝ)])

end Bernays
