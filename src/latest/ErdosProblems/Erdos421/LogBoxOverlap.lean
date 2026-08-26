import ErdosProblems.Erdos421.LogFrequencyBoxes
import ErdosProblems.Erdos421.LogCoefficientSpacing

/-! # Uniform overlap multiplicity for logarithmic frequency boxes -/

namespace Erdos421

noncomputable def logBoxCover (k N : ℕ) (t M A : ℝ) (a : UnitAddTorus (Fin k)) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n ↦ a ∈ logFrequencyBox k t M (A + n))

@[simp] theorem mem_logBoxCover {k N n : ℕ} {t M A : ℝ} {a : UnitAddTorus (Fin k)} :
    n ∈ logBoxCover k N t M A a ↔ n < N ∧ a ∈ logFrequencyBox k t M (A + n) := by
  classical
  simp only [logBoxCover, Finset.mem_filter, Finset.mem_range]

theorem logFrequencyBoxes_overlap {k : ℕ} (hk : 0 < k) (N : ℕ) {t M A : ℝ}
    (ht : t ≠ 0) (hM : 0 < M) (hA : 0 < A) (htA : |t| ≤ A ^ k)
    (a : UnitAddTorus (Fin k)) :
    ((logBoxCover k N t M A a).card : ℝ) ≤
      1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * M ^ k) := by
  let j : Fin k := ⟨k - 1, Nat.sub_lt hk (by decide)⟩
  let e : ℝ := |t| / (2 * Real.pi * (A + N) ^ (k + 1))
  let S := logBoxCover k N t M A a
  have hj : (j : ℕ) + 1 = k := by dsimp [j]; omega
  have hj2 : (j : ℕ) + 2 = k + 1 := by omega
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have he : 0 < e := by dsimp [e]; positivity
  have hspan : ∀ i ∈ S, ∀ m ∈ S,
      |logTaylorCoefficients k t (A + i) j - logTaylorCoefficients k t (A + m) j| ≤ 1 / 2 := by
    intro i _ m _
    apply logTaylorCoefficients_span j hA (le_add_of_nonneg_right (Nat.cast_nonneg i))
      (le_add_of_nonneg_right (Nat.cast_nonneg m))
    simpa only [hj] using htA
  have hsep : ∀ i ∈ S, ∀ m ∈ S, i ≤ m → e * ((m : ℝ) - i) ≤
      |logTaylorCoefficients k t (A + m) j - logTaylorCoefficients k t (A + i) j| := by
    intro i _ m hm him
    have hmN : m < N := (mem_logBoxCover.mp hm).1
    have hmi : (i : ℝ) ≤ m := Nat.cast_le.mpr him
    have hmR : (m : ℝ) ≤ N := Nat.cast_le.mpr hmN.le
    have h := logTaylorCoefficients_separation j t (by positivity : 0 < A + (i : ℝ))
      (by linarith : A + (i : ℝ) ≤ A + m) (by linarith : A + (m : ℝ) ≤ A + N)
    rw [hj2, show A + (m : ℝ) - (A + i) = (m : ℝ) - i by ring, abs_sub_comm] at h
    exact h
  have hnear : ∀ i ∈ S, dist (logTaylorCoefficients k t (A + i) j : UnitAddCircle) (a j) ≤
      polynomialBoxRadius k M j := by
    intro i hi
    have hb := (mem_logBoxCover.mp hi).2
    change a ∈ torusBox (fun l ↦ (logTaylorCoefficients k t (A + i) l : UnitAddCircle))
      (polynomialBoxRadius k M) at hb
    have hc := Set.mem_pi.mp hb j (Set.mem_univ j)
    simpa only [Metric.mem_closedBall, dist_comm] using hc
  have hpack := separated_circle_arc_card_bound S
    (fun i ↦ logTaylorCoefficients k t (A + i) j) (a j)
    (polynomialBoxRadius_pos hk hM j).le he hspan hsep hnear
  have hradius : polynomialBoxRadius k M j = 1 / (2 * Real.pi * (k : ℝ) ^ 2 * M ^ k) := by
    unfold polynomialBoxRadius
    rw [hj]
    ring
  calc
    _ ≤ (2 * polynomialBoxRadius k M j + e) / e := hpack
    _ = _ := by
      rw [hradius]
      dsimp only [e]
      field_simp
      ring

end Erdos421
