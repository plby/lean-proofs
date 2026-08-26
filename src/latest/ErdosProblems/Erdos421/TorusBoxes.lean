import ErdosProblems.Erdos421.TorusMoments
import Mathlib.MeasureTheory.Group.AddCircle

/-! # Frequency boxes on the unit torus and nearby real representatives -/

namespace Erdos421

open MeasureTheory

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusBox {k : ℕ} (c : UnitAddTorus (Fin k)) (d : Fin k → ℝ) :
    Set (UnitAddTorus (Fin k)) := Set.pi Set.univ (fun j ↦ Metric.closedBall (c j) (d j))

theorem measurableSet_torusBox {k : ℕ} (c : UnitAddTorus (Fin k)) (d : Fin k → ℝ) :
    MeasurableSet (torusBox c d) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_closedBall)

theorem normalizedCircle_volume_closedBall (c : UnitAddCircle) (r : ℝ) :
    (volume : Measure UnitAddCircle) (Metric.closedBall c r) =
      ENNReal.ofReal (min 1 (2 * r)) := by
  change AddCircle.haarAddCircle (Metric.closedBall c r) = _
  have h := AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  simp only [ENNReal.ofReal_one, one_smul] at h
  rw [← h]
  exact AddCircle.volume_closedBall 1 r

theorem volume_torusBox {k : ℕ} (c : UnitAddTorus (Fin k)) (d : Fin k → ℝ) :
    volume (torusBox c d) = ∏ j : Fin k, ENNReal.ofReal (min 1 (2 * d j)) := by
  rw [torusBox, volume_pi_pi]
  simp only [normalizedCircle_volume_closedBall]

theorem volume_torusBox_real {k : ℕ} (c : UnitAddTorus (Fin k)) (d : Fin k → ℝ)
    (hd : ∀ j, 0 ≤ d j) (hhalf : ∀ j, 2 * d j ≤ 1) :
    volume.real (torusBox c d) = ∏ j : Fin k, 2 * d j := by
  change (volume (torusBox c d)).toReal = _
  rw [volume_torusBox, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [min_eq_right (hhalf j), ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hd j))]

theorem exists_real_lift_at_distance (a : UnitAddCircle) (c : ℝ) :
    ∃ b : ℝ, (b : UnitAddCircle) = a ∧ |b - c| = dist a (c : UnitAddCircle) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective a
  have hx' : (x : UnitAddCircle) = a := hx
  refine ⟨x - (round (x - c) : ℝ), ?_, ?_⟩
  · have hz : ((round (x - c) : ℝ) : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff 1).mpr
      exact ⟨round (x - c), by simp only [zsmul_eq_mul, mul_one]⟩
    rw [AddCircle.coe_sub, hz, sub_zero]
    exact hx'
  · rw [← hx', dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
    congr 1
    ring

theorem exists_real_lift_of_mem_torusBox {k : ℕ} (c d : Fin k → ℝ)
    (a : UnitAddTorus (Fin k)) (ha : a ∈ torusBox (fun j ↦ (c j : UnitAddCircle)) d) :
    ∃ b : Fin k → ℝ, (∀ j, (b j : UnitAddCircle) = a j) ∧
      ∀ j, |b j - c j| ≤ d j := by
  choose b hb hd using fun j ↦ exists_real_lift_at_distance (a j) (c j)
  refine ⟨b, hb, fun j ↦ ?_⟩
  rw [hd j]
  exact Metric.mem_closedBall.mp (Set.mem_pi.mp ha j (Set.mem_univ j))

theorem unitCircle_dist_eq_abs_sub {x y : ℝ} (hxy : |x - y| ≤ 1 / 2) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) = |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa only [abs_one] using hxy

theorem separated_circle_arc_card_bound (S : Finset ℕ) (f : ℕ → ℝ)
    (a : UnitAddCircle) {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e)
    (hspan : ∀ i ∈ S, ∀ j ∈ S, |f i - f j| ≤ 1 / 2)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → e * ((j : ℝ) - i) ≤ |f j - f i|)
    (hnear : ∀ i ∈ S, dist (f i : UnitAddCircle) a ≤ d) :
    (S.card : ℝ) ≤ (2 * d + e) / e := by
  by_cases hS : S.Nonempty
  · have hmin := S.min'_mem hS
    have hmax := S.max'_mem hS
    have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) :=
      fun i hi ↦ Finset.mem_Icc.mpr ⟨S.min'_le i hi, S.le_max' i hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hnat : S.card + S.min' hS ≤ S.max' hS + 1 := by
      have horder := S.min'_le_max' hS
      omega
    have hreal : (S.card : ℝ) + (S.min' hS : ℝ) ≤ (S.max' hS : ℝ) + 1 := by
      exact_mod_cast hnat
    have habs : |f (S.max' hS) - f (S.min' hS)| ≤ 2 * d := by
      rw [← unitCircle_dist_eq_abs_sub (hspan _ hmax _ hmin)]
      apply (dist_triangle _ a _).trans
      rw [dist_comm a]
      linarith [hnear _ hmax, hnear _ hmin]
    have hs := hsep _ hmin _ hmax (S.min'_le_max' hS)
    apply (le_div_iff₀ he).mpr
    nlinarith
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hzero, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos421
