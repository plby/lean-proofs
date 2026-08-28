import Wikipedia.NoExoticSixSphere.OrthogonalPolygonRealization
import Wikipedia.NoExoticSixSphere.OrthogonalPrefixEnergy
import Wikipedia.NoExoticSixSphere.IntervalPartition

/-!
# Polygon energy is the actual integral energy of its realization

The corners are handled by interval integrability and equality of derivatives
on open subdivision intervals. The finite smooth energy is exactly the
ambient path energy, not a substitute for it. A smooth path with matching
vertices has at least this energy when every chosen generator is short.
-/

open scoped ContDiff
open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalVertexSpace OrthogonalPathEnergy
  HilbertSchmidt

variable {n m : ℕ}

theorem deriv_path_eq_segment (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Ioo (τ i.castSucc) (τ i.succ)) :
    deriv (fun r ↦ (path a b τ v r).1.1) t =
      deriv (fun r ↦ (rescaledSegment (vertices a b v i.castSucc) (generator a b v i)
        (τ i.castSucc) (τ i.succ) r).1.1) t := by
  have he : (fun r ↦ (path a b τ v r).1.1) =ᶠ[nhds t]
      (fun r ↦ (rescaledSegment (vertices a b v i.castSucc) (generator a b v i)
        (τ i.castSucc) (τ i.succ) r).1.1) := by
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
    intro r hr
    exact congrArg (fun q : OrthogonalOperators n ↦ q.1.1)
      (path_eq_segment a b τ hτ hv i ⟨hr.1.le, hr.2.le⟩)
  exact he.deriv_eq

theorem integrable_squareSpeed_interval (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    IntervalIntegrable (fun t ↦ squareNorm (deriv (fun r ↦ (path a b τ v r).1.1) t))
      MeasureTheory.volume (τ i.castSucc) (τ i.succ) := by
  have htime : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
  have hc := continuous_squareSpeed
    (contDiff_rescaledSegment (vertices a b v i.castSucc) (generator a b v i)
      (τ i.castSucc) (τ i.succ))
  apply (hc.intervalIntegrable (τ i.castSucc) (τ i.succ)).congr_uIoo
  intro t ht
  rw [uIoo_of_le htime.le] at ht
  exact (congrArg squareNorm (deriv_path_eq_segment a b τ hτ hv i ht)).symm

theorem path_energy_eq (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    OrthogonalPathEnergy.energy (fun t ↦ (path a b τ v t).1.1) (τ 0) (τ (Fin.last (m + 1))) =
      energy a b τ v := by
  rw [energy_eq_segment_sum]
  unfold OrthogonalPathEnergy.energy
  rw [IntervalPartition.integral_eq_sum_adjacent τ _ (integrable_squareSpeed_interval a b τ hτ hv)]
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr_Ioo_of_le
    (hτ (show i.castSucc < i.succ by simp)).le
  intro t ht
  exact congrArg squareNorm (deriv_path_eq_segment a b τ hτ hv i ht)

theorem energy_le_of_matching_vertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m)
    {γ : ℝ → OrthogonalOperators n} (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1))
    (hmatch : ∀ j, γ (τ j) = vertices a b v j)
    (hshort : ∀ i, ‖(generator a b v i : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi) :
    energy a b τ v ≤
      OrthogonalPathEnergy.energy (fun t ↦ (γ t).1.1) (τ 0) (τ (Fin.last (m + 1))) := by
  unfold OrthogonalPathEnergy.energy
  rw [IntervalPartition.integral_eq_sum_adjacent τ _
    (fun i ↦ (continuous_squareSpeed hγ).intervalIntegrable (τ i.castSucc) (τ i.succ))]
  apply Finset.sum_le_sum
  intro i _
  have hend : γ (τ i.succ) = γ (τ i.castSucc) * OrthogonalExponential.exp (generator a b v i) := by
    rw [hmatch, hmatch]
    exact (generator_endpoint a b hv i).symm
  exact short_generator_energy_div_le hγ _ (hshort i)
    (hτ (show i.castSucc < i.succ by simp)) hend

end NoExoticSixSphere.OrthogonalPolygon
