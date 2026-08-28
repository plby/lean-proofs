import Wikipedia.HopfProblem.OrbitPairSpherePolygonRealization
import Wikipedia.HopfProblem.OrbitPairSphereShortGeodesic

/-!
# Polygon energy equals the actual integral energy of its realization

On the open subdivision intervals the realization has the derivative of its
smooth canonical segment. The finitely many corners do not change the integral.
The proof establishes interval integrability before summing the integrals.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

open NoExoticSixSphere SphereAngle SpherePairedGeodesic

theorem energy_rescaledSegment {n : ℕ} (a b : Sphere n)
    (hab : (a, b) ∈ nonantipodal n) (l u : ℝ) :
    SpherePathEnergy.energy (fun t => (rescaledSegment a b l u t).val) l u =
      sphereCost n (a, b) / (u - l) := by
  change SpherePathEnergy.energy (SphereTangentExponential.segment a.val
    (tangentLog a.val b.val (ClosedHemisphere.unit_norm a)) l u) l u = _
  rw [SphereTangentExponential.energy_segment (ClosedHemisphere.unit_norm a)]
  change ‖logVector a.val b.val‖ ^ 2 / (u - l) = _
  rw [norm_logVector (x := a.val) (y := b.val)
    (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab]
  rfl

end Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

namespace Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy

theorem energy_congr_Icc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : ℝ → E} {l u : ℝ} (hlu : l ≤ u) (h : ∀ t ∈ Icc l u, f t = g t) :
    energy f l u = energy g l u := by
  apply intervalIntegral.integral_congr_Ioo_of_le hlu
  intro t ht
  have he : f =ᶠ[nhds t] g := Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
    (fun r hr => h r ⟨hr.1.le, hr.2.le⟩)
  exact congrArg (fun w : E => ‖w‖ ^ 2) he.deriv_eq

end Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereCanonicalGeodesic

variable {n m : ℕ}

theorem deriv_path_eq_segment (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) (i : Fin (m + 1))
    {t : ℝ} (ht : t ∈ Ioo (τ i.castSucc) (τ i.succ)) :
    deriv (fun r => (path a b τ hτ v r).val) t =
      deriv (fun r => (rescaledSegment (vertices a b v.val i.castSucc)
        (vertices a b v.val i.succ) (τ i.castSucc) (τ i.succ) r).val) t := by
  have he : (fun r => (path a b τ hτ v r).val) =ᶠ[nhds t]
      (fun r => (rescaledSegment (vertices a b v.val i.castSucc)
        (vertices a b v.val i.succ) (τ i.castSucc) (τ i.succ) r).val) := by
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
    intro r hr
    exact congrArg Subtype.val (path_eq_segment a b τ hτ v i ⟨hr.1.le, hr.2.le⟩)
  exact he.deriv_eq

theorem integrable_squareSpeed_interval (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) (i : Fin (m + 1)) :
    IntervalIntegrable (fun t => ‖deriv (fun r => (path a b τ hτ v r).val) t‖ ^ 2)
      MeasureTheory.volume (τ i.castSucc) (τ i.succ) := by
  have htime := hτ (show i.castSucc < i.succ by simp)
  have hc := ((contDiff_rescaledSegment_val (vertices a b v.val i.castSucc)
    (vertices a b v.val i.succ) (τ i.castSucc) (τ i.succ)).deriv' (n := ∞)).continuous.norm.pow 2
  apply (hc.intervalIntegrable (τ i.castSucc) (τ i.succ)).congr_uIoo
  intro t ht
  rw [uIoo_of_le htime.le] at ht
  exact (congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => ‖w‖ ^ 2)
    (deriv_path_eq_segment a b τ hτ v i ht)).symm

theorem path_energy_eq (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) :
    SpherePathEnergy.energy (fun t => (path a b τ hτ v t).val)
      (τ 0) (τ (Fin.last (m + 1))) = energy a b τ v.val := by
  unfold SpherePathEnergy.energy
  rw [IntervalPartition.integral_eq_sum_adjacent τ _ (integrable_squareSpeed_interval a b τ hτ v)]
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  change _ = SpherePairedGeodesic.sphereCost n
    (vertices a b v.val i.castSucc, vertices a b v.val i.succ) / (τ i.succ - τ i.castSucc)
  rw [← energy_rescaledSegment _ _ (v.2 i) (τ i.castSucc) (τ i.succ)]
  apply intervalIntegral.integral_congr_Ioo_of_le
    (hτ (show i.castSucc < i.succ by simp)).le
  intro t ht
  exact congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => ‖w‖ ^ 2)
    (deriv_path_eq_segment a b τ hτ v i ht)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
