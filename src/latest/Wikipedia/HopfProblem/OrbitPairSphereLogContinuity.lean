import Wikipedia.HopfProblem.OrbitPairSphereAngleLogarithm
import Wikipedia.HopfProblem.OrbitPairSpherePolygonFirstVariation

/-!
# Continuity of the actual spherical logarithm and polygon balances

The explicit arccos coefficient is singular as written on the diagonal,
but the actual logarithm vector tends to zero there because its norm is
exactly the endpoint angle. Away from the diagonal ordinary division
gives continuity. Consequently the actual tangent balance varies
continuously throughout the nonantipodal polygon domain.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SphereAngle

open NoExoticSixSphere GLOrthonormalization SpherePairedGeodesic

theorem continuousAt_sphereLog {n : ℕ} (p : Sphere n × Sphere n)
    (hp : p ∈ nonantipodal n) :
    ContinuousAt (fun q : Sphere n × Sphere n => logVector q.1.val q.2.val) p := by
  have hx : Continuous (fun q : Sphere n × Sphere n => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun q : Sphere n × Sphere n => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun q : Sphere n × Sphere n => inner ℝ q.1.val q.2.val) := hx.inner hy
  by_cases he : p.1 = p.2
  · have hz : logVector p.1.val p.2.val = 0 := by
      rw [he]
      exact logVector_diagonal (ClosedHemisphere.unit_norm p.2)
    change Tendsto (fun q : Sphere n × Sphere n => logVector q.1.val q.2.val)
      (𝓝 p) (𝓝 (logVector p.1.val p.2.val))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    have ha0 : Real.arccos (inner ℝ p.1.val p.2.val) = 0 := by
      rw [he, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow, Real.arccos_one]
    have ha : Tendsto (fun q : Sphere n × Sphere n => Real.arccos (inner ℝ q.1.val q.2.val))
        (𝓝 p) (𝓝 0) := by
      have ht : Tendsto
          (fun q : Sphere n × Sphere n => Real.arccos (inner ℝ q.1.val q.2.val))
          (𝓝 p) (𝓝 (Real.arccos (inner ℝ p.1.val p.2.val))) :=
        (Real.continuous_arccos.comp hc).continuousAt
      simpa only [ha0] using ht
    apply ha.congr'
    filter_upwards [(isOpen_nonantipodal n).mem_nhds hp] with q hq
    exact (norm_logVector (x := q.1.val) (y := q.2.val)
      (ClosedHemisphere.unit_norm q.1) (ClosedHemisphere.unit_norm q.2) hq).symm
  · have hne : p.1.val ≠ p.2.val := fun h => he (Subtype.ext h)
    have hs : Real.sqrt (1 - inner ℝ p.1.val p.2.val ^ 2) ≠ 0 :=
      ne_of_gt (sqrt_one_sub_inner_sq_pos (ClosedHemisphere.unit_norm p.1)
        (ClosedHemisphere.unit_norm p.2) hp hne)
    have hf : ContinuousAt (fun q : Sphere n × Sphere n => factor (inner ℝ q.1.val q.2.val)) p :=
      (Real.continuous_arccos.comp hc).continuousAt.div
        (Real.continuous_sqrt.comp (continuous_const.sub (hc.pow 2))).continuousAt hs
    exact hf.smul (hy.sub (hc.smul hx)).continuousAt

theorem continuousOn_sphereLog (n : ℕ) :
    ContinuousOn (fun q : Sphere n × Sphere n => logVector q.1.val q.2.val) (nonantipodal n) :=
  fun p hp => (continuousAt_sphereLog p hp).continuousWithinAt

end Wikipedia.HopfProblem.OrbitPair.SphereAngle

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereAngle SpherePairedGeodesic

variable {n m : ℕ}

theorem continuousAt_outgoingLog (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m) (i : Fin (m + 1)) :
    ContinuousAt (fun w : Space n m => outgoingLog a b τ w i) v := by
  have hc := ContinuousAt.comp
    (g := fun q : Sphere n × Sphere n => logVector q.1.val q.2.val)
    (f := fun w : Space n m => edge a b w i)
    (continuousAt_sphereLog (edge a b v i) (hv i))
    (contMDiff_edge a b i).continuous.continuousAt
  have hscale : ContinuousAt (fun _ : Space n m => (1 / (τ i.succ - τ i.castSucc) : ℝ)) v :=
    continuousAt_const
  exact hscale.smul hc

theorem continuousAt_incomingLog (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m) (i : Fin (m + 1)) :
    ContinuousAt (fun w : Space n m => incomingLog a b τ w i) v := by
  have hmem : (vertices a b v i.succ, vertices a b v i.castSucc) ∈ nonantipodal n := by
    change -1 < inner ℝ (vertices a b v i.succ).val (vertices a b v i.castSucc).val
    rw [real_inner_comm]
    exact hv i
  have he : Continuous (fun w : Space n m => (vertices a b w i.succ, vertices a b w i.castSucc)) :=
    (contMDiff_vertices a b i.succ).continuous.prodMk (contMDiff_vertices a b i.castSucc).continuous
  have hc := ContinuousAt.comp
    (g := fun q : Sphere n × Sphere n => logVector q.1.val q.2.val)
    (f := fun w : Space n m => (vertices a b w i.succ, vertices a b w i.castSucc))
    (continuousAt_sphereLog _ hmem) he.continuousAt
  have hscale : ContinuousAt (fun _ : Space n m => (1 / (τ i.succ - τ i.castSucc) : ℝ)) v :=
    continuousAt_const
  exact hscale.smul hc

theorem continuousAt_balance (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m) :
    ContinuousAt (balance a b τ) v := by
  apply continuousAt_pi.mpr
  intro j
  exact (continuousAt_incomingLog a b τ hv j.castSucc).add
    (continuousAt_outgoingLog a b τ hv j.succ)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
