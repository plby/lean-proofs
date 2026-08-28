import Wikipedia.HopfProblem.OrbitPairSphereLogContinuity

/-!
# Canonical geodesic segments for all nonantipodal sphere pairs

Exponentiate the actual tangent logarithm. The resulting segment lies on the
original sphere at every real time and has the literal endpoints. Continuity
is joint in time and both endpoints on the whole nonantipodal domain, including
coincident endpoints. The ambient curve is smooth for each fixed pair.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

open NoExoticSixSphere GLOrthonormalization CayleyTransform SphereAngle
  SpherePairedGeodesic SphereTangentExponential

variable {n : ℕ}

theorem continuous_skew {X : Type*} [TopologicalSpace X]
    {x y : X → Vector n} (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun q => SkewWedge.skew (x q) (y q)) := by
  have hc : Continuous (fun q => SkewWedge.operator (x q) (y q)) :=
    (((InnerProductSpace.rankOne ℝ).continuous.comp hy).clm_apply hx).sub
      (((InnerProductSpace.rankOne ℝ).continuous.comp hx).clm_apply hy)
  exact hc.subtype_mk _

def segment (a b : Sphere n) (t : ℝ) : Sphere n :=
  ⟨curve a.val (tangentLog a.val b.val (ClosedHemisphere.unit_norm a)) t, by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      norm_curve (ClosedHemisphere.unit_norm a) (tangentLog a.val b.val
        (ClosedHemisphere.unit_norm a)) t⟩

theorem segment_zero (a b : Sphere n) : segment a b 0 = a :=
  Subtype.ext (curve_zero _ _)

theorem segment_one (a b : Sphere n) (h : (a, b) ∈ nonantipodal n) : segment a b 1 = b :=
  Subtype.ext (curve_tangentLog_one (ClosedHemisphere.unit_norm a)
    (ClosedHemisphere.unit_norm b) h)

theorem segment_self (a : Sphere n) (t : ℝ) : segment a a t = a := by
  apply Subtype.ext
  change curve a.val (tangentLog a.val a.val (ClosedHemisphere.unit_norm a)) t = a.val
  have hz : tangentLog a.val a.val (ClosedHemisphere.unit_norm a) = 0 :=
    Subtype.ext (logVector_diagonal (ClosedHemisphere.unit_norm a))
  rw [hz, curve_zero_velocity]

theorem continuous_segment {X : Type*} [TopologicalSpace X]
    (a b : X → Sphere n) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ x, (a x, b x) ∈ nonantipodal n) :
    Continuous (fun p : ℝ × X => segment (a p.2) (b p.2) p.1) := by
  have hav : Continuous (fun x => (a x).val) := continuous_subtype_val.comp ha
  have hl : Continuous (fun x => logVector (a x).val (b x).val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp
      (g := fun q : Sphere n × Sphere n => logVector q.1.val q.2.val)
      (f := fun x : X => (a x, b x))
      (continuousAt_sphereLog (a x, b x) (hab x)) (ha.prodMk hb).continuousAt
  have hK : Continuous (fun x => SkewWedge.skew (a x).val (logVector (a x).val (b x).val)) :=
    continuous_skew hav hl
  have hs : Continuous (fun p : ℝ × X =>
      p.1 • SkewWedge.skew (a p.2).val (logVector (a p.2).val (b p.2).val)) :=
    continuous_fst.smul (hK.comp continuous_snd)
  have hc : Continuous (fun p : ℝ × X => (segment (a p.2) (b p.2) p.1).val) :=
    (OrthogonalExponential.contDiff_exp_operator.continuous.comp hs).clm_apply
      (hav.comp continuous_snd)
  exact hc.subtype_mk _

theorem contDiff_segment_val (a b : Sphere n) :
    ContDiff ℝ ∞ (fun t => (segment a b t).val) :=
  contDiff_curve a.val (tangentLog a.val b.val (ClosedHemisphere.unit_norm a))

theorem energy_segment (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n) :
    SpherePathEnergy.energy (fun t => (segment a b t).val) 0 1 = sphereCost n (a, b) := by
  change SpherePathEnergy.energy
    (curve a.val (tangentLog a.val b.val (ClosedHemisphere.unit_norm a))) 0 1 = _
  rw [SphereTangentExponential.energy_curve (ClosedHemisphere.unit_norm a)]
  change ‖logVector a.val b.val‖ ^ 2 = _
  rw [norm_logVector (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab]
  rfl

def rescaledSegment (a b : Sphere n) (l u t : ℝ) : Sphere n :=
  segment a b ((t - l) / (u - l))

theorem rescaledSegment_start (a b : Sphere n) (l u : ℝ) : rescaledSegment a b l u l = a := by
  rw [rescaledSegment, sub_self, zero_div, segment_zero]

theorem rescaledSegment_end (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n)
    {l u : ℝ} (hlu : l ≠ u) : rescaledSegment a b l u u = b := by
  rw [rescaledSegment, div_self (sub_ne_zero.mpr hlu.symm), segment_one a b hab]

theorem contDiff_rescaledSegment_val (a b : Sphere n) (l u : ℝ) :
    ContDiff ℝ ∞ (fun t => (rescaledSegment a b l u t).val) :=
  (contDiff_segment_val a b).comp ((contDiff_id.sub contDiff_const).div_const _)

end Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic
