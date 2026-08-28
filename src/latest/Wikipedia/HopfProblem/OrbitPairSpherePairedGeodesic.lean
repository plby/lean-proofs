import Wikipedia.HopfProblem.OrbitPairSphereLocalGeodesic
import Wikipedia.HopfProblem.OrbitPairSphereGeodesicTransport

/-!
# Short energy-minimizing sphere segments with both endpoints varying

Rotate the first endpoint to the fixed center of a constructed logarithm,
use that logarithm for the second endpoint, and rotate the segment back.
The domain is an actual open neighborhood of the diagonal base pair.
All smoothness is proved on the ambient product, including coincident
endpoints. The segment has its literal endpoints and never increases the
energy of a smooth sphere path with those endpoints.
-/

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential SphereGeodesicTransport

variable {n : ℕ} {x : Vector n} {ε : ℝ} (d : LocalLogData x ε)

def domain : Set (Vector n × Vector n) :=
  {p | p.1 ≠ 0 ∧ x + p.1 ≠ 0 ∧ backward x p.1 p.2 ∈ d.domain}

theorem isOpen_domain : IsOpen (domain d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ha : {q : Vector n × Vector n | q.1 ≠ 0} ∈ 𝓝 p :=
    (isClosed_eq continuous_fst (continuous_const (y := (0 : Vector n)))).isOpen_compl.mem_nhds hp.1
  have hs : {q : Vector n × Vector n | x + q.1 ≠ 0} ∈ 𝓝 p :=
    (isClosed_eq (continuous_const.add continuous_fst)
      (continuous_const (y := (0 : Vector n)))).isOpen_compl.mem_nhds hp.2.1
  have hc : ContinuousAt (fun q : Vector n × Vector n => backward x q.1 q.2) p :=
    (contDiffAt_backward contDiffAt_const contDiffAt_fst contDiffAt_snd hp.1 hp.2.1).continuousAt
  have hr := hc (d.isOpen_domain.mem_nhds hp.2.2)
  filter_upwards [ha, hs, hr] with q hqa hqs hqr
  exact ⟨hqa, hqs, hqr⟩

theorem base_mem_domain (hx : ‖x‖ = 1) : (x, x) ∈ domain d := by
  have hn : x ≠ 0 := by intro h; simpa [h] using hx
  refine ⟨hn, ?_, ?_⟩
  · intro h
    have htwo : (2 : ℝ) • x = 0 := by simpa only [two_smul] using h
    exact hn ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
  · simpa only [backward_self] using d.base_mem_domain hx

def segment (a b : Vector n) (l u t : ℝ) : Vector n :=
  forward x a (d.segmentTo (backward x a b) l u t)

theorem contDiffOn_family (l u : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Vector n × Vector n) =>
      segment d q.2.1 q.2.2 l u q.1) (univ ×ˢ domain d) := by
  intro q hq
  have ha : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hb : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hr : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) => backward x q.2.1 q.2.2) q :=
    contDiffAt_backward contDiffAt_const ha hb hq.2.1 hq.2.2.1
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) =>
      d.log (backward x q.2.1 q.2.2)) q :=
    ContDiffAt.comp (f := fun q : ℝ × (Vector n × Vector n) => backward x q.2.1 q.2.2)
      (g := d.log) q (d.contDiffOn_log.contDiffAt (d.isOpen_domain.mem_nhds hq.2.2.2)) hr
  have hp : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) =>
      (q.1, d.log (backward x q.2.1 q.2.2))) q := contDiffAt_fst.prodMk hl
  have hg : ContDiffAt ℝ ∞ (fun q : ℝ × (Vector n × Vector n) =>
      SphereTangentExponential.segment x (d.log (backward x q.2.1 q.2.2)) l u q.1) q :=
    ContDiffAt.comp
      (g := fun p : ℝ × Tangent x => SphereTangentExponential.segment x p.2 l u p.1)
      (f := fun q : ℝ × (Vector n × Vector n) => (q.1, d.log (backward x q.2.1 q.2.2)))
      q (contDiff_segment_family x l u).contDiffAt hp
  exact (contDiffAt_forward contDiffAt_const ha hg hq.2.1 hq.2.2.1).contDiffWithinAt

theorem contDiff_segment (a b : Vector n) (l u : ℝ) : ContDiff ℝ ∞ (segment d a b l u) := by
  have hc := SphereTangentExponential.contDiff_segment x (d.log (backward x a b)) l u
  exact (localRotationEquiv x a).toContinuousLinearEquiv.contDiff.comp hc

theorem segment_start (hx : ‖x‖ = 1) {a b : Vector n} (ha : ‖a‖ = 1) (l u : ℝ) :
    segment d a b l u l = a := by
  rw [segment, d.segmentTo_start, forward_base hx ha]

theorem segment_end (hx : ‖x‖ = 1) {a b : Vector n} (hb : ‖b‖ = 1)
    (hp : (a, b) ∈ domain d) {l u : ℝ} (hlu : l ≠ u) : segment d a b l u u = b := by
  rw [segment, d.segmentTo_end hx ((norm_backward x a b).trans hb) hp.2.2 hlu,
    forward_backward]

theorem segment_diagonal (hx : ‖x‖ = 1) {a : Vector n} (ha : ‖a‖ = 1) (l u t : ℝ) :
    segment d a a l u t = a := by
  rw [segment, backward_base hx ha, d.segmentTo_base, forward_base hx ha]

theorem norm_segment (hx : ‖x‖ = 1) (a b : Vector n) (l u t : ℝ) :
    ‖segment d a b l u t‖ = 1 := by
  rw [segment, norm_forward]
  exact d.norm_segmentTo hx _ l u t

theorem energy_segment (a b : Vector n) (l u : ℝ) :
    SpherePathEnergy.energy (segment d a b l u) l u =
      SpherePathEnergy.energy (d.segmentTo (backward x a b) l u) l u :=
  energy_forward x a
    (SphereTangentExponential.contDiff_segment x (d.log (backward x a b)) l u) l u

theorem energy_le (hx : ‖x‖ = 1) (hε : ε ≤ Real.pi / 2)
    {γ : ℝ → Vector n} (hγ : ContDiff ℝ ∞ γ) (hunit : ∀ t, ‖γ t‖ = 1)
    {l u : ℝ} (hlu : l < u) (hp : (γ l, γ u) ∈ domain d) :
    SpherePathEnergy.energy (segment d (γ l) (γ u) l u) l u ≤ SpherePathEnergy.energy γ l u := by
  have hb : ContDiff ℝ ∞ (fun t => backward x (γ l) (γ t)) :=
    (localRotationEquiv x (γ l)).symm.toContinuousLinearEquiv.contDiff.comp hγ
  have hn (t : ℝ) : ‖backward x (γ l) (γ t)‖ = 1 :=
    (norm_backward x (γ l) (γ t)).trans (hunit t)
  have h := d.segmentTo_energy_le hx hε hb hn hlu (backward_base hx (hunit l)) hp.2.2
  rw [energy_backward x (γ l) hγ] at h
  rw [energy_segment]
  exact h

end Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic
