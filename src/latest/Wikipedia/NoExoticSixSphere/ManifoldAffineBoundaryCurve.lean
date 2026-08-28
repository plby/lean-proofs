import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities
import Wikipedia.NoExoticSixSphere.SphereFamilyClosedCurve
import Wikipedia.NoExoticSixSphere.GenericFamilyLocalCurve
import Wikipedia.NoExoticSixSphere.ReflectionQuotientChart
import Wikipedia.NoExoticSixSphere.FamilyDoublePointOpenLocus

/-!
# Actual manifold-family curve charts at intrinsic singularities

The genuine chartwise regularity supplies a local Euclidean reflection chart.
It is transported to the original ordered closure and then to its actual
unordered quotient. The resulting half-line chart identifies coordinate zero
exactly with diagonal pairs throughout its source.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily FamilyEmbedding InvolutionQuotient

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (p : Parameters e)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
  (S : Set SourceChart) (C : Set (TargetChart n M))
  (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
  (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
  (hp : ∀ t x, ambient e f p t x ∈ r.domain)
  (hgen : GenericInCharts e r f hf S C p)

include hS hC hp hgen hg

theorem exists_closed_curve_at_singular (q : ℝ × Sphere 3)
    (ht : q.1 ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ singularParameters (n := n) (map e r f p)) :
    ∃ ha : (q.1, (q.2, q.2)) ∈ closure (doublePoints (map e r f p)),
    ∃ d : OpenPartialHomeomorph (closure (doublePoints (map e r f p))) ℝ,
      (⟨(q.1, (q.2, q.2)), ha⟩ : closure (doublePoints (map e r f p))) ∈ d.source ∧
      d ⟨(q.1, (q.2, q.2)), ha⟩ = 0 ∧
      (∀ a ∈ d.source, swapClosure (map e r f p) a ∈ d.source) ∧
      ∀ a ∈ d.source, d (swapClosure (map e r f p) a) = -d a := by
  obtain ⟨s, hs, hqs⟩ := hS q.2
  obtain ⟨c, hc, hqc⟩ := hC (map e r f p q.1 q.2)
  let U : Set (ℝ × Vector 3) := {z | (p, z) ∈ chartDomain e r f hf s c}
  have hU : IsOpen U :=
    (chartDomain e r f hf s c).isOpen.preimage (continuous_const.prodMk continuous_id)
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hqs
  have hqU : (q.1, s q.2) ∈ U := by
    change ((s q.2 ∈ s.target ∧ q.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p q.1 (s.symm (s q.2)) ∈ r.domain) ∧
        map e r f p q.1 (s.symm (s q.2)) ∈ c.source
    rw [hleft]
    exact ⟨⟨⟨s.map_source hqs, ht⟩, hp _ _⟩, hqc⟩
  have hF : ContDiffOn ℝ ∞ (uncurry (coordinateFamily (map e r f p) s c)) U :=
    (contDiffOn_chartCoordinates e r f hf s c).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz ↦ hz)
  have hJ : ¬ Injective (chartJet e r f s c (p, q.1, s q.2)) := by
    have h := injective_chartJet_iff e r f hf p hg s c (q.1, s q.2) hqU
    rw [hleft] at h
    exact h.not.mpr hq
  have hres := (hgen.1 s hs c hc).residual_regular (q.1, s q.2) hqU hJ
  apply SphereFamily.exists_closed_curve_of_coordinate_curve
    (map e r f p) hg.continuous s c q hqs hqc
  exact exists_closed_curve_of_local_regular_residual
    (coordinateFamily (map e r f p) s c) hU hF (q.1, s q.2) hqU hres

theorem singular_diagonal_mem_closure (q : ℝ × Sphere 3)
    (ht : q.1 ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ singularParameters (n := n) (map e r f p)) :
    (q.1, (q.2, q.2)) ∈ closure (doublePoints (map e r f p)) :=
  (exists_closed_curve_at_singular e r f hf p hg S C hS hC hp hgen q ht hq).choose

theorem exists_unordered_chart_at_singular (q : ℝ × Sphere 3)
    (ht : q.1 ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ singularParameters (n := n) (map e r f p)) :
    ∃ ha : (q.1, (q.2, q.2)) ∈ closure (doublePoints (map e r f p)),
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) HalfLine,
      unorderedProj (map e r f p) ⟨(q.1, (q.2, q.2)), ha⟩ ∈ d.source ∧
      d (unorderedProj (map e r f p) ⟨(q.1, (q.2, q.2)), ha⟩) = ⟨0, le_rfl⟩ ∧
      ∀ a ∈ d.source, (d a).val = 0 ↔ a ∈ diagonalOrbits (map e r f p) := by
  obtain ⟨ha, c, hcq, hczero, hcswap, hcneg⟩ :=
    exists_closed_curve_at_singular e r f hf p hg S C hS hC hp hgen q ht hq
  let k : ReflectionChart (swapClosure (map e r f p)) := ⟨c, hcswap, hcneg⟩
  let d := k.quotientChart (swapClosure_involutive (map e r f p))
    (swapClosure (map e r f p)).continuous
  have hcenter := k.quotientChart_center (swapClosure_involutive (map e r f p))
    (swapClosure (map e r f p)).continuous hcq hczero
  refine ⟨ha, d, hcenter.1, hcenter.2, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact (k.quotientChart_zero_iff_fixed (swapClosure_involutive (map e r f p))
    (swapClosure (map e r f p)).continuous hb).trans
    ((swapClosure_fixed_iff (map e r f p) b).trans
      (mem_diagonalOrbits_iff (map e r f p) b).symm)

end NoExoticSixSphere.ManifoldAffineSphereFamily
