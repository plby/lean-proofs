import Wikipedia.HopfProblem.DegreeCollapseRadialCylinderSmooth
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalRegularity

/-!
# The fixed Morse normal derivative of an actual transverse native trace

The source may be any native manifold, in particular the time-times-sphere
parameter space. The original belt normal is surjective and annihilates
the belt tangent map. Native transversality and equal dimensions then give
an invertible normal derivative of the original trace.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M G H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [ChartedSpace H X] {f : M → ℝ} {p : M}

theorem bijective_native_trace_beltNormal
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ G = Module.finrank ℝ d.chart.NegativeCoordinates)
    (g : X → d.UpperLevel) (x : X)
    (v : sphere (0 : d.chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) g x →
    d.surgery.beltSphere v = g x →
    NativeTransversality.At I (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g d.surgery.beltSphere x v →
    Bijective (mfderiv I 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg hcross htrans
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let A : G →L[ℝ] RegularLevel.Model E := mfderiv I 𝓘(ℝ, RegularLevel.Model E) g x
  have hQ : Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQB : Q.comp B = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hAB : Surjective (A.coprod B) := htrans hcross
  have hi : Bijective (Q.comp A) := TransverseCoordinates.bijective_normal_comp Q B A hQ
    (TransverseCoordinates.surjective_coprod_swap A B hAB) hQB hdim
  have hx : g x ∈ d.beltNormalDomain := hcross ▸ d.belt_mem_normalDomain v
  have hnormal := d.contMDiffOn_beltNormal hf |>.contMDiffAt (d.isOpen_beltNormalDomain.mem_nhds hx)
  have heq : (mfderiv I 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x :
      G →L[ℝ] d.chart.NegativeCoordinates) = Q.comp A := by
    rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp)) hg, ← hcross]
    rfl
  rw [heq]
  exact hi

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
