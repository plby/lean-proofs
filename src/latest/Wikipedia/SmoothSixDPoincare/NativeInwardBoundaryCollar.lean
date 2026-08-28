import Wikipedia.SmoothSixDPoincare.HeightChartInwardCollar
import Wikipedia.SmoothSixDPoincare.RegularLevelHeightCollar
import Wikipedia.SmoothSixDPoincare.NativeSmoothBoundaryBodies

/-!
# Actual inward collars for the native regular sublevel bodies

The original regular-level height chart constructs the collar, including
the empty-boundary case. A commuting body/boundary equivalence transports
these data exactly. No collar-preservation theorem for arbitrary new
attachments is assumed here.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}

def HasInwardCollar (U : SmoothBoundaryBody J) : Prop := Nonempty (InwardBoundaryCollar U.inclusion)

theorem hasInwardCollar_transport {U V : SmoothBoundaryBody J}
    (e : Equiv U V) (h : U.HasInwardCollar) : V.HasInwardCollar :=
  h.map (fun C => C.transport e.boundary.toHomeomorph e.body e.boundary_point)

theorem hasInwardCollar_iff {U V : SmoothBoundaryBody J} (e : Equiv U V) :
    U.HasInwardCollar ↔ V.HasInwardCollar :=
  ⟨hasInwardCollar_transport e, hasInwardCollar_transport e.symm⟩

end SmoothBoundaryBody

namespace RegularLevel

def sublevelBoundaryInclusion {M : Type*} [TopologicalSpace M] (f : M → ℝ) (b : ℝ) :
    C({x : M // f x = b}, {x : M // f x ≤ b}) :=
  HeightChartInwardCollar.levelInclusion ⟨Subtype.val, continuous_subtype_val⟩
    (fun x => x.property)

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

include hf hreg in
theorem nonempty_inwardBoundaryCollar :
    Nonempty (InwardBoundaryCollar (sublevelBoundaryInclusion f b)) := by
  classical
  let _ := chartedSpace hf hreg
  let _ : CompactSpace {x : M // f x = b} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  by_cases hx : Nonempty {x : M // f x = b}
  · let _ := hx
    obtain ⟨ε, hε, Ψ, hsource, hzero, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
    exact ⟨HeightChartInwardCollar.collar ε Ψ.toOpenPartialHomeomorph hε hsource hheight
      hf.continuous ⟨Subtype.val, continuous_subtype_val⟩ (fun x => x.property) hzero hband⟩
  · let _ : IsEmpty {x : M // f x = b} := not_nonempty_iff.mp hx
    exact ⟨InwardBoundaryCollar.ofIsEmpty (sublevelBoundaryInclusion f b)⟩

end RegularLevel

namespace ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

theorem lowerSmoothBody_hasInwardCollar : (d.lowerSmoothBody hf).HasInwardCollar :=
  RegularLevel.nonempty_inwardBoundaryCollar hf d.lower_regular

theorem upperSmoothBody_hasInwardCollar : (d.upperSmoothBody hf).HasInwardCollar :=
  RegularLevel.nonempty_inwardBoundaryCollar hf d.upper_regular

end ManifoldMorse.MorseSurgeryData
end Wikipedia.SmoothSixDPoincare
