import Wikipedia.SmoothSixDPoincare.MorseSphereEmbeddings
import Wikipedia.SmoothSixDPoincare.MorseBoundaryContractions

/-!
# Constructed Morse surgery with its actual smooth embedded core spheres

The surgery presentation, endpoint regularity, and exact core identities are
constructed at a uniquely valued Morse critical point. The attaching and belt
spheres are smooth embeddings with injective native differentials in the two
actual regular levels. The new piece retains its actual attachment map, and
the attachment retains its proved quadratic boundary-orbit formula.
No differentiability of the full flow is assumed.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

open Classical in
/-- A surgery of the actual Morse levels, retaining the original chart core maps. -/
structure MorseSurgeryData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : SignedMorseChart (E := E) f p
  block : closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
    closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆ chart.splitChart.target
  attachmentHomeomorph :
    ↥({x : M | f x ≤ f p - radius ^ 2} ∪
      range (chart.attachingHandleMap radius radius_pos block)) ≃ₜ
      {x : M // f x ≤ f p + radius ^ 2}
  attachment_frontier : ∀ x, f (attachmentHomeomorph x) = f p + radius ^ 2 ↔
    x.val ∈ frontier ({y : M | f y ≤ f p - radius ^ 2} ∪
      range (chart.attachingHandleMap radius radius_pos block))
  attachment_fixed : ∀ x, f x.val = f p + radius ^ 2 →
    (attachmentHomeomorph x).val = x.val
  attachment_model_orbits :
    chart.FollowsModelBoundaryOrbits radius radius_pos block attachmentHomeomorph
  surgery : SurgeryBoundaryPair chart.NegativeCoordinates chart.PositiveCoordinates
    {x : M // f x = f p - radius ^ 2 ∧ x ∈
      frontier ({y | f y ≤ f p - radius ^ 2} ∪
        range (chart.normHandleMap radius radius_pos block))}
    {x : M // f x = f p - radius ^ 2} {x : M // f x = f p + radius ^ 2}
  oldExterior_eq : ∀ r, (surgery.oldExterior r : M) = r.val
  newExterior_eq : ∀ r, (surgery.newExterior r : M) =
    (attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩).val
  oldPiece_eq : ∀ z, (surgery.oldPiece z : M) = chart.normHandleMap radius radius_pos block
    (PuncturedHandle.sphereToBall z.1, z.2)
  newPiece_eq : ∀ z, (surgery.newPiece z : M) =
    (attachmentHomeomorph
      ⟨chart.normHandleMap radius radius_pos block (z.1, PuncturedHandle.sphereToBall z.2),
        Or.inr ⟨chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2), rfl⟩⟩).val
  belt_eq : surgery.beltSphere = chart.beltCoreMap radius radius_pos block
  lower_regular : ∀ x, f x = f p - radius ^ 2 → x ∉ criticalPoints E f
  upper_regular : ∀ x, f x = f p + radius ^ 2 → x ∉ criticalPoints E f

namespace MorseSurgeryData

variable {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)

/-- The original lower regular level as a subspace, without changing its topology. -/
abbrev LowerLevel := {x : M // f x = f p - d.radius ^ 2}

/-- The original upper regular level as a subspace, without changing its topology. -/
abbrev UpperLevel := {x : M // f x = f p + d.radius ^ 2}

open Classical in
theorem attaching_eq :
    d.surgery.attachingSphere = d.chart.attachingCoreMap d.radius d.radius_pos d.block :=
  d.chart.attachingSphere_eq_attachingCoreMap d.radius d.radius_pos d.block
    d.surgery d.oldPiece_eq

open Classical in
theorem attaching_isClosedEmbedding [T2Space M] : IsClosedEmbedding d.surgery.attachingSphere := by
  rw [d.attaching_eq]
  exact d.chart.attachingCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

open Classical in
theorem belt_isClosedEmbedding [T2Space M] : IsClosedEmbedding d.surgery.beltSphere := by
  rw [d.belt_eq]
  exact d.chart.beltCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem attaching_smooth (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact d.chart.contMDiff_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular

open Classical in
theorem belt_smooth (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.beltSphere := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.contMDiff_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular

open Classical in
theorem attaching_derivative_injective (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)]
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.attachingSphere u) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact d.chart.injective_mfderiv_attachingCoreMap n hf
    d.radius d.radius_pos d.block d.lower_regular u

open Classical in
theorem belt_derivative_injective (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.injective_mfderiv_beltCoreMap n hf
    d.radius d.radius_pos d.block d.upper_regular v

include hf in
open Classical in
/-- The same constructed surgery retains the proved whole-boundary contraction transfer. -/
theorem upper_circle_nullhomotopies [T2Space M] (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p - d.radius ^ 2}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p + d.radius ^ 2}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
  d.chart.surgery_newBoundary_circle_nullhomotopies n hn hf d.radius d.radius_pos d.block
    d.lower_regular d.surgery d.oldPiece_eq hdim hnull

end MorseSurgeryData

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct all native surgery data below a prescribed radius, retaining critical isolation. -/
theorem exists_morseSurgeryData_lt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p, d.radius < ε ∧
      ∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p := by
  obtain ⟨ρ, hρ, hρε, c, hblock, e, he, hfixed, hlevel, hlower, hupper, horbits, hband⟩ :=
    exists_morse_boundary_attachment_with_model_orbits_lt hf hm hp hunique hε
  exact ⟨{
    radius := ρ
    radius_pos := hρ
    chart := c
    block := hblock
    attachmentHomeomorph := e
    attachment_frontier := he
    attachment_fixed := hfixed
    attachment_model_orbits := horbits
    surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he
    oldExterior_eq := fun _ => rfl
    newExterior_eq := fun _ => rfl
    oldPiece_eq := fun _ => rfl
    newPiece_eq := fun _ => rfl
    belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e he hfixed
    lower_regular := hlower
    upper_regular := hupper }, hρε, hband⟩

open Classical in
/-- All surgery data, including the exact smooth belt map, come from the original Morse function. -/
theorem nonempty_morseSurgeryData {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    Nonempty (MorseSurgeryData E f p) := by
  obtain ⟨d, _, _⟩ := exists_morseSurgeryData_lt hf hm hp hunique zero_lt_one
  exact ⟨d⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
