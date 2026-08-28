import Wikipedia.SmoothSixDPoincare.MorseAttachingNeighborhood

/-!
# A native diffeomorphism on a neighborhood of the entire closed attaching face

The source is the full open region of valid sphere-times-vector Morse
coordinates, not only the interior of the transverse unit disk. The exact
original closed attaching face, including its edge, is contained in it.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (c : SignedMorseChart (E := E) f p)

open Classical in
theorem contMDiff_attachingRawCoordinates (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates))
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞ (c.attachingRawCoordinates ρ) := by
  have hu : ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (Subtype.val : PuncturedHandle.UnitSphere c.NegativeCoordinates → c.NegativeCoordinates) :=
    contMDiff_coe_sphere (n := n)
  have hraw : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates))
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.PositiveCoordinates =>
        ((z.1 : c.NegativeCoordinates), z.2)) :=
    (hu.comp contMDiff_fst).prodMk_space contMDiff_snd
  exact (MorseHandle.contDiff_ambientMap ρ).contMDiff.comp hraw

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem contMDiff_attachingNeighborhoodMap (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates)) 𝓘(ℝ, RegularLevel.Model E) ∞
      (c.attachingNeighborhoodMap ρ hρ) := by
  let _ := RegularLevel.chartedSpace hf hreg
  have hc : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates))
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun z : c.attachingSource ρ hρ => c.attachingRawCoordinates ρ z.val) :=
    (c.contMDiff_attachingRawCoordinates n ρ).comp contMDiff_subtype_val
  have hM := c.splitChart.contMDiffOn_invFun.comp_contMDiff hc (fun z => z.property)
  have hL : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates))
      𝓘(ℝ, RegularLevel.Model E) ∞
      (fun z : c.attachingSource ρ hρ => (c.attachingNeighborhoodMap ρ hρ z).val) :=
    (RegularLevel.contMDiff_iff_inclusion hf hreg
      ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates)) _).mpr hM
  exact (ContMDiff.subtypeVal_comp_iff (c.attachingTarget ρ) _).mp hL

open Classical in
theorem contMDiff_attachingNeighborhoodInverse (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates)) ∞
      (c.attachingNeighborhoodInverse ρ hρ) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  have hi : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞
      (fun y : c.attachingTarget ρ => (y.val : M)) :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_subtype_val
  have hc : ContMDiff 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun y : c.attachingTarget ρ => c.attachingInverseCoordinates ρ (y.val : M)) :=
    (MorseHandle.contDiff_ambientInverse hρ).contMDiff.comp
      (c.splitChart.contMDiffOn_toFun.comp_contMDiff hi (fun y => y.property))
  have hneg : ContMDiff 𝓘(ℝ, RegularLevel.Model E) (𝓡 n) ∞
      (fun y : c.attachingTarget ρ => (c.attachingNeighborhoodInverse ρ hρ y).val.1) :=
    (contDiff_fst.contMDiff.comp hc).codRestrict_sphere (n := n)
      (fun y => mem_sphere_zero_iff_norm.mpr
        (c.norm_attachingInverseCoordinates_fst ρ hρ y.val y.property))
  have hpos : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (fun y : c.attachingTarget ρ => (c.attachingNeighborhoodInverse ρ hρ y).val.2) :=
    (show ContDiff ℝ ∞
      (Prod.snd : c.NegativeCoordinates × c.PositiveCoordinates → c.PositiveCoordinates)
      from contDiff_snd).contMDiff.comp hc
  exact (ContMDiff.subtypeVal_comp_iff (c.attachingSource ρ hρ) _).mp (hneg.prodMk hpos)

open Classical in
/-- The original closed attaching face has a genuine native smooth coordinate neighborhood. -/
def attachingNeighborhoodDiffeomorph (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ, c.PositiveCoordinates)) 𝓘(ℝ, RegularLevel.Model E)
      (c.attachingSource ρ hρ) (c.attachingTarget ρ) ∞ := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact {
    toEquiv := (c.attachingNeighborhoodHomeomorph ρ hρ).toEquiv
    contMDiff_toFun := c.contMDiff_attachingNeighborhoodMap hf n ρ hρ hreg
    contMDiff_invFun := c.contMDiff_attachingNeighborhoodInverse hf n ρ hρ hreg }

open Classical in
/-- The native diffeomorphism retains every original closed-face point, including the corner. -/
theorem attachingNeighborhoodDiffeomorph_face (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ (u : PuncturedHandle.UnitSphere c.NegativeCoordinates)
      (v : MorseHandle.UnitDisk c.PositiveCoordinates),
      ((c.attachingNeighborhoodDiffeomorph hf n ρ hρ hreg
        (c.closedAttachingPoint ρ hρ hblock u v)).val : M) =
          (c.attachingBoundaryMap ρ hρ hblock (u, v) : M) := by
  let _ := RegularLevel.chartedSpace hf hreg
  intro u v
  rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
