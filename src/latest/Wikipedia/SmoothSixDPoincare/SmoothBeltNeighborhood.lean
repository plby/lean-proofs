import Wikipedia.SmoothSixDPoincare.MorseBeltNeighborhood

/-!
# Native smooth coordinates around the whole actual belt sphere

Both directions are smooth in the original regular-level atlas. The forward
map is the inverse Morse chart composed with the explicit curved coordinates;
the inverse is obtained from the original chart and the explicit triangular
inverse. This does not assert smoothness of a topological surgery realization.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (c : SignedMorseChart (E := E) f p)

open Classical in
theorem contMDiff_beltRawCoordinates (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates))
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞ (c.beltRawCoordinates ρ) := by
  have hv : ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (Subtype.val : PuncturedHandle.UnitSphere c.PositiveCoordinates → c.PositiveCoordinates) :=
    contMDiff_coe_sphere (n := n)
  have hraw : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates))
      𝓘(ℝ, c.PositiveCoordinates × c.NegativeCoordinates) ∞
      (fun z : PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates =>
        ((z.1 : c.PositiveCoordinates), z.2)) :=
    (hv.comp contMDiff_fst).prodMk_space contMDiff_snd
  have hswap : ContDiff ℝ ∞
      (Prod.swap : c.PositiveCoordinates × c.NegativeCoordinates →
        c.NegativeCoordinates × c.PositiveCoordinates) :=
    contDiff_snd.prodMk contDiff_fst
  exact hswap.contMDiff.comp ((MorseHandle.contDiff_ambientMap ρ).contMDiff.comp hraw)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem contMDiff_beltNeighborhoodMap (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates)) 𝓘(ℝ, RegularLevel.Model E) ∞
      (c.beltNeighborhoodMap ρ hρ) := by
  let _ := RegularLevel.chartedSpace hf hreg
  have hc : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates))
      𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun z : c.beltSource ρ hρ => c.beltRawCoordinates ρ z.val) :=
    (c.contMDiff_beltRawCoordinates n ρ).comp contMDiff_subtype_val
  have hM := c.splitChart.contMDiffOn_invFun.comp_contMDiff hc (fun z => z.property)
  have hL : ContMDiff ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates))
      𝓘(ℝ, RegularLevel.Model E) ∞
      (fun z : c.beltSource ρ hρ => (c.beltNeighborhoodMap ρ hρ z).val) :=
    (RegularLevel.contMDiff_iff_inclusion hf hreg
      ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates)) _).mpr hM
  exact (ContMDiff.subtypeVal_comp_iff (c.beltTarget ρ) _).mp hL

open Classical in
theorem contMDiff_beltNeighborhoodInverse (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates)) ∞
      (c.beltNeighborhoodInverse ρ hρ) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  have hi : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞
      (fun y : c.beltTarget ρ => (y.val : M)) :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_subtype_val
  have hswap : ContDiff ℝ ∞
      (Prod.swap : c.NegativeCoordinates × c.PositiveCoordinates →
        c.PositiveCoordinates × c.NegativeCoordinates) :=
    contDiff_snd.prodMk contDiff_fst
  have hc : ContMDiff 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, c.PositiveCoordinates × c.NegativeCoordinates) ∞
      (fun y : c.beltTarget ρ => c.beltInverseCoordinates ρ (y.val : M)) :=
    (MorseHandle.contDiff_ambientInverse hρ).contMDiff.comp
      (hswap.contMDiff.comp
        (c.splitChart.contMDiffOn_toFun.comp_contMDiff hi (fun y => y.property)))
  have hpos : ContMDiff 𝓘(ℝ, RegularLevel.Model E) (𝓡 n) ∞
      (fun y : c.beltTarget ρ => (c.beltNeighborhoodInverse ρ hρ y).val.1) :=
    (contDiff_fst.contMDiff.comp hc).codRestrict_sphere (n := n)
      (fun y => mem_sphere_zero_iff_norm.mpr
        (c.norm_beltInverseCoordinates_fst ρ hρ y.val y.property))
  have hneg : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (fun y : c.beltTarget ρ => (c.beltNeighborhoodInverse ρ hρ y).val.2) :=
    (show ContDiff ℝ ∞
      (Prod.snd : c.PositiveCoordinates × c.NegativeCoordinates → c.NegativeCoordinates)
      from contDiff_snd).contMDiff.comp hc
  exact (ContMDiff.subtypeVal_comp_iff (c.beltSource ρ hρ) _).mp (hpos.prodMk hneg)

open Classical in
/-- A native smooth coordinate neighborhood around the actual positive Morse core. -/
def beltNeighborhoodDiffeomorph (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ, c.NegativeCoordinates)) 𝓘(ℝ, RegularLevel.Model E)
      (c.beltSource ρ hρ) (c.beltTarget ρ) ∞ := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact {
    toEquiv := (c.beltNeighborhoodHomeomorph ρ hρ).toEquiv
    contMDiff_toFun := c.contMDiff_beltNeighborhoodMap hf n ρ hρ hreg
    contMDiff_invFun := c.contMDiff_beltNeighborhoodInverse hf n ρ hρ hreg }

open Classical in
theorem beltNeighborhoodDiffeomorph_zero (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltNeighborhoodDiffeomorph hf n ρ hρ hreg (c.beltZeroPoint ρ hρ hblock v)).val =
        c.beltCoreMap ρ hρ hblock v := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact c.beltNeighborhoodHomeomorph_zero ρ hρ hblock

open Classical in
theorem beltNeighborhoodDiffeomorph_normal (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ z : c.beltSource ρ hρ,
      (c.splitChart ((c.beltNeighborhoodDiffeomorph hf n ρ hρ hreg z).val : M)).1 =
        ρ • z.val.2 := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact c.beltNeighborhoodHomeomorph_normal ρ hρ

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
