import Wikipedia.SmoothSixDPoincare.MorseBeltSphereSmooth
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Embeddings and injective native differentials of the Morse core spheres

Both maps are restrictions of the original handle embedding. Their native
differentials are injective because they are the sphere inclusion, followed
by an injective linear map and the inverse Morse chart.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace PartialChart

variable {N F E H M : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- An injective linear image of a sphere remains immersive in a smooth partial chart. -/
theorem injective_mfderiv_linear_sphere {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞) (L : N →L[ℝ] F)
    (hL : Injective L) (u : sphere (0 : N) 1) (hu : L (u : N) ∈ Φ.source) :
    Injective (mfderiv (𝓡 n) I (fun v : sphere (0 : N) 1 => Φ (L (v : N))) u) := by
  have hcoesm : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞
      (Subtype.val : sphere (0 : N) 1 → N) :=
    contMDiff_coe_sphere (E := N) (n := n)
  have hcoe := hcoesm.mdifferentiableAt (x := u) (by simp)
  have hlinear : MDifferentiableAt 𝓘(ℝ, N) 𝓘(ℝ, F) L (u : N) :=
    L.differentiableAt.mdifferentiableAt
  have hinner := hlinear.comp u hcoe
  have hsphere : Injective (mfderiv (𝓡 n) 𝓘(ℝ, N)
      (Subtype.val : sphere (0 : N) 1 → N) u) := by
    convert! injective_mvfderiv_subtypeVal_sphere u
  change Injective (mfderiv (𝓡 n) I (Φ ∘ (L ∘ Subtype.val)) u)
  rw [mfderiv_comp u (Φ.mdifferentiableAt (by simp) hu) hinner,
    mfderiv_comp u hlinear hcoe, mfderiv_eq_fderiv, L.fderiv]
  exact (bijective_mfderiv Φ hu).injective.comp (hL.comp hsphere)

end PartialChart

namespace ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
theorem injective_attachingCoreMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    Injective (c.attachingCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh := c.attachingHandleMap_injective ρ hρ hblock
    (congrArg (fun y : {y : M // f y = f p - ρ ^ 2} => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.1 : c.NegativeCoordinates)) hh)

open Classical in
theorem injective_beltCoreMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    Injective (c.beltCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh := c.attachingHandleMap_injective ρ hρ hblock
    (congrArg (fun y : {y : M // f y = f p + ρ ^ 2} => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.2 : c.PositiveCoordinates)) hh)

open Classical in
theorem attachingCoreMap_isClosedEmbedding [T2Space M] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    IsClosedEmbedding (c.attachingCoreMap ρ hρ hblock) :=
  (c.attachingCoreMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.injective_attachingCoreMap ρ hρ hblock)

open Classical in
theorem beltCoreMap_isClosedEmbedding [T2Space M] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    IsClosedEmbedding (c.beltCoreMap ρ hρ hblock) :=
  (c.beltCoreMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.injective_beltCoreMap ρ hρ hblock)

open Classical in
theorem injective_mfderiv_attachingCoreMap_ambient (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) u) := by
  let L : c.NegativeCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inl ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Injective L := by
    intro x y hxy
    apply smul_right_injective c.NegativeCoordinates hρ.ne'
    exact congrArg Prod.fst hxy
  have hu : L (u : c.NegativeCoordinates) ∈ c.splitChart.target := by
    have hh := hblock (MorseHandle.modelMap_mem_product hρ
      (⟨(u : c.NegativeCoordinates), sphere_subset_closedBall u.property⟩,
        (⟨0, by simp⟩ : MorseHandle.UnitDisk c.PositiveCoordinates)))
    simpa [L, MorseHandle.modelMap] using hh
  have heq : Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun v : PuncturedHandle.UnitSphere c.NegativeCoordinates => c.splitChart.symm (L v) := by
    funext v
    rw [Function.comp_apply, c.attachingCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL u hu

open Classical in
theorem injective_mfderiv_beltCoreMap_ambient (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) v) := by
  let L : c.PositiveCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inr ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Injective L := by
    intro x y hxy
    apply smul_right_injective c.PositiveCoordinates hρ.ne'
    exact congrArg Prod.snd hxy
  have hv : L (v : c.PositiveCoordinates) ∈ c.splitChart.target := by
    have hh := hblock (MorseHandle.modelMap_mem_product hρ
      ((⟨0, by simp⟩ : MorseHandle.UnitDisk c.NegativeCoordinates),
        ⟨(v : c.PositiveCoordinates), sphere_subset_closedBall v.property⟩))
    simpa [L, MorseHandle.modelMap] using hh
  have heq : Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun u : PuncturedHandle.UnitSphere c.PositiveCoordinates => c.splitChart.symm (L u) := by
    funext u
    rw [Function.comp_apply, c.beltCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL v hv

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open Classical in
/-- The attaching sphere is immersive in the actual lower-level manifold. -/
theorem injective_mfderiv_attachingCoreMap (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    letI := RegularLevel.chartedSpace hf hreg
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (c.attachingCoreMap ρ hρ hblock) u) := by
  exact RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n)
    (c.attachingCoreMap ρ hρ hblock) u
    (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock u)
    (c.injective_mfderiv_attachingCoreMap_ambient n ρ hρ hblock u)

open Classical in
/-- The belt sphere is immersive in the actual upper-level manifold. -/
theorem injective_mfderiv_beltCoreMap (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf hreg
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (c.beltCoreMap ρ hρ hblock) v) := by
  exact RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n)
    (c.beltCoreMap ρ hρ hblock) v
    (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock v)
    (c.injective_mfderiv_beltCoreMap_ambient n ρ hρ hblock v)

end ManifoldMorse.SignedMorseChart

end Wikipedia.SmoothSixDPoincare
