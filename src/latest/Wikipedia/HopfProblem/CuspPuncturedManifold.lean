import Wikipedia.HopfProblem.CuspPuncturedBasic
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Wikipedia.HopfProblem.CuspPuncturedLocalExponential

/-!
# The logarithmic cover is locally biholomorphic to the actual punctured cusp

The local exponential charts and the analytic quotient projection compose
to give local analytic inverses on the whole punctured cusp, with its
existing open-submanifold atlas.  No transported target atlas is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

/-- Holomorphicity descends through a surjective local analytic
diffeomorphism, with the target's existing manifold structure. -/
theorem contMDiff_of_comp_localDiffeomorph
    {E F F' H K K' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace K' P]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
    (L : ModelWithCorners ℂ F' K') {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f)
    {g : N → P} (hgf : ContMDiff I L ω (g ∘ f)) : ContMDiff J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]

namespace CuspUniformization

open ToricCharts ToricSpace CuspQuotient

local notation "Ilog" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

theorem totalCuspCover_continuous : Continuous (totalCuspCover C ε) :=
  (quotientMap_continuous C ε).comp (totalExponentialLift_holomorphic ε).continuous

theorem puncturedCuspCover_continuous : Continuous (puncturedCuspCover C ε) :=
  (totalCuspCover_continuous C ε).subtype_mk _

theorem puncturedQuotientMap_continuous : Continuous (puncturedQuotientMap C ε) :=
  ((quotientMap_continuous C ε).comp continuous_subtype_val).subtype_mk _

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

theorem quotientMap_isLocalDiffeomorph :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph I₃ I₃ ω (quotientMap C ε) := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact CoveringQuotient.project_isLocalDiffeomorph
    (quotientMap_covering C ε hε hε1 hC hR)
    (fun g => tubeTranslate_holomorphic C (disc ε) g.toAdd hC)

theorem puncturedQuotientMap_isLocalDiffeomorph :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph I₃ I₃ ω (puncturedQuotientMap C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact isLocalDiffeomorph_restrictOpens I₃ I₃
    (quotientMap_isLocalDiffeomorph C ε hε hε1 hC hR)
    (puncturedTubeOpen ε) (puncturedQuotientOpen C ε) (fun _ hx => hx)

theorem puncturedCuspCover_isLocalDiffeomorph :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph Ilog I₃ ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro p
  change IsLocalDiffeomorphAt Ilog I₃ ω
    (puncturedQuotientMap C ε ∘ puncturedExponential ε) p
  exact (puncturedExponential_isLocalDiffeomorph ε p).comp
    (K := I₃) (P := PuncturedQuotient C ε)
    (puncturedQuotientMap_isLocalDiffeomorph C ε hε hε1 hC hR (puncturedExponential ε p))

theorem puncturedCuspCover_holomorphic :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff Ilog I₃ ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).contMDiff

include hε hε1 hC hR in
theorem puncturedCuspCover_isLocalHomeomorph : IsLocalHomeomorph (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).isLocalHomeomorph

include hε hε1 hC hR in
theorem puncturedCuspCover_isOpenMap : IsOpenMap (puncturedCuspCover C ε) :=
  (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR).isOpenMap

end CuspUniformization

end Wikipedia.HopfProblem
