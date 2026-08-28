import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct

/-!
# The geometric base torus inside the actual central cusp fibre

The source's constructed phase shear gives a continuous section of the
actual base projection.  Its image is a genuine embedded two-torus in
the original central fibre; at an admissible cusp radius it is closed.
The explicit formula retains the frozen phase character and does not
choose a splitting of homology groups.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb PeriodTorusHigherHomology SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The marked product collapse lies over its literal second factor. -/
@[simp] theorem baseTorusProjection_productCollapse
    (p : CompactFibreTorus × ProductTorus 2) :
    baseTorusProjection C r hr (productCollapse C r hr p) = p.2 := by
  rcases p with ⟨u, t⟩
  obtain ⟨y, rfl⟩ := coordinateProjection_surjective 2 t
  rw [productCollapse_coordinateProjection, baseTorusProjection_honeycombCollapseMap]
  exact baseTorusPoint_realCuspVector y

/-- The base section uses the actual source phase gauge, with free phase
coordinate equal to one. -/
def baseTorusSection : C(ProductTorus 2, QuotientCentralFibre C r) where
  toFun t := productCollapse C r hr (1, t)
  continuous_toFun :=
    (productCollapse C r hr).continuous.comp (continuous_const.prodMk continuous_id)

@[simp] theorem baseTorusSection_apply (t : ProductTorus 2) :
    baseTorusSection C r hr t = productCollapse C r hr (1, t) := rfl

/-- Exact geometric representatives of the base section, including the
frozen phase correction. -/
theorem baseTorusSection_coordinateProjection (y : CuspHoneycombTiling.Plane) :
    baseTorusSection C r hr (coordinateProjection 2 y) =
      honeycombCollapseMap C r hr
        (sourcePhaseCharacter (C 0) (realCuspVector y), realCuspVector y) := by
  rw [baseTorusSection_apply, productCollapse_coordinateProjection, one_mul]

@[simp] theorem baseTorusProjection_section (t : ProductTorus 2) :
    baseTorusProjection C r hr (baseTorusSection C r hr t) = t :=
  baseTorusProjection_productCollapse C r hr (1, t)

theorem baseTorusSection_injective : Function.Injective (baseTorusSection C r hr) :=
  (show Function.LeftInverse (baseTorusProjection C r hr) (baseTorusSection C r hr)
    from baseTorusProjection_section C r hr).injective

theorem baseTorusSection_isEmbedding
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsEmbedding (baseTorusSection C r hr) :=
  (show Function.LeftInverse (baseTorusProjection C r hr) (baseTorusSection C r hr)
    from baseTorusProjection_section C r hr).isEmbedding
      (baseTorusProjection_continuous C r hr hC) (baseTorusSection C r hr).continuous

/-- The actual subset of the central fibre given by this section. -/
def baseTorusImage : Set (QuotientCentralFibre C r) :=
  Set.range (baseTorusSection C r hr)

theorem baseTorusImage_isCompact : IsCompact (baseTorusImage C r hr) :=
  isCompact_range (baseTorusSection C r hr).continuous

/-- The image is homeomorphic to the marked standard two-torus. -/
def baseTorusHomeomorph
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ProductTorus 2 ≃ₜ baseTorusImage C r hr :=
  (baseTorusSection_isEmbedding C r hr hC).toHomeomorph

@[simp] theorem baseTorusHomeomorph_coe
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (t : ProductTorus 2) :
    (baseTorusHomeomorph C r hr hC t : QuotientCentralFibre C r) =
      baseTorusSection C r hr t := rfl

theorem baseTorusSection_isClosedEmbedding (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r) : IsClosedEmbedding (baseTorusSection C r hr) := by
  let := CuspQuotient.quotient_t2Space C r hr hr1 hC hR
  exact (baseTorusSection C r hr).continuous.isClosedEmbedding
    (baseTorusSection_injective C r hr)

theorem baseTorusImage_isClosed (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r) : IsClosed (baseTorusImage C r hr) :=
  (baseTorusSection_isClosedEmbedding C r hr hr1 hC hR).isClosed_range

end Wikipedia.HopfProblem.CuspCentralHomology
