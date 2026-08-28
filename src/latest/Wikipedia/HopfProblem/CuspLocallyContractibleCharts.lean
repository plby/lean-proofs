import Wikipedia.HopfProblem.CuspLocallyContractibleModel
import Wikipedia.HopfProblem.CuspNormalizationChart

/-!
# Original normal-crossing charts restricted to the actual central fibre

Each normalization chart restricts to a genuine homeomorphism between
an open subset of the original zero-product affine fibre and an open
subset of the original quotient central fibre.  Both directions are
the unchanged chart maps.  The local contractibility assertion uses
these actual open subspaces, not a replacement homotopy model.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspLocallyContractible

open ToricCharts ToricFan ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "E₃" => CoordinateSpace 3
local notation "W" => {q : QuotientSpace C ε // projection C ε q = 0}
local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The chart target intersected with the literal affine zero-product fibre. -/
def centralModelOpen : Opens centralAffine :=
  ⟨(Subtype.val : centralAffine → E₃) ⁻¹' (e).target,
    (e).open_target.preimage continuous_subtype_val⟩

/-- The chart source intersected with the literal original quotient central fibre. -/
def centralFibreOpen : Opens W :=
  ⟨(Subtype.val : W → QuotientSpace C ε) ⁻¹' (e).source,
    (e).open_source.preimage continuous_subtype_val⟩

/-- The original inverse chart maps the actual zero-product fibre to the original central fibre. -/
def centralChartForward (z : centralModelOpen C ε hε hε1 hC hR a s) :
    centralFibreOpen C ε hε hε1 hC hR a s :=
  ⟨⟨(e).symm z.val.val, by
    rw [normalizationChart_projection C ε hε hε1 hC hR a s z.property]
    exact z.val.property⟩, (e).map_target z.property⟩

/-- The original forward chart maps original central points to the literal zero-product fibre. -/
def centralChartBackward (x : centralFibreOpen C ε hε hε1 hC hR a s) :
    centralModelOpen C ε hε hε1 hC hR a s :=
  ⟨⟨(e) x.val.val, by
    have h := normalizationChart_projection C ε hε hε1 hC hR a s
      ((e).map_source x.property)
    rw [(e).left_inv x.property] at h
    exact h.symm.trans x.val.property⟩, (e).map_source x.property⟩

theorem centralChartForward_continuous :
    Continuous (centralChartForward C ε hε hε1 hC hR a s) := by
  have h : Continuous (fun z : centralModelOpen C ε hε hε1 hC hR a s =>
      (e).symm z.val.val) :=
    (e).symm.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.property)
  exact h.subtype_mk _ |>.subtype_mk _

theorem centralChartBackward_continuous :
    Continuous (centralChartBackward C ε hε hε1 hC hR a s) := by
  have h : Continuous (fun x : centralFibreOpen C ε hε hε1 hC hR a s => (e) x.val.val) :=
    (e).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.property)
  exact h.subtype_mk _ |>.subtype_mk _

/-- The genuine chart homeomorphism on the original central-fibre subspaces. -/
def centralChartHomeomorph :
    centralModelOpen C ε hε hε1 hC hR a s ≃ₜ centralFibreOpen C ε hε hε1 hC hR a s where
  toFun := centralChartForward C ε hε hε1 hC hR a s
  invFun := centralChartBackward C ε hε hε1 hC hR a s
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (e).right_inv z.property
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (e).left_inv x.property
  continuous_toFun := centralChartForward_continuous C ε hε hε1 hC hR a s
  continuous_invFun := centralChartBackward_continuous C ε hε hε1 hC hR a s

@[simp] theorem centralChartHomeomorph_apply_val
    (z : centralModelOpen C ε hε hε1 hC hR a s) :
    (centralChartHomeomorph C ε hε hε1 hC hR a s z).val.val = (e).symm z.val.val := rfl

@[simp] theorem centralChartHomeomorph_symm_apply_val
    (x : centralFibreOpen C ε hε hε1 hC hR a s) :
    ((centralChartHomeomorph C ε hε hε1 hC hR a s).symm x).val.val = (e) x.val.val := rfl

/-- Each actual central-fibre chart source has a basis of contractible neighbourhoods. -/
theorem centralFibreOpen_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace (centralFibreOpen C ε hε hε1 hC hR a s) := by
  have : StronglyLocallyContractibleSpace (centralModelOpen C ε hε hε1 hC hR a s) :=
    (centralModelOpen C ε hε hε1 hC hR a s).isOpen.stronglyLocallyContractibleSpace
  exact Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace
    (centralChartHomeomorph C ε hε hε1 hC hR a s).symm.isOpenEmbedding

/-- Original quotient representatives and original toric charts cover every central point. -/
theorem centralFibreOpen_cover (x : W) :
    ∃ (a : Tube (disc ε)) (s : Triangle), x ∈ centralFibreOpen C ε hε hε1 hC hR a s := by
  obtain ⟨a, ha⟩ := (show Function.Surjective (quotientMap C ε) from Quotient.mk_surjective) x.val
  obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (a : Space)
  refine ⟨a, s, ?_⟩
  change x.val ∈ (normalizationChart C ε hε hε1 hC hR a s).source
  rw [← ha]
  exact normalizationChart_mem_source C ε hε hε1 hC hR a s ⟨z, hz⟩

end Wikipedia.HopfProblem.CuspLocallyContractible
