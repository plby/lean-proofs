import Wikipedia.SmoothSixDPoincare.SmoothMorseHandleAmbient
import Wikipedia.SmoothSixDPoincare.MorseBeltSphereSmooth

/-!
# Exact product coordinates around the actual positive Morse core

The positive sphere times the negative vector space parametrizes the upper
quadratic level, wherever the original split chart is defined. Its inverse
normal coordinate is the original negative Morse coordinate divided by the
positive radius. No smoothness of the surgery realization is used.
-/

noncomputable section

open Set Metric Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (c : SignedMorseChart (E := E) f p)

open Classical in
def beltRawCoordinates (ρ : ℝ)
    (z : PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  (MorseHandle.ambientMap ρ ((z.1 : c.PositiveCoordinates), z.2)).swap

open Classical in
theorem continuous_beltRawCoordinates (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltRawCoordinates ρ) :=
  continuous_swap.comp ((MorseHandle.ambientHomeomorph ρ hρ).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

open Classical in
def beltSource (ρ : ℝ) (hρ : 0 < ρ) :
    Opens (PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :=
  ⟨c.beltRawCoordinates ρ ⁻¹' c.splitChart.target,
    c.splitChart.open_target.preimage (c.continuous_beltRawCoordinates ρ hρ)⟩

open Classical in
def beltTarget (ρ : ℝ) : Opens {y : M // f y = f p + ρ ^ 2} :=
  ⟨Subtype.val ⁻¹' c.splitChart.source,
    c.splitChart.open_source.preimage continuous_subtype_val⟩

open Classical in
def beltNeighborhoodMap (ρ : ℝ) (hρ : 0 < ρ) (z : c.beltSource ρ hρ) :
    c.beltTarget ρ :=
  ⟨⟨c.splitChart.symm (c.beltRawCoordinates ρ z.val), by
      rw [c.splitChart_inverse_equation z.property]
      have hh := MorseHandle.ambientMap_lower_sphere hρ z.val.1 z.val.2
      change -‖(c.beltRawCoordinates ρ z.val).2‖ ^ 2 +
        ‖(c.beltRawCoordinates ρ z.val).1‖ ^ 2 = -(ρ ^ 2) at hh
      linarith⟩,
    c.splitChart.map_target' z.property⟩

open Classical in
theorem continuous_beltNeighborhoodMap (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodMap ρ hρ) := by
  have hc : Continuous (fun z : c.beltSource ρ hρ =>
      c.splitChart.symm (c.beltRawCoordinates ρ z.val)) :=
    c.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      ((c.continuous_beltRawCoordinates ρ hρ).comp continuous_subtype_val)
      (fun z => z.property)
  exact (hc.subtype_mk _).subtype_mk _

open Classical in
def beltInverseCoordinates (ρ : ℝ) (y : M) :
    c.PositiveCoordinates × c.NegativeCoordinates :=
  MorseHandle.ambientInverse ρ (c.splitChart y).swap

open Classical in
theorem continuousOn_beltInverseCoordinates (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (c.beltInverseCoordinates ρ) c.splitChart.source :=
  (MorseHandle.ambientHomeomorph ρ hρ).symm.continuous.comp_continuousOn
    (continuous_swap.comp_continuousOn c.splitChart.contMDiffOn_toFun.continuousOn)

open Classical in
theorem beltInverseCoordinates_neighborhoodMap (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    c.beltInverseCoordinates ρ ((c.beltNeighborhoodMap ρ hρ z).val : M) =
      ((z.val.1 : c.PositiveCoordinates), z.val.2) := by
  have hr : c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val := c.splitChart.right_inv' z.property
  change MorseHandle.ambientInverse ρ
    (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).swap = _
  rw [hr]
  exact MorseHandle.ambientInverse_ambientMap hρ _

open Classical in
theorem norm_beltInverseCoordinates_fst (ρ : ℝ) (hρ : 0 < ρ)
    (y : {y : M // f y = f p + ρ ^ 2}) (hy : (y : M) ∈ c.splitChart.source) :
    ‖(c.beltInverseCoordinates ρ y).1‖ = 1 := by
  apply MorseHandle.norm_ambientInverse_fst_of_lower hρ
  have hh := c.splitChart_equation hy
  rw [y.property] at hh
  change -‖(c.splitChart (y : M)).2‖ ^ 2 +
    ‖(c.splitChart (y : M)).1‖ ^ 2 = -(ρ ^ 2)
  linarith

open Classical in
def beltNeighborhoodInverse (ρ : ℝ) (hρ : 0 < ρ) (y : c.beltTarget ρ) :
    c.beltSource ρ hρ := by
  let v : PuncturedHandle.UnitSphere c.PositiveCoordinates :=
    ⟨(c.beltInverseCoordinates ρ (y.val : M)).1, mem_sphere_zero_iff_norm.mpr
      (c.norm_beltInverseCoordinates_fst ρ hρ y.val y.property)⟩
  refine ⟨(v, (c.beltInverseCoordinates ρ (y.val : M)).2), ?_⟩
  change (MorseHandle.ambientMap ρ
    (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap ∈ c.splitChart.target
  rw [MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
  exact c.splitChart.map_source' y.property

open Classical in
theorem continuous_beltNeighborhoodInverse (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodInverse ρ hρ) := by
  have hc : Continuous (fun y : c.beltTarget ρ =>
      c.beltInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_beltInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  exact ((hc.fst.subtype_mk _).prodMk hc.snd).subtype_mk _

open Classical in
/-- Exact sphere-times-normal coordinates on the upper level inside the original Morse chart. -/
def beltNeighborhoodHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    c.beltSource ρ hρ ≃ₜ c.beltTarget ρ where
  toFun := c.beltNeighborhoodMap ρ hρ
  invFun := c.beltNeighborhoodInverse ρ hρ
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst
        (c.beltInverseCoordinates_neighborhoodMap ρ hρ z))
    · exact congrArg (fun w : c.PositiveCoordinates × c.NegativeCoordinates => w.2)
        (c.beltInverseCoordinates_neighborhoodMap ρ hρ z)
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change c.splitChart.symm
      (MorseHandle.ambientMap ρ
        (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap = (y.val : M)
    rw [MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
    exact c.splitChart.left_inv' y.property
  continuous_toFun := c.continuous_beltNeighborhoodMap ρ hρ
  continuous_invFun := c.continuous_beltNeighborhoodInverse ρ hρ

open Classical in
/-- The Morse block gives a uniform neighborhood around the entire positive core. -/
theorem enlarged_closed_belt_subset_source (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    (univ : Set (PuncturedHandle.UnitSphere c.PositiveCoordinates)) ×ˢ
      closedBall (0 : c.NegativeCoordinates) (3 / 2 : ℝ) ⊆ c.beltSource ρ hρ := by
  rintro ⟨v, u⟩ ⟨_, hu⟩
  have hh := MorseHandle.ambientMap_sphere_mem_product hρ v u
    (mem_closedBall_zero_iff.mp hu)
  exact hblock ⟨hh.2, hh.1⟩

open Classical in
def beltZeroPoint (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) : c.beltSource ρ hρ :=
  ⟨(v, 0), c.enlarged_closed_belt_subset_source ρ hρ hblock
    ⟨mem_univ v, by norm_num⟩⟩

open Classical in
/-- The zero section is the original belt core, with its original sphere parametrization. -/
theorem beltNeighborhoodHomeomorph_zero (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    (c.beltNeighborhoodHomeomorph ρ hρ (c.beltZeroPoint ρ hρ hblock v)).val =
      c.beltCoreMap ρ hρ hblock v := by
  apply Subtype.ext
  rw [c.beltCoreMap_coe]
  change c.splitChart.symm (c.beltRawCoordinates ρ (v, 0)) = _
  simp [beltRawCoordinates, MorseHandle.ambientMap]

open Classical in
/-- The normal projection in the original chart is exactly the scaled product coordinate. -/
theorem beltNeighborhoodHomeomorph_normal (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    (c.splitChart ((c.beltNeighborhoodHomeomorph ρ hρ z).val : M)).1 = ρ • z.val.2 := by
  have hr : c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val := c.splitChart.right_inv' z.property
  change (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).1 = _
  rw [hr]
  rfl

open Classical in
theorem beltNeighborhoodHomeomorph_inverse_normal (ρ : ℝ) (hρ : 0 < ρ)
    (y : c.beltTarget ρ) :
    ((c.beltNeighborhoodHomeomorph ρ hρ).symm y).val.2 =
      ρ⁻¹ • (c.splitChart (y.val : M)).1 := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
