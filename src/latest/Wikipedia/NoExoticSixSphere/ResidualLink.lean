import Wikipedia.NoExoticSixSphere.ResidualLocalCoordinates
import Wikipedia.NoExoticSixSphere.CorankOneEuclideanCoordinates

/-!
# A genuine small link in residual inverse-function coordinates

The parameter sphere is a fixed signed Euclidean isometry of the standard
unit sphere. Its scaled image and its radial contraction stay in the chosen
closed target ball. Pulling them back by the actual inverse chart gives the
local link and the interior points used to contract the leading block.
-/

noncomputable section

open Set Function Metric unitInterval

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne

def scaledParameter (ε : ℝ) (q : Sphere 3) : Vector 4 :=
  ε • WhitneyCusp.residualCoordinates q.val

def contractedParameter (ε : ℝ) (p : I × Sphere 3) : Vector 4 :=
  (1 - (p.1 : ℝ)) • scaledParameter ε p.2

theorem continuous_scaledParameter (ε : ℝ) : Continuous (scaledParameter ε) :=
  (continuous_const : Continuous (fun _ : Sphere 3 ↦ ε)).smul
    (WhitneyCusp.residualCoordinates.continuous.comp continuous_subtype_val)

theorem continuous_contractedParameter (ε : ℝ) : Continuous (contractedParameter ε) :=
  (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    ((continuous_scaledParameter ε).comp continuous_snd)

theorem norm_scaledParameter {ε : ℝ} (hε : 0 < ε) (q : Sphere 3) :
    ‖scaledParameter ε q‖ = ε := by
  rw [scaledParameter, norm_smul, Real.norm_eq_abs, abs_of_pos hε,
    WhitneyCusp.residualCoordinates.norm_map, ClosedHemisphere.unit_norm, mul_one]

theorem scaledParameter_ne_zero {ε : ℝ} (hε : 0 < ε) (q : Sphere 3) :
    scaledParameter ε q ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_scaledParameter hε]
  exact hε

theorem scaledParameter_mem_closedBall {ε : ℝ} (hε : 0 < ε) (q : Sphere 3) :
    scaledParameter ε q ∈ closedBall (0 : Vector 4) ε := by
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right, norm_scaledParameter hε]

theorem contractedParameter_mem_closedBall {ε : ℝ} (hε : 0 < ε) (p : I × Sphere 3) :
    contractedParameter ε p ∈ closedBall (0 : Vector 4) ε := by
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right, contractedParameter, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.1.property.2), norm_scaledParameter hε]
  nlinarith [p.1.property.1]

theorem contractedParameter_zero (ε : ℝ) (q : Sphere 3) :
    contractedParameter ε (0, q) = scaledParameter ε q := by
  simp [contractedParameter]

theorem contractedParameter_one (ε : ℝ) (q : Sphere 3) : contractedParameter ε (1, q) = 0 := by
  simp [contractedParameter]

variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {D : X → BlockMap E (Vector 4)}

def Data.link (d : Data D) (ε : ℝ) (q : Sphere 3) : X := d.coord.symm (scaledParameter ε q)

def Data.radial (d : Data D) (ε : ℝ) (p : I × Sphere 3) : X :=
  d.coord.symm (contractedParameter ε p)

theorem Data.link_mem_source (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    d.link ε q ∈ d.coord.source :=
  d.coord.toOpenPartialHomeomorph.map_target (hball (scaledParameter_mem_closedBall hε q))

theorem Data.residual_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    residual (D (d.link ε q)) = scaledParameter ε q :=
  d.residual_inverse (hball (scaledParameter_mem_closedBall hε q))

theorem Data.leading_radial (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (p : I × Sphere 3) :
    (leading (D (d.radial ε p))).IsInvertible :=
  d.leading_inverse (hball (contractedParameter_mem_closedBall hε p))

theorem Data.radial_zero (d : Data D) (ε : ℝ) (q : Sphere 3) :
    d.radial ε (0, q) = d.link ε q := by
  unfold Data.radial Data.link
  rw [contractedParameter_zero]

theorem Data.radial_one (d : Data D) (ε : ℝ) (q : Sphere 3) :
    d.radial ε (1, q) = d.coord.symm 0 := by
  unfold Data.radial
  rw [contractedParameter_one]

theorem Data.continuous_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) : Continuous (d.link ε) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hy := hball (scaledParameter_mem_closedBall hε q)
  have hγ := d.coord.toOpenPartialHomeomorph.symm.continuousOn.continuousAt
    (d.coord.open_target.mem_nhds hy)
  exact hγ.comp (continuous_scaledParameter ε).continuousAt

theorem Data.continuous_radial (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) : Continuous (d.radial ε) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hy := hball (contractedParameter_mem_closedBall hε p)
  have hγ := d.coord.toOpenPartialHomeomorph.symm.continuousOn.continuousAt
    (d.coord.open_target.mem_nhds hy)
  exact hγ.comp (continuous_contractedParameter ε).continuousAt

end NoExoticSixSphere.ResidualCoordinates
