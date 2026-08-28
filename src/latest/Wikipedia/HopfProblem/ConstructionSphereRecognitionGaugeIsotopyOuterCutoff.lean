import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCutoff
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Outer localization inside the original small elliptic filling

The scalar cutoff is one below a plateau containing the original boundary
radius and zero past a strictly larger admissible radius.  Its argument
is squared radius, and it is constructed from `Real.smoothTransition`.
The larger radius is chosen in the same original strict power-radius
domain, whose openness supplies a point strictly to the right.

This is only an outer cutoff: it is not compactly supported on the whole
real line by itself.  Multiplication by the separately proved
inner-vanishing collar vector supplies the inner localization.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open ThreefoldOverlapMappingTorus

/-- The original strict radius conditions leave room for a larger radius,
without taking a real root or replacing the prescribed power-radius domain. -/
theorem exists_largerRadius {n : ℕ} {r : ℝ} (a : Radius n r) :
    ∃ b : Radius n r, (a : ℝ) < (b : ℝ) := by
  have hopen : IsOpen {x : ℝ | 0 < x ∧ x < 1 ∧ x ^ n < r} :=
    (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt continuous_id continuous_const).inter
        (isOpen_lt (continuous_id.pow n) continuous_const))
  obtain ⟨b, hb, hab⟩ := nonempty_nhds_inter_Ioi (hopen.mem_nhds a.property)
    (not_isMax_of_lt a.property.2.1)
  exact ⟨⟨b, hb⟩, hab⟩

/-- A strictly larger radius still belonging to the original radius subtype. -/
def largerRadius {n : ℕ} {r : ℝ} (a : Radius n r) : Radius n r :=
  Classical.choose (exists_largerRadius a)

@[simp] theorem lt_largerRadius {n : ℕ} {r : ℝ} (a : Radius n r) :
    (a : ℝ) < (largerRadius a : ℝ) :=
  Classical.choose_spec (exists_largerRadius a)

@[simp] theorem largerRadius_pos {n : ℕ} {r : ℝ} (a : Radius n r) :
    0 < (largerRadius a : ℝ) := (largerRadius a).property.1

@[simp] theorem largerRadius_lt_one {n : ℕ} {r : ℝ} (a : Radius n r) :
    (largerRadius a : ℝ) < 1 := (largerRadius a).property.2.1

@[simp] theorem largerRadius_pow_lt {n : ℕ} {r : ℝ} (a : Radius n r) :
    (largerRadius a : ℝ) ^ n < r := (largerRadius a).property.2.2

/-- The exact outer cutoff, with squared-radius argument `σ`. -/
def outerRadialCutoff (a b σ : ℝ) : ℝ :=
  Real.smoothTransition ((b ^ 2 - σ) / ((b ^ 2 - a ^ 2) / 2))

/-- Each fixed pair of radii gives a genuinely smooth real function. -/
theorem outerRadialCutoff_contDiff (a b : ℝ) :
    ContDiff ℝ ∞ (outerRadialCutoff a b) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const ((b ^ 2 - a ^ 2) / 2))

theorem outerRadialCutoff_nonneg (a b σ : ℝ) : 0 ≤ outerRadialCutoff a b σ :=
  Real.smoothTransition.nonneg _

theorem outerRadialCutoff_le_one (a b σ : ℝ) : outerRadialCutoff a b σ ≤ 1 :=
  Real.smoothTransition.le_one _

theorem outerRadialCutoff_mem_Icc (a b σ : ℝ) :
    outerRadialCutoff a b σ ∈ Icc (0 : ℝ) 1 :=
  ⟨outerRadialCutoff_nonneg a b σ, outerRadialCutoff_le_one a b σ⟩

private theorem outerRadialCutoff_den_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < (b ^ 2 - a ^ 2) / 2 :=
  div_pos (sub_pos.mpr ((sq_lt_sq₀ ha (ha.trans hab.le)).mpr hab)) (by norm_num)

/-- The whole inner side, including the explicit plateau, is unchanged. -/
theorem outerRadialCutoff_eq_one {a b σ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hσ : σ ≤ (a ^ 2 + b ^ 2) / 2) : outerRadialCutoff a b σ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (one_le_div (outerRadialCutoff_den_pos ha hab)).mpr (by linarith)

/-- The outer boundary and every point beyond it have zero cutoff. -/
theorem outerRadialCutoff_eq_zero_of_ge {a b σ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hσ : b ^ 2 ≤ σ) : outerRadialCutoff a b σ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hσ)
    (outerRadialCutoff_den_pos ha hab).le

/-- In particular, the cutoff equals one on the original boundary radius. -/
theorem outerRadialCutoff_at_radius_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    outerRadialCutoff a b (a ^ 2) = 1 := by
  have hs : a ^ 2 < b ^ 2 := (sq_lt_sq₀ ha (ha.trans hab.le)).mpr hab
  exact outerRadialCutoff_eq_one ha hab (by linarith)

/-- The equality to one holds on an actual neighborhood, not just one radius. -/
theorem outerRadialCutoff_eventually_eq_one {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ σ in 𝓝 (a ^ 2), outerRadialCutoff a b σ = 1 := by
  have hs : a ^ 2 < b ^ 2 := (sq_lt_sq₀ ha (ha.trans hab.le)).mpr hab
  have hm : a ^ 2 < (a ^ 2 + b ^ 2) / 2 := by linarith
  filter_upwards [Iio_mem_nhds hm] with σ hσ
  exact outerRadialCutoff_eq_one ha hab hσ.le

theorem outerRadialCutoff_support_subset {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Function.support (outerRadialCutoff a b) ⊆ Iio (b ^ 2) := by
  intro σ hσ
  change outerRadialCutoff a b σ ≠ 0 at hσ
  exact lt_of_not_ge (fun h => hσ (outerRadialCutoff_eq_zero_of_ge ha hab h))

/-- Taking closed support still stays within the strictly admissible outer radius. -/
theorem outerRadialCutoff_tsupport_subset {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    tsupport (outerRadialCutoff a b) ⊆ Iic (b ^ 2) := by
  exact closure_minimal
    ((outerRadialCutoff_support_subset ha hab).trans Iio_subset_Iic_self) isClosed_Iic

/-- The chosen admissible outer radius gives the required value on the native boundary. -/
theorem outerRadialCutoff_largerRadius_at_radius_sq {n : ℕ} {r : ℝ} (a : Radius n r) :
    outerRadialCutoff (a : ℝ) (largerRadius a : ℝ) ((a : ℝ) ^ 2) = 1 :=
  outerRadialCutoff_at_radius_sq a.property.1.le (lt_largerRadius a)

/-- The equality to one persists near that exact original boundary radius. -/
theorem outerRadialCutoff_largerRadius_eventually_eq_one {n : ℕ} {r : ℝ}
    (a : Radius n r) :
    ∀ᶠ σ in 𝓝 ((a : ℝ) ^ 2), outerRadialCutoff (a : ℝ) (largerRadius a : ℝ) σ = 1 :=
  outerRadialCutoff_eventually_eq_one a.property.1.le (lt_largerRadius a)

/-- Outside the original small filling's power-radius bound, the outer cutoff
already vanishes.  This holds for every nonnegative root radius `u`. -/
theorem outerRadialCutoff_largerRadius_eq_zero_of_radius_le_pow {n : ℕ} {r : ℝ}
    (a : Radius n r) {u : ℝ} (hu : 0 ≤ u) (hru : r ≤ u ^ n) :
    outerRadialCutoff (a : ℝ) (largerRadius a : ℝ) (u ^ 2) = 0 := by
  have hbu : (largerRadius a : ℝ) < u :=
    lt_of_pow_lt_pow_left₀ n hu ((largerRadius_pow_lt a).trans_le hru)
  exact outerRadialCutoff_eq_zero_of_ge a.property.1.le (lt_largerRadius a)
    ((sq_le_sq₀ (largerRadius_pos a).le hu).mpr hbu.le)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
