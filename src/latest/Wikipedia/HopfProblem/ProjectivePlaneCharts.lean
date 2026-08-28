import Wikipedia.HopfProblem.ProjectivePlane
import Wikipedia.HopfProblem.ToricCharts
import Mathlib.Topology.ContinuousOn
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.StdBasis

/-!
# The three affine charts of the complex projective plane

The chart conventions are cyclic: `[1:u:v]`, `[v:1:u]`, and `[u:v:1]`.
All parametrizations and coordinate changes refer to the genuine scalar
quotient of nonzero homogeneous vectors.  The open-chart topology is
proved from that quotient topology.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ProjectivePlane

open ToricCharts

/-- The cyclic homogeneous parametrizations `[1:u:v]`, `[v:1:u]`, `[u:v:1]`. -/
def homogeneous (k : Fin 3) (z : CoordinateSpace 2) : Homogeneous :=
  ![![1, z 0, z 1], ![z 1, 1, z 0], ![z 0, z 1, 1]] k

@[simp] theorem homogeneous_pivot (k : Fin 3) (z : CoordinateSpace 2) :
    homogeneous k z k = 1 := by fin_cases k <;> rfl

@[simp] theorem homogeneous_next (k : Fin 3) (z : CoordinateSpace 2) :
    homogeneous k z (k + 1) = z 0 := by fin_cases k <;> rfl

@[simp] theorem homogeneous_last (k : Fin 3) (z : CoordinateSpace 2) :
    homogeneous k z (k + 2) = z 1 := by fin_cases k <;> rfl

theorem homogeneous_ne_zero (k : Fin 3) (z : CoordinateSpace 2) :
    homogeneous k z ≠ 0 := by
  intro h
  have hk := congrFun h k
  simp at hk

def affineMap (k : Fin 3) (z : CoordinateSpace 2) : Space :=
  quotientMap ⟨homogeneous k z, homogeneous_ne_zero k z⟩

/-- The two affine ratios relative to the `k`th homogeneous coordinate. -/
def ratios (k : Fin 3) (v : Homogeneous) : CoordinateSpace 2 :=
  ![v (k + 1) / v k, v (k + 2) / v k]

theorem ratios_smul (k : Fin 3) {a : ℂ} (ha : a ≠ 0) (v : Homogeneous) :
    ratios k (a • v) = ratios k v := by
  ext i
  fin_cases i <;> simp [ratios, mul_div_mul_left _ _ ha]

def affineCoords (k : Fin 3) : Space → CoordinateSpace 2 :=
  Projectivization.lift (fun v : NonzeroVector => ratios k v.1) (by
    intro v w a h
    have ha : a ≠ 0 := by
      intro ha
      apply v.2
      simpa [ha] using h
    rw [h]
    exact ratios_smul k ha w.1)

@[simp] theorem affineCoords_quotientMap (k : Fin 3) (v : NonzeroVector) :
    affineCoords k (quotientMap v) = ratios k v.1 := rfl

@[simp] theorem affineCoords_affineMap (k : Fin 3) (z : CoordinateSpace 2) :
    affineCoords k (affineMap k z) = z := by
  change ratios k (homogeneous k z) = z
  simp only [ratios, homogeneous_next, homogeneous_last, homogeneous_pivot, div_one]
  ext i
  fin_cases i <;> rfl

theorem affineMap_injective (k : Fin 3) : Function.Injective (affineMap k) := by
  intro z w h
  have he := congrArg (affineCoords k) h
  simpa using he

/-- The standard projective open subset where the `k`th coordinate is nonzero. -/
def affineTarget (k : Fin 3) : Set Space :=
  quotientMap '' {v : NonzeroVector | v.1 k ≠ 0}

theorem quotientMap_mem_affineTarget_iff (k : Fin 3) (v : NonzeroVector) :
    quotientMap v ∈ affineTarget k ↔ v.1 k ≠ 0 := by
  constructor
  · rintro ⟨w, hw, he⟩ hv
    obtain ⟨a, ha⟩ := (quotientMap_eq_iff w v).mp he
    apply hw
    rw [← ha]
    simp [hv]
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem quotientMap_preimage_affineTarget (k : Fin 3) :
    quotientMap ⁻¹' affineTarget k = {v : NonzeroVector | v.1 k ≠ 0} := by
  ext v
  exact quotientMap_mem_affineTarget_iff k v

theorem affineTarget_isOpen (k : Fin 3) : IsOpen (affineTarget k) := by
  rw [← quotientMap_isQuotientMap.isOpen_preimage, quotientMap_preimage_affineTarget]
  exact isOpen_ne_fun ((continuous_apply k).comp continuous_subtype_val) continuous_const

theorem affineMap_mem_target (k : Fin 3) (z : CoordinateSpace 2) :
    affineMap k z ∈ affineTarget k := by
  apply (quotientMap_mem_affineTarget_iff k _).mpr
  simp

theorem homogeneous_ratios (k : Fin 3) (v : Homogeneous) (hv : v k ≠ 0) :
    homogeneous k (ratios k v) = (v k)⁻¹ • v := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp_all [homogeneous, ratios, div_eq_mul_inv, mul_comm]
  ring

theorem affineMap_affineCoords (k : Fin 3) (x : Space) (hx : x ∈ affineTarget k) :
    affineMap k (affineCoords k x) = x := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [affineCoords_quotientMap]
  apply (quotientMap_eq_iff_scalar _ v).mpr
  exact ⟨(v.1 k)⁻¹, (homogeneous_ratios k v.1 hv).symm⟩

theorem affineMap_range (k : Fin 3) : range (affineMap k) = affineTarget k := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact affineMap_mem_target k z
  · intro hx
    exact ⟨affineCoords k x, affineMap_affineCoords k x hx⟩

theorem affineMap_jointly_surjective (x : Space) :
    ∃ k : Fin 3, ∃ z : CoordinateSpace 2, affineMap k z = x := by
  obtain ⟨v, rfl⟩ := quotientMap_surjective x
  have hex : ∃ k, v.1 k ≠ 0 := by
    by_contra h
    push Not at h
    exact v.2 (funext h)
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, affineCoords k (quotientMap v),
    affineMap_affineCoords k _ ((quotientMap_mem_affineTarget_iff k v).mpr hk)⟩

theorem affineTarget_cover : (⋃ k : Fin 3, affineTarget k) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨k, z, rfl⟩ := affineMap_jointly_surjective x
  exact ⟨k, affineMap_mem_target k z⟩

theorem homogeneous_continuous (k : Fin 3) : Continuous (homogeneous k) := by
  fin_cases k
  · change Continuous (fun z : CoordinateSpace 2 => ![1, z 0, z 1])
    fun_prop
  · change Continuous (fun z : CoordinateSpace 2 => ![z 1, 1, z 0])
    fun_prop
  · change Continuous (fun z : CoordinateSpace 2 => ![z 0, z 1, 1])
    fun_prop

theorem affineMap_continuous (k : Fin 3) : Continuous (affineMap k) :=
  quotientMap_continuous.comp ((homogeneous_continuous k).subtype_mk _)

theorem affineCoords_continuousOn (k : Fin 3) :
    ContinuousOn (affineCoords k) (affineTarget k) := by
  rw [quotientMap_isQuotientMap.continuousOn_isOpen_iff (affineTarget_isOpen k),
    quotientMap_preimage_affineTarget]
  change ContinuousOn (fun v : NonzeroVector => ratios k v.1) _
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact (((continuous_apply (k + 1)).comp continuous_subtype_val).continuousOn.div
      ((continuous_apply k).comp continuous_subtype_val).continuousOn (fun v hv => hv))
  · exact (((continuous_apply (k + 2)).comp continuous_subtype_val).continuousOn.div
      ((continuous_apply k).comp continuous_subtype_val).continuousOn (fun v hv => hv))

/-- Each affine patch is an open partial homeomorphism for the actual
scalar-quotient topology. -/
def parametrization (k : Fin 3) : OpenPartialHomeomorph (CoordinateSpace 2) Space where
  toFun := affineMap k
  invFun := affineCoords k
  source := univ
  target := affineTarget k
  map_source' z _ := affineMap_mem_target k z
  map_target' _ _ := mem_univ _
  left_inv' z _ := affineCoords_affineMap k z
  right_inv' x hx := affineMap_affineCoords k x hx
  open_source := isOpen_univ
  open_target := affineTarget_isOpen k
  continuousOn_toFun := (affineMap_continuous k).continuousOn
  continuousOn_invFun := affineCoords_continuousOn k

@[simp] theorem parametrization_apply (k : Fin 3) (z : CoordinateSpace 2) :
    parametrization k z = affineMap k z := rfl

@[simp] theorem parametrization_source (k : Fin 3) : (parametrization k).source = univ := rfl

@[simp] theorem parametrization_target (k : Fin 3) :
    (parametrization k).target = affineTarget k := rfl

@[simp] theorem parametrization_symm_apply (k : Fin 3) (x : Space) :
    (parametrization k).symm x = affineCoords k x := rfl

theorem affineMap_isOpenEmbedding (k : Fin 3) : IsOpenEmbedding (affineMap k) :=
  (parametrization k).isOpenEmbedding rfl

/-- A single ratio formula for all nine ordered pairs of affine charts. -/
def crossCoordinates (i j : Fin 3) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  ratios j (homogeneous i z)

@[simp] theorem affineCoords_cross (i j : Fin 3) (z : CoordinateSpace 2) :
    affineCoords j (affineMap i z) = crossCoordinates i j z := rfl

theorem affineMap_cross_eq_iff (i j : Fin 3) (z w : CoordinateSpace 2) :
    affineMap i z = affineMap j w ↔
      homogeneous i z j ≠ 0 ∧ w = crossCoordinates i j z := by
  constructor
  · intro h
    have ht : affineMap i z ∈ affineTarget j := h ▸ affineMap_mem_target j w
    refine ⟨(quotientMap_mem_affineTarget_iff j _).mp ht, ?_⟩
    have he := congrArg (affineCoords j) h
    simpa using he.symm
  · rintro ⟨hz, rfl⟩
    exact (affineMap_affineCoords j (affineMap i z)
      ((quotientMap_mem_affineTarget_iff j _).mpr hz)).symm

theorem crossCoordinates_self (i : Fin 3) (z : CoordinateSpace 2) :
    crossCoordinates i i z = z := affineCoords_affineMap i z

theorem crossCoordinates_next (i : Fin 3) (z : CoordinateSpace 2) :
    crossCoordinates i (i + 1) z = ![z 1 / z 0, (z 0)⁻¹] := by
  fin_cases i <;> change ![z 1 / z 0, 1 / z 0] = _ <;> simp

theorem crossCoordinates_last (i : Fin 3) (z : CoordinateSpace 2) :
    crossCoordinates i (i + 2) z = ![(z 1)⁻¹, z 0 / z 1] := by
  fin_cases i <;> change ![1 / z 1, z 0 / z 1] = _ <;> simp

theorem affineMap_next_eq_iff (i : Fin 3) (z w : CoordinateSpace 2) :
    affineMap i z = affineMap (i + 1) w ↔
      z 0 ≠ 0 ∧ w = ![z 1 / z 0, (z 0)⁻¹] := by
  rw [affineMap_cross_eq_iff, homogeneous_next, crossCoordinates_next]

theorem affineMap_last_eq_iff (i : Fin 3) (z w : CoordinateSpace 2) :
    affineMap i z = affineMap (i + 2) w ↔
      z 1 ≠ 0 ∧ w = ![(z 1)⁻¹, z 0 / z 1] := by
  rw [affineMap_cross_eq_iff, homogeneous_last, crossCoordinates_last]

/-- The three coordinate points, the centers of the standard three-point blow-up. -/
def coordinatePoint (k : Fin 3) : Space := affineMap k 0

theorem homogeneous_zero (k : Fin 3) : homogeneous k 0 = Pi.single k 1 := by
  ext i
  fin_cases k <;> fin_cases i <;> simp [homogeneous]

theorem coordinatePoint_mem_target_iff (i j : Fin 3) :
    coordinatePoint i ∈ affineTarget j ↔ i = j := by
  change quotientMap ⟨homogeneous i 0, homogeneous_ne_zero i 0⟩ ∈ affineTarget j ↔ i = j
  rw [quotientMap_mem_affineTarget_iff]
  by_cases h : i = j
  · simp [h]
  · simp [homogeneous_zero, h, Ne.symm h]

theorem coordinatePoint_injective : Function.Injective coordinatePoint := by
  intro i j h
  apply (coordinatePoint_mem_target_iff i j).mp
  rw [h]
  exact affineMap_mem_target j 0

/-- The three blow-up centers are genuinely independent projective points,
so in particular they are non-collinear. -/
theorem coordinatePoint_independent : Projectivization.Independent coordinatePoint := by
  exact Projectivization.Independent.mk (fun k => homogeneous k 0)
    (fun k => homogeneous_ne_zero k 0)
    (by simpa only [homogeneous_zero] using Pi.linearIndependent_single_one (Fin 3) ℂ)

end Wikipedia.HopfProblem.ProjectivePlane
