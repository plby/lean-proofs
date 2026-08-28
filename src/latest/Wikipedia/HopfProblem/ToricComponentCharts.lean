import Wikipedia.HopfProblem.ToricDivisors
import Mathlib.Topology.LocalAtTarget

/-!
# Coordinate charts on the central ray components

Inserting a zero coordinate identifies complex two-space with the affine
part of a ray component. These maps are open embeddings for the actual
subspace topology. Their transition functions are restrictions of the
already proved holomorphic toric coordinate changes.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

def insertZero (j : Fin 3) (z : CoordinateSpace 2) : CoordinateSpace 3 := Fin.insertNth j 0 z

def removeCoordinate (j : Fin 3) (z : CoordinateSpace 3) : CoordinateSpace 2 := Fin.removeNth j z

@[simp] theorem insertZero_at (j : Fin 3) (z : CoordinateSpace 2) : insertZero j z j = 0 :=
  Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℂ) j 0 z

@[simp] theorem removeCoordinate_insertZero (j : Fin 3) (z : CoordinateSpace 2) :
    removeCoordinate j (insertZero j z) = z :=
  Fin.removeNth_insertNth (α := fun _ : Fin 3 => ℂ) j 0 z

theorem insertZero_removeCoordinate (j : Fin 3) (z : CoordinateSpace 3) (hz : z j = 0) :
    insertZero j (removeCoordinate j z) = z :=
  Fin.insertNth_eq_iff.mpr ⟨hz.symm, rfl⟩

theorem insertZero_holomorphic (j : Fin 3) : ContDiff ℂ ω (insertZero j) := by
  apply contDiff_pi.mpr
  intro k
  obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simpa only [insertZero_at] using
      (contDiff_const : ContDiff ℂ ω (fun _ : CoordinateSpace 2 => (0 : ℂ)))
  · simpa only [insertZero, Fin.insertNth_apply_succAbove] using (contDiff_apply ℂ ℂ l)

theorem removeCoordinate_holomorphic (j : Fin 3) : ContDiff ℂ ω (removeCoordinate j) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_apply ℂ ℂ (j.succAbove i)

/-- An affine toric chart together with the coordinate belonging to the given ray. -/
structure ChartIndex (v : Fin 2 → ℤ) where
  triangle : Triangle
  coordinate : Fin 3
  vertex_eq : triangle.vertex coordinate = v

variable {v : Fin 2 → ℤ}

theorem insertZero_mem (c : ChartIndex v) (z : CoordinateSpace 2) :
    inclusion c.triangle (insertZero c.coordinate z) ∈ rayDivisor v := by
  have h := (mem_rayDivisor_vertex c.triangle c.coordinate
    (insertZero c.coordinate z)).mpr (insertZero_at c.coordinate z)
  simpa only [c.vertex_eq] using h

def planeHomeomorph (c : ChartIndex v) :
    CoordinateSpace 2 ≃ₜ inclusion c.triangle ⁻¹' rayDivisor v := by
  refine
    { toFun := fun z => ⟨insertZero c.coordinate z, insertZero_mem c z⟩
      invFun := fun w => removeCoordinate c.coordinate w
      left_inv := fun z => removeCoordinate_insertZero c.coordinate z
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro w
    apply Subtype.ext
    apply insertZero_removeCoordinate
    have hw : inclusion c.triangle (w : CoordinateSpace 3) ∈ rayDivisor v := w.2
    exact (mem_rayDivisor_vertex c.triangle c.coordinate w).mp
      (by simpa only [c.vertex_eq] using hw)
  · exact (insertZero_holomorphic c.coordinate).continuous.subtype_mk _
  · exact (removeCoordinate_holomorphic c.coordinate).continuous.comp continuous_subtype_val

def affineInclusion (c : ChartIndex v) (z : CoordinateSpace 2) : rayDivisor v :=
  ⟨inclusion c.triangle (insertZero c.coordinate z), insertZero_mem c z⟩

theorem affineInclusion_openEmbedding (c : ChartIndex v) : IsOpenEmbedding (affineInclusion c) :=
  ((inclusion_openEmbedding c.triangle).restrictPreimage (rayDivisor v)).comp
    (planeHomeomorph c).isOpenEmbedding

theorem affineInclusion_jointly_surjective (x : rayDivisor v) :
    ∃ c : ChartIndex v, ∃ z : CoordinateSpace 2, affineInclusion c z = x := by
  obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (x : Space)
  have hx : inclusion s z ∈ rayDivisor v := by rw [hz]; exact x.2
  obtain ⟨j, hj, hv⟩ := (mem_rayDivisor_inclusion v s z).mp hx
  refine ⟨⟨s, j, hv⟩, removeCoordinate j z, ?_⟩
  apply Subtype.ext
  change inclusion s (insertZero j (removeCoordinate j z)) = (x : Space)
  rw [insertZero_removeCoordinate j z hj]
  exact hz

def parametrization (c : ChartIndex v) : OpenPartialHomeomorph (CoordinateSpace 2) (rayDivisor v) :=
  (affineInclusion_openEmbedding c).toOpenPartialHomeomorph (affineInclusion c)

@[simp] theorem parametrization_apply (c : ChartIndex v) (z : CoordinateSpace 2) :
    parametrization c z = affineInclusion c z := rfl

@[simp] theorem parametrization_source (c : ChartIndex v) : (parametrization c).source = univ := rfl

@[simp] theorem parametrization_target (c : ChartIndex v) :
    (parametrization c).target = range (affineInclusion c) := by simp [parametrization]

theorem parametrization_transition (c d : ChartIndex v) {z : CoordinateSpace 2}
    (hz : affineInclusion c z ∈ range (affineInclusion d)) :
    insertZero c.coordinate z ∈ (chartChange c.triangle d.triangle).source ∧
      (parametrization d).symm (affineInclusion c z) =
        removeCoordinate d.coordinate
          (chartChange c.triangle d.triangle (insertZero c.coordinate z)) := by
  obtain ⟨w, hw⟩ := hz
  have he := (inclusion_eq_iff c.triangle d.triangle
    (insertZero c.coordinate z) (insertZero d.coordinate w)).mp (congrArg Subtype.val hw).symm
  refine ⟨he.1, ?_⟩
  rw [← hw, he.2, removeCoordinate_insertZero]
  exact (parametrization d).left_inv (Set.mem_univ w)

theorem transition_holomorphic (c d : ChartIndex v) :
    ContDiffOn ℂ ω ((parametrization c).trans (parametrization d).symm)
      ((parametrization c).trans (parametrization d).symm).source := by
  let U := ((parametrization c).trans (parametrization d).symm).source
  have h (z : CoordinateSpace 2) (hz : z ∈ U) :=
    parametrization_transition c d (by simpa using hz.2)
  have hi : ContDiffOn ℂ ω (insertZero c.coordinate) U :=
    (insertZero_holomorphic c.coordinate).contDiffOn
  have ht := (chartChange_holomorphic c.triangle d.triangle).comp hi (fun z hz => (h z hz).1)
  have hr := (removeCoordinate_holomorphic d.coordinate).comp_contDiffOn ht
  exact hr.congr (fun z hz => (h z hz).2)

end Wikipedia.HopfProblem.ToricComponent
