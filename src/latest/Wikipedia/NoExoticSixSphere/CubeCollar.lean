import Wikipedia.NoExoticSixSphere.CylinderTime
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Constant collars for generalized loops

Apply the existing interval collar in every cube coordinate. A generalized
loop becomes constant on an open neighborhood of the entire cube boundary.
The interpolation is a homotopy relative to every boundary face.
-/

open Set unitInterval

namespace NoExoticSixSphere.CubeCollar

variable (N : Type*)

def region : Set (N → I) :=
  {x | ∃ i, (x i : ℝ) < 1 / 3 ∨ 2 / 3 < (x i : ℝ)}

theorem isOpen_region : IsOpen (region N) := by
  have he : region N = ⋃ i : N, {x : N → I | (x i : ℝ) < 1 / 3 ∨ 2 / 3 < (x i : ℝ)} := by
    ext x
    simp only [region, mem_ofPred_eq, mem_iUnion]
  rw [he]
  apply isOpen_iUnion
  intro i
  have hc : Continuous (fun x : N → I ↦ (x i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact (isOpen_lt hc continuous_const).union (isOpen_lt continuous_const hc)

theorem isClosed_boundary [Finite N] : IsClosed (Cube.boundary N) := by
  have he : Cube.boundary N = ⋃ i : N, {x : N → I | x i = 0 ∨ x i = 1} := by
    ext x
    simp only [Cube.boundary, mem_ofPred_eq, mem_iUnion]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro i
  exact (isClosed_eq (continuous_apply i) continuous_const).union
    (isClosed_eq (continuous_apply i) continuous_const)

theorem boundary_subset_region : Cube.boundary N ⊆ region N := by
  rintro x ⟨i, hi | hi⟩
  · exact ⟨i, Or.inl (by rw [hi]; norm_num)⟩
  · exact ⟨i, Or.inr (by rw [hi]; norm_num)⟩

noncomputable def map : C((N → I), (N → I)) where
  toFun x i := CylinderTime.collar (x i : ℝ)
  continuous_toFun := continuous_pi (fun i ↦ CylinderTime.continuous_collar.comp
    (continuous_subtype_val.comp (continuous_apply i)))

theorem map_mem_boundary {x : N → I} (hx : x ∈ region N) : map N x ∈ Cube.boundary N := by
  rcases hx with ⟨i, hi | hi⟩
  · exact ⟨i, Or.inl (CylinderTime.collar_left hi.le)⟩
  · exact ⟨i, Or.inr (CylinderTime.collar_right hi.le)⟩

noncomputable def blend : C(I × (N → I), (N → I)) where
  toFun p i := CylinderTime.blend p.1 (p.2 i)
  continuous_toFun := continuous_pi (fun i ↦ CylinderTime.continuous_blend.comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))

theorem blend_zero (x : N → I) : blend N (0, x) = x := by
  funext i
  exact CylinderTime.blend_zero (x i)

theorem blend_one (x : N → I) : blend N (1, x) = map N x := by
  funext i
  exact CylinderTime.blend_one (x i)

theorem blend_mem_boundary (t : I) {x : N → I} (hx : x ∈ Cube.boundary N) :
    blend N (t, x) ∈ Cube.boundary N := by
  rcases hx with ⟨i, hi | hi⟩
  · refine ⟨i, Or.inl ?_⟩
    change CylinderTime.blend t (x i) = 0
    rw [hi, CylinderTime.blend_left]
  · refine ⟨i, Or.inr ?_⟩
    change CylinderTime.blend t (x i) = 1
    rw [hi, CylinderTime.blend_right]

variable {N} {X : Type*} [TopologicalSpace X] {b : X}

noncomputable def genLoop (p : GenLoop N X b) : GenLoop N X b :=
  ⟨p.1.comp (map N), fun _x hx ↦ p.2 _ (map_mem_boundary N (boundary_subset_region N hx))⟩

theorem genLoop_eq_base (p : GenLoop N X b) {x : N → I} (hx : x ∈ region N) :
    genLoop p x = b := p.2 _ (map_mem_boundary N hx)

noncomputable def homotopy (p : GenLoop N X b) :
    p.1.HomotopyRel (genLoop p).1 (Cube.boundary N) where
  toFun z := p (blend N z)
  continuous_toFun := p.1.continuous.comp (blend N).continuous
  map_zero_left x := by change p (blend N (0, x)) = p x; rw [blend_zero]
  map_one_left x := by change p (blend N (1, x)) = p (map N x); rw [blend_one]
  prop' t x hx := (p.2 _ (blend_mem_boundary N t hx)).trans (p.2 x hx).symm

end NoExoticSixSphere.CubeCollar
