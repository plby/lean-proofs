import Wikipedia.NoExoticSixSphere.CylinderFiberSlab

/-!
# The interior-time part of a bounded cylinder fiber

The strict-time part of the slab is the same open subspace as the strict-time
part of the full cylinder fiber. This identification retains the ambient
point and the original subtype topologies.
-/

open Set TopologicalSpace

namespace NoExoticSixSphere.CylinderFiberSlab

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (b : N) (s t : ℝ)

def interiorDomain : Opens (slab F b s t) := timeDomain F b s t ⟨Ioo s t, isOpen_Ioo⟩

def fiberInterior : Opens {p : ℝ × M // F p = b} :=
  CylinderFiberProduct.timeDomain F b ⟨Ioo s t, isOpen_Ioo⟩

noncomputable def interiorHomeomorph : interiorDomain F b s t ≃ₜ fiberInterior F b s t where
  toFun p := ⟨p.val.val, p.property⟩
  invFun p := ⟨⟨p.val, ⟨p.property.1.le, p.property.2.le⟩⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun p : interiorDomain F b s t ↦ p.val.val) :=
      (continuous_subtype_val : Continuous
        (Subtype.val : slab F b s t → {p : ℝ × M // F p = b})).comp continuous_subtype_val
    exact h.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun p : fiberInterior F b s t ↦ p.val) := continuous_subtype_val
    exact (h.subtype_mk _).subtype_mk _

theorem interiorHomeomorph_val (p : interiorDomain F b s t) :
    (interiorHomeomorph F b s t p).val.val = p.val.val.val := rfl

end NoExoticSixSphere.CylinderFiberSlab
