import Wikipedia.NoExoticSixSphere.CylinderFiberProduct
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Bounded slabs and their actual endpoint product neighborhoods

Intersect a cylinder fiber with a closed time interval. If the original map
is constant in time on an open set, the corresponding open piece of this
slab is homeomorphic to the restricted closed time interval times the
endpoint fiber. This includes the one-sided endpoints, not just interior time.
-/

open Set Topology TopologicalSpace

namespace NoExoticSixSphere.CylinderFiberSlab

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (b : N) (s t : ℝ)

abbrev slab := {p : {p : ℝ × M // F p = b} // p.val.1 ∈ Icc s t}

theorem compactSpace [CompactSpace M] [T2Space N] : CompactSpace (slab F b s t) := by
  have hclosed : IsClosed {p | F p = b} := isClosed_eq F.continuous continuous_const
  have he := Topology.IsClosedEmbedding.subtypeVal hclosed
  have hc := (isCompact_Icc : IsCompact (Icc s t)).prod
    (isCompact_univ : IsCompact (univ : Set M))
  have hs : IsCompact {p : {p : ℝ × M // F p = b} | p.val.1 ∈ Icc s t} := by
    convert he.isCompact_preimage hc using 1
    ext p
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, and_true]
  exact isCompact_iff_compactSpace.mp hs

def timeDomain (U : Opens ℝ) : Opens (slab F b s t) :=
  ⟨{p | p.val.val.1 ∈ U}, U.isOpen.preimage
    (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))⟩

def timeSlice (U : Opens ℝ) : Opens (Icc s t) :=
  ⟨{r | r.val ∈ U}, U.isOpen.preimage continuous_subtype_val⟩

variable (f : C(M, N)) (U : Opens ℝ)
  (hconstant : ∀ r ∈ U, ∀ x, F (r, x) = f x)

noncomputable def homeomorph :
    timeDomain F b s t U ≃ₜ timeSlice s t U × {x : M // f x = b} where
  toFun p := (⟨⟨p.val.val.val.1, p.val.property⟩, p.property⟩,
    ⟨p.val.val.val.2, (hconstant _ p.property _).symm.trans p.val.val.property⟩)
  invFun p := ⟨⟨⟨(p.1.val.val, p.2.val),
      (hconstant _ p.1.property _).trans p.2.property⟩, p.1.val.property⟩, p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun p : timeDomain F b s t U ↦ p.val.val.val) :=
      (continuous_subtype_val : Continuous
        (Subtype.val : {p : ℝ × M // F p = b} → ℝ × M)).comp
          (continuous_subtype_val.comp continuous_subtype_val)
    exact ((h.fst.subtype_mk _).subtype_mk _).prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have htime : Continuous (fun p : timeSlice s t U × {x : M // f x = b} ↦
        p.1.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have h : Continuous (fun p : timeSlice s t U × {x : M // f x = b} ↦
        (p.1.val.val, p.2.val)) :=
      htime.prodMk (continuous_subtype_val.comp continuous_snd)
    exact ((h.subtype_mk _).subtype_mk _).subtype_mk _

theorem homeomorph_time (p : timeDomain F b s t U) :
    (homeomorph F b s t f U hconstant p).1.val.val = p.val.val.val.1 := rfl

theorem homeomorph_symm_val (p : timeSlice s t U × {x : M // f x = b}) :
    ((homeomorph F b s t f U hconstant).symm p).val.val.val = (p.1.val.val, p.2.val) := rfl

end NoExoticSixSphere.CylinderFiberSlab
