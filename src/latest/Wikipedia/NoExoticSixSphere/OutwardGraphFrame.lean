import Wikipedia.NoExoticSixSphere.CollaredDiskRadialOperator
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend

/-!
# Moving an added height-normal column to the actual outward normal

Graph the time differential while retaining the original normal columns.
The new normal column moves from the height axis to the outward vector.
Its complement coefficient is a convex combination of one and the negative
outward time derivative, hence stays positive. Every intermediate normal-
plus-derivative operator is injective. No extension of the outward vector
over the disk or annulus is assumed.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.OutwardGraphFrame

open GLOrthonormalization CollaredDiskFrame

variable {N k : ℕ}

def normal (r : ℝ) (A : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    Vector (k + 1) →L[ℝ] (Vector N × ℝ) :=
  (((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp A).coprod
    (radialColumn (r • ν) (1 - r))).comp EuclideanSpace.finAddEquivProd.toContinuousLinearMap

theorem normal_apply (r : ℝ) (A : Vector k →L[ℝ] Vector N) (ν : Vector N)
    (u : Vector (k + 1)) :
    normal r A ν u =
      (A (EuclideanSpace.finAddEquivProd u).1 +
        EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd u).2 • (r • ν),
        EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd u).2 * (1 - r)) := by
  simp only [normal, radialColumn, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    Prod.smul_mk, Prod.mk_add_mk, zero_add, smul_eq_mul]
  rfl

def graph (D : Vector 4 →L[ℝ] Vector N) (ξ : Vector N →L[ℝ] ℝ) :
    Vector 4 →L[ℝ] (Vector N × ℝ) := D.prod (ξ.comp D)

theorem graph_apply (D : Vector 4 →L[ℝ] Vector N) (ξ : Vector N →L[ℝ] ℝ) (v : Vector 4) :
    graph D ξ v = (D v, ξ (D v)) := rfl

theorem complementCoefficient_pos (r : ℝ) (hr : r ∈ Set.Icc 0 1)
    (ν : Vector N) (ξ : Vector N →L[ℝ] ℝ) (hν : ξ ν < 0) :
    0 < (1 - r) + r * (-ξ ν) := by
  have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (show (0 : ℝ) < 1 by norm_num)
    (neg_pos.mpr hν) (sub_nonneg.mpr hr.2) hr.1 (show (1 - r) + r = 1 by ring)
  simpa only [smul_eq_mul, mul_one, Set.mem_Ioi] using h

theorem coprod_injective_of_coefficient (r : ℝ)
    (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N)
    (ν : Vector N) (ξ : Vector N →L[ℝ] ℝ)
    (hAD : Injective (A.coprod D)) (hA : ∀ u, ξ (A u) = 0)
    (hp : 0 < (1 - r) + r * (-ξ ν)) :
    Injective ((normal r A ν).coprod (graph D ξ)) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨u, v⟩ h
  let w := EuclideanSpace.finAddEquivProd (n := k) (m := 1) u
  let c : ℝ := EuclideanTailCoordinates.scalar.symm w.2
  have he : (A w.1 + c • (r • ν) + D v, c * (1 - r) + ξ (D v)) = (0, 0) := by
    change normal r A ν u + graph D ξ v = 0 at h
    rw [normal_apply, graph_apply] at h
    exact h
  have hs : A w.1 + c • (r • ν) + D v = 0 := congrArg Prod.fst he
  have hh : c * (1 - r) + ξ (D v) = 0 := congrArg Prod.snd he
  have hξ : c * (r * ξ ν) + ξ (D v) = 0 := by
    have h' := congrArg ξ hs
    simpa only [map_add, map_smul, hA, map_zero, zero_add, smul_eq_mul] using h'
  have hpc : ((1 - r) + r * (-ξ ν)) * c = 0 := by nlinarith [hh, hξ]
  have hc : c = 0 := (mul_eq_zero.mp hpc).resolve_left hp.ne'
  have huv : (w.1, v) = (0, 0) := by
    apply hAD
    change A w.1 + D v = A 0 + D 0
    simpa only [hc, zero_smul, add_zero, map_zero] using hs
  have hu₁ : w.1 = 0 := congrArg (fun z : Vector k × Vector 4 ↦ z.1) huv
  have hv₀ : v = 0 := congrArg (fun z : Vector k × Vector 4 ↦ z.2) huv
  have hu : u = 0 := by
    apply (EuclideanSpace.finAddEquivProd (n := k) (m := 1)).injective
    change w = 0
    apply Prod.ext hu₁
    exact EuclideanTailCoordinates.scalar.symm.injective (hc.trans (map_zero _).symm)
  exact Prod.ext hu hv₀

theorem coprod_injective (r : ℝ) (hr : r ∈ Set.Icc 0 1)
    (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N)
    (ν : Vector N) (ξ : Vector N →L[ℝ] ℝ)
    (hAD : Injective (A.coprod D)) (hA : ∀ u, ξ (A u) = 0) (hν : ξ ν < 0) :
    Injective ((normal r A ν).coprod (graph D ξ)) :=
  coprod_injective_of_coefficient r A D ν ξ hAD hA
    (complementCoefficient_pos r hr ν ξ hν)

theorem normal_one (A : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    normal 1 A ν = (ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
      (OrthogonalFrameAppend.operator A ν) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [normal_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    OrthogonalFrameAppend.operator_apply, one_smul, sub_self, mul_zero]

theorem continuous_normal {X : Type*} [TopologicalSpace X]
    (r : X → ℝ) (A : X → Vector k →L[ℝ] Vector N) (ν : X → Vector N)
    (hr : Continuous r) (hA : Continuous A) (hν : Continuous ν) :
    Continuous (fun x ↦ normal (r x) (A x) (ν x)) := by
  apply continuous_clm_apply.mpr
  intro u
  simp only [normal_apply]
  have hc : Continuous (fun _ : X ↦
      EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd u).2) :=
    continuous_const
  exact ((hA.clm_apply continuous_const).add
    (hc.smul (hr.smul hν))).prodMk (hc.mul (continuous_const.sub hr))

theorem continuous_graph {X : Type*} [TopologicalSpace X]
    (D : X → Vector 4 →L[ℝ] Vector N) (ξ : X → Vector N →L[ℝ] ℝ)
    (hD : Continuous D) (hξ : Continuous ξ) : Continuous (fun x ↦ graph (D x) (ξ x)) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (hD.clm_apply continuous_const).prodMk
    (hξ.clm_apply (hD.clm_apply continuous_const))

end NoExoticSixSphere.OutwardGraphFrame
