import Wikipedia.NoExoticSixSphere.OpenFiberCollapse
import Mathlib.Topology.Homotopy.Basic

/-!
# Based collapse homotopies from fiber-coordinate changes

A continuously varying family of fiber homeomorphisms, with jointly
continuous inverses, gives an open tube over the parameter space. Compactness
of the parameter and base then proves continuity of its collapse, including
at infinity. Every time slice is exactly the collapse of the changed tube.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval

namespace NoExoticSixSphere.OpenFiberCollapse

variable {B M K T Y : Type*} [TopologicalSpace B] [TopologicalSpace M]
  [TopologicalSpace K] [TopologicalSpace T] [TopologicalSpace Y]

def fiberCoordinates (L : B → K ≃ₜ K)
    (hc : Continuous (fun p : B × K ↦ L p.1 p.2))
    (hi : Continuous (fun p : B × K ↦ (L p.1).symm p.2)) : B × K ≃ₜ B × K where
  toFun p := (p.1, L p.1 p.2)
  invFun p := (p.1, (L p.1).symm p.2)
  left_inv p := Prod.ext rfl ((L p.1).symm_apply_apply p.2)
  right_inv p := Prod.ext rfl ((L p.1).apply_symm_apply p.2)
  continuous_toFun := continuous_fst.prodMk hc
  continuous_invFun := continuous_fst.prodMk hi

variable (τ : M × K → Y) (L : T × M → K ≃ₜ K)

def coordinateTube (t : T) (p : M × K) : Y := τ (p.1, L (t, p.1) p.2)

def parameterTube (p : (T × M) × K) : T × Y :=
  (p.1.1, τ (p.1.2, L p.1 p.2))

omit [TopologicalSpace M] [TopologicalSpace T] [TopologicalSpace Y] in
theorem injective_coordinateTube (hτ : Injective τ) (t : T) :
    Injective (coordinateTube τ L t) := by
  intro p q h
  have h' := hτ h
  have hm := congrArg (fun z : M × K ↦ z.1) h'
  have hk := congrArg (fun z : M × K ↦ z.2) h'
  change p.1 = q.1 at hm
  change L (t, p.1) p.2 = L (t, q.1) q.2 at hk
  rw [hm] at hk
  exact Prod.ext hm ((L (t, q.1)).injective hk)

theorem injective_parameterTube (hτ : Injective τ) : Injective (parameterTube τ L) := by
  rintro ⟨⟨t, m⟩, k⟩ ⟨⟨s, n⟩, l⟩ h
  have ht : t = s := congrArg Prod.fst h
  subst s
  have hmk : (m, k) = (n, l) :=
    injective_coordinateTube τ L hτ t (congrArg Prod.snd h)
  cases hmk
  rfl

theorem isOpenEmbedding_parameterTube (hτ : IsOpenEmbedding τ)
    (hc : Continuous (fun p : (T × M) × K ↦ L p.1 p.2))
    (hi : Continuous (fun p : (T × M) × K ↦ (L p.1).symm p.2)) :
    IsOpenEmbedding (parameterTube τ L) :=
  ((Homeomorph.refl T).isOpenEmbedding.prodMap hτ).comp
    ((Homeomorph.prodAssoc T M K).isOpenEmbedding.comp
      (fiberCoordinates L hc hi).isOpenEmbedding)

theorem isOpenEmbedding_coordinateTube (hτ : IsOpenEmbedding τ)
    (hc : Continuous (fun p : (T × M) × K ↦ L p.1 p.2))
    (hi : Continuous (fun p : (T × M) × K ↦ (L p.1).symm p.2)) (t : T) :
    IsOpenEmbedding (coordinateTube τ L t) := by
  have hj : Continuous (fun p : M × K ↦ ((t, p.1), p.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  exact hτ.comp (fiberCoordinates (fun m ↦ L (t, m)) (hc.comp hj) (hi.comp hj)).isOpenEmbedding

theorem collapse_parameterTube (hτ : Injective τ) (t : T) (y : Y) :
    collapse (parameterTube τ L) (t, y) = collapse (coordinateTube τ L t) y := by
  by_cases hy : y ∈ range (coordinateTube τ L t)
  · obtain ⟨⟨m, k⟩, rfl⟩ := hy
    change collapse (parameterTube τ L) (parameterTube τ L ((t, m), k)) = _
    rw [collapse_apply _ (injective_parameterTube τ L hτ),
      collapse_apply _ (injective_coordinateTube τ L hτ t)]
  · have hty : (t, y) ∉ range (parameterTube τ L) := by
      rintro ⟨⟨⟨s, m⟩, k⟩, h⟩
      have ht : s = t := congrArg Prod.fst h
      subst s
      exact hy ⟨(m, k), congrArg Prod.snd h⟩
    rw [collapse_of_not_mem _ hty, collapse_of_not_mem _ hy]

section Compact

variable [CompactSpace T] [T2Space T] [CompactSpace M] [T2Space Y] [LocallyCompactSpace Y]
  (hτ : IsOpenEmbedding τ)
  (hc : Continuous (fun p : (T × M) × K ↦ L p.1 p.2))
  (hi : Continuous (fun p : (T × M) × K ↦ (L p.1).symm p.2))

def coordinateCollapseFamily : C(T × OnePoint Y, OnePoint K) :=
  ⟨collapse (parameterTube (fun p ↦ (τ p : OnePoint Y)) L),
    continuous_collapse _ (isOpenEmbedding_parameterTube _ L
      (OnePoint.isOpenEmbedding_coe.comp hτ) hc hi)⟩

theorem coordinateCollapseFamily_apply (t : T) (y : OnePoint Y) :
    coordinateCollapseFamily τ L hτ hc hi (t, y) =
      collapseOnePoint (coordinateTube τ L t) y :=
  collapse_parameterTube (fun p ↦ (τ p : OnePoint Y)) L
    (OnePoint.coe_injective.comp hτ.injective) t y

theorem coordinateCollapseFamily_infty (t : T) :
    coordinateCollapseFamily τ L hτ hc hi (t, OnePoint.infty) = OnePoint.infty := by
  rw [coordinateCollapseFamily_apply, collapseOnePoint_infty]

def coordinateCollapseMap (t : T) : C(OnePoint Y, OnePoint K) :=
  (coordinateCollapseFamily τ L hτ hc hi).comp
    ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _))

end Compact

variable [CompactSpace M] [T2Space Y] [LocallyCompactSpace Y]
  (L : I × M → K ≃ₜ K) (hτ : IsOpenEmbedding τ)
  (hc : Continuous (fun p : (I × M) × K ↦ L p.1 p.2))
  (hi : Continuous (fun p : (I × M) × K ↦ (L p.1).symm p.2))

def coordinateCollapseHomotopy :
    (coordinateCollapseMap τ L hτ hc hi 0).Homotopy (coordinateCollapseMap τ L hτ hc hi 1) where
  toContinuousMap := coordinateCollapseFamily τ L hτ hc hi
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem coordinateCollapseHomotopy_infty (t : I) :
    coordinateCollapseHomotopy τ L hτ hc hi (t, OnePoint.infty) = OnePoint.infty :=
  coordinateCollapseFamily_infty τ L hτ hc hi t

end NoExoticSixSphere.OpenFiberCollapse
