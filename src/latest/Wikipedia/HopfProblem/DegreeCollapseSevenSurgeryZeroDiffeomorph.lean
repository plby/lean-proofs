import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryRetainedTimeBand
import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# The old and new zero fibers are diffeomorphic in their native atlases

Every new zero lies in the retained old patch. The actual open seam-band
diffeomorphism supplies both smooth directions between the independently
constructed regular-fiber atlases. No atlas is transferred along a bare
equivalence or homeomorphism of the zero sets.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def originalTimeMap : C(M, ℝ) := ⟨T.time, T.smooth.continuous⟩

abbrev OriginalZero := {p : M // T.time p = 0}

@[instance_reducible]
def originalZeroAtlas : ChartedSpace (Vector 6) (OriginalZero A T) :=
  regularFiberAtlas (originalTimeMap A T) T.smooth 0 T.regular 6 (by simp)

theorem originalZero_isManifold : letI := originalZeroAtlas A T;
    IsManifold (𝓡 6) ∞ (OriginalZero A T) :=
  regularFiber_isManifold (originalTimeMap A T) T.smooth 0 T.regular 6 (by simp)

def resultTimeMap : C(Target A hR, ℝ) := by
  let := targetChartedSpace A hR
  exact ⟨timeFunction A hR T, (contMDiff_timeFunction A hR T).continuous⟩

abbrev ResultZero := {p : Target A hR // timeFunction A hR T p = 0}

@[instance_reducible]
def resultZeroAtlas : letI := targetChartedSpace A hR;
    ChartedSpace (Vector 6) (ResultZero A hR T) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  exact regularFiberAtlas (resultTimeMap A hR T) (contMDiff_timeFunction A hR T) 0
    (regular_timeFunction_zero A hR T) 6 (by simp)

theorem resultZero_isManifold : letI := targetChartedSpace A hR;
    letI := resultZeroAtlas A hR T; IsManifold (𝓡 6) ∞ (ResultZero A hR T) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  exact regularFiber_isManifold (resultTimeMap A hR T) (contMDiff_timeFunction A hR T) 0
    (regular_timeFunction_zero A hR T) 6 (by simp)

def originalZeroToBand (p : OriginalZero A T) : retainedTimeBand A T :=
  ⟨p.val, zero_mem_retainedTimeBand A T p.property⟩

def zeroMap (p : OriginalZero A T) : ResultZero A hR T :=
  ⟨retainedTimeMap A hR T (originalZeroToBand A T p),
    (timeFunction_retainedTimeMap A hR T (originalZeroToBand A T p)).trans p.property⟩

def resultZeroToImage (p : ResultZero A hR T) : retainedTimeImage A hR T :=
  ⟨p.val, by
    obtain ⟨q, hq, hqp⟩ := (timeFunction_zero_iff A hR T p.val).mp p.property
    exact ⟨⟨q.val, zero_mem_retainedTimeBand A T hq⟩, hqp⟩⟩

theorem bijective_zeroMap : Bijective (zeroMap A hR T) := by
  constructor
  · intro p q he
    have h := (isOpenEmbedding_retainedTimeMap A hR T).injective
      (congrArg (fun z : ResultZero A hR T ↦ z.val) he)
    exact Subtype.ext (congrArg (fun z : retainedTimeBand A T ↦ z.val) h)
  · intro p
    obtain ⟨q, hq, hqp⟩ := (timeFunction_zero_iff A hR T p.val).mp p.property
    exact ⟨⟨q.val, hq⟩, Subtype.ext hqp⟩

def zeroEquiv : OriginalZero A T ≃ ResultZero A hR T :=
  Equiv.ofBijective (zeroMap A hR T) (bijective_zeroMap A hR T)

theorem contMDiff_zeroMap : letI := targetChartedSpace A hR;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (zeroMap A hR T) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  have ho : ContMDiff (𝓡 6) (𝓡 7) ∞ (originalZeroToBand A T) :=
    (ContMDiff.subtypeVal_comp_iff (retainedTimeBand A T) (originalZeroToBand A T)).mp
      (regularFiber_contMDiff_subtype_val (originalTimeMap A T) T.smooth 0 T.regular 6 (by simp))
  apply (regularFiber_contMDiff_iff_ambient (resultTimeMap A hR T)
    (contMDiff_timeFunction A hR T) 0 (regular_timeFunction_zero A hR T) 6 (by simp) _).mpr
  have hm : ContMDiff (𝓡 7) (𝓡 7) ∞ (retainedTimeMap A hR T) :=
    fun p ↦ (isLocalDiffeomorphAt_retainedTimeMap A hR T p).contMDiffAt
  exact hm.comp ho

theorem contMDiff_zeroEquiv_symm : letI := targetChartedSpace A hR;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (zeroEquiv A hR T).symm := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  apply (regularFiber_contMDiff_iff_ambient (originalTimeMap A T) T.smooth 0 T.regular 6
    (by simp) (zeroEquiv A hR T).symm).mpr
  let D := retainedTimeDiffeomorph A hR T
  have hg : ContMDiff (𝓡 6) (𝓡 7) ∞ (resultZeroToImage A hR T) :=
    (ContMDiff.subtypeVal_comp_iff (retainedTimeImage A hR T) (resultZeroToImage A hR T)).mp
      (regularFiber_contMDiff_subtype_val (resultTimeMap A hR T)
        (contMDiff_timeFunction A hR T) 0 (regular_timeFunction_zero A hR T) 6 (by simp))
  have hs : ContMDiff (𝓡 6) (𝓡 7) ∞
      (fun p : ResultZero A hR T ↦ (D.symm (resultZeroToImage A hR T p)).val) :=
    contMDiff_subtype_val.comp (D.symm.contMDiff.comp hg)
  have he : (fun p : ResultZero A hR T ↦ ((zeroEquiv A hR T).symm p).val) =
      (fun p ↦ (D.symm (resultZeroToImage A hR T p)).val) := by
    funext p
    let q := originalZeroToBand A T ((zeroEquiv A hR T).symm p)
    have hq : D q = resultZeroToImage A hR T p :=
      Subtype.ext (congrArg (fun z : ResultZero A hR T ↦ z.val)
        ((zeroEquiv A hR T).apply_symm_apply p))
    exact congrArg Subtype.val ((D.symm_apply_apply q).symm.trans (congrArg D.symm hq))
  rw [he]
  exact hs

def zeroDiffeomorph : letI := targetChartedSpace A hR;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    OriginalZero A T ≃ₘ⟮𝓡 6, 𝓡 6⟯ ResultZero A hR T := by
  let := targetChartedSpace A hR
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  exact
    { toEquiv := zeroEquiv A hR T
      contMDiff_toFun := contMDiff_zeroMap A hR T
      contMDiff_invFun := contMDiff_zeroEquiv_symm A hR T }

theorem zeroDiffeomorph_point (p : OriginalZero A T) :
    letI := targetChartedSpace A hR;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    (zeroDiffeomorph A hR T p).val =
      retainedTimeMap A hR T (originalZeroToBand A T p) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
