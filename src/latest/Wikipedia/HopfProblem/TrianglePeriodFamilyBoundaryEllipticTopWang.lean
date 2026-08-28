import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTailHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceTopCoordinates

/-!
# Actual top-degree Wang equivalences for the elliptic boundary tori

The real four-torus has zero fifth singular homology. Thus its actual
mapping-torus Wang boundary is injective in degree five. If the actual
fourth-homology monodromy is the identity, exactness also makes that same
boundary surjective. For every literal elliptic affine monodromy, the
identity follows from the proved affine-to-triangle homology comparison
and the actual triangle action on fourth homology. No matrix action or
mapping-torus homology group is supplied as an extra hypothesis there.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorus MappingTorusHomology HomologyDifference

/-- Vanishing of the actual fifth homology of the fibre makes the top Wang boundary injective. -/
theorem H5ToH4Wang_injective (f : RealTorus₄ ≃ₜ RealTorus₄) :
    Function.Injective (wangBoundary f 4) := by
  let : Subsingleton (SingularHomology RealTorus₄ 5) :=
    realTorus_homology_subsingleton_of_lt (by decide : 4 < 5)
  have hzero : fibreHomologyMap f 5 = 0 := by
    apply LinearMap.ext
    intro a
    exact (congrArg (fibreHomologyMap f 5) (Subsingleton.elim a 0)).trans
      (map_zero (fibreHomologyMap f 5))
  apply LinearMap.ker_eq_bot.mp
  rw [← wang_exact_at_mappingTorus f 4, hzero, LinearMap.range_zero]

/-- Identity actual top monodromy makes the same Wang boundary surjective. -/
theorem H5ToH4Wang_surjective (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id) :
    Function.Surjective (wangBoundary f 4) := by
  intro a
  have ha : a ∈ LinearMap.ker (wangDifference f 4) := by
    change a - monodromyHomologyMap f 4 a = 0
    rw [hf, LinearMap.id_apply, sub_self]
  rw [← wangBoundary_range f 4] at ha
  exact ha

/-- The actual signed Wang boundary itself is the top-degree linear equivalence. -/
def H5ToH4WangEquiv (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id) :
    SingularHomology (Torus f) 5 ≃ₗ[ℤ] SingularHomology RealTorus₄ 4 :=
  LinearEquiv.ofBijective (wangBoundary f 4)
    ⟨H5ToH4Wang_injective f, H5ToH4Wang_surjective f hf⟩

@[simp] theorem H5ToH4WangEquiv_toLinearMap (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id) :
    (H5ToH4WangEquiv f hf).toLinearMap = wangBoundary f 4 := rfl

@[simp] theorem H5ToH4WangEquiv_apply (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id)
    (a : SingularHomology (Torus f) 5) :
    H5ToH4WangEquiv f hf a = wangBoundary f 4 a := rfl

/-- The inverse has the prescribed actual Wang boundary, with its sign unchanged. -/
@[simp] theorem wangBoundary_H5ToH4WangEquiv_symm (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id)
    (a : SingularHomology RealTorus₄ 4) :
    wangBoundary f 4 ((H5ToH4WangEquiv f hf).symm a) = a :=
  (H5ToH4WangEquiv f hf).apply_symm_apply a

/-- Integral coordinates obtained from the actual Wang boundary and the actual fibre marking. -/
def H5WangCoordinates (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id) :
    SingularHomology (Torus f) 5 ≃ₗ[ℤ] ℤ :=
  (H5ToH4WangEquiv f hf).trans realTorusH4Equiv

@[simp] theorem H5WangCoordinates_apply (f : RealTorus₄ ≃ₜ RealTorus₄)
    (hf : monodromyHomologyMap f 4 = LinearMap.id)
    (a : SingularHomology (Torus f) 5) :
    H5WangCoordinates f hf a = realTorusH4Equiv (wangBoundary f 4 a) := rfl

/-- Every actual elliptic affine map acts identically on actual fourth torus homology. -/
theorem ellipticMonodromyHomologyFour_identity (j : Kind) (v : Lattice) :
    monodromyHomologyMap (flatTorusAffine j v) 4 = LinearMap.id := by
  change singularHomologyMap (flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) 4 = _
  rw [flatTorusAffine_homology_triangle, triangleHomologyFour_identity]
  rfl

/-- The actual degree-five Wang equivalence for every original elliptic affine monodromy. -/
def ellipticH5ToH4WangEquiv (j : Kind) (v : Lattice) :
    SingularHomology (Torus (flatTorusAffine j v)) 5 ≃ₗ[ℤ]
      SingularHomology RealTorus₄ 4 :=
  H5ToH4WangEquiv (flatTorusAffine j v) (ellipticMonodromyHomologyFour_identity j v)

@[simp] theorem ellipticH5ToH4WangEquiv_toLinearMap (j : Kind) (v : Lattice) :
    (ellipticH5ToH4WangEquiv j v).toLinearMap = wangBoundary (flatTorusAffine j v) 4 := rfl

@[simp] theorem ellipticH5ToH4WangEquiv_apply (j : Kind) (v : Lattice)
    (a : SingularHomology (Torus (flatTorusAffine j v)) 5) :
    ellipticH5ToH4WangEquiv j v a = wangBoundary (flatTorusAffine j v) 4 a := rfl

/-- The actual fifth homology of every such elliptic boundary mapping torus is integrally marked. -/
def ellipticH5WangCoordinates (j : Kind) (v : Lattice) :
    SingularHomology (Torus (flatTorusAffine j v)) 5 ≃ₗ[ℤ] ℤ :=
  H5WangCoordinates (flatTorusAffine j v) (ellipticMonodromyHomologyFour_identity j v)

@[simp] theorem ellipticH5WangCoordinates_apply (j : Kind) (v : Lattice)
    (a : SingularHomology (Torus (flatTorusAffine j v)) 5) :
    ellipticH5WangCoordinates j v a =
      realTorusH4Equiv (wangBoundary (flatTorusAffine j v) 4 a) := rfl

/-- Specialization to the source's actual main elliptic twist. -/
def ellipticMainH5ToH4WangEquiv (j : Kind) :
    SingularHomology (Torus (flatTorusAffine j j.twist)) 5 ≃ₗ[ℤ]
      SingularHomology RealTorus₄ 4 :=
  ellipticH5ToH4WangEquiv j j.twist

@[simp] theorem ellipticMainH5ToH4WangEquiv_toLinearMap (j : Kind) :
    (ellipticMainH5ToH4WangEquiv j).toLinearMap =
      wangBoundary (flatTorusAffine j j.twist) 4 := rfl

/-- The source's actual main-twist boundary has the integral marking induced by Wang. -/
def ellipticMainH5WangCoordinates (j : Kind) :
    SingularHomology (Torus (flatTorusAffine j j.twist)) 5 ≃ₗ[ℤ] ℤ :=
  ellipticH5WangCoordinates j j.twist

@[simp] theorem ellipticMainH5WangCoordinates_apply (j : Kind)
    (a : SingularHomology (Torus (flatTorusAffine j j.twist)) 5) :
    ellipticMainH5WangCoordinates j a =
      realTorusH4Equiv (wangBoundary (flatTorusAffine j j.twist) 4 a) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
