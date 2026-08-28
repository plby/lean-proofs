import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRingEvaluation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Local rings of the genuine holomorphic-function sheaf

A germ is invertible precisely when its value at the point is nonzero.
For the nontrivial direction, continuity gives a smaller open domain on
which an actual representative never vanishes; its pointwise reciprocal
is holomorphic of order `ω`. These actual reciprocal sections prove that
the categorical stalks are local rings, without a local-ring hypothesis.
-/

noncomputable section

open Set Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- A genuine holomorphic-function stalk element is a unit exactly when
its evaluation at the point is nonzero. -/
theorem isUnit_stalk_iff (x : M) (φ : (presheaf I M).stalk x) :
    IsUnit φ ↔ stalkEval I M x φ ≠ 0 := by
  constructor
  · intro hφ
    exact (hφ.map (stalkEval I M x)).ne_zero
  · intro hφ
    obtain ⟨U, hxU, f, rfl⟩ := (presheaf I M).exists_germ_eq φ
    have hfx : f ⟨x, hxU⟩ ≠ 0 :=
      fun hzero => hφ ((stalkEval_germ I M U x hxU f).trans hzero)
    let V : Opens M :=
      ⟨Subtype.val '' {y : U | f y ≠ 0},
        U.isOpen.isOpenMap_subtype_val _
          (isOpen_ne_fun f.contMDiff.continuous continuous_const)⟩
    have hVU : V ≤ U := Subtype.coe_image_subset (U : Set M) {y : U | f y ≠ 0}
    have hxV : x ∈ V := ⟨⟨x, hxU⟩, hfx, rfl⟩
    let fV : Section I M V := ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ hVU f
    have hfV (y : V) : fV y ≠ 0 := by
      obtain ⟨u, hu, heu⟩ := y.property
      have hy : Set.inclusion hVU y = u := Subtype.ext heu.symm
      change f (Set.inclusion hVU y) ≠ 0
      rw [hy]
      exact hu
    let g : Section I M V := ⟨fun y => (fV y)⁻¹, by
      intro y
      exact ((contDiffAt_inv ℂ (hfV y)).contMDiffAt).comp y
        fV.contMDiff.contMDiffAt⟩
    have hfg : fV * g = 1 := by
      apply ContMDiffMap.ext
      intro y
      exact mul_inv_cancel₀ (hfV y)
    have hgf : g * fV = 1 := by
      apply ContMDiffMap.ext
      intro y
      exact inv_mul_cancel₀ (hfV y)
    let γ : Section I M V →+* (presheaf I M).stalk x :=
      ((presheaf I M).germ V x hxV).hom
    refine ⟨⟨γ fV, γ g, ?_, ?_⟩, ?_⟩
    · rw [← map_mul, hfg, map_one]
    · rw [← map_mul, hgf, map_one]
    · exact (presheaf I M).germ_res_apply (homOfLE hVU) x hxV f

/-- The nonunits are exactly the genuine germs vanishing at the point. -/
theorem nonunits_stalk (x : M) :
    nonunits ((presheaf I M).stalk x) = RingHom.ker (stalkEval I M x) := by
  ext φ
  change (¬ IsUnit φ) ↔ stalkEval I M x φ = 0
  simp only [isUnit_stalk_iff, not_not]

/-- The actual categorical holomorphic stalk is a local ring. -/
instance stalk_isLocalRing (x : M) : IsLocalRing ((presheaf I M).stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

/-- The actual complex-charted space with its order-`ω` holomorphic
function sheaf, as a genuine locally ringed space. -/
def locallyRingedSpace : AlgebraicGeometry.LocallyRingedSpace where
  carrier := TopCat.of M
  presheaf := presheaf I M
  IsSheaf := (sheaf I M).property
  isLocalRing x := stalk_isLocalRing I M x

/-- The locally ringed space has the original underlying space. -/
theorem locallyRingedSpace_carrier :
    (locallyRingedSpace I M).carrier = TopCat.of M := rfl

/-- Its structure presheaf is literally the actual holomorphic presheaf. -/
theorem locallyRingedSpace_presheaf :
    (locallyRingedSpace I M).presheaf = presheaf I M := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
