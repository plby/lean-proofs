import Wikipedia.HopfProblem.CuspCircleOrbitLocalQuotient
import Wikipedia.HopfProblem.OrbitPairRadialHomeomorph
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The radius-preserving normal orbit quotient

We retain the original opposite-weight circle action and its native
topological quotient. The source and target below have Euclidean norms
(`WithLp 2`), rather than the maximum norms on ordinary products.

The map `radialHopfMap` is the polynomial Hopf invariant divided by the
source radius. It induces an explicit homeomorphism on the native orbit
space and preserves the radius exactly, including at the fixed origin.
-/

noncomputable section

open Topology Set

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- The real four-dimensional normal space with its Euclidean norm. -/
abbrev Normal := WithLp 2 (ℂ × ℂ)

/-- The real three-dimensional transverse orbit space with its Euclidean norm. -/
abbrev Transverse := WithLp 2 (ℂ × ℝ)

/-- The original polynomial invariant, with Euclidean norms on both sides. -/
def euclideanHopfMap (v : Normal) : Transverse :=
  WithLp.toLp 2 (hopfMap v.ofLp)

@[simp] theorem euclideanHopfMap_zero : euclideanHopfMap 0 = 0 := by
  simp [euclideanHopfMap, hopfMap]

theorem continuous_euclideanHopfMap : Continuous euclideanHopfMap :=
  (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
    (hopfMap_continuous.comp (WithLp.prod_continuous_ofLp 2 ℂ ℂ))

theorem norm_euclideanHopfMap (v : Normal) : ‖euclideanHopfMap v‖ = ‖v‖ ^ 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp
  calc
    ‖euclideanHopfMap v‖ ^ 2 =
        Complex.normSq (hopfMap v.ofLp).1 + (hopfMap v.ofLp).2 ^ 2 := by
      simp [WithLp.prod_norm_sq_eq_of_L2, euclideanHopfMap,
        Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
    _ = (Complex.normSq v.fst + Complex.normSq v.snd) ^ 2 :=
      hopfMap_radius_squared v.ofLp
    _ = (‖v‖ ^ 2) ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [Complex.normSq_eq_norm_sq]

/-- The radial Hopf quotient, with radius `r` rather than `r²`. -/
def radialHopfMap (v : Normal) : Transverse := Radial.root (euclideanHopfMap v)

@[simp] theorem radialHopfMap_zero : radialHopfMap 0 = 0 := by
  simp [radialHopfMap]

/-- The quotient formula is literal division by the source Euclidean radius. -/
theorem radialHopfMap_eq (v : Normal) :
    radialHopfMap v = ‖v‖⁻¹ • euclideanHopfMap v := by
  rw [radialHopfMap, Radial.root, norm_euclideanHopfMap, Real.sqrt_sq (norm_nonneg v)]

/-- The radial quotient preserves radius even at the fixed point. -/
theorem norm_radialHopfMap (v : Normal) : ‖radialHopfMap v‖ = ‖v‖ := by
  rw [radialHopfMap, Radial.norm_root, norm_euclideanHopfMap,
    Real.sqrt_sq (norm_nonneg v)]

theorem radialHopfMap_eq_zero_iff (v : Normal) : radialHopfMap v = 0 ↔ v = 0 := by
  rw [← norm_eq_zero, norm_radialHopfMap, norm_eq_zero]

theorem continuous_radialHopfMap : Continuous radialHopfMap :=
  Radial.continuous_root.comp continuous_euclideanHopfMap

/-- The native opposite-weight orbit quotient, in radial coordinates. -/
def radialOrbitHomeomorph : NormalOrbitSpace ≃ₜ Transverse :=
  (normalOrbitSpaceHomeomorph.trans (WithLp.homeomorphProd 2 ℂ ℝ).symm).trans
    Radial.squareHomeomorph.symm

@[simp] theorem radialOrbitHomeomorph_projection (v : Normal) :
    radialOrbitHomeomorph (normalOrbitProjection v.ofLp) = radialHopfMap v := rfl

/-- This is the same orbit relation as before; no new quotient relation is introduced. -/
theorem radialHopfMap_eq_iff (v w : Normal) :
    radialHopfMap v = radialHopfMap w ↔
      ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ unitNormalAction u v.ofLp = w.ofLp := by
  rw [← radialOrbitHomeomorph_projection, ← radialOrbitHomeomorph_projection,
    radialOrbitHomeomorph.injective.eq_iff, normalOrbitProjection_eq_iff]

theorem radialHopfMap_surjective : Function.Surjective radialHopfMap := by
  intro y
  obtain ⟨x, hx⟩ := radialOrbitHomeomorph.surjective y
  obtain ⟨v, rfl⟩ := normalOrbitProjection_surjective x
  exact ⟨WithLp.toLp 2 v, hx⟩

theorem radialHopfMap_isQuotientMap : IsQuotientMap radialHopfMap := by
  have hq : IsQuotientMap (normalOrbitProjection ∘ (WithLp.homeomorphProd 2 ℂ ℂ)) :=
    normalOrbitProjection_isQuotientMap.comp
      (WithLp.homeomorphProd 2 ℂ ℂ).isQuotientMap
  have h : IsQuotientMap
      (radialOrbitHomeomorph ∘ (normalOrbitProjection ∘ (WithLp.homeomorphProd 2 ℂ ℂ))) :=
    radialOrbitHomeomorph.isQuotientMap.comp hq
  have he :
      radialOrbitHomeomorph ∘ (normalOrbitProjection ∘ (WithLp.homeomorphProd 2 ℂ ℂ)) =
        radialHopfMap := funext radialOrbitHomeomorph_projection
  rw [he] at h
  exact h

/-- The actual linear action, with Euclidean source coordinates. -/
def oppositeAction (u : ℂˣ) (v : Normal) : Normal :=
  WithLp.toLp 2 (unitNormalAction u v.ofLp)

theorem continuous_oppositeAction (u : ℂˣ) : Continuous (oppositeAction u) := by
  unfold oppositeAction unitNormalAction
  fun_prop

/-- Saturation is a union of inverse images under the original circle action. -/
theorem radialHopfMap_saturation (s : Set Normal) :
    radialHopfMap ⁻¹' (radialHopfMap '' s) =
      ⋃ u : {u : ℂˣ // ‖(u : ℂ)‖ = 1}, oppositeAction u.val ⁻¹' s := by
  ext v
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨u, hu, he⟩ := (radialHopfMap_eq_iff v w).mp he.symm
    refine ⟨⟨u, hu⟩, ?_⟩
    change WithLp.toLp 2 (unitNormalAction u v.ofLp) ∈ s
    simpa only [he, WithLp.toLp_ofLp] using hw
  · rintro ⟨u, hu⟩
    refine ⟨oppositeAction u.val v, hu, ?_⟩
    exact ((radialHopfMap_eq_iff _ _).mpr ⟨u.val, u.property, rfl⟩).symm

theorem radialHopfMap_isOpenMap : IsOpenMap radialHopfMap := by
  intro s hs
  apply radialHopfMap_isQuotientMap.isOpen_preimage.mp
  rw [radialHopfMap_saturation]
  exact isOpen_iUnion (fun u => hs.preimage (continuous_oppositeAction u.val))

/-- Openness is needed to take products and restrict to the normal tube. -/
theorem radialHopfMap_isOpenQuotientMap : IsOpenQuotientMap radialHopfMap :=
  ⟨radialHopfMap_surjective, continuous_radialHopfMap, radialHopfMap_isOpenMap⟩

/-- Ordinary open balls pull back to ordinary open balls of the same radius. -/
theorem radialHopfMap_preimage_ball (r : ℝ) :
    radialHopfMap ⁻¹' Metric.ball 0 r = Metric.ball 0 r := by
  ext v
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_radialHopfMap]

/-- In particular, the meridian sphere is the actual quotient of a normal sphere. -/
theorem radialHopfMap_preimage_sphere (r : ℝ) :
    radialHopfMap ⁻¹' Metric.sphere 0 r = Metric.sphere 0 r := by
  ext v
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_zero_right, norm_radialHopfMap]

end Wikipedia.HopfProblem.OrbitPair
