import Wikipedia.NoExoticSixSphere.GeometricArfFrameHomotopy

/-!
# Positive rescaling of the actual normal frame preserves its quadratic form

The explicit positive interpolation stays injective and in the original
normal range. It gives a genuine normal-frame homotopy, including for
nonconstant positive scale functions. Neither the normal framing nor its
sphere-dependent source twist is replaced by a constant frame.
-/

noncomputable section

open Function unitInterval
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (ρ : M → ℝ) (hρ : Continuous ρ)

def positiveNormalScale (p : I × M) : ℝ :=
  (1 - (p.1 : ℝ)) + (p.1 : ℝ) * ρ p.2

omit [TopologicalSpace M] [ChartedSpace (Vector 6) M] in
theorem positiveNormalScale_pos (hpos : ∀ x, 0 < ρ x) (p : I × M) :
    0 < positiveNormalScale ρ p := by
  have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ))
    (show (0 : ℝ) < 1 from zero_lt_one) (hpos p.2)
    (sub_nonneg.mpr p.1.property.2) p.1.property.1
    (show (1 - (p.1 : ℝ)) + (p.1 : ℝ) = 1 by ring)
  simpa only [positiveNormalScale, smul_eq_mul, mul_one, Set.mem_Ioi] using h

def positiveNormalFamily : C(I × M, e.NormalModel →L[ℝ] Vector e.ambientDimension) where
  toFun p := positiveNormalScale ρ p • a.ambient p.2
  continuous_toFun := by
    have ht : Continuous (fun p : I × M ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).add (ht.mul (hρ.comp continuous_snd))).smul
      (a.contMDiff_ambient.continuous.comp continuous_snd)

theorem positiveNormalFamily_injective (hpos : ∀ x, 0 < ρ x) (p : I × M) :
    Injective (positiveNormalFamily e a ρ hρ p) :=
  (LinearEquiv.smulOfNeZero ℝ (Vector e.ambientDimension)
    (positiveNormalScale ρ p) (positiveNormalScale_pos ρ hpos p).ne').injective.comp
      (a.ambient_injective p.2)

theorem positiveNormalFamily_range (p : I × M) :
    (positiveNormalFamily e a ρ hρ p).range ≤ (e.normalProjection p.2).range := by
  rintro _ ⟨v, rfl⟩
  exact (e.normalProjection p.2).range.smul_mem _ (a.equiv p.2 v).property

theorem positiveNormalFamily_zero (x : M) :
    positiveNormalFamily e a ρ hρ (0, x) = a.ambient x := by
  change ((1 - (0 : ℝ)) + (0 : ℝ) * ρ x) • a.ambient x = _
  rw [sub_zero, zero_mul, add_zero, one_smul]

theorem positiveNormalFamily_one (x : M) :
    positiveNormalFamily e a ρ hρ (1, x) = ρ x • a.ambient x := by
  change ((1 - (1 : ℝ)) + (1 : ℝ) * ρ x) • a.ambient x = _
  rw [sub_self, one_mul, zero_add]

end NoExoticSixSphere.EuclideanEmbedding

namespace NoExoticSixSphere.GeometricArf

open GLOrthonormalization EuclideanEmbedding

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]

theorem invariant_eq_of_positive_rescaling (ρ : M → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (he : ∀ x, b.ambient x = ρ x • a.ambient x) :
    invariant e a r m = invariant e b r' m' :=
  invariant_eq_of_normal_family e a b r r' m m'
    (e.positiveNormalFamily a ρ hρ) (e.positiveNormalFamily_injective a ρ hρ hpos)
    (e.positiveNormalFamily_range a ρ hρ) (e.positiveNormalFamily_zero a ρ hρ)
    (fun x ↦ (e.positiveNormalFamily_one a ρ hρ x).trans (he x).symm)

end NoExoticSixSphere.GeometricArf
