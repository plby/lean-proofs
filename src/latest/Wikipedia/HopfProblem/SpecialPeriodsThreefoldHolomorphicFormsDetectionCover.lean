import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPeriodPullback
import Wikipedia.HopfProblem.TrianglePeriodFamilyLocal
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFunctor

/-!
# The actual regular vector cover detects native covectors

The vector-cover map factors through the original period-lattice covering,
the original free triangle covering, and the actual open inclusion of the
regular family into the glued threefold.  Each factor is locally
biholomorphic for its already constructed complex atlas.  Consequently
its genuine tangent derivative is invertible, in every degree of the
alternating covector bundle.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open TrianglePeriodFamily
open HolomorphicDifferentialForms (Form)

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] chartedSpace specialRegularFamilyChartedSpace
  coverChartedSpace cover_isManifold space_isManifold

/-- The actual period-vector cover is locally biholomorphic, with no
change to either the source atlas or the global glued atlas. -/
theorem globalCover_isLocalDiffeomorph :
    IsLocalDiffeomorph IF IF ω globalCover := by
  let := data.periods.totalChartedSpace
  intro x
  have hperiod := data.periods.quotientMap_isLocalDiffeomorph x
  have htriangle := data.quotient_isLocalDiffeomorph
    (regularCovering specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂) (data.periods.quotientMap x)
  exact (hperiod.comp (K := IF) (P := SpecialRegularFamily) htriangle).comp
    (K := IF) (P := Threefold.Space)
    (regularFamilyInclusion_isLocalDiffeomorph
      (data.quotient (data.periods.quotientMap x)))

/-- The cover reaches precisely the actual regular locus, rather than
an abstractly identified replacement of that locus. -/
theorem range_globalCover :
    range globalCover = (regularLocus : Set Threefold.Space) := by
  rw [← range_regularFamilyInclusion]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨data.quotient (data.periods.quotientMap x), rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := data.quotient_surjective u
    obtain ⟨x, rfl⟩ := data.periods.quotientMap_surjective t
    exact ⟨x, rfl⟩

theorem globalCover_mem_regularLocus (x : Cover) :
    globalCover x ∈ regularLocus := by
  change globalCover x ∈ (regularLocus : Set Threefold.Space)
  rw [← range_globalCover]
  exact mem_range_self x

/-- Surjectivity here concerns the genuine manifold derivative, not a
separately supplied coordinate matrix. -/
theorem globalCover_mfderiv_surjective (x : Cover) :
    Function.Surjective (mfderiv IF IF globalCover x) :=
  (globalCover_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)
    |>.surjective

/-- A zero actual pullback forces the original covector to vanish at
each point reached by the cover, in every exterior degree. -/
theorem globalCoverPullback_zero_at {p : ℕ} (θ : Form Model Threefold.Space p)
    (hθ : globalCoverPullback θ = 0) (x : Cover) : θ (globalCover x) = 0 := by
  ext v
  choose w hw using fun i : Fin p => globalCover_mfderiv_surjective x (v i)
  have hx := congrArg (fun η : Form Model Cover p => η x) hθ
  change (θ (globalCover x)).compContinuousLinearMap
    (mfderiv IF IF globalCover x) = 0 at hx
  have hv := DFunLike.congr_fun hx w
  have hvec : (fun i => mfderiv IF IF globalCover x (w i)) = v := funext hw
  change θ (globalCover x) (fun i => mfderiv IF IF globalCover x (w i)) = 0 at hv
  rw [hvec] at hv
  exact hv

/-- Vanishing of the vector-cover pullback is equivalent to vanishing
of the genuine covectors on the full actual regular locus. -/
theorem globalCoverPullback_eq_zero_iff_regular {p : ℕ}
    (θ : Form Model Threefold.Space p) :
    globalCoverPullback θ = 0 ↔ ∀ y ∈ regularLocus, θ y = 0 := by
  constructor
  · intro hθ y hy
    have hy' : y ∈ range globalCover := by
      rw [range_globalCover]
      exact hy
    obtain ⟨x, rfl⟩ := hy'
    exact globalCoverPullback_zero_at θ hθ x
  · intro hθ
    apply ContMDiffSection.ext
    intro x
    ext v
    change θ (globalCover x) (fun i => mfderiv IF IF globalCover x (v i)) = 0
    rw [hθ _ (globalCover_mem_regularLocus x)]
    rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
