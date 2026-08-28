import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticRegular

/-!
# The genuine lifted base paths of the elliptic boundary cylinders

The positive boundary angle lifts to the actual inverse Cayley
neighborhood, and its endpoint is the inverse triangle generator.
The logarithm used by the full fibre gauge is continuous along that
entire real cylinder.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.EllipticFilling
open Wikipedia.HopfProblem.Elliptic

theorem specialBoundaryRoot_continuous (j : Kind) : Continuous (specialBoundaryRoot j) :=
  (root_continuous j.order (specialBaseCover.radius (some j))).comp
    (continuous_const.prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_id.div_const (j.order : ℝ))))

theorem specialBoundaryLog_continuous (j : Kind) : Continuous (specialBoundaryLog j) :=
  continuous_const.add (Complex.continuous_ofReal.div_const (j.order : ℂ))

/-- One positive base turn is exactly an inverse root rotation. -/
theorem specialBoundaryRoot_add_one (j : Kind) (t : ℝ) :
    familyRotation j (specialBoundaryRoot j (t + 1)) = specialBoundaryRoot j t := by
  have h := root_sub_order j (specialBaseCover.radius (some j)) (specialRootRadius j)
    (((t + 1) / j.order : ℝ) : Circle)
  have ht : ((((t + 1) / j.order : ℝ) : Circle) - (((1 : ℝ) / j.order : ℝ) : Circle)) =
      ((t / j.order : ℝ) : Circle) := by
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  exact h.symm.trans (congrArg (root j.order (specialBaseCover.radius (some j))
    (specialRootRadius j)) ht)

/-- The actual lifted boundary path in the original regular triangle locus. -/
def specialBoundaryBase (j : Kind) : C(ℝ, TriangleRegularPoint) :=
  ⟨fun t => localBase j ⟨specialBoundaryRoot j t, specialBoundaryRoot_ne_zero j t⟩,
    (localBase_continuous j).comp ((specialBoundaryRoot_continuous j).subtype_mk _)⟩

/-- Its exact endpoint transformation, agreeing with the actual positive meridians. -/
theorem specialBoundaryBase_endpoint (j : Kind) (t : ℝ) :
    specialBoundaryBase j (t + 1) =
      (Triangle.ellipticGenerator j)⁻¹ • specialBoundaryBase j t := by
  let z₁ : LogGauge.BaseStar :=
    ⟨specialBoundaryRoot j (t + 1), specialBoundaryRoot_ne_zero j (t + 1)⟩
  let z₀ : LogGauge.BaseStar := ⟨specialBoundaryRoot j t, specialBoundaryRoot_ne_zero j t⟩
  have hz : puncturedRotation j z₁ = z₀ := Subtype.ext (specialBoundaryRoot_add_one j t)
  have hb := localBase_rotation j z₁
  rw [hz] at hb
  have hi := congrArg (fun z : TriangleRegularPoint => (Triangle.ellipticGenerator j)⁻¹ • z) hb
  change localBase j z₁ = (Triangle.ellipticGenerator j)⁻¹ • localBase j z₀
  simpa only [inv_smul_smul] using hi.symm

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
