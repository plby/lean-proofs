import Wikipedia.HopfProblem.EllipticAffineMaps
import Wikipedia.HopfProblem.EllipticCyclicAction
import Wikipedia.HopfProblem.EllipticFiniteQuotient
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# The actual elliptic quotient surfaces

For each admissible fixed period and each admissible integral twist, the
order-three or order-four affine biholomorphism gives a proved free action
of the corresponding finite cyclic group.  Its actual orbit quotient is
a compact Hausdorff complex surface, with the quotient topology and a
holomorphic atlas obtained from local lifts.  The covering degree is
exactly three or four.

The chosen twists `ε` and `-ε'` satisfy all the required arithmetic
conditions unconditionally.  Explicit fixed periods give concrete
inhabitants of both constructions.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

instance (j : Kind) : NeZero j.order := ⟨Nat.ne_of_gt j.order_pos⟩

/-- The finite cyclic group of the source's specified order. -/
abbrev CyclicGroup (j : Kind) := Multiplicative (ZMod j.order)

/-- The actual cyclic action of the affine biholomorphism. -/
@[instance_reducible] def affineAction (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : MulAction (CyclicGroup j) p.val.Torus :=
  CyclicAction.action (affinePermutation j p v) (affinePermutation_pow_order j p v hv)

theorem affineAction_generator_smul (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (x : p.val.Torus) :
    letI := affineAction j p v hv
    CyclicAction.generator j.order • x = affineBiholomorph j p v x :=
  CyclicAction.generator_smul (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv) x

/-- Freeness of this concrete action is equivalent to admissibility. -/
theorem affineAction_free_iff (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    IsCancelSMul (CyclicGroup j) p.val.Torus ↔ AdmissibleTwist j v := by
  refine (CyclicAction.isCancelSMul_iff (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv)).trans ?_
  simpa only [Equiv.Perm.coe_pow] using affinePermutation_free_iff j p v hv

theorem affineAction_free (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := affineAction j p v hv.1
    IsCancelSMul (CyclicGroup j) p.val.Torus :=
  (affineAction_free_iff j p v hv.1).mpr hv

theorem affineAction_holomorphic (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) :
    letI := affineAction j p v hv
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω (fun x : p.val.Torus => g • x) :=
  CyclicAction.smul_contMDiff (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv) (affineBiholomorph j p v).contMDiff_toFun g

theorem affineAction_continuous (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    ContinuousConstSMul (CyclicGroup j) p.val.Torus :=
  CyclicAction.continuousConstSMul (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv) (affineBiholomorph j p v).continuous

/-- The actual finite-orbit quotient of the actual complex period torus. -/
abbrev Surface (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

/-- The quotient projection onto the elliptic surface. -/
def surfaceProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : p.val.Torus → Surface j p v hv :=
  @FiniteQuotient.project (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

theorem surfaceProjection_surjective (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Surjective (surfaceProjection j p v hv) :=
  Quotient.mk_surjective

theorem surfaceProjection_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Continuous (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) p.val.Torus

instance surfaceCompact (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : CompactSpace (Surface j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.spaceCompactSpace (CyclicGroup j) p.val.Torus

instance surfaceT2 (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : T2Space (Surface j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  exact FiniteQuotient.spaceT2Space (CyclicGroup j) p.val.Torus

instance surfaceSecondCountable (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : SecondCountableTopology (Surface j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  exact FiniteQuotient.spaceSecondCountableTopology (CyclicGroup j) p.val.Torus

instance surfacePathConnected (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : PathConnectedSpace (Surface j p v hv) :=
  (surfaceProjection_surjective j p v hv).pathConnectedSpace
    (surfaceProjection_continuous j p v hv)

/-- The complex atlas constructed from the actual quotient covering. -/
instance surfaceChartedSpace (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : ChartedSpace ComplexPlane₂ (Surface j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.chartedSpace (E := ComplexPlane₂) (CyclicGroup j) p.val.Torus

instance surfaceIsManifold (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    IsManifold (modelWithCornersSelf ℂ ComplexPlane₂) ω (Surface j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.isManifold (CyclicGroup j) p.val.Torus
    (affineAction_holomorphic j p v hv.1)

theorem surfaceProjection_isCoveringMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) p.val.Torus

theorem surfaceProjection_holomorphic (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_holomorphic (CyclicGroup j) p.val.Torus
    (affineAction_holomorphic j p v hv.1)

/-- The holomorphic quotient covering has the prescribed exact degree. -/
theorem surfaceProjection_fibre_card (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Surface j p v hv) :
    Nat.card (surfaceProjection j p v hv ⁻¹' {y}) = j.order := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  change Nat.card (FiniteQuotient.project (CyclicGroup j) p.val.Torus ⁻¹' {y}) = j.order
  rw [FiniteQuotient.fibre_card (CyclicGroup j) p.val.Torus]
  simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

/-- A local lift from the surface to its covering torus. -/
def surfaceLocalInverse (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : p.val.Torus) :
    OpenPartialHomeomorph (Surface j p v hv) p.val.Torus := by
  letI := affineAction j p v hv.1
  letI := affineAction_continuous j p v hv.1
  letI := affineAction_free j p v hv
  exact FiniteQuotient.localInverse (CyclicGroup j) p.val.Torus x

theorem surfaceLocalInverse_holomorphic (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : p.val.Torus) :
    ContMDiffOn (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω (surfaceLocalInverse j p v hv x)
      (surfaceLocalInverse j p v hv x).source := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.localInverse_holomorphic (CyclicGroup j) p.val.Torus
    (affineAction_holomorphic j p v hv.1) x

/-- The source's chosen quotient, with all twist conditions already proved. -/
abbrev MainSurface (j : Kind) (p : FixedPeriod j) :=
  Surface j p j.twist (mainTwist_admissible j)

/-- An explicit compact complex surface of each of the two prescribed orders. -/
abbrev ExampleSurface (j : Kind) := MainSurface j (exampleFixedPeriod j)

instance exampleSurfaceT2 (j : Kind) : T2Space (ExampleSurface j) :=
  surfaceT2 j (exampleFixedPeriod j) j.twist (mainTwist_admissible j)

instance exampleSurfaceSecondCountable (j : Kind) :
    SecondCountableTopology (ExampleSurface j) :=
  surfaceSecondCountable j (exampleFixedPeriod j) j.twist (mainTwist_admissible j)

instance exampleSurfaceChartedSpace (j : Kind) :
    ChartedSpace ComplexPlane₂ (ExampleSurface j) :=
  surfaceChartedSpace j (exampleFixedPeriod j) j.twist (mainTwist_admissible j)

instance exampleSurfaceIsManifold (j : Kind) :
    IsManifold (modelWithCornersSelf ℂ ComplexPlane₂) ω (ExampleSurface j) :=
  surfaceIsManifold j (exampleFixedPeriod j) j.twist (mainTwist_admissible j)

theorem exampleSurface_compact_complex (j : Kind) :
    CompactSpace (ExampleSurface j) ∧ T2Space (ExampleSurface j) ∧
      SecondCountableTopology (ExampleSurface j) ∧
      IsManifold (modelWithCornersSelf ℂ ComplexPlane₂) ω (ExampleSurface j) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Wikipedia.HopfProblem.Elliptic
