import Wikipedia.HopfProblem.EllipticEquivariantCentralFamily

/-!
# The genuine central quotient surface for arbitrary equivariant periods

The finite affine quotient of the actual central period torus embeds
closedly and holomorphically into the quotient of the supplied varying
family. Its image is the entire literal central fibre, with its original
subspace topology.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

theorem centralInclusion_quotient_invariant (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (x : D.centralPeriod.val.Torus) :
    letI := affineAction j D.centralPeriod v hv.1
    D.quotient v hv (D.centralInclusion (g • x)) =
      D.quotient v hv (D.centralInclusion x) := by
  let := affineAction j D.centralPeriod v hv.1
  let := D.action v hv.1
  rw [D.centralInclusion_smul]
  exact D.quotient_smul v hv g (D.centralInclusion x)

/-- The actual finite affine central quotient inside the actual varying
family quotient. Its source uses the native fixed-period quotient atlas. -/
def centralFibreInclusion (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j D.centralPeriod v hv → D.Space v hv := by
  let := affineAction j D.centralPeriod v hv.1
  exact FiniteQuotient.descend (D.quotient v hv ∘ D.centralInclusion)
    (D.centralInclusion_quotient_invariant v hv)

@[simp] theorem centralFibreInclusion_surfaceProjection (v : Lattice)
    (hv : AdmissibleTwist j v) (x : D.centralPeriod.val.Torus) :
    D.centralFibreInclusion v hv (surfaceProjection j D.centralPeriod v hv x) =
      D.quotient v hv (D.centralInclusion x) := rfl

theorem centralFibreInclusion_continuous (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (D.centralFibreInclusion v hv) := by
  let := affineAction j D.centralPeriod v hv.1
  exact FiniteQuotient.descend_continuous (D.quotient v hv ∘ D.centralInclusion)
    (D.centralInclusion_quotient_invariant v hv)
    ((D.quotient_continuous v hv).comp D.centralInclusion_continuous)

/-- The ambient cyclic action introduces no extra identifications on
the central torus beyond its genuine affine quotient. -/
theorem centralFibreInclusion_injective (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Injective (D.centralFibreInclusion v hv) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := surfaceProjection_surjective j D.centralPeriod v hv a
  obtain ⟨y, rfl⟩ := surfaceProjection_surjective j D.centralPeriod v hv b
  rw [D.centralFibreInclusion_surfaceProjection, D.centralFibreInclusion_surfaceProjection] at hab
  let := affineAction j D.centralPeriod v hv.1
  let := D.action v hv.1
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff_mem_orbit v hv _ _).mp hab
  apply (FiniteQuotient.project_eq_iff_mem_orbit
    (CyclicGroup j) D.centralPeriod.val.Torus x y).mpr
  refine ⟨g, D.centralInclusion_injective ?_⟩
  rw [D.centralInclusion_smul]
  exact hg

theorem centralFibreInclusion_isClosedEmbedding (v : Lattice) (hv : AdmissibleTwist j v) :
    IsClosedEmbedding (D.centralFibreInclusion v hv) :=
  (D.centralFibreInclusion_continuous v hv).isClosedEmbedding
    (D.centralFibreInclusion_injective v hv)

/-- The quotient embedding is holomorphic for the supplied family's
quotient atlas, not for a substituted constant-family atlas. -/
theorem centralFibreInclusion_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ FamilyModel) ω (D.centralFibreInclusion v hv) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  let := affineAction j D.centralPeriod v hv.1
  let := affineAction_continuous j D.centralPeriod v hv.1
  let := affineAction_free j D.centralPeriod v hv
  exact FiniteQuotient.descend_holomorphic (D.quotient v hv ∘ D.centralInclusion)
    (D.centralInclusion_quotient_invariant v hv) (modelWithCornersSelf ℂ FamilyModel)
    ((D.quotient_holomorphic v hv).comp D.centralInclusion_holomorphic)

theorem range_centralFibreInclusion (v : Lattice) (hv : AdmissibleTwist j v) :
    range (D.centralFibreInclusion v hv) = D.projection v hv ⁻¹' {Elliptic.discZero} := by
  rw [D.projection_central_fibre]
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := surfaceProjection_surjective j D.centralPeriod v hv s
    exact ⟨D.centralInclusion x, rfl,
      (D.centralFibreInclusion_surfaceProjection v hv x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (D.mem_range_centralInclusion_iff x).mpr hx
    refine ⟨surfaceProjection j D.centralPeriod v hv y, ?_⟩
    rw [D.centralFibreInclusion_surfaceProjection, hy]

@[simp] theorem projection_centralFibreInclusion (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :
    D.projection v hv (D.centralFibreInclusion v hv x) = Elliptic.discZero := by
  have hx := mem_range_self (f := D.centralFibreInclusion v hv) x
  rw [D.range_centralFibreInclusion] at hx
  exact hx

/-- The actual fixed-period quotient surface is homeomorphic to the
literal central fibre, without changing the fibre's subspace topology. -/
def centralFibreHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j D.centralPeriod v hv ≃ₜ D.projection v hv ⁻¹' {Elliptic.discZero} :=
  (D.centralFibreInclusion_isClosedEmbedding v hv).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (D.range_centralFibreInclusion v hv))

@[simp] theorem centralFibreHomeomorph_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :
    (D.centralFibreHomeomorph v hv x : D.Space v hv) = D.centralFibreInclusion v hv x := rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
