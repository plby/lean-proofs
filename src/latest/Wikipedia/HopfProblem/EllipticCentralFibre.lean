import Wikipedia.HopfProblem.EllipticCentralFamily
import Wikipedia.HopfProblem.EllipticFillings

/-!
# The actual central quotient surface in the logarithmic filling

The holomorphic inclusion of the central torus is equivariant for the
two actual finite actions.  It therefore descends to a holomorphic closed
embedding of the previously constructed quotient surface.  Its image is
exactly the central fibre of the actual proper filling projection.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

/-- The central torus inclusion intertwines every element of the two
cyclic actions, not only their generators. -/
theorem centralInclusion_smul (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : (centralPeriod j).val.Torus) :
    letI := affineAction j (centralPeriod j) v hv
    letI := familyAction j v hv
    centralInclusion j (g • x) = g • centralInclusion j x := by
  let := affineAction j (centralPeriod j) v hv
  let := familyAction j v hv
  change centralInclusion j ((affinePermutation j (centralPeriod j) v ^ g.toAdd.val) x) =
    (familyPermutation j v ^ g.toAdd.val) (centralInclusion j x)
  exact (familyPermutation_pow_centralInclusion j v g.toAdd.val x).symm

/-- The quotient of the central inclusion is constant on the source orbits. -/
theorem centralInclusion_quotient_invariant (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (x : (centralPeriod j).val.Torus) :
    letI := affineAction j (centralPeriod j) v hv.1
    fillingQuotient j v hv (centralInclusion j (g • x)) =
      fillingQuotient j v hv (centralInclusion j x) := by
  let := affineAction j (centralPeriod j) v hv.1
  let := familyAction j v hv.1
  rw [centralInclusion_smul]
  exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g (centralInclusion j x)

/-- The induced inclusion of the actual quotient surface into the actual filling. -/
def centralFibreInclusion (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j (centralPeriod j) v hv → Filling j v hv := by
  letI := affineAction j (centralPeriod j) v hv.1
  exact FiniteQuotient.descend (fillingQuotient j v hv ∘ centralInclusion j)
    (centralInclusion_quotient_invariant j v hv)

@[simp] theorem centralFibreInclusion_surfaceProjection (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : (centralPeriod j).val.Torus) :
    centralFibreInclusion j v hv (surfaceProjection j (centralPeriod j) v hv x) =
      fillingQuotient j v hv (centralInclusion j x) := rfl

theorem centralFibreInclusion_continuous (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : Continuous (centralFibreInclusion j v hv) := by
  let := affineAction j (centralPeriod j) v hv.1
  exact FiniteQuotient.descend_continuous (fillingQuotient j v hv ∘ centralInclusion j)
    (centralInclusion_quotient_invariant j v hv)
    ((fillingQuotient_continuous j v hv).comp (centralInclusion_continuous j))

/-- No new identifications are introduced on the central torus by the
action on the surrounding family. -/
theorem centralFibreInclusion_injective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Injective (centralFibreInclusion j v hv) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := surfaceProjection_surjective j (centralPeriod j) v hv a
  obtain ⟨y, rfl⟩ := surfaceProjection_surjective j (centralPeriod j) v hv b
  rw [centralFibreInclusion_surfaceProjection, centralFibreInclusion_surfaceProjection] at hab
  let := affineAction j (centralPeriod j) v hv.1
  let := familyAction j v hv.1
  obtain ⟨g, hg⟩ :=
    (FiniteQuotient.project_eq_iff_mem_orbit (CyclicGroup j) (Family j) _ _).mp hab
  apply (FiniteQuotient.project_eq_iff_mem_orbit
    (CyclicGroup j) (centralPeriod j).val.Torus x y).mpr
  refine ⟨g, (centralInclusion_injective j) ?_⟩
  rw [centralInclusion_smul]
  exact hg

theorem centralFibreInclusion_isClosedEmbedding (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsClosedEmbedding (centralFibreInclusion j v hv) :=
  (centralFibreInclusion_continuous j v hv).isClosedEmbedding
    (centralFibreInclusion_injective j v hv)

/-- The descended inclusion is holomorphic for both constructed complex atlases. -/
theorem centralFibreInclusion_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ FamilyModel) ω (centralFibreInclusion j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := affineAction j (centralPeriod j) v hv.1
  let := affineAction_continuous j (centralPeriod j) v hv.1
  let := affineAction_free j (centralPeriod j) v hv
  exact FiniteQuotient.descend_holomorphic (fillingQuotient j v hv ∘ centralInclusion j)
    (centralInclusion_quotient_invariant j v hv) (modelWithCornersSelf ℂ FamilyModel)
    ((fillingQuotient_holomorphic j v hv).comp (centralInclusion_holomorphic j))

/-- The image is exactly the actual central fibre of the proper filling map. -/
theorem range_centralFibreInclusion (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    range (centralFibreInclusion j v hv) = fillingProjection j v hv ⁻¹' {Elliptic.discZero} := by
  rw [fillingProjection_central_fibre]
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := surfaceProjection_surjective j (centralPeriod j) v hv s
    exact ⟨centralInclusion j x, rfl, (centralFibreInclusion_surfaceProjection j v hv x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (mem_range_centralInclusion_iff j x).mpr hx
    refine ⟨surfaceProjection j (centralPeriod j) v hv y, ?_⟩
    rw [centralFibreInclusion_surfaceProjection, hy]

@[simp] theorem fillingProjection_centralFibreInclusion (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    fillingProjection j v hv (centralFibreInclusion j v hv x) = Elliptic.discZero := by
  have hx : centralFibreInclusion j v hv x ∈ range (centralFibreInclusion j v hv) :=
    mem_range_self x
  rw [range_centralFibreInclusion] at hx
  exact hx

/-- The previously constructed compact complex surface is homeomorphic
to the actual central fibre with its subspace topology. -/
def centralFibreHomeomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j (centralPeriod j) v hv ≃ₜ fillingProjection j v hv ⁻¹' {Elliptic.discZero} :=
  (centralFibreInclusion_isClosedEmbedding j v hv).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_centralFibreInclusion j v hv))

@[simp] theorem centralFibreHomeomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    (centralFibreHomeomorph j v hv x : Filling j v hv) = centralFibreInclusion j v hv x := rfl

end Wikipedia.HopfProblem.Elliptic
