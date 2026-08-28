import Wikipedia.HopfProblem.SingularCohomologyFree
import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction

/-!
# Actual cohomological invariance under the elliptic deck action

The finite period cover is invariant under the actual affine cyclic
action.  Functoriality of the actual singular cochain pullback therefore
places every pulled-back cohomology class in the actual deck-invariant
submodule.  No universal-coefficient, torsion-freeness, or invariant-rank
assumption is needed for this assertion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

/-- The actual continuous deck map for a specified element of the affine cyclic action. -/
def surfaceDeckMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) : C(p.val.Torus, p.val.Torus) := by
  letI := affineAction j p v hv.1
  letI := affineAction_continuous j p v hv.1
  exact ⟨fun x => g • x, continuous_const_smul g⟩

@[simp] theorem surfaceDeckMap_apply (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (x : p.val.Torus) :
    letI := affineAction j p v hv.1
    surfaceDeckMap j p v hv g x = g • x := rfl

/-- The affine generator as an actual continuous self-map of the period torus. -/
def surfaceAffineGenerator (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    C(p.val.Torus, p.val.Torus) :=
  ⟨affineBiholomorph j p v, (affineBiholomorph j p v).continuous⟩

/-- The distinguished cyclic element acts by the original affine biholomorphism. -/
theorem surfaceDeckMap_generator (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    surfaceDeckMap j p v hv (CyclicAction.generator j.order) = surfaceAffineGenerator j p v := by
  ext x
  exact affineAction_generator_smul j p v hv.1 x

/-- The actual finite covering projection is unchanged by every actual deck map. -/
theorem periodCover_comp_deckMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) :
    (periodCover j p v hv).comp (surfaceDeckMap j p v hv g) = periodCover j p v hv := by
  let := affineAction j p v hv.1
  ext x
  exact FiniteQuotient.project_smul (CyclicGroup j) p.val.Torus g x

/-- Functoriality proves the actual cohomology-pullback operator is deck invariant. -/
theorem periodCover_cohomology_comp_deckMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (n : ℕ) :
    (singularCohomologyPullback (surfaceDeckMap j p v hv g) n).comp
      (singularCohomologyPullback (periodCover j p v hv) n) =
      singularCohomologyPullback (periodCover j p v hv) n := by
  rw [← singularCohomologyPullback_comp, periodCover_comp_deckMap]

/-- Every actual pulled-back class is fixed by every actual affine deck transformation. -/
theorem periodCover_cohomology_deck_invariant (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (n : ℕ)
    (a : SingularCohomology (Surface j p v hv) n) :
    singularCohomologyPullback (surfaceDeckMap j p v hv g) n
      (singularCohomologyPullback (periodCover j p v hv) n a) =
      singularCohomologyPullback (periodCover j p v hv) n a :=
  DFunLike.congr_fun (periodCover_cohomology_comp_deckMap j p v hv g n) a

/-- In particular, the literal source affine generator fixes every pulled-back class. -/
theorem periodCover_cohomology_affine_invariant (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularCohomology (Surface j p v hv) n) :
    singularCohomologyPullback (surfaceAffineGenerator j p v) n
      (singularCohomologyPullback (periodCover j p v hv) n a) =
      singularCohomologyPullback (periodCover j p v hv) n a := by
  rw [← surfaceDeckMap_generator j p v hv]
  exact periodCover_cohomology_deck_invariant j p v hv _ n a

/-- The actual invariant submodule of the original period torus's integral singular cohomology. -/
def periodCohomologyInvariants (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) : Submodule ℤ (SingularCohomology p.val.Torus n) :=
  ⨅ g : CyclicGroup j,
    LinearMap.ker (singularCohomologyPullback (surfaceDeckMap j p v hv g) n - LinearMap.id)

theorem mem_periodCohomologyInvariants_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) (a : SingularCohomology p.val.Torus n) :
    a ∈ periodCohomologyInvariants j p v hv n ↔
      ∀ g : CyclicGroup j, singularCohomologyPullback (surfaceDeckMap j p v hv g) n a = a := by
  simp only [periodCohomologyInvariants, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

/-- The genuine finite-cover pullback lands in this actual invariant module. -/
theorem periodCover_cohomology_mem_invariants (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) (a : SingularCohomology (Surface j p v hv) n) :
    singularCohomologyPullback (periodCover j p v hv) n a ∈
      periodCohomologyInvariants j p v hv n := by
  rw [mem_periodCohomologyInvariants_iff]
  intro g
  exact periodCover_cohomology_deck_invariant j p v hv g n a

/-- The actual integral cohomology pullback with codomain restricted to deck invariants. -/
def periodCoverCohomologyToInvariants (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    SingularCohomology (Surface j p v hv) n →ₗ[ℤ] periodCohomologyInvariants j p v hv n where
  toFun a := ⟨singularCohomologyPullback (periodCover j p v hv) n a,
    periodCover_cohomology_mem_invariants j p v hv n a⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' r a := by
    apply Subtype.ext
    change singularCohomologyPullback (periodCover j p v hv) n
        ((inferInstance : Module ℤ (SingularCohomology (Surface j p v hv) n)).smul r a) =
      ((inferInstance : Module ℤ (periodCohomologyInvariants j p v hv n)).smul r
        ⟨singularCohomologyPullback (periodCover j p v hv) n a,
          periodCover_cohomology_mem_invariants j p v hv n a⟩).val
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact map_zsmul (singularCohomologyPullback (periodCover j p v hv) n) r a

@[simp] theorem periodCoverCohomologyToInvariants_coe (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularCohomology (Surface j p v hv) n) :
    (periodCoverCohomologyToInvariants j p v hv n a : SingularCohomology p.val.Torus n) =
      singularCohomologyPullback (periodCover j p v hv) n a := rfl

/-- The restricted map retains the genuine evaluation/pushforward
duality on every homology class. -/
theorem periodCoverCohomologyToInvariants_evaluate (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularCohomology (Surface j p v hv) n) (b : SingularHomology p.val.Torus n) :
    singularEvaluation p.val.Torus n (periodCoverCohomologyToInvariants j p v hv n a) b =
      singularEvaluation (Surface j p v hv) n a
        (singularHomologyMap (periodCover j p v hv) n b) :=
  singularEvaluation_naturality (periodCover j p v hv) n a b

end Wikipedia.HopfProblem.Elliptic.HigherHomology
