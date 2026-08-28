import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology
import Wikipedia.HopfProblem.EllipticEquivariantData
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic

/-!
# The literal elliptic coinvariant-circle coordinate

The first real-period circle coordinate of the original affine elliptic
action changes by exactly `γ(v) / m`.  Consequently the actual covering
family maps equivariantly to the disc times this circle.  Real times of
the original vertical flow translate only the fourth real-period column,
so this map is invariant under that flow.

All formulas use the existing standard-lattice quotient, affine actions,
and varying-period family; no replacement torus or assumed equivariance
is involved.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticGamma

open Elliptic SpecialPeriods TrianglePeriodFamily.GammaZero

theorem fibreGamma_surjective : Function.Surjective fibreGamma := by
  intro c
  refine ⟨PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (Fin.cons c 0), ?_⟩
  change PeriodTorusHigherHomology.flatTorusCircleHomeomorph
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (Fin.cons c 0)) 0 = c
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem fibreGamma_isOpenMap : IsOpenMap fibreGamma :=
  (isOpenMap_eval (0 : Fin 4)).comp
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph.isOpenMap

/-- Addition in the original torus adds its literal first circle coordinates. -/
theorem fibreGamma_add (x y : RealTorus₄) :
    fibreGamma (x + y) = fibreGamma x + fibreGamma y := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective y
  rw [← map_add, fibreGamma_mkQ, fibreGamma_mkQ, fibreGamma_mkQ]
  exact AddCircle.coe_add (1 : ℝ) (u 0) (v 0)

/-- The actual affine elliptic generator has exactly the prescribed circle shift. -/
theorem fibreGamma_flatTorusAffine (j : Kind) (v : Lattice) (x : RealTorus₄) :
    fibreGamma (flatTorusAffine j v x) =
      fibreGamma x + (((v 0 : ℝ) / j.order : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [flatTorusAffine_mkQ, fibreGamma_mkQ, fibreGamma_mkQ]
  have h : flatAffine j v u 0 = u 0 + (v 0 : ℝ) / j.order := by
    change flatLinear j u 0 + (1 / (j.order : ℝ)) * (v 0 : ℝ) = _
    rw [flatLinear_gamma]
    ring
  rw [h, AddCircle.coe_add]

/-- The circle shift of every iterate, without requiring an invariant twist. -/
theorem fibreGamma_flatTorusAffine_iterate (j : Kind) (v : Lattice) (r : ℕ)
    (x : RealTorus₄) :
    fibreGamma ((flatTorusAffine j v)^[r] x) =
      fibreGamma x + (((r : ℝ) * (v 0 : ℝ) / j.order : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [flatTorusAffine_iterate_mkQ, fibreGamma_mkQ, fibreGamma_mkQ,
    flatAffine_iterate_gamma]
  have h : ((r : ℝ) / j.order) * (γ v : ℝ) = (r : ℝ) * (v 0 : ℝ) / j.order := by
    change ((r : ℝ) / j.order) * (v 0 : ℝ) = _
    ring
  rw [h, AddCircle.coe_add]

/-- The two native twists have first coordinates `+1` and `-1`. -/
theorem twist_gamma_eq_one_or_neg_one (j : Kind) :
    j.twist 0 = 1 ∨ j.twist 0 = -1 := by
  cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem three_twist_gamma : Kind.three.twist 0 = 1 := rfl

@[simp] theorem four_twist_gamma : Kind.four.twist 0 = -1 := rfl

/-- Normalize the first circle by the sign of the actual elliptic twist. -/
def normalizedGamma (j : Kind) : C(RealTorus₄, AddCircle (1 : ℝ)) :=
  ⟨fun x => j.twist 0 • fibreGamma x, by
    cases j
    · simpa only [three_twist_gamma, one_zsmul] using fibreGamma.continuous
    · simp only [four_twist_gamma, neg_one_zsmul]
      exact continuous_neg.comp fibreGamma.continuous⟩

@[simp] theorem normalizedGamma_apply (j : Kind) (x : RealTorus₄) :
    normalizedGamma j x = j.twist 0 • fibreGamma x := rfl

/-- Both native main generators translate the normalized coordinate by `+1/m`. -/
theorem normalizedGamma_flatTorusAffine (j : Kind) (x : RealTorus₄) :
    normalizedGamma j (flatTorusAffine j j.twist x) =
      normalizedGamma j x + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  rw [normalizedGamma_apply, normalizedGamma_apply, fibreGamma_flatTorusAffine, smul_add]
  congr 1
  cases j <;>
    simp only [three_twist_gamma, four_twist_gamma, one_zsmul, neg_one_zsmul,
      Int.cast_neg, Int.cast_one, neg_div, AddCircle.coe_neg, neg_neg]

/-- An arbitrary translation with zero first real coordinate is invisible to γ. -/
theorem fibreGamma_add_mkQ_of_zero (x : RealTorus₄) (u : RealPlane₄) (hu : u 0 = 0) :
    fibreGamma (x + standardLattice.mkQ u) = fibreGamma x := by
  rw [fibreGamma_add, fibreGamma_mkQ, hu, AddCircle.coe_zero, add_zero]

/-- The literal fourth-coordinate translation preserves the original γ circle. -/
theorem fibreGamma_add_delta (x : RealTorus₄) (t : ℝ) :
    fibreGamma (x + standardLattice.mkQ (Pi.single (3 : Fin 4) t)) = fibreGamma x := by
  apply fibreGamma_add_mkQ_of_zero
  simp

/-- The same equality directly on original real representatives. -/
theorem fibreGamma_mkQ_add_delta (x : RealPlane₄) (t : ℝ) :
    fibreGamma (standardLattice.mkQ (x + Pi.single (3 : Fin 4) t)) =
      (x 0 : AddCircle (1 : ℝ)) := by
  rw [map_add, fibreGamma_add_delta, fibreGamma_mkQ]

/-- The native period-basis version of the delta translation formula. -/
theorem fibreGamma_add_smul_delta (x : RealTorus₄) (t : ℝ) :
    fibreGamma (x + standardLattice.mkQ (t • Pi.basisFun ℝ (Fin 4) 3)) =
      fibreGamma x := by
  apply fibreGamma_add_mkQ_of_zero
  simp [Pi.basisFun_apply]

section PeriodFlow

open Threefold.VerticalAction

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- A real time of the original complex vertical flow is precisely the fourth
real-period vector, for every point of the varying family. -/
theorem inverse_vector_real (b : B) (t : ℝ) :
    (P.periodEquiv b).symm (Period.vector (t : ℂ)) =
      t • Pi.basisFun ℝ (Fin 4) 3 := by
  apply (P.periodEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, Period.periodEquiv_delta]
  ext i
  fin_cases i <;> simp [Period.vector]

/-- Pointwise equality with the original native vertical flow, not merely an
equality of induced homology classes. -/
theorem fibreGamma_periodFlow_real (t : ℝ) (x : P.TotalSpace) :
    fibreGamma (Period.flow P (t : ℂ) x).2 = fibreGamma x.2 := by
  change fibreGamma
    (x.2 + standardLattice.mkQ ((P.periodEquiv x.1).symm (Period.vector (t : ℂ)))) = _
  rw [inverse_vector_real, fibreGamma_add_smul_delta]

/-- The normalized coordinate is invariant under the same original delta flow. -/
theorem normalizedGamma_periodFlow_real (j : Kind) (t : ℝ) (x : P.TotalSpace) :
    normalizedGamma j (Period.flow P (t : ℂ) x).2 = normalizedGamma j x.2 := by
  rw [normalizedGamma_apply, normalizedGamma_apply, fibreGamma_periodFlow_real]

end PeriodFlow

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual full covering family mapped to its base and coinvariant circle. -/
def coverMap : C(D.TotalSpace, Disc × AddCircle (1 : ℝ)) :=
  ⟨fun x => (x.1, fibreGamma x.2),
    continuous_fst.prodMk (fibreGamma.continuous.comp continuous_snd)⟩

@[simp] theorem coverMap_apply (x : D.TotalSpace) :
    coverMap D x = (x.1, fibreGamma x.2) := rfl

@[simp] theorem coverMap_mkQ (s : Disc) (x : RealPlane₄) :
    coverMap D (s, standardLattice.mkQ x) =
      (s, (x 0 : AddCircle (1 : ℝ))) := by
  rw [coverMap_apply, fibreGamma_mkQ]

theorem coverMap_surjective : Function.Surjective (coverMap D) := by
  rintro ⟨s, c⟩
  obtain ⟨x, hx⟩ := fibreGamma_surjective c
  exact ⟨(s, x), Prod.ext rfl hx⟩

theorem coverMap_isOpenMap : IsOpenMap (coverMap D) := by
  change IsOpenMap (Prod.map (id : Disc → Disc) fibreGamma)
  exact (Homeomorph.refl Disc).isOpenMap.prodMap fibreGamma_isOpenMap

/-- The covering-family map is a genuine open topological quotient. -/
theorem coverMap_isOpenQuotientMap : IsOpenQuotientMap (coverMap D) :=
  ⟨coverMap_surjective D, (coverMap D).continuous, coverMap_isOpenMap D⟩

/-- Exact equivariance with the literal affine generator of the full family. -/
theorem coverMap_permutation (v : Lattice) (x : D.TotalSpace) :
    coverMap D (D.permutation v x) =
      (familyRotation j x.1,
        fibreGamma x.2 + (((v 0 : ℝ) / j.order : ℝ) : AddCircle (1 : ℝ))) := by
  rw [D.permutation_apply, coverMap_apply, fibreGamma_flatTorusAffine]

/-- Exact equivariance with every element of the original finite cyclic action. -/
theorem coverMap_action (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    coverMap D (g • x) =
      ((familyRotation j)^[g.toAdd.val] x.1,
        fibreGamma x.2 +
          (((g.toAdd.val : ℝ) * (v 0 : ℝ) / j.order : ℝ) : AddCircle (1 : ℝ))) := by
  let := D.action v hv
  rw [D.action_apply, coverMap_apply, fibreGamma_flatTorusAffine_iterate]

/-- The full covering-family map is invariant under every real time of the
native vertical flow, including over the central elliptic fibre. -/
theorem coverMap_periodFlow_real (t : ℝ) (x : D.TotalSpace) :
    coverMap D (Threefold.VerticalAction.Period.flow D.periods (t : ℂ) x) =
      coverMap D x := by
  apply Prod.ext
  · rfl
  · exact fibreGamma_periodFlow_real D.periods t x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticGamma
