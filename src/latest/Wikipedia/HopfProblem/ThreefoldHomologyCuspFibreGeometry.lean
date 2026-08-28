import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibreSmall
import Wikipedia.HopfProblem.CuspFibreTori
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology

/-!
# The original cusp boundary fibre at every logarithmic height

The whole-family comparison restricts to a homeomorphism from the actual
real period torus onto the literal nonzero cusp fibre.  Its underlying
map is the existing boundary-fibre inclusion, with the original varying
real period vectors.  Interpolating logarithmic height gives a genuine
homotopy between any two such inclusions in the original full cap.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods.CuspFamily CuspUniformization CuspControlledRetraction
open ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyFinitenessCusp

/-- The literal nonzero parameter of the time-zero fibre at the chosen height. -/
def heightParameter (D : Data) (h : Height D.radius) : ℂ :=
  exponential (logPoint D.radius D.radius_pos 0 h)

theorem heightParameter_ne_zero (D : Data) (h : Height D.radius) :
    heightParameter D h ≠ 0 := exponential_ne_zero _

theorem heightParameter_norm_lt (D : Data) (h : Height D.radius) :
    ‖heightParameter D h‖ < D.radius :=
  (mem_logBase _ _).mp (logPoint D.radius D.radius_pos 0 h).property

theorem heightParameter_norm (D : Data) (h : Height D.radius) :
    ‖heightParameter D h‖ = Real.exp (-2 * Real.pi * (h : ℝ)) := by
  change ‖exponential (logPoint D.radius D.radius_pos 0 h)‖ = _
  calc
    _ = Real.exp (Real.log ‖exponential (logPoint D.radius D.radius_pos 0 h)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (exponential_ne_zero _))).symm
    _ = _ := by rw [log_norm_exponential, logPoint_im]

/-- The existing boundary-fibre map, followed by the original full-cap inclusion. -/
def fibreToFull (D : Data) (h : Height D.radius) : C(RealTorus₄, FullSpace D) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(PuncturedQuotient D.correction D.radius, FullSpace D)).comp (fibreToPunctured D h)

@[simp] theorem fibreToFull_apply (D : Data) (h : Height D.radius) (x : RealTorus₄) :
    fibreToFull D h x = (fibreToPunctured D h x).val := rfl

theorem fibreToFull_projection (D : Data) (h : Height D.radius) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (fibreToFull D h x) =
      heightParameter D h := boundaryCylinder_base D h 0 x

theorem fibreToFull_realCoordinates (D : Data) (h : Height D.radius) (x : RealPlane₄) :
    fibreToFull D h (standardLattice.mkQ x) =
      (puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos 0 h : ℂ),
          D.periods.periodEquiv (logPoint D.radius D.radius_pos 0 h) x),
          (logPoint D.radius D.radius_pos 0 h).property⟩).val :=
  congrArg Subtype.val (fibreToPunctured_realCoordinates D h x)

/-- The original real-period fibre parametrization, with codomain its literal fibre. -/
def fibreAtHeight (D : Data) (h : Height D.radius) :
    C(RealTorus₄, ActualQuotientFibre D.correction D.radius (heightParameter D h)) where
  toFun x := ⟨fibreToFull D h x, fibreToFull_projection D h x⟩
  continuous_toFun := (fibreToFull D h).continuous.subtype_mk _

theorem fibreToPunctured_product (D : Data) (h : Height D.radius) (x : RealTorus₄) :
    puncturedProductHomeomorph D (fibreToPunctured D h x) =
      (h, MappingTorus.HomologyCover.fibreInclusion monodromy x) :=
  (puncturedProductHomeomorph D).apply_symm_apply _

/-- No nontrivial mapping-torus deck shift identifies points at time zero. -/
theorem fibreAtHeight_injective (D : Data) (h : Height D.radius) :
    Function.Injective (fibreAtHeight D h) := by
  intro x y hxy
  have hfull : fibreToFull D h x = fibreToFull D h y :=
    congrArg (fun q : ActualQuotientFibre D.correction D.radius (heightParameter D h) => q.val) hxy
  have hp : fibreToPunctured D h x = fibreToPunctured D h y :=
    Subtype.ext hfull
  have hm := congrArg Prod.snd (congrArg (puncturedProductHomeomorph D) hp)
  rw [fibreToPunctured_product, fibreToPunctured_product] at hm
  change MappingTorus.mk monodromy (0, x) = MappingTorus.mk monodromy (0, y) at hm
  obtain ⟨k, hk, he⟩ := (MappingTorus.mk_eq_mk_iff monodromy _ _).mp hm
  have hk0 : k = 0 := by
    have hk' : (k : ℝ) = 0 := by
      change (0 : ℝ) = 0 + (k : ℝ) at hk
      linarith
    exact_mod_cast hk'
  subst k
  simpa using he.symm

/-- Every literal fibre point is represented by the original real-period coordinates. -/
theorem fibreAtHeight_surjective (D : Data) (h : Height D.radius) :
    Function.Surjective (fibreAtHeight D h) := by
  intro q
  let s := logPoint D.radius D.radius_pos 0 h
  have hs : ‖exponential (s : ℂ)‖ < D.radius := (mem_logBase _ _).mp s.property
  have hq : q.val ∈ Set.range
      (fibreMap D.correction D.radius s hs (D.logarithmic_height s) (D.logarithmic_drift s)) := by
    rw [fibreMap_range]
    exact q.property
  obtain ⟨y, hy⟩ := hq
  obtain ⟨z, rfl⟩ := (periodData D.correction s
    (D.logarithmic_height s) (D.logarithmic_drift s)).lattice.mkQ_surjective y
  refine ⟨standardLattice.mkQ ((D.periods.periodEquiv s).symm z), Subtype.ext ?_⟩
  change fibreToFull D h (standardLattice.mkQ ((D.periods.periodEquiv s).symm z)) = q.val
  rw [fibreToFull_realCoordinates]
  change fibreCover D.correction D.radius s hs
    (D.periods.periodEquiv s ((D.periods.periodEquiv s).symm z)) = q.val
  rw [LinearEquiv.apply_symm_apply]
  exact hy

/-- The actual boundary fibre is homeomorphic to the literal original nonzero fibre. -/
def heightFibreHomeomorph (D : Data) (h : Height D.radius) :
    RealTorus₄ ≃ₜ ActualQuotientFibre D.correction D.radius (heightParameter D h) := by
  letI := CuspQuotient.quotient_t2Space D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fibreAtHeight D h)
      ⟨fibreAtHeight_injective D h, fibreAtHeight_surjective D h⟩)
    (fibreAtHeight D h).continuous

@[simp] theorem heightFibreHomeomorph_apply (D : Data) (h : Height D.radius)
    (x : RealTorus₄) :
    (heightFibreHomeomorph D h x).val = fibreToFull D h x := rfl

/-- This homeomorphism preserves the original full-cap fibre inclusion exactly. -/
theorem heightFibreHomeomorph_inclusion (D : Data) (h : Height D.radius) :
    (actualFibreInclusion D (heightParameter D h)).comp
      (heightFibreHomeomorph D h : C(RealTorus₄, _)) = fibreToFull D h := rfl

/-- Height interpolation keeps the same real period-torus coordinate throughout. -/
def fibreHeightHomotopy (D : Data) (h₀ h₁ : Height D.radius) :
    (fibreToFull D h₀).Homotopy (fibreToFull D h₁) where
  toFun p := ((puncturedProductHomeomorph D).symm
    (heightContraction D.radius h₀ (p.1, h₁),
      MappingTorus.HomologyCover.fibreInclusion monodromy p.2)).val
  continuous_toFun := continuous_subtype_val.comp
    ((puncturedProductHomeomorph D).symm.continuous.comp
      (((heightContraction D.radius h₀).continuous.comp
        (continuous_fst.prodMk continuous_const)).prodMk
          ((MappingTorus.HomologyCover.fibreInclusion monodromy).continuous.comp continuous_snd)))
  map_zero_left x := congrArg (fun h : Height D.radius =>
    ((puncturedProductHomeomorph D).symm
      (h, MappingTorus.HomologyCover.fibreInclusion monodromy x)).val)
    ((heightContraction D.radius h₀).map_zero_left h₁)
  map_one_left x := congrArg (fun h : Height D.radius =>
    ((puncturedProductHomeomorph D).symm
      (h, MappingTorus.HomologyCover.fibreInclusion monodromy x)).val)
    ((heightContraction D.radius h₀).map_one_left h₁)

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
