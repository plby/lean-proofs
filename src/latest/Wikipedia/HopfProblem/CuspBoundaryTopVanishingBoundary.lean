import Wikipedia.HopfProblem.CuspBoundaryGammaZeroBoundaryMap
import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

/-!
# The literal gamma-zero boundary at every cusp height

These maps use the already constructed invariant three-torus mapping
torus and its actual inclusion in the full cusp boundary.  Height is
changed inside the original punctured cusp product, without changing
the boundary point.  The whole boundary, not just its time-zero fibre,
therefore has a genuine homotopy at any two allowed heights.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open SpecialPeriods.CuspFamily CuspUniformization CuspRetraction
open ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyCuspFibre
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual gamma-zero sub-mapping-torus included in the original punctured cusp. -/
def gammaBoundaryToPunctured (D : Data) (h : Height D.radius) :
    C(CuspBoundaryGammaZero.Boundary, PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp CuspBoundaryGammaZero.boundaryMap

/-- The same actual map into the entire original fixed-radius cusp cap. -/
def gammaBoundaryToFull (D : Data) (h : Height D.radius) :
    C(CuspBoundaryGammaZero.Boundary, CuspQuotient.QuotientSpace D.correction D.radius) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(PuncturedQuotient D.correction D.radius,
      CuspQuotient.QuotientSpace D.correction D.radius)).comp (gammaBoundaryToPunctured D h)

@[simp] theorem gammaBoundaryToFull_apply (D : Data) (h : Height D.radius)
    (q : CuspBoundaryGammaZero.Boundary) :
    gammaBoundaryToFull D h q = (gammaBoundaryToPunctured D h q).val := rfl

theorem gammaBoundaryToPunctured_mk (D : Data) (h : Height D.radius)
    (t : ℝ) (x : ProductTorus 3) :
    gammaBoundaryToPunctured D h
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy (t, x)) =
      boundaryCylinder D h (t, CuspBoundaryGammaZero.fibreMap x) := rfl

/-- Original real period representatives retain their literal zero first coordinate. -/
theorem gammaBoundaryToFull_realCoordinates (D : Data) (h : Height D.radius)
    (t : ℝ) (x : Fin 3 → ℝ) :
    gammaBoundaryToFull D h
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
          (t, coordinateProjection 3 x)) =
      (puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos t h : ℂ),
          D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) (Fin.cons 0 x)),
          (logPoint D.radius D.radius_pos t h).property⟩).val := by
  change (gammaBoundaryToPunctured D h
    (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
      (t, coordinateProjection 3 x))).val = _
  rw [gammaBoundaryToPunctured_mk, CuspBoundaryGammaZero.fibreMap_coordinateProjection]
  exact congrArg Subtype.val (boundaryCylinder_realCoordinates D h t (Fin.cons 0 x))

/-- All real angular positions have the same genuine norm at a fixed height. -/
theorem logPoint_exponential_norm (D : Data) (h : Height D.radius) (t : ℝ) :
    ‖exponential (logPoint D.radius D.radius_pos t h : ℂ)‖ =
      ‖heightParameter D h‖ := by
  rw [heightParameter_norm]
  calc
    _ = Real.exp (Real.log ‖exponential (logPoint D.radius D.radius_pos t h : ℂ)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (exponential_ne_zero _))).symm
    _ = _ := by rw [log_norm_exponential, logPoint_im]

theorem gammaBoundaryToFull_projection_norm (D : Data) (h : Height D.radius)
    (q : CuspBoundaryGammaZero.Boundary) :
    ‖CuspQuotient.projection D.correction D.radius (gammaBoundaryToFull D h q)‖ =
      ‖heightParameter D h‖ := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective CuspBoundaryGammaZero.restrictedMonodromy q
  change ‖CuspQuotient.projection D.correction D.radius
    (gammaBoundaryToPunctured D h
      (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy (t, x)))‖ = _
  rw [gammaBoundaryToPunctured_mk, boundaryCylinder_base]
  exact logPoint_exponential_norm D h t

/-- The original whole sub-boundary lies in each closed tube containing its norm circle. -/
def gammaBoundaryToClosed (D : Data) (h : Height D.radius) (η : ℝ)
    (hη : ‖heightParameter D h‖ ≤ η) :
    C(CuspBoundaryGammaZero.Boundary, ClosedQuotient D.correction D.radius η) where
  toFun q := ⟨gammaBoundaryToFull D h q, by
    rw [gammaBoundaryToFull_projection_norm]
    exact hη⟩
  continuous_toFun := (gammaBoundaryToFull D h).continuous.subtype_mk _

@[simp] theorem gammaBoundaryToClosed_coe (D : Data) (h : Height D.radius) (η : ℝ)
    (hη : ‖heightParameter D h‖ ≤ η) (q : CuspBoundaryGammaZero.Boundary) :
    (gammaBoundaryToClosed D h η hη q).val = gammaBoundaryToFull D h q := rfl

/-- Height interpolation keeps the same actual point of the whole invariant sub-mapping-torus. -/
def gammaBoundaryHeightHomotopy (D : Data) (h₀ h₁ : Height D.radius) :
    (gammaBoundaryToFull D h₀).Homotopy (gammaBoundaryToFull D h₁) where
  toFun p := ((puncturedProductHomeomorph D).symm
    (heightContraction D.radius h₀ (p.1, h₁), CuspBoundaryGammaZero.boundaryMap p.2)).val
  continuous_toFun := continuous_subtype_val.comp
    ((puncturedProductHomeomorph D).symm.continuous.comp
      (((heightContraction D.radius h₀).continuous.comp
        (continuous_fst.prodMk continuous_const)).prodMk
          (CuspBoundaryGammaZero.boundaryMap.continuous.comp continuous_snd)))
  map_zero_left q := congrArg (fun h : Height D.radius =>
    ((puncturedProductHomeomorph D).symm (h, CuspBoundaryGammaZero.boundaryMap q)).val)
      ((heightContraction D.radius h₀).map_zero_left h₁)
  map_one_left q := congrArg (fun h : Height D.radius =>
    ((puncturedProductHomeomorph D).symm (h, CuspBoundaryGammaZero.boundaryMap q)).val)
      ((heightContraction D.radius h₀).map_one_left h₁)

theorem gammaBoundaryToFull_homology_eq (D : Data) (h₀ h₁ : Height D.radius) (n : ℕ) :
    singularHomologyMap (gammaBoundaryToFull D h₀) n =
      singularHomologyMap (gammaBoundaryToFull D h₁) n :=
  homotopy_homologyMap (gammaBoundaryHeightHomotopy D h₀ h₁) n

/-- The global filling coefficient is exactly this original-height map, not a new cap model. -/
theorem gammaBoundaryToFilling_eq :
    (ThreefoldOverlapMappingTorus.boundaryToFilling none).comp
        CuspBoundaryGammaZero.boundaryMap =
      gammaBoundaryToFull specialData specialHeight := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  rfl

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
