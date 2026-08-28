import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspQuotient
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyComparison
import Wikipedia.HopfProblem.MappingTorusHomologyHomotopies

/-!
# The actual punctured cusp overlap and its boundary mapping torus

Contracting only logarithmic height identifies the entire punctured cusp
with the mapping torus of the actual integral monodromy `M₀`. The inverse
lands at any specified allowed height. Its cylinder formula uses the
actual varying real period matrices followed by the original toric
exponential quotient. The fibre, endpoint, and base-circle formulas are
therefore formulas for the native whole overlap, not a substitute fibre.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap ContDiff

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp

open SpecialPeriods.CuspFamily CuspUniformization

/-- Affine height interpolation stays in the actual logarithmic half-line. -/
def heightContraction (r : ℝ) (h : Height r) :
    (ContinuousMap.const (Height r) h).Homotopy (ContinuousMap.id (Height r)) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (h : ℝ) + (p.1 : ℝ) * (p.2 : ℝ),
    (convex_Ioi (heightThreshold r)) h.property p.2.property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩
  continuous_toFun :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      continuous_const).add ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change (1 - (0 : ℝ)) * (h : ℝ) + 0 * (x : ℝ) = (h : ℝ)
    simp only [sub_zero, one_mul, zero_mul, add_zero]
  map_one_left x := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) * (h : ℝ) + 1 * (x : ℝ) = (x : ℝ)
    simp only [sub_self, zero_mul, one_mul, zero_add]

/-- Projection onto the mapping torus with the explicit prescribed-height inverse. -/
def heightProductHomotopyEquiv (r : ℝ) (h : Height r) :
    (Height r × Boundary) ≃ₕ Boundary where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const Boundary h).prodMk (ContinuousMap.id Boundary)
  left_inv :=
    (show (ContinuousMap.const (Height r) h).Homotopic (ContinuousMap.id (Height r))
      from ⟨heightContraction r h⟩).prodMap (.refl (ContinuousMap.id Boundary))
  right_inv := .refl (ContinuousMap.id Boundary)

/-- The entire actual integer-monodromy quotient has the genuine boundary
mapping-torus homotopy type, at the specified logarithmic height. -/
def familyMappingTorusHomotopyEquiv (D : Data) (h : Height D.radius) :
    D.Space ≃ₕ Boundary :=
  (familyProductHomeomorph D).toHomotopyEquiv.trans
    (heightProductHomotopyEquiv D.radius h)

@[simp] theorem familyMappingTorusHomotopyEquiv_apply (D : Data) (h : Height D.radius)
    (q : D.Space) :
    familyMappingTorusHomotopyEquiv D h q = (familyProductHomeomorph D q).2 := rfl

@[simp] theorem familyMappingTorusHomotopyEquiv_symm_apply (D : Data)
    (h : Height D.radius) (q : Boundary) :
    (familyMappingTorusHomotopyEquiv D h).symm q =
      (familyProductHomeomorph D).symm (h, q) := rfl

theorem familyMappingTorusHomotopyEquiv_symm_mk (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    (familyMappingTorusHomotopyEquiv D h).symm (MappingTorus.mk monodromy (t, x)) =
      D.quotient (logPoint D.radius D.radius_pos t h, x) :=
  familyProductHomeomorph_symm_mk D h t x

/-- The existing whole-family biholomorphism, retaining its original topologies. -/
def puncturedFamilyHomeomorph (D : Data) :
    D.Space ≃ₜ PuncturedQuotient D.correction D.radius := by
  letI := D.chartedSpace
  letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  exact D.puncturedFamilyBiholomorph.toHomeomorph

@[simp] theorem puncturedFamilyHomeomorph_iteratedCover (D : Data)
    (p : LogCover D.radius) :
    puncturedFamilyHomeomorph D (D.iteratedCover p) =
      puncturedCuspCover D.correction D.radius p := by
  let := D.chartedSpace
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  exact D.puncturedFamilyBiholomorph_iteratedCover p

theorem puncturedFamilyHomeomorph_base (D : Data) (q : D.Space) :
    CuspQuotient.projection D.correction D.radius (puncturedFamilyHomeomorph D q) =
      (D.projection q : ℂ) := by
  let := D.chartedSpace
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  exact D.puncturedFamilyBiholomorph_preserves_base q

/-- The actual varying real period vector is followed by the original
whole-family toric exponential quotient. -/
theorem puncturedFamilyHomeomorph_realCoordinates (D : Data)
    (s : LogBase D.radius) (x : RealPlane₄) :
    puncturedFamilyHomeomorph D (D.quotient (s, standardLattice.mkQ x)) =
      puncturedCuspCover D.correction D.radius
        ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ := by
  have he : D.iteratedCover
      ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ =
        D.quotient (s, standardLattice.mkQ x) := by
    change D.quotient (s, standardLattice.mkQ
      ((D.periods.periodEquiv s).symm (D.periods.periodEquiv s x))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [← he, puncturedFamilyHomeomorph_iteratedCover]

/-- A homeomorphism of the entire native punctured cusp with height times boundary. -/
def puncturedProductHomeomorph (D : Data) :
    PuncturedQuotient D.correction D.radius ≃ₜ Height D.radius × Boundary :=
  (puncturedFamilyHomeomorph D).symm.trans (familyProductHomeomorph D)

/-- The whole actual punctured cusp overlap is homotopy equivalent to the
mapping torus of the proved integral `M₀` monodromy. -/
def puncturedMappingTorusHomotopyEquiv (D : Data) (h : Height D.radius) :
    PuncturedQuotient D.correction D.radius ≃ₕ Boundary :=
  (puncturedFamilyHomeomorph D).symm.toHomotopyEquiv.trans
    (familyMappingTorusHomotopyEquiv D h)

/-- The boundary representative at the prescribed logarithmic height. -/
def boundaryInclusion (D : Data) (h : Height D.radius) :
    C(Boundary, PuncturedQuotient D.correction D.radius) :=
  (puncturedMappingTorusHomotopyEquiv D h).invFun

/-- The literal real-cylinder map into the native whole punctured cusp. -/
def boundaryCylinder (D : Data) (h : Height D.radius) :
    C(ℝ × RealTorus₄, PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp
    ⟨MappingTorus.mk monodromy, MappingTorus.mk_continuous monodromy⟩

theorem boundaryCylinder_apply (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder D h (t, x) =
      puncturedFamilyHomeomorph D (D.quotient (logPoint D.radius D.radius_pos t h, x)) := by
  change puncturedFamilyHomeomorph D
    ((familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x))) = _
  rw [familyProductHomeomorph_symm_mk]

/-- Explicit whole-cylinder formula in the actual complex period coordinates. -/
theorem boundaryCylinder_realCoordinates (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealPlane₄) :
    boundaryCylinder D h (t, standardLattice.mkQ x) =
      puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos t h : ℂ),
          D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) x),
          (logPoint D.radius D.radius_pos t h).property⟩ := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_realCoordinates]

/-- The native overlap map satisfies the actual `M₀` endpoint gluing. -/
theorem boundaryCylinder_endpoint (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder D h (t + 1, x) = boundaryCylinder D h (t, monodromy x) :=
  congrArg (boundaryInclusion D h) (MappingTorus.mk_add_one monodromy t x)

/-- The actual cusp projection on the boundary cylinder is the normalized exponential. -/
theorem boundaryCylinder_base (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (boundaryCylinder D h (t, x)) =
      exponential ((t : ℂ) + (h : ℝ) * Complex.I) := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_base, D.projection_quotient]
  rfl

/-- The actual circle coordinate of a punctured-cusp point. -/
def puncturedBaseCircle (D : Data) :
    C(PuncturedQuotient D.correction D.radius, MappingTorus.Circle) :=
  (familyBaseCircle D).comp
    ⟨(puncturedFamilyHomeomorph D).symm, (puncturedFamilyHomeomorph D).symm.continuous⟩

theorem puncturedBaseCircle_cover (D : Data) (p : LogCover D.radius) :
    puncturedBaseCircle D (puncturedCuspCover D.correction D.radius p) =
      (p.1.1.re : MappingTorus.Circle) := by
  change familyBaseCircle D
    ((puncturedFamilyHomeomorph D).symm (puncturedCuspCover D.correction D.radius p)) = _
  rw [← puncturedFamilyHomeomorph_iteratedCover D p, Homeomorph.symm_apply_apply]
  exact familyBaseCircle_quotient D (D.familyCover p)

theorem puncturedBaseCircle_boundaryCylinder (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    puncturedBaseCircle D (boundaryCylinder D h (t, x)) = (t : MappingTorus.Circle) := by
  rw [boundaryCylinder_apply]
  change familyBaseCircle D ((puncturedFamilyHomeomorph D).symm
    (puncturedFamilyHomeomorph D (D.quotient (logPoint D.radius D.radius_pos t h, x)))) = _
  rw [Homeomorph.symm_apply_apply, familyBaseCircle_quotient, logPoint_re]

/-- The whole-overlap equivalence preserves the actual base-circle coordinate. -/
theorem puncturedMappingTorusHomotopyEquiv_base (D : Data) (h : Height D.radius)
    (q : PuncturedQuotient D.correction D.radius) :
    MappingTorus.base monodromy (puncturedMappingTorusHomotopyEquiv D h q) =
      puncturedBaseCircle D q := rfl

/-- The actual original fibre included at time zero and the prescribed height. -/
def fibreToPunctured (D : Data) (h : Height D.radius) :
    C(RealTorus₄, PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp (MappingTorus.HomologyCover.fibreInclusion monodromy)

@[simp] theorem fibreToPunctured_apply (D : Data) (h : Height D.radius) (x : RealTorus₄) :
    fibreToPunctured D h x = boundaryCylinder D h (0, x) := rfl

theorem fibreToPunctured_realCoordinates (D : Data) (h : Height D.radius) (x : RealPlane₄) :
    fibreToPunctured D h (standardLattice.mkQ x) =
      puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos 0 h : ℂ),
          D.periods.periodEquiv (logPoint D.radius D.radius_pos 0 h) x),
          (logPoint D.radius D.radius_pos 0 h).property⟩ :=
  boundaryCylinder_realCoordinates D h 0 x

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp
