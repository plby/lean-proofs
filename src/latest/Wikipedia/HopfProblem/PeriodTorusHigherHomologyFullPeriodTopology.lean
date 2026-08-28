import Wikipedia.HopfProblem.PeriodTorusHigherHomologyFullPeriodCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusFirstHomology
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Arbitrary full period tori as products of four actual circles

Every full period matrix gives an actual additive homeomorphism from its
complex lattice quotient to the product of four additive circles. No
special period-domain form is required. The ordered integral pair `(m,n)`
has circle coordinates `(m₀,m₁,n₀,n₁)`, and the homeomorphism preserves the
actual positive straight period loops in exactly that order.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open Elliptic FirstHurewicz PeriodTorusHigherHomology

variable (p : FullPeriodMatrix)

/-- The full real period isomorphism, with coordinate order
`(m₀,m₁,n₀,n₁)` rather than the alternate `(n,m)` order. -/
def coordinatePeriodEquiv : (Fin 4 → ℝ) ≃L[ℝ] ComplexPlane₂ :=
  (realCoordinatesEquiv.symm.trans p.periodEquiv).toContinuousLinearEquiv

@[simp] theorem coordinatePeriodEquiv_apply (x : Fin 4 → ℝ) :
    p.coordinatePeriodEquiv x = p.periodLinear (realCoordinatesEquiv.symm x) := rfl

/-- Integral coordinate tuples map to exactly the given periods `m + Z n`. -/
theorem coordinatePeriodEquiv_integer (c : IntegerPeriods) :
    p.coordinatePeriodEquiv (fun i => (integerCoordinatesEquiv c i : ℝ)) =
      p.periodVector c := by
  rw [coordinatePeriodEquiv_apply, ← realCoordinatesEquiv_intCast,
    LinearEquiv.symm_apply_apply]
  exact (p.periodVector_eq_periodLinear c).symm

/-- The inverse full-period map recovers the ordered integral coordinates
of each actual period vector. -/
@[simp] theorem coordinatePeriodEquiv_symm_periodVector (c : IntegerPeriods) :
    p.coordinatePeriodEquiv.symm (p.periodVector c) =
      fun i => (integerCoordinatesEquiv c i : ℝ) := by
  rw [← p.coordinatePeriodEquiv_integer c, ContinuousLinearEquiv.symm_apply_apply]

/-- The standard integral lattice is carried onto the actual full period lattice. -/
theorem coordinatePeriodEquiv_map_standardLattice :
    standardLattice.map (p.coordinatePeriodEquiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.lattice := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, rfl⟩ := (standardLattice_mem_iff x).mp hx
    have hv := p.coordinatePeriodEquiv_integer (integerCoordinatesEquiv.symm v)
    rw [LinearEquiv.apply_symm_apply] at hv
    change p.coordinatePeriodEquiv (fun i => (v i : ℝ)) ∈ p.lattice
    rw [hv]
    exact p.periodVector_mem_lattice _
  · intro hz
    obtain ⟨m, n, hmn⟩ := (p.mem_lattice_iff z).mp hz
    refine ⟨realCast (integerCoordinatesEquiv (m, n)),
      (standardLattice_mem_iff _).mpr ⟨integerCoordinatesEquiv (m, n), rfl⟩, ?_⟩
    exact (p.coordinatePeriodEquiv_integer (m, n)).trans hmn.symm

/-- The actual quotient of the real coordinate space is integrally
linearly equivalent to the actual complex full-period quotient. -/
def flatTorusLinearEquiv : RealTorus₄ ≃ₗ[ℤ] p.Torus :=
  Submodule.Quotient.equiv standardLattice p.lattice
    (p.coordinatePeriodEquiv.toLinearEquiv.restrictScalars ℤ)
    p.coordinatePeriodEquiv_map_standardLattice

@[simp] theorem flatTorusLinearEquiv_mkQ (x : Fin 4 → ℝ) :
    p.flatTorusLinearEquiv (standardLattice.mkQ x) =
      p.lattice.mkQ (p.coordinatePeriodEquiv x) := rfl

/-- The quotient equivalence is a genuine homeomorphism for the quotient topologies. -/
def flatTorusHomeomorph : RealTorus₄ ≃ₜ p.Torus where
  toEquiv := p.flatTorusLinearEquiv.toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact p.lattice.continuous_mkQ.comp p.coordinatePeriodEquiv.continuous
  continuous_invFun := by
    apply p.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp p.coordinatePeriodEquiv.symm.continuous

@[simp] theorem flatTorusHomeomorph_mkQ (x : Fin 4 → ℝ) :
    p.flatTorusHomeomorph (standardLattice.mkQ x) =
      p.lattice.mkQ (p.coordinatePeriodEquiv x) := rfl

@[simp] theorem flatTorusHomeomorph_symm_mkQ (z : ComplexPlane₂) :
    p.flatTorusHomeomorph.symm (p.lattice.mkQ z) =
      standardLattice.mkQ (p.coordinatePeriodEquiv.symm z) := rfl

/-- An arbitrary full complex period torus is homeomorphic to four actual circles. -/
def productTorusHomeomorph : p.Torus ≃ₜ ProductTorus 4 :=
  p.flatTorusHomeomorph.symm.trans flatTorusCircleHomeomorph

/-- The same actual coordinate map as an integral linear equivalence. -/
def productTorusLinearEquiv : p.Torus ≃ₗ[ℤ] ProductTorus 4 :=
  p.flatTorusLinearEquiv.symm.trans
    (LinearEquiv.ofBijective flatTorusCircleMap
      ⟨flatTorusCircleMap_injective, flatTorusCircleMap_surjective⟩)

@[simp] theorem productTorusLinearEquiv_apply (x : p.Torus) :
    p.productTorusLinearEquiv x = p.productTorusHomeomorph x := rfl

/-- The topological coordinate equivalence also preserves the actual additive group law. -/
def productTorusAddEquiv : p.Torus ≃+ ProductTorus 4 :=
  p.productTorusLinearEquiv.toAddEquiv

@[simp] theorem productTorusAddEquiv_apply (x : p.Torus) :
    p.productTorusAddEquiv x = p.productTorusHomeomorph x := rfl

/-- The formula on every covering-space representative fixes the actual map. -/
@[simp] theorem productTorusHomeomorph_mkQ (z : ComplexPlane₂) :
    p.productTorusHomeomorph (p.lattice.mkQ z) =
      coordinateProjection 4 (p.coordinatePeriodEquiv.symm z) := rfl

@[simp] theorem productTorusHomeomorph_coordinate_mkQ (x : Fin 4 → ℝ) :
    p.productTorusHomeomorph (p.lattice.mkQ (p.coordinatePeriodEquiv x)) =
      coordinateProjection 4 x := by
  rw [p.productTorusHomeomorph_mkQ, ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem productTorusHomeomorph_zero :
    p.productTorusHomeomorph 0 = 0 := p.productTorusLinearEquiv.map_zero

@[simp] theorem productTorusHomeomorph_add (x y : p.Torus) :
    p.productTorusHomeomorph (x + y) =
      p.productTorusHomeomorph x + p.productTorusHomeomorph y :=
  p.productTorusLinearEquiv.map_add x y

@[simp] theorem productTorusHomeomorph_zsmul (k : ℤ) (x : p.Torus) :
    p.productTorusHomeomorph (k • x) = k • p.productTorusHomeomorph x :=
  p.productTorusLinearEquiv.map_smul k x

/-- The inverse coordinate homeomorphism preserves addition as well. -/
@[simp] theorem productTorusHomeomorph_symm_add (x y : ProductTorus 4) :
    p.productTorusHomeomorph.symm (x + y) =
      p.productTorusHomeomorph.symm x + p.productTorusHomeomorph.symm y := by
  apply p.productTorusHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, p.productTorusHomeomorph_add,
    Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- Every actual straight period loop has the positive circle-coordinate
formula with the original `(m,n)` marking. -/
theorem productTorusHomeomorph_periodLoop_apply (c : IntegerPeriods) (t : unitInterval) :
    p.productTorusHomeomorph (p.periodLoop c t) =
      coordinatePeriodLoop 4 (integerCoordinatesEquiv c) t := by
  rw [p.periodLoop_apply, p.productTorusHomeomorph_mkQ, map_smul,
    p.coordinatePeriodEquiv_symm_periodVector]
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

/-- The marked loop comparison holds for actual paths, with only the
definitional zero-basepoint transport required by the coordinate map. -/
theorem productTorusHomeomorph_periodLoop (c : IntegerPeriods) :
    (p.periodLoop c).map p.productTorusHomeomorph.continuous =
      (coordinatePeriodLoop 4 (integerCoordinatesEquiv c)).cast
        p.productTorusHomeomorph_zero p.productTorusHomeomorph_zero := by
  apply Path.ext
  funext t
  exact p.productTorusHomeomorph_periodLoop_apply c t

/-- The genuine induced singular `H₁` map retains the positive marked period classes. -/
theorem productTorusHomeomorph_inducedHomology_periodLoop (c : IntegerPeriods) :
    inducedHomology (p.productTorusHomeomorph : C(_, _))
        (loopHomologyClass (p.periodLoop c)) =
      loopHomologyClass (coordinatePeriodLoop 4 (integerCoordinatesEquiv c)) := by
  rw [inducedHomology_loopHomologyClass, p.productTorusHomeomorph_periodLoop]
  rfl

/-- The existing arbitrary full-period first-homology marking is compatible
with the actual topological circle-coordinate comparison. -/
theorem productTorusHomeomorph_inducedHomology_singularH1Equiv (c : IntegerPeriods) :
    inducedHomology (p.productTorusHomeomorph : C(_, _)) (p.singularH1Equiv.symm c) =
      loopHomologyClass (coordinatePeriodLoop 4 (integerCoordinatesEquiv c)) := by
  rw [p.singularH1Equiv_symm_apply]
  exact p.productTorusHomeomorph_inducedHomology_periodLoop c

end Wikipedia.HopfProblem.FullPeriodMatrix
