import Wikipedia.HopfProblem.EllipticEquivariantData
import Wikipedia.HopfProblem.EllipticLogGaugeBranches

/-!
# The actual logarithmic period translation

The normalized principal logarithm is used only to select representatives.
Changing it by an integer adds an actual period, so the quotient map is
independent of this choice.  Holomorphicity will follow from the local
logarithms, not from a nonexistent global logarithm on the punctured disc.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

def baseOpen : TopologicalSpace.Opens Disc :=
  ⟨{z | (z : ℂ) ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

abbrev BaseStar := baseOpen

def familyOpen : TopologicalSpace.Opens (Disc × RealTorus₄) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

abbrev FamilyStar (_P : HolomorphicPeriodMap ℂ Disc) := familyOpen

def coverOpen : TopologicalSpace.Opens (Disc × ComplexPlane₂) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

abbrev CoverStar := coverOpen

variable (P : HolomorphicPeriodMap ℂ Disc)

def project (x : CoverStar) : FamilyStar P := ⟨P.quotientMap x, x.2⟩

@[simp] theorem project_coe (x : CoverStar) :
    (project P x : P.TotalSpace) = P.quotientMap x := rfl

@[simp] theorem project_base (x : CoverStar) : (project P x).1.1 = x.1.1 := rfl

theorem project_surjective : Function.Surjective (project P) := by
  intro x
  obtain ⟨y, hy⟩ := P.quotientMap_surjective x.1
  have hy0 : (y.1 : ℂ) ≠ 0 := by
    have hb : y.1 = x.1.1 := congrArg Prod.fst hy
    rw [hb]
    exact x.2
  exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩

theorem project_continuous : Continuous (project P) :=
  (P.quotientMap_localHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

/-- The actual complex period vector associated with the integral coefficient vector. -/
def periodVector (v : Lattice) (z : Disc) : ComplexPlane₂ := P.periodEquiv z (realCast v)

@[simp] theorem periodVector_neg (v : Lattice) (z : Disc) :
    periodVector P (-v) z = -periodVector P v z := by
  change P.periodEquiv z (realCast (-v)) = -P.periodEquiv z (realCast v)
  rw [show realCast (-v) = -realCast v by ext i; simp [realCast], map_neg]

theorem periodVector_mem_lattice (v : Lattice) (z : Disc) :
    periodVector P v z ∈ (P.point z).lattice := by
  rw [← P.periodEquiv_map_lattice z]
  exact Submodule.mem_map.mpr
    ⟨realCast v, (standardLattice_mem_iff _).mpr ⟨v, rfl⟩, rfl⟩

theorem periodVector_holomorphic (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (periodVector P v) :=
  P.holomorphic_periodEquiv_const (realCast v)

/-- Adding an integral multiple of this vector does not change a point
of the actual varying-period family. -/
theorem quotientMap_integer_period (v : Lattice) (z : Disc) (u : ComplexPlane₂)
    (a : ℂ) (n : ℤ) :
    P.quotientMap (z, u + (a + n) • periodVector P v z) =
      P.quotientMap (z, u + a • periodVector P v z) := by
  rw [← P.fibreInclusion_mkQ, ← P.fibreInclusion_mkQ]
  apply congrArg (P.fibreInclusion z)
  apply (Submodule.Quotient.eq _).mpr
  have hp := (P.point z).lattice.smul_mem n (periodVector_mem_lattice P v z)
  convert hp using 1
  rw [add_smul, Int.cast_smul_eq_zsmul]
  abel

theorem quotientMap_eq_of_scalar_int (v : Lattice) (z : Disc) (u : ComplexPlane₂)
    {a b : ℂ} (hab : ∃ n : ℤ, a = b + n) :
    P.quotientMap (z, u + a • periodVector P v z) =
      P.quotientMap (z, u + b • periodVector P v z) := by
  obtain ⟨n, rfl⟩ := hab
  exact quotientMap_integer_period P v z u b n

/-- The representative of the logarithmic section in the real-torus
trivialization; no holomorphicity of this representative is asserted. -/
def sectionCoordinate (v : Lattice) (z : Disc) : RealTorus₄ :=
  standardLattice.mkQ ((P.periodEquiv z).symm (logarithm z • periodVector P v z))

@[simp] theorem sectionCoordinate_neg (v : Lattice) (z : Disc) :
    sectionCoordinate P (-v) z = -sectionCoordinate P v z := by
  simp only [sectionCoordinate, periodVector_neg, smul_neg, map_neg]

/-- The global logarithmic translation on the actual punctured family. -/
def gaugeMap (v : Lattice) (x : FamilyStar P) : FamilyStar P :=
  ⟨(x.1.1, x.1.2 + sectionCoordinate P v x.1.1), x.2⟩

@[simp] theorem gaugeMap_base (v : Lattice) (x : FamilyStar P) :
    (gaugeMap P v x).1.1 = x.1.1 := rfl

@[simp] theorem gaugeMap_neg_gaugeMap (v : Lattice) (x : FamilyStar P) :
    gaugeMap P (-v) (gaugeMap P v x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.1.2 + sectionCoordinate P v x.1.1) + sectionCoordinate P (-v) x.1.1 = x.1.2
    rw [sectionCoordinate_neg, add_neg_cancel_right]

def gaugeEquiv (v : Lattice) : Equiv.Perm (FamilyStar P) where
  toFun := gaugeMap P v
  invFun := gaugeMap P (-v)
  left_inv := gaugeMap_neg_gaugeMap P v
  right_inv x := by simpa only [neg_neg] using gaugeMap_neg_gaugeMap P (-v) x

@[simp] theorem gaugeEquiv_apply (v : Lattice) (x : FamilyStar P) :
    gaugeEquiv P v x = gaugeMap P v x := rfl

@[simp] theorem gaugeEquiv_symm_apply (v : Lattice) (x : FamilyStar P) :
    (gaugeEquiv P v).symm x = gaugeMap P (-v) x := rfl

/-- A representative translation using any selected scalar branch. -/
def gaugeLift (v : Lattice) (a : ℂ → ℂ) (x : CoverStar) : CoverStar :=
  ⟨(x.1.1, x.1.2 + a x.1.1 • periodVector P v x.1.1), x.2⟩

@[simp] theorem gaugeMap_project (v : Lattice) (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v logarithm x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change standardLattice.mkQ ((P.periodEquiv x.1.1).symm x.1.2) +
      standardLattice.mkQ ((P.periodEquiv x.1.1).symm
        (logarithm x.1.1 • periodVector P v x.1.1)) =
    standardLattice.mkQ ((P.periodEquiv x.1.1).symm
      (x.1.2 + logarithm x.1.1 • periodVector P v x.1.1))
  rw [map_add, map_add]

/-- Every local logarithm represents exactly the same global translation. -/
theorem gaugeMap_project_localLog (v : Lattice) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v (localLog z₀) x) := by
  rw [gaugeMap_project]
  apply Subtype.ext
  exact quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
    (logarithm_eq_localLog_add_int hz₀ x.2)

def zeroSection (z : BaseStar) : FamilyStar P := ⟨(z.1, 0), z.2⟩

/-- The source's logarithmic section, as a section of the actual family. -/
def sectionMap (v : Lattice) : BaseStar → FamilyStar P := gaugeMap P v ∘ zeroSection P

@[simp] theorem sectionMap_base (v : Lattice) (z : BaseStar) :
    (sectionMap P v z).1.1 = z.1 := rfl

theorem sectionMap_formula (v : Lattice) (z : BaseStar) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, logarithm z.1 • periodVector P v z.1) := by
  apply Prod.ext
  · rfl
  · exact zero_add _

end Wikipedia.HopfProblem.Elliptic.LogGauge
