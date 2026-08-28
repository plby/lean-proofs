import Wikipedia.HopfProblem.FundamentalGroupVanKampenCover
import Wikipedia.HopfProblem.FundamentalGroupVanKampenPathSubtypes
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerationCore

/-!
# Local path values from compatible fundamental-group homomorphisms

Paths are closed by the constructed coherent based paths.  Their actual
homotopy classes in each open subspace are evaluated by the given group
homomorphism.  Compatibility on the intersection proves agreement for
every local path, not just for one chosen set of loops.
-/

noncomputable section

open Set Path.Homotopic.Quotient
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

open TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

namespace TwoOpenCover

variable (D : TwoOpenCover X)

/-- The coherent based path, regarded as a path in one of the open subspaces. -/
def chartPath (i : Bool) (x : D.chart i) : Path (D.baseChart i) x :=
  pathIn (D.pathTo x.val) (D.base_mem_chart i) x.property
    (D.pathTo_mem i x.val x.property)

@[simp] theorem chartPath_base (i : Bool) :
    D.chartPath i (D.baseChart i) = Path.refl (D.baseChart i) := by
  simp only [chartPath, baseChart, D.pathTo_base, pathIn_refl]

def chartPathClass (i : Bool) (x : D.chart i) :
    Path.Homotopic.Quotient (D.baseChart i) x :=
  Path.Homotopic.Quotient.mk (D.chartPath i x)

@[simp] theorem chartPathClass_base (i : Bool) :
    D.chartPathClass i (D.baseChart i) = refl (D.baseChart i) := by
  simp only [chartPathClass, D.chartPath_base, mk_refl]

/-- Close an intrinsic local path to an actual local fundamental-group element. -/
def closePath (i : Bool) {x y : D.chart i} (p : Path x y) :
    FundamentalGroup (D.chart i) (D.baseChart i) :=
  basedLoop (D.chartPathClass i) (Path.Homotopic.Quotient.mk p)

@[simp] theorem closePath_refl (i : Bool) (x : D.chart i) :
    D.closePath i (Path.refl x) = 1 := basedLoop_refl _ _

theorem closePath_trans (i : Bool) {x y z : D.chart i} (p : Path x y) (q : Path y z) :
    D.closePath i (p.trans q) = D.closePath i q * D.closePath i p := by
  exact basedLoop_trans (D.chartPathClass i)
    (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

theorem closePath_homotopic (i : Bool) {x y : D.chart i} {p q : Path x y}
    (hpq : Path.Homotopic p q) : D.closePath i p = D.closePath i q := by
  unfold closePath
  rw [Path.Homotopic.Quotient.eq.mpr hpq]

theorem closePath_loop (i : Bool) (p : Path (D.baseChart i) (D.baseChart i)) :
    D.closePath i p = Path.Homotopic.Quotient.mk p := by
  simp only [closePath, basedLoop, D.chartPathClass_base, refl_trans]
  exact trans_refl _

def chartHom (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) :
    FundamentalGroup (D.chart i) (D.baseChart i) →* G := by
  cases i
  · exact fU
  · exact fV

def localValue (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool)
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.chart i) : G :=
  (D.chartHom fU fV i (D.closePath i
    (pathIn (S := (D.chart i : Set X)) p (by simpa using hp 0)
      (by simpa using hp 1) hp)))⁻¹

theorem localValue_refl (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (i : Bool) (x : X) (hx : ∀ t, Path.refl x t ∈ D.chart i) :
    D.localValue fU fV i (Path.refl x) hx = 1 := by
  simp only [localValue, pathIn_refl, D.closePath_refl, map_one, inv_one]

theorem localValue_trans (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (i : Bool) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i)
    (hpq : ∀ t, p.trans q t ∈ D.chart i) :
    D.localValue fU fV i (p.trans q) hpq =
      D.localValue fU fV i p hp * D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  have hz : z ∈ D.chart i := by simpa using hq 1
  unfold localValue
  rw [pathIn_trans p q hx hy hz hp hq hpq, D.closePath_trans, map_mul, mul_inv_rev]

theorem localValue_subpath_mul (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (i : Bool) {x y : X} (p : Path x y) (a b c : I) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : ∀ t, p.subpath a b t ∈ D.chart i)
    (hpbc : ∀ t, p.subpath b c t ∈ D.chart i)
    (hpac : ∀ t, p.subpath a c t ∈ D.chart i) :
    D.localValue fU fV i (p.subpath a c) hpac =
      D.localValue fU fV i (p.subpath a b) hpab *
        D.localValue fU fV i (p.subpath b c) hpbc := by
  have ha : p a ∈ D.chart i := by simpa using hpab 0
  have hb : p b ∈ D.chart i := by simpa using hpab 1
  have hc : p c ∈ D.chart i := by simpa using hpbc 1
  have H := subpathTransSubpathIn p a b c hab hbc ha hb hc hpab hpbc hpac
  unfold localValue
  rw [← D.closePath_homotopic i ⟨H⟩, D.closePath_trans, map_mul, mul_inv_rev]

theorem localValue_homotopy (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (i : Bool) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ D.chart i) :
    D.localValue fU fV i p hp = D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  unfold localValue
  rw [D.closePath_homotopic i ⟨homotopyIn p q hx hy hp hq H hH⟩]

end TwoOpenCover

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
