import Wikipedia.HopfProblem.PeriodDomain
import Wikipedia.HopfProblem.QuotientManifold
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Convex.Topology

/-!
# The actual period lattices and their compact quotients

For every point of the open period domain, the four complex columns of `Π`
are proved to be a real basis. Their integral span is consequently a discrete
full lattice. The quotient of `ℂ²` is a compact complex manifold with the
analytic atlas constructed in `QuotientManifold.lean`.

These are the individual tori used in Theorem 3.4(iv). No equivariant
holomorphic period map, or compact threefold, is assumed or constructed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem

open scoped Matrix
open scoped ContDiff

abbrev ComplexPlane₂ := Fin 2 → ℂ

/-- Pair adjacent real coordinates to obtain the two complex coordinates. -/
def complexCoordinates : (Fin 4 → ℝ) ≃ₗ[ℝ] ComplexPlane₂ where
  toFun x := ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩]
  invFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by
    ext i : 1
    fin_cases i <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The nondegenerate period domain specified in Definition 3.1. -/
abbrev PeriodDomain := {p : PeriodPoint // p.Admissible}

namespace PeriodDomain

/-- A concrete point shows that this period domain is nonempty. -/
def basePoint : PeriodDomain :=
  ⟨⟨Complex.I, 0, -Complex.I⟩, by
    norm_num [PeriodPoint.Admissible, PeriodPoint.discriminant]⟩

/-- The real period matrix is an invertible real-linear map. -/
def realEquiv (p : PeriodDomain) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 4)) p.val.realMatrix
    (isUnit_iff_ne_zero.mpr (ne_of_lt (p.val.det_realMatrix_neg p.property)))

theorem realEquiv_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    p.realEquiv v = p.val.realMatrix *ᵥ v := by
  simp [realEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

/-- The real basis furnished by the four period columns. -/
def basis (p : PeriodDomain) : Module.Basis (Fin 4) ℝ ComplexPlane₂ :=
  (Pi.basisFun ℝ (Fin 4)).map (p.realEquiv.trans complexCoordinates)

theorem basis_apply (p : PeriodDomain) (j : Fin 4) :
    p.basis j = fun i => p.val.matrix i j := by
  simp only [basis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    realEquiv_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]
  ext i : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, PeriodPoint.matrix]

/-- The integral span of the columns of `Π`, as in Definition 3.3. -/
def lattice (p : PeriodDomain) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range (fun j i => p.val.matrix i j))

theorem lattice_eq_span_basis (p : PeriodDomain) :
    p.lattice = Submodule.span ℤ (Set.range p.basis) := by
  unfold lattice
  congr 2
  funext j
  exact (p.basis_apply j).symm

instance lattice_discrete (p : PeriodDomain) : DiscreteTopology p.lattice := by
  rw [lattice_eq_span_basis]
  infer_instance

instance lattice_isZLattice (p : PeriodDomain) : IsZLattice ℝ p.lattice := by
  constructor
  rw [lattice_eq_span_basis]
  exact ZSpan.span_top p.basis

instance lattice_addSubgroup_discrete (p : PeriodDomain) :
    DiscreteTopology p.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology p.lattice)

instance lattice_isClosed (p : PeriodDomain) : IsClosed (p.lattice : Set ComplexPlane₂) := by
  change IsClosed (p.lattice.toAddSubgroup : Set ComplexPlane₂)
  exact AddSubgroup.isClosed_of_discrete (H := p.lattice.toAddSubgroup)

theorem lattice_rank (p : PeriodDomain) : Module.finrank ℤ p.lattice = 4 := by
  rw [ZLattice.rank ℝ p.lattice, Module.finrank_eq_card_basis p.basis]
  rfl

/-- The fibre `ℂ² / ΠΛ`, with its genuine quotient topology. -/
abbrev Torus (p : PeriodDomain) := ComplexPlane₂ ⧸ p.lattice

instance torus_t3 (p : PeriodDomain) : T3Space p.Torus := inferInstance

instance torus_pathConnected (p : PeriodDomain) : PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

theorem torus_complex_manifold (p : PeriodDomain) :
    IsManifold (modelWithCornersSelf ℂ ComplexPlane₂) ω p.Torus := inferInstance

theorem torus_projection_holomorphic (p : PeriodDomain) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (p.lattice.mkQ : ComplexPlane₂ → p.Torus) :=
  DiscreteQuotient.contMDiff_mkQ p.lattice ω

/-- The compactness conclusion for each individual torus in Theorem 3.4(iv). -/
instance torus_compact (p : PeriodDomain) : CompactSpace p.Torus := by
  let f := p.lattice.mkQ
  have hf : Continuous f := p.lattice.continuous_mkQ
  have hper : ∀ z w, w ∈ p.lattice → f (z + w) = f z := by
    intro z w hw
    have hw' : f w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic p.lattice f hf hper
  have hs : Function.Surjective f := Submodule.Quotient.mk_surjective p.lattice
  exact ⟨by simpa only [Set.range_eq_univ.mpr hs] using hc⟩

end PeriodDomain

end Wikipedia.HopfProblem
