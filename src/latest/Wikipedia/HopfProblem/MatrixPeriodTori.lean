import Wikipedia.HopfProblem.PeriodTori
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Tori with period matrix `(1, Z)`

Invertibility of the imaginary part of `Z` makes the four period columns
a real basis. Their integral span is a discrete full lattice, whose
quotient carries the constructed compact complex-torus structure.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem

abbrev RealPair₂ := (Fin 2 → ℝ) × (Fin 2 → ℝ)

structure FullPeriodMatrix where
  matrix : Matrix (Fin 2) (Fin 2) ℂ
  nondegenerate : Function.Bijective (matrix.map Complex.im).mulVecLin

namespace FullPeriodMatrix

variable (p : FullPeriodMatrix)

def imaginaryEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofBijective (p.matrix.map Complex.im).mulVecLin p.nondegenerate

def periodLinear : RealPair₂ →ₗ[ℝ] ComplexPlane₂ where
  toFun x := fun i => (x.1 i : ℂ) + (p.matrix *ᵥ fun j => (x.2 j : ℂ)) i
  map_add' x y := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.ofReal_add,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  map_smul' a x := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [Complex.real_smul, RingHom.id_apply]
    ring

theorem periodLinear_re (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).re = x.1 i + ((p.matrix.map Complex.re) *ᵥ x.2) i := by
  simp [periodLinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re]

theorem periodLinear_im (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).im = p.imaginaryEquiv x.2 i := by
  simp [periodLinear, imaginaryEquiv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.mul_im]

theorem periodLinear_bijective : Function.Bijective p.periodLinear := by
  constructor
  · intro x y hxy
    have him : p.imaginaryEquiv x.2 = p.imaginaryEquiv y.2 := by
      ext i
      simpa only [periodLinear_im] using congrArg Complex.im (congrFun hxy i)
    have hs : x.2 = y.2 := p.imaginaryEquiv.injective him
    apply Prod.ext _ hs
    ext i
    have he := congrArg Complex.re (congrFun hxy i)
    simpa only [periodLinear_re, hs, add_left_inj] using he
  · intro z
    let b := p.imaginaryEquiv.symm (fun i => (z i).im)
    let a := (fun i => (z i).re) - (p.matrix.map Complex.re) *ᵥ b
    refine ⟨(a, b), ?_⟩
    ext i
    apply Complex.ext
    · simp [periodLinear_re, a]
    · simpa only [periodLinear_im] using congrFun (p.imaginaryEquiv.apply_symm_apply _) i

def periodEquiv : RealPair₂ ≃ₗ[ℝ] ComplexPlane₂ :=
  LinearEquiv.ofBijective p.periodLinear p.periodLinear_bijective

def basis : Module.Basis (Fin 2 ⊕ Fin 2) ℝ ComplexPlane₂ :=
  ((Pi.basisFun ℝ (Fin 2)).prod (Pi.basisFun ℝ (Fin 2))).map p.periodEquiv

theorem basis_inl (j : Fin 2) : p.basis (Sum.inl j) = Pi.single j 1 := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply,
      Pi.basisFun_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem basis_inr (j : Fin 2) : p.basis (Sum.inr j) = fun i => p.matrix i j := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply,
      Pi.basisFun_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def lattice : Submodule ℤ ComplexPlane₂ := Submodule.span ℤ (range p.basis)

theorem basis_integer_sum (c : Fin 2 ⊕ Fin 2 → ℤ) :
    ∑ j, c j • p.basis j = (fun i => (c (Sum.inl i) : ℂ)) +
      p.matrix *ᵥ (fun i => (c (Sum.inr i) : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [Fintype.sum_sum_type, basis_inl, basis_inr, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Pi.single_apply, zsmul_eq_mul, mul_comm]

theorem mem_lattice_iff (z : ComplexPlane₂) : z ∈ p.lattice ↔
    ∃ m n : Fin 2 → ℤ, z = (fun i => (m i : ℂ)) + p.matrix *ᵥ (fun i => (n i : ℂ)) := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c (Sum.inl i), fun i => c (Sum.inr i),
      hc.symm.trans (p.basis_integer_sum c)⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨Sum.elim m n, p.basis_integer_sum (Sum.elim m n)⟩

instance lattice_discrete : DiscreteTopology p.lattice := by unfold lattice; infer_instance

instance lattice_isZLattice : IsZLattice ℝ p.lattice := ⟨ZSpan.span_top p.basis⟩

instance lattice_addSubgroup_discrete : DiscreteTopology p.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology p.lattice)

instance lattice_closed : IsClosed (p.lattice : Set ComplexPlane₂) :=
  AddSubgroup.isClosed_of_discrete (H := p.lattice.toAddSubgroup)

abbrev Torus := ComplexPlane₂ ⧸ p.lattice

instance torus_t3 : T3Space p.Torus := inferInstance

instance torus_pathConnected : PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

theorem torus_complex_manifold :
    IsManifold (modelWithCornersSelf ℂ ComplexPlane₂) ω p.Torus := inferInstance

instance torus_compact : CompactSpace p.Torus := by
  have hper : ∀ z w, w ∈ p.lattice → p.lattice.mkQ (z + w) = p.lattice.mkQ z := by
    intro z w hw
    have hw' : p.lattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic p.lattice p.lattice.mkQ
    p.lattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr p.lattice.mkQ_surjective] using hc⟩

end FullPeriodMatrix

end Wikipedia.HopfProblem
