import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Actual cohomology of zero-differential cochain complexes

If every differential is zero, every cochain is a cocycle and no
nonzero cocycle is a coboundary.  The canonical cocycle-class map is
therefore a linear equivalence onto Mathlib's actual homology object.
Its inverse gives an explicit equivalence with the original cochain
module, preserving literal representatives and actual homology maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

section OneComplex

variable (K : CochainComplex (ModuleCat.{0} ℤ) ℕ)
  (hzero : ∀ i j, K.d i j = 0)

include hzero

/-- With zero differential, the underlying cochain identifies the
actual concrete cocycle module with the entire degree module. -/
def zeroDifferentialCocycleEquiv (n : ℕ) : Cocycle K n ≃ₗ[ℤ] K.X n where
  toFun := Subtype.val
  invFun x := mkCocycle K n x
    (by simp only [hzero, ModuleCat.hom_zero, LinearMap.zero_apply])
  left_inv c := Subtype.ext rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem zeroDifferentialCocycleEquiv_apply (n : ℕ) (c : Cocycle K n) :
    zeroDifferentialCocycleEquiv K hzero n c = c.val := rfl

@[simp] theorem zeroDifferentialCocycleEquiv_symm_apply (n : ℕ) (x : K.X n) :
    ((zeroDifferentialCocycleEquiv K hzero n).symm x).val = x := rfl

/-- Zero incoming differentials make the actual cocycle-class map
injective, by the proved criterion for equality modulo coboundaries. -/
theorem cocycleClass_injective_of_zeroDifferential (n : ℕ) :
    Function.Injective (cocycleClass K n) := by
  intro c d hcd
  obtain ⟨b, hb⟩ := (cocycleClass_eq_iff K n c d).mp hcd
  apply Subtype.ext
  apply sub_eq_zero.mp
  simpa only [hzero, ModuleCat.hom_zero, LinearMap.zero_apply] using hb.symm

private def zeroDifferentialClassEquiv (n : ℕ) : Cocycle K n ≃ₗ[ℤ] K.homology n :=
  LinearEquiv.ofBijective (cocycleClass K n)
    ⟨cocycleClass_injective_of_zeroDifferential K hzero n, cocycleClass_surjective K n⟩

/-- The actual categorical homology of a zero-differential cochain
complex is linearly equivalent to its original degree module. -/
def zeroDifferentialHomologyEquiv (n : ℕ) : K.homology n ≃ₗ[ℤ] K.X n :=
  (zeroDifferentialClassEquiv K hzero n).symm.trans
    (zeroDifferentialCocycleEquiv K hzero n)

/-- The equivalence sends each actual cocycle class to its literal
underlying cochain. -/
@[simp] theorem zeroDifferentialHomologyEquiv_cocycleClass
    (n : ℕ) (c : Cocycle K n) :
    zeroDifferentialHomologyEquiv K hzero n (cocycleClass K n c) = c.val := by
  change zeroDifferentialCocycleEquiv K hzero n
    ((zeroDifferentialClassEquiv K hzero n).symm
      (zeroDifferentialClassEquiv K hzero n c)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- In the inverse direction, a cochain is sent to its actual cocycle
class, with the zero differential supplying the cocycle proof. -/
@[simp] theorem zeroDifferentialHomologyEquiv_symm_apply (n : ℕ) (x : K.X n) :
    (zeroDifferentialHomologyEquiv K hzero n).symm x =
      cocycleClass K n (mkCocycle K n x
        (by simp only [hzero, ModuleCat.hom_zero, LinearMap.zero_apply])) := rfl

/-- The representative formula is independent of the supplied proof
that a given cochain is a cocycle. -/
@[simp] theorem zeroDifferentialHomologyEquiv_mkCocycle (n : ℕ) (x : K.X n)
    (hx : (K.d n (n + 1)).hom x = 0) :
    zeroDifferentialHomologyEquiv K hzero n
      (cocycleClass K n (mkCocycle K n x hx)) = x :=
  zeroDifferentialHomologyEquiv_cocycleClass K hzero n (mkCocycle K n x hx)

end OneComplex

section Naturality

variable {K L : CochainComplex (ModuleCat.{0} ℤ) ℕ}
  (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) (f : K ⟶ L)

/-- For two zero-differential complexes, the actual map on homology
becomes the given degree component of the cochain map. -/
theorem zeroDifferentialHomologyEquiv_naturality (n : ℕ) (a : K.homology n) :
    zeroDifferentialHomologyEquiv L hL n ((HomologicalComplex.homologyMap f n).hom a) =
      (f.f n).hom (zeroDifferentialHomologyEquiv K hK n a) := by
  obtain ⟨c, rfl⟩ := cocycleClass_surjective K n a
  rw [homologyMap_cocycleClass, zeroDifferentialHomologyEquiv_cocycleClass,
    zeroDifferentialHomologyEquiv_cocycleClass, mapCocycles_val]

/-- The inverse coordinate identifications preserve the same actual
cochain-map and homology-map diagram. -/
theorem zeroDifferentialHomologyEquiv_symm_naturality (n : ℕ) (x : K.X n) :
    (HomologicalComplex.homologyMap f n).hom
      ((zeroDifferentialHomologyEquiv K hK n).symm x) =
      (zeroDifferentialHomologyEquiv L hL n).symm ((f.f n).hom x) := by
  apply (zeroDifferentialHomologyEquiv L hL n).injective
  rw [zeroDifferentialHomologyEquiv_naturality hK hL f,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end Naturality

end Wikipedia.HopfProblem.SingularCohomologyFree
