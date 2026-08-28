import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Genuine algebraic tensor powers of complex vector spaces

The powers used here are Mathlib's tensor products indexed by `Fin n`.
Their maps and equivalences act on the entire tensor product.  Pure powers
are elementary tensors with the same vector in each factor; their
nonvanishing is proved using a separating linear functional.
-/

noncomputable section

open scoped TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

/-- The actual algebraic tensor power, including its degree-zero case. -/
abbrev TensorPower (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) :=
  _root_.TensorPower ℂ n V

variable {V W U : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

/-- Apply a linear map separately in every tensor factor. -/
def tensorPowerMap (f : V →ₗ[ℂ] W) (n : ℕ) :
    TensorPower V n →ₗ[ℂ] TensorPower W n :=
  PiTensorProduct.map (fun _ : Fin n => f)

@[simp] theorem tensorPowerMap_tprod (f : V →ₗ[ℂ] W) (n : ℕ) (v : Fin n → V) :
    tensorPowerMap f n (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => f (v i)) :=
  PiTensorProduct.map_tprod _ _

@[simp] theorem tensorPowerMap_id (n : ℕ) :
    tensorPowerMap (LinearMap.id : V →ₗ[ℂ] V) n = LinearMap.id :=
  PiTensorProduct.map_id

/-- Functoriality is an identity of linear maps on full tensor products. -/
theorem tensorPowerMap_comp (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] U) (n : ℕ) :
    tensorPowerMap (g.comp f) n = (tensorPowerMap g n).comp (tensorPowerMap f n) :=
  PiTensorProduct.map_comp _ _

/-- Tensor a genuine linear equivalence in every factor. -/
def tensorPowerCongr (e : V ≃ₗ[ℂ] W) (n : ℕ) :
    TensorPower V n ≃ₗ[ℂ] TensorPower W n :=
  PiTensorProduct.congr (fun _ : Fin n => e)

@[simp] theorem tensorPowerCongr_toLinearMap (e : V ≃ₗ[ℂ] W) (n : ℕ) :
    (tensorPowerCongr e n).toLinearMap = tensorPowerMap e.toLinearMap n := rfl

@[simp] theorem tensorPowerCongr_tprod (e : V ≃ₗ[ℂ] W) (n : ℕ) (v : Fin n → V) :
    tensorPowerCongr e n (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => e (v i)) :=
  PiTensorProduct.congr_tprod _ _

@[simp] theorem tensorPowerCongr_refl (n : ℕ) :
    tensorPowerCongr (LinearEquiv.refl ℂ V) n = LinearEquiv.refl ℂ (TensorPower V n) := by
  apply LinearEquiv.toLinearMap_injective
  exact tensorPowerMap_id n

theorem tensorPowerCongr_trans (e : V ≃ₗ[ℂ] W) (d : W ≃ₗ[ℂ] U) (n : ℕ) :
    tensorPowerCongr (e.trans d) n = (tensorPowerCongr e n).trans (tensorPowerCongr d n) := by
  apply LinearEquiv.toLinearMap_injective
  exact tensorPowerMap_comp e.toLinearMap d.toLinearMap n

@[simp] theorem tensorPowerCongr_symm (e : V ≃ₗ[ℂ] W) (n : ℕ) :
    (tensorPowerCongr e n).symm = tensorPowerCongr e.symm n := rfl

/-- The elementary tensor with `n` copies of a vector. -/
def purePower (v : V) (n : ℕ) : TensorPower V n :=
  PiTensorProduct.tprod ℂ (fun _ : Fin n => v)

@[simp] theorem tensorPowerMap_purePower (f : V →ₗ[ℂ] W) (n : ℕ) (v : V) :
    tensorPowerMap f n (purePower v n) = purePower (f v) n :=
  tensorPowerMap_tprod f n _

@[simp] theorem tensorPowerCongr_purePower (e : V ≃ₗ[ℂ] W) (n : ℕ) (v : V) :
    tensorPowerCongr e n (purePower v n) = purePower (e v) n :=
  tensorPowerCongr_tprod e n _

/-- Simultaneous scaling in all factors has degree `n`. -/
theorem purePower_smul (c : ℂ) (v : V) (n : ℕ) :
    purePower (c • v) n = c ^ n • purePower v n := by
  simpa only [purePower, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => V)).map_smul_univ
      (fun _ => c) (fun _ => v)

/-- The linear functional obtained by multiplying the evaluations in all factors. -/
def tensorPowerEval (φ : V →ₗ[ℂ] ℂ) (n : ℕ) : TensorPower V n →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap (fun _ => φ))

@[simp] theorem tensorPowerEval_tprod (φ : V →ₗ[ℂ] ℂ) (n : ℕ) (v : Fin n → V) :
    tensorPowerEval φ n (PiTensorProduct.tprod ℂ v) = ∏ i, φ (v i) := by
  simp only [tensorPowerEval, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

@[simp] theorem tensorPowerEval_purePower (φ : V →ₗ[ℂ] ℂ) (n : ℕ) (v : V) :
    tensorPowerEval φ n (purePower v n) = φ v ^ n := by
  simp only [purePower, tensorPowerEval_tprod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A nonzero vector has nonzero pure powers in every degree, without a
finite-dimensionality hypothesis. -/
theorem purePower_ne_zero {v : V} (hv : v ≠ 0) (n : ℕ) : purePower v n ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  intro h
  have he := congrArg (tensorPowerEval φ n) h
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [tensorPowerEval_purePower, hφ, one_pow, map_zero] using he

theorem purePower_zero (n : ℕ) (hn : 0 < n) : purePower (0 : V) n = 0 := by
  simpa only [zero_smul, zero_pow (Nat.ne_of_gt hn)] using
    (purePower_smul (0 : ℂ) (0 : V) n)

theorem purePower_eq_zero_iff (n : ℕ) (hn : 0 < n) (v : V) :
    purePower v n = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact purePower_ne_zero hv n h
  · rintro rfl
    exact purePower_zero n hn

/-- The empty tensor product is canonically the scalar field. -/
def zeroTensorPowerEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] :
    TensorPower V 0 ≃ₗ[ℂ] ℂ :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

@[simp] theorem zeroTensorPowerEquiv_purePower (v : V) :
    zeroTensorPowerEquiv V (purePower v 0) = 1 :=
  PiTensorProduct.isEmptyEquiv_apply_tprod _ _

/-- A tensor product with one factor is canonically the original vector space. -/
def oneTensorPowerEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] :
    TensorPower V 1 ≃ₗ[ℂ] V :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

@[simp] theorem oneTensorPowerEquiv_purePower (v : V) :
    oneTensorPowerEquiv V (purePower v 1) = v :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

@[simp] theorem oneTensorPowerEquiv_symm_apply (v : V) :
    (oneTensorPowerEquiv V).symm v = purePower v 1 :=
  PiTensorProduct.subsingletonEquiv_symm_apply' _ _

/-- Concatenating tensor factors gives the canonical sum-of-degrees equivalence. -/
def addTensorPowerEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] (m n : ℕ) :
    TensorPower V m ⊗[ℂ] TensorPower V n ≃ₗ[ℂ] TensorPower V (m + n) :=
  _root_.TensorPower.mulEquiv

/-- Concatenation sends the tensor product of two pure powers to their combined power. -/
@[simp] theorem addTensorPowerEquiv_purePower (v : V) (m n : ℕ) :
    addTensorPowerEquiv V m n (purePower v m ⊗ₜ[ℂ] purePower v n) =
      purePower v (m + n) := by
  change _root_.TensorPower.mulEquiv
      (PiTensorProduct.tprod ℂ (fun _ : Fin m => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin n => v)) = _
  rw [← _root_.TensorPower.gMul_def, _root_.TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  exact Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) i

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
