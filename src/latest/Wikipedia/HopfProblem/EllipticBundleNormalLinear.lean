import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The normal line to a product fibre

The vertical tangent space to `{0} × V` is the kernel of the first projection.
The actual quotient by this submodule is continuously complex-linearly equivalent
to `ℂ`.  A linear map whose first component is multiplication by `c` induces
exactly that multiplication on the quotient, irrespective of its second component.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.Elliptic.NormalLinear

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The tangent inclusion of the product fibre. -/
def verticalInclusion : V →L[ℂ] ℂ × V := ContinuousLinearMap.inr ℂ ℂ V

@[simp] theorem verticalInclusion_apply (v : V) :
    verticalInclusion V v = (0, v) := rfl

/-- The actual vertical submodule of the product tangent space. -/
def vertical : Submodule ℂ (ℂ × V) := LinearMap.ker (LinearMap.fst ℂ ℂ V)

@[simp] theorem mem_vertical (p : ℂ × V) : p ∈ vertical V ↔ p.1 = 0 := Iff.rfl

theorem vertical_eq_ker_fst :
    vertical V = (ContinuousLinearMap.fst ℂ ℂ V).ker := rfl

theorem range_verticalInclusion :
    (verticalInclusion V).range = vertical V := LinearMap.range_inr ℂ ℂ V

theorem isClosed_vertical : IsClosed (vertical V : Set (ℂ × V)) :=
  (ContinuousLinearMap.fst ℂ ℂ V).isClosed_ker

/-- The first coordinate descends to the actual submodule quotient. -/
def normalProjection : ((ℂ × V) ⧸ vertical V) →L[ℂ] ℂ :=
  (vertical V).liftQL (ContinuousLinearMap.fst ℂ ℂ V) le_rfl

@[simp] theorem normalProjection_mk (p : ℂ × V) :
    normalProjection V (Submodule.Quotient.mk p) = p.1 := rfl

/-- The inverse sends a scalar to the class of the horizontal vector `(z,0)`. -/
def normalEquiv : ((ℂ × V) ⧸ vertical V) ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.equivOfInverse (normalProjection V)
    ((vertical V).mkQL.comp (ContinuousLinearMap.inl ℂ ℂ V))
    (by
      intro q
      obtain ⟨p, rfl⟩ := (vertical V).mkQ_surjective q
      change Submodule.Quotient.mk (p.1, (0 : V)) = Submodule.Quotient.mk p
      apply (Submodule.Quotient.eq (vertical V)).mpr
      simp only [mem_vertical, Prod.fst_sub, sub_self])
    (by intro z; rfl)

@[simp] theorem normalEquiv_mk (p : ℂ × V) :
    normalEquiv V (Submodule.Quotient.mk p) = p.1 := rfl

@[simp] theorem normalEquiv_symm_apply (z : ℂ) :
    (normalEquiv V).symm z = Submodule.Quotient.mk (z, (0 : V)) := rfl

variable {V}

theorem map_mem_vertical (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) {p : ℂ × V} (hp : p ∈ vertical V) :
    L p ∈ vertical V := by
  rw [mem_vertical, hL, (mem_vertical V p).mp hp, mul_zero]

theorem vertical_le_comap (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) :
    vertical V ≤ (vertical V).comap L.toLinearMap :=
  fun _ hp => map_mem_vertical L c hL hp

/-- The actual map induced by `L` on the normal quotient. -/
def normalMap (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) :
    ((ℂ × V) ⧸ vertical V) →L[ℂ] ((ℂ × V) ⧸ vertical V) :=
  (vertical V).liftQL ((vertical V).mkQL.comp L) (by
    intro p hp
    change Submodule.Quotient.mk (L p) = 0
    exact (Submodule.Quotient.mk_eq_zero (vertical V)).mpr (map_mem_vertical L c hL hp))

@[simp] theorem normalMap_mk (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) (p : ℂ × V) :
    normalMap L c hL (Submodule.Quotient.mk p) = Submodule.Quotient.mk (L p) := rfl

theorem normalMap_toLinearMap (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) :
    (normalMap L c hL).toLinearMap =
      (vertical V).mapQ (vertical V) L.toLinearMap (vertical_le_comap L c hL) := rfl

theorem normalEquiv_normalMap (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) (q : (ℂ × V) ⧸ vertical V) :
    normalEquiv V (normalMap L c hL q) = c * normalEquiv V q := by
  obtain ⟨p, rfl⟩ := (vertical V).mkQ_surjective q
  exact hL p

/-- The whole induced quotient map, not merely its value on a chosen generator,
is scalar multiplication. -/
theorem normalMap_eq_smul (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂ)
    (hL : ∀ p, (L p).1 = c * p.1) :
    normalMap L c hL = c • ContinuousLinearMap.id ℂ ((ℂ × V) ⧸ vertical V) := by
  ext q
  apply (normalEquiv V).injective
  simpa only [smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul] using normalEquiv_normalMap L c hL q

/-- A nonzero normal multiplier gives an actual continuous-linear automorphism
of the quotient. -/
def unitNormalEquiv (c : ℂˣ) :
    ((ℂ × V) ⧸ vertical V) ≃L[ℂ] ((ℂ × V) ⧸ vertical V) :=
  ContinuousLinearEquiv.smulLeft c

@[simp] theorem unitNormalEquiv_apply (c : ℂˣ) (q : (ℂ × V) ⧸ vertical V) :
    unitNormalEquiv c q = (c : ℂ) • q := rfl

theorem normalMap_eq_unitNormalEquiv (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂˣ)
    (hL : ∀ p, (L p).1 = (c : ℂ) * p.1) :
    normalMap L (c : ℂ) hL = (unitNormalEquiv c).toContinuousLinearMap := by
  rw [normalMap_eq_smul]
  rfl

theorem normalMap_bijective (L : (ℂ × V) →L[ℂ] (ℂ × V)) (c : ℂˣ)
    (hL : ∀ p, (L p).1 = (c : ℂ) * p.1) :
    Function.Bijective (normalMap L (c : ℂ) hL) := by
  rw [normalMap_eq_unitNormalEquiv]
  exact (unitNormalEquiv c).bijective

/-- A germwise first-coordinate identity determines the normal part of the
actual derivative.  The remaining components of the map may be nonlinear. -/
theorem fst_fderiv_of_eventuallyEq (F : (ℂ × V) → ℂ × V) (p : ℂ × V) (c : ℂ)
    (hF : DifferentiableAt ℂ F p)
    (he : (fun w => (F w).1) =ᶠ[𝓝 p] (fun w => c * w.1)) :
    ∀ v, (fderiv ℂ F p v).1 = c * v.1 := by
  have hfst : HasFDerivAt (fun w => (F w).1)
      ((ContinuousLinearMap.fst ℂ ℂ V).comp (fderiv ℂ F p)) p :=
    (ContinuousLinearMap.fst ℂ ℂ V).hasFDerivAt.comp p hF.hasFDerivAt
  have hmul : HasFDerivAt (fun w : ℂ × V => c * w.1)
      (c • ContinuousLinearMap.fst ℂ ℂ V) p :=
    (c • ContinuousLinearMap.fst ℂ ℂ V).hasFDerivAt
  intro v
  exact congrArg (fun L : (ℂ × V) →L[ℂ] ℂ => L v)
    (hfst.unique (hmul.congr_of_eventuallyEq he))

/-- An injective complex-linear tangent map into the vertical space has the
entire vertical space as its range when the fibre model is finite-dimensional. -/
theorem range_eq_vertical_of_injective [FiniteDimensional ℂ V]
    (L : V →L[ℂ] ℂ × V) (hf : ∀ v, (L v).1 = 0) (hI : Function.Injective L) :
    L.range = vertical V := by
  have hinj : Function.Injective
      (((ContinuousLinearMap.snd ℂ ℂ V).comp L).toLinearMap) := by
    intro v w h
    apply hI
    exact Prod.ext ((hf v).trans (hf w).symm) h
  have hsurj := LinearMap.surjective_of_injective hinj
  apply le_antisymm
  · rintro p ⟨v, rfl⟩
    exact (mem_vertical V (L v)).mpr (hf v)
  · intro p hp
    obtain ⟨v, hv⟩ := hsurj p.2
    refine ⟨v, Prod.ext ?_ hv⟩
    exact (hf v).trans ((mem_vertical V p).mp hp).symm

/-- The product-fibre inclusion has its actual continuous-linear inclusion as
Fréchet derivative at every point. -/
theorem fderiv_verticalInclusion (v : V) :
    fderiv ℂ (fun w : V => ((0 : ℂ), w)) v = verticalInclusion V :=
  (verticalInclusion V).fderiv

theorem range_fderiv_verticalInclusion (v : V) :
    (fderiv ℂ (fun w : V => ((0 : ℂ), w)) v).range = vertical V := by
  rw [fderiv_verticalInclusion, range_verticalInclusion]

end Wikipedia.HopfProblem.Elliptic.NormalLinear
