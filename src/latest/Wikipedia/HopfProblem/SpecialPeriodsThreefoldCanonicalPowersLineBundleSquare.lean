import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleGauges

/-!
# The native square bundle and the two-factor tensor bundle

The same-cover square cocycle and the paired-cover tensor cocycle are
compared on their actual chart intersections.  The gauge is determined
by the original transitions, and its preferred-fibre map is the identity.
Consequently it gives a true holomorphic comparison with the full
two-factor tensor product, including its native fibre multiplication law.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H) (A : TransitionData M ι)

/-- Actual chart-pair units comparing the native square with the native
tensor product of the original bundle with itself. -/
def squareTensorGauge [A.IsHolomorphic I] : CrossGauge I (A.power 2) (tensor A A) where
  value i x := A.transition i.1 i.2.1 x * A.transition i.1 i.2.2 x
  compatible i j x hx := by
    have h₁ := A.transition_comp i.1 i.2.1 j.2.1 x
      ⟨⟨hx.1.1, hx.1.2.1⟩, hx.2.2.1⟩
    have h₂ := A.transition_comp i.1 i.2.2 j.2.2 x
      ⟨⟨hx.1.1, hx.1.2.2⟩, hx.2.2.2⟩
    have h₃ := A.transition_comp i.1 j.1 j.2.1 x
      ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2.1⟩
    have h₄ := A.transition_comp i.1 j.1 j.2.2 x
      ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2.2⟩
    change (A.transition i.2.1 j.2.1 x * A.transition i.2.2 j.2.2 x) *
        (A.transition i.1 i.2.1 x * A.transition i.1 i.2.2 x) =
      (A.transition j.1 j.2.1 x * A.transition j.1 j.2.2 x) *
        A.transition i.1 j.1 x ^ 2
    calc
      _ = (A.transition i.2.1 j.2.1 x * A.transition i.1 i.2.1 x) *
          (A.transition i.2.2 j.2.2 x * A.transition i.1 i.2.2 x) := by ac_rfl
      _ = A.transition i.1 j.2.1 x * A.transition i.1 j.2.2 x := by rw [h₁, h₂]
      _ = (A.transition j.1 j.2.1 x * A.transition i.1 j.1 x) *
          (A.transition j.1 j.2.2 x * A.transition i.1 j.1 x) := by rw [h₃, h₄]
      _ = _ := by rw [pow_two]; ac_rfl
  holomorphicOn i :=
    ((A.transition_holomorphic I i.1 i.2.1).mono
      (fun _ hx => ⟨hx.1, hx.2.1⟩)).mul
      ((A.transition_holomorphic I i.1 i.2.2).mono
        (fun _ hx => ⟨hx.1, hx.2.2⟩))

variable [A.IsHolomorphic I]

theorem squareTensorGauge_preferred (x : M) :
    (squareTensorGauge I A).value
      ((A.power 2).indexAt x, (tensor A A).indexAt x) x = 1 := by
  change A.transition (A.indexAt x) (A.indexAt x) x *
    A.transition (A.indexAt x) (A.indexAt x) x = 1
  rw [A.transition_self _ _ (A.mem_baseSet_at x), one_mul]

theorem squareTensorGauge_fiberEquiv_apply (x : M) (v : (A.power 2).core.Fiber x) :
    (squareTensorGauge I A).fiberEquiv x v = id (α := ℂ) v := by
  rw [CrossGauge.fiberEquiv_apply, squareTensorGauge_preferred]
  change (1 : ℂ) * id (α := ℂ) v = id (α := ℂ) v
  exact one_mul _

theorem squareTensorGauge_fiberEquiv_symm_apply (x : M) (v : (tensor A A).core.Fiber x) :
    ((squareTensorGauge I A).fiberEquiv x).symm v = id (α := ℂ) v := by
  rw [CrossGauge.fiberEquiv_symm_apply, squareTensorGauge_preferred]
  simp only [Units.val_one, inv_one, one_mul]
  rfl

/-- The actual native map retains the preferred fibre coordinate, but
its holomorphicity is the proved cross-cover gauge holomorphicity. -/
theorem squareTensorGauge_diffeomorph_mk (x : M) (v : (A.power 2).core.Fiber x) :
    (squareTensorGauge I A).diffeomorph ⟨x, v⟩ = ⟨x, id (α := ℂ) v⟩ := by
  rw [CrossGauge.diffeomorph_mk, squareTensorGauge_fiberEquiv_apply]

/-- Full algebraic two-factor tensor identification of the native square fibre. -/
def squareFiberTensorEquiv (x : M) :
    A.core.Fiber x ⊗[ℂ] A.core.Fiber x ≃ₗ[ℂ] (A.power 2).core.Fiber x :=
  (fibreTensorEquiv A A x).trans ((squareTensorGauge I A).fiberEquiv x).symm.toLinearEquiv

@[simp] theorem squareFiberTensorEquiv_tmul (x : M) (v w : A.core.Fiber x) :
    squareFiberTensorEquiv I A x (v ⊗ₜ[ℂ] w) = id (α := ℂ) v * id (α := ℂ) w := by
  change ((squareTensorGauge I A).fiberEquiv x).symm (fibreTensorEquiv A A x (v ⊗ₜ[ℂ] w)) = _
  rw [squareTensorGauge_fiberEquiv_symm_apply, fibreTensorEquiv_tmul]
  rfl

/-- The full tensor-fibre identification commutes with the original
native square-to-tensor comparison. -/
theorem squareFiberTensorEquiv_intertwines (x : M)
    (v : A.core.Fiber x ⊗[ℂ] A.core.Fiber x) :
    (squareTensorGauge I A).fiberEquiv x (squareFiberTensorEquiv I A x v) =
      fibreTensorEquiv A A x v :=
  ((squareTensorGauge I A).fiberEquiv x).apply_symm_apply _

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
