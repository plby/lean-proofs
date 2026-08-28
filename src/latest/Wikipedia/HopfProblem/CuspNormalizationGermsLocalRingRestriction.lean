import Wikipedia.HopfProblem.CuspNormalizationGermsLocalRing
import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction

/-!
# The local ring of actual analytic germs on the plane union

For a nonempty collection of branches, evaluation at the origin is
defined on the literal restricted function germs.  The restricted ring
is a nontrivial quotient of the ambient analytic local ring.  Its units
are exactly the germs nonzero at the origin, and its maximal ideal is
the kernel of this evaluation.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts

local notation "E₃" => CoordinateSpace 3

/-- Evaluation of a restricted germ at the actual origin of the union.
The germ is first pulled back to the subspace, where ordinary germ
evaluation applies.  No branch is chosen. -/
def restrictedEval (s : Finset (Fin 3)) (hs : s.Nonempty) :
    RestrictedAnalyticGerm s →+* ℂ := by
  let origin : planeUnion s := ⟨0, by
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, hj, rfl⟩⟩
  have hval : Tendsto (Subtype.val : planeUnion s → E₃)
      (𝓝 origin) (𝓝[planeUnion s] (0 : E₃)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt,
      Eventually.of_forall Subtype.property⟩
  exact (Filter.Germ.valueRingHom (x := origin)).comp
    ((compTendstoRingHom (Subtype.val : planeUnion s → E₃) hval).comp
      (toPlaneUnion s).range.subtype)

/-- Restricting an ambient germ does not change its value at the origin. -/
@[simp] theorem restrictedEval_rangeRestrict (s : Finset (Fin 3))
    (hs : s.Nonempty) (φ : AmbientGerm) :
    restrictedEval s hs ((toPlaneUnion s).rangeRestrict φ) = eval (0 : E₃) φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

@[simp] theorem restrictedEval_ofAnalytic (s : Finset (Fin 3))
    (hs : s.Nonempty) (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    restrictedEval s hs ((toPlaneUnion s).rangeRestrict (ofAnalytic f hf)) = f 0 := rfl

/-- Constant germs give all values under restricted evaluation. -/
theorem restrictedEval_surjective (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Surjective (restrictedEval s hs) := by
  intro c
  exact ⟨(toPlaneUnion s).rangeRestrict (constant (0 : E₃) c),
    (restrictedEval_rangeRestrict s hs _).trans (eval_constant _ c)⟩

/-- A nonempty plane union has a nontrivial actual analytic-germ ring. -/
theorem restrictedAnalyticGerm_nontrivial (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Nontrivial (RestrictedAnalyticGerm s) :=
  (restrictedEval s hs).domain_nontrivial

instance restrictedAnalyticGerm_instNontrivial (s : Finset (Fin 3)) [Nonempty s] :
    Nontrivial (RestrictedAnalyticGerm s) :=
  restrictedAnalyticGerm_nontrivial s (Finset.nonempty_coe_sort.mp inferInstance)

/-- The actual restricted germ ring is a quotient of the ambient local ring. -/
theorem restrictedAnalyticGerm_isLocalRing (s : Finset (Fin 3)) (hs : s.Nonempty) :
    IsLocalRing (RestrictedAnalyticGerm s) := by
  have := restrictedAnalyticGerm_nontrivial s hs
  exact IsLocalRing.of_surjective' (toPlaneUnion s).rangeRestrict
    (toPlaneUnion s).rangeRestrict_surjective

instance restrictedAnalyticGerm_instIsLocalRing (s : Finset (Fin 3)) [Nonempty s] :
    IsLocalRing (RestrictedAnalyticGerm s) :=
  restrictedAnalyticGerm_isLocalRing s (Finset.nonempty_coe_sort.mp inferInstance)

/-- A restricted germ is invertible exactly when its value is nonzero. -/
@[simp] theorem restricted_isUnit_iff_eval_ne_zero (s : Finset (Fin 3))
    (hs : s.Nonempty) (ψ : RestrictedAnalyticGerm s) :
    IsUnit ψ ↔ restrictedEval s hs ψ ≠ 0 := by
  constructor
  · intro hψ
    exact (hψ.map (restrictedEval s hs)).ne_zero
  · obtain ⟨φ, rfl⟩ := (toPlaneUnion s).rangeRestrict_surjective ψ
    intro hφ
    have hu : IsUnit φ := (isUnit_iff_eval_ne_zero φ).mpr
      (by simpa only [restrictedEval_rangeRestrict] using hφ)
    exact hu.map (toPlaneUnion s).rangeRestrict

instance restrictedEval_isLocalHom (s : Finset (Fin 3)) (hs : s.Nonempty) :
    IsLocalHom (restrictedEval s hs) where
  map_nonunit ψ hψ := (restricted_isUnit_iff_eval_ne_zero s hs ψ).mpr hψ.ne_zero

/-- Actual restriction to a nonempty union is a local ring homomorphism. -/
instance toPlaneUnion_rangeRestrict_isLocalHom (s : Finset (Fin 3)) [Nonempty s] :
    IsLocalHom (toPlaneUnion s).rangeRestrict :=
  IsLocalHom.of_surjective (toPlaneUnion s).rangeRestrict
    (toPlaneUnion s).rangeRestrict_surjective

/-- The unique maximal ideal consists of the restricted germs vanishing
at the actual origin. -/
theorem restricted_maximalIdeal_eq_ker_eval (s : Finset (Fin 3)) [Nonempty s]
    (hs : s.Nonempty) :
    IsLocalRing.maximalIdeal (RestrictedAnalyticGerm s) = RingHom.ker (restrictedEval s hs) :=
  (IsLocalRing.ker_eq_maximalIdeal (restrictedEval s hs)
    (restrictedEval_surjective s hs)).symm

@[simp] theorem restricted_mem_maximalIdeal_iff_eval_eq_zero
    (s : Finset (Fin 3)) [Nonempty s] (hs : s.Nonempty) (ψ : RestrictedAnalyticGerm s) :
    ψ ∈ IsLocalRing.maximalIdeal (RestrictedAnalyticGerm s) ↔ restrictedEval s hs ψ = 0 := by
  rw [restricted_maximalIdeal_eq_ker_eval s hs]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.Germs
