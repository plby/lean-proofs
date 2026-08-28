import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCohomology
import Mathlib.Topology.Sets.Compacts
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Integral compact-support cohomology from the original relative groups

Take the directed limit over actual compact subsets, using the proved
integral support-extension maps. Every class has a genuine supported
representative, and equality is agreement on a common larger compact
support. On a compact space the original map forgetting support is an
equivalence with integral singular cohomology.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable (X : Type) [TopologicalSpace X] (p : ℕ)

abbrev Component (K : Compacts X) : Type :=
  IntegralSupportedCohomology.Cohomology (K : Set X) p

def transition (K L : Compacts X) (h : K ≤ L) : Component X p K →ₗ[ℤ] Component X p L :=
  IntegralSupportedCohomology.extend h p

instance directedSystem : DirectedSystem (Component X p) (transition X p · · ·) where
  map_self {K} a := LinearMap.congr_fun
    (IntegralSupportedCohomology.extend_refl (K : Set X) p) a
  map_map {_N _L _K} hKL hLN a :=
    (LinearMap.congr_fun (IntegralSupportedCohomology.extend_trans hKL hLN p) a).symm

/-- The actual directed limit with integral coefficients. -/
abbrev Cohomology : Type := DirectLimit (Component X p) (transition X p)

def of (K : Compacts X) : Component X p K →ₗ[ℤ] Cohomology X p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.of ℤ (Compacts X) (Component X p) (transition X p) K).toAddMonoidHom

theorem of_transition {K L : Compacts X} (h : K ≤ L) (a : Component X p K) :
    of X p L (transition X p K L h a) = of X p K a :=
  DirectLimit.Module.of_f (R := ℤ) (f := transition X p) (i := K) (j := L) (hij := h) (x := a)

theorem exists_representative (a : Cohomology X p) :
    ∃ (K : Compacts X) (b : Component X p K), of X p K b = a := by
  induction a using DirectLimit.induction with
  | _ K a => exact ⟨K, a, rfl⟩

theorem of_eq_iff (K L : Compacts X) (a : Component X p K) (b : Component X p L) :
    of X p K a = of X p L b ↔
      ∃ (N : Compacts X) (hK : K ≤ N) (hL : L ≤ N),
        transition X p K N hK a = transition X p L N hL b :=
  Quotient.eq

def lift {P : Type} [AddCommGroup P] [Module ℤ P]
    (f : ∀ K : Compacts X, Component X p K →ₗ[ℤ] P)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L) (a : Component X p K),
      f L (transition X p K L h a) = f K a) : Cohomology X p →ₗ[ℤ] P :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.lift ℤ (Compacts X) (Component X p) (transition X p) f hf).toAddMonoidHom

theorem lift_of {P : Type} [AddCommGroup P] [Module ℤ P]
    (f : ∀ K : Compacts X, Component X p K →ₗ[ℤ] P)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L) (a : Component X p K),
      f L (transition X p K L h a) = f K a) (K : Compacts X) (a : Component X p K) :
    lift X p f hf (of X p K a) = f K a := rfl

section Compact

variable [CompactSpace X]

/-- The actual whole space is a final support when the space is compact. -/
def toTop : Cohomology X p →ₗ[ℤ] Component X p ⊤ :=
  lift X p (fun K => transition X p K ⊤ le_top) (by
    intro K L h a
    exact (LinearMap.congr_fun
      (IntegralSupportedCohomology.extend_trans h (show (L : Set X) ⊆ Set.univ from le_top) p)
      a).symm)

theorem toTop_of (K : Compacts X) (a : Component X p K) :
    toTop X p (of X p K a) = transition X p K ⊤ le_top a := rfl

theorem toTop_of_top (a : Component X p ⊤) : toTop X p (of X p ⊤ a) = a := by
  rw [toTop_of]
  exact LinearMap.congr_fun (IntegralSupportedCohomology.extend_refl (Set.univ : Set X) p) a

theorem of_top_toTop (a : Cohomology X p) : of X p ⊤ (toTop X p a) = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  rw [toTop_of]
  exact of_transition X p le_top b

def topEquiv : Cohomology X p ≃ₗ[ℤ] Component X p ⊤ where
  toFun := toTop X p
  invFun := of X p ⊤
  left_inv := of_top_toTop X p
  right_inv := toTop_of_top X p
  map_add' := (toTop X p).map_add
  map_smul' := (toTop X p).map_smul

/-- The original forgetting map identifies compact-support and absolute integral cohomology. -/
def absoluteEquiv : Cohomology X p ≃ₗ[ℤ] SingularCohomologyFree.SingularCohomology X p :=
  (topEquiv X p).trans (IntegralSupportedCohomology.absoluteEquiv (X := X) p)

theorem absoluteEquiv_of (K : Compacts X) (a : Component X p K) :
    absoluteEquiv X p (of X p K a) = IntegralSupportedCohomology.toAbsolute (K : Set X) p a :=
  IntegralSupportedCohomology.toAbsolute_extend (Set.subset_univ (K : Set X)) p a

end Compact

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
