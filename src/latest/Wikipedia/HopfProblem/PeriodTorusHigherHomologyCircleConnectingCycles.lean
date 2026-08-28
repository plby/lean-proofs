import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual Mayer--Vietoris connecting map on concrete cycles

Concrete kernel cycles represent the same actual categorical homology
classes as `cyclesMk` followed by `homologyπ`. This identifies the existing
lift--boundary formula for the actual connecting homomorphism with the
concrete cycle-class API, first for small chains and then for the proved
open-cover comparison with the full singular chain complex.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The categorical constructor of a concrete cycle is the inverse of
the canonical isomorphism from categorical cycles to the kernel. -/
theorem cyclesMk_eq_moduleCatCyclesIso_inv (c : Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    K.cyclesMk c.1 j hj hc = ((K.sc n).moduleCatCyclesIso.inv).hom c := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have h₁ : (K.iCycles n).hom (K.cyclesMk c.1 j hj hc) = c.1 :=
    K.i_cyclesMk c.1 j hj hc
  have h₂ := congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_iCycles)
  exact h₁.trans h₂.symm

/-- The concrete cycle class is the categorical cycle class for any
presentation of the outgoing differential with the correct next degree. -/
theorem cycleClass_eq_homologyClassOfCycle_of_next (c : Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    cycleClass K n c = homologyClassOfCycle K c.1 j hj hc := by
  rw [homologyClassOfCycle, cyclesMk_eq_moduleCatCyclesIso_inv]
  exact (congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_π)).symm

/-- In the usual natural-number indexing, a concrete cycle has precisely
the same class as the actual categorical `cyclesMk` construction. -/
theorem cycleClass_eq_homologyClassOfCycle (c : Cycle K n) :
    cycleClass K n c = homologyClassOfCycle K c.1 (n - 1) (next_nat n)
      (cycle_condition K n c) :=
  cycleClass_eq_homologyClassOfCycle_of_next K n c (n - 1) (next_nat n)
    (cycle_condition K n c)

end Wikipedia.HopfProblem.SingularMayerVietoris.ModuleHomology

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

/-- The connecting map of any actual short exact chain sequence sends
a lifted cycle to the class of the lifted boundary, in the concrete API. -/
theorem connectingMap_cycleClass
    {S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (c : Cycle S.X₃ (n + 1))
    (z₂ : S.X₂.X (n + 1)) (hz₂ : (S.g.f (n + 1)).hom z₂ = c.1)
    (z₁ : Cycle S.X₁ n) (hz₁ : (S.f.f n).hom z₁.1 = (S.X₂.d (n + 1) n).hom z₂) :
    connectingMap hS n (cycleClass S.X₃ (n + 1) c) = cycleClass S.X₁ n z₁ := by
  have hc : (S.X₃.d (n + 1) n).hom c.1 = 0 := by
    have h := cycle_condition S.X₃ (n + 1) c
    rw [Nat.add_sub_cancel] at h
    exact h
  have hnext : (ComplexShape.down ℕ).next (n + 1) = n :=
    (ComplexShape.down ℕ).next_eq' (by simp)
  have h₃ := cycleClass_eq_homologyClassOfCycle_of_next S.X₃ (n + 1) c n hnext hc
  have hδ := connectingMap_homologyClassOfCycle hS n c.1 hc z₂ hz₂ z₁.1 hz₁
  have h₁ := cycleClass_eq_homologyClassOfCycle_of_next S.X₁ n z₁
    ((ComplexShape.down ℕ).next n) rfl
    (connectingMap_lift_is_cycle hS n z₂ z₁.1 hz₁ _)
  exact (congrArg (connectingMap hS n) h₃).trans (hδ.trans h₁.symm)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Concrete cycle formula for the connecting map of the proved actual
small-chain Mayer--Vietoris short exact sequence, for arbitrary subsets. -/
theorem smallConnectingMap_cycleClass (n : ℕ) (c : Cycle (smallComplex U V) (n + 1))
    (z₂ : (middleComplex U V).X (n + 1))
    (hz₂ : ((rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ : Cycle (singularComplex (U ∩ V : Set X)) n)
    (hz₁ : ((leftMap U V).f n).hom z₁.1 =
      ((middleComplex U V).d (n + 1) n).hom z₂) :
    smallConnectingMap U V n (cycleClass (smallComplex U V) (n + 1) c) =
      cycleClass (singularComplex (U ∩ V : Set X)) n z₁ :=
  connectingMap_cycleClass (chainSequence_shortExact U V) n c z₂ hz₂ z₁ hz₁

/-- The full open-cover connecting map has the same concrete lift--boundary
formula on the actual ambient class of a small singular cycle. -/
theorem connectingHomomorphism_cycleClass
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (c : Cycle (smallComplex U V) (n + 1))
    (z₂ : (middleComplex U V).X (n + 1))
    (hz₂ : ((rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ : Cycle (singularComplex (U ∩ V : Set X)) n)
    (hz₁ : ((leftMap U V).f n).hom z₁.1 =
      ((middleComplex U V).d (n + 1) n).hom z₂) :
    connectingHomomorphism U V hU hV hcover n
        (cycleClass (singularComplex X) (n + 1)
          (mapCycles (smallInclusion U V) (n + 1) c)) =
      cycleClass (singularComplex (U ∩ V : Set X)) n z₁ := by
  rw [← homologyMap_cycleClass]
  change connectingHomomorphism U V hU hV hcover n
    (smallHomologyComparison U V (n + 1) (cycleClass (smallComplex U V) (n + 1) c)) = _
  rw [connectingHomomorphism_comparison]
  exact smallConnectingMap_cycleClass U V n c z₂ hz₂ z₁ hz₁

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
