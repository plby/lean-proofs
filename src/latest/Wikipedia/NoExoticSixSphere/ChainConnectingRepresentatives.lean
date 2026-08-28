import Wikipedia.HopfProblem.SingularMayerVietorisSequenceAlgebra
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

/-!
# Original cycle classes and the native chain connecting map

The concrete cycle kernel and categorical cycle object give the same
homology class. The genuine connecting map therefore retains its
lift--boundary formula on the original concrete cycle representatives.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris ModuleHomology

namespace NoExoticSixSphere.ChainConnecting

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

theorem cyclesMk_eq (n : ℕ) (a : Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hz : (K.d n j).hom a.val = 0) :
    K.cyclesMk a.val j hj hz =
      ((K.sc n).moduleCatCyclesIso.inv).hom a := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have h₁ := K.i_cyclesMk a.val j hj hz
  have h₂ := congrArg (fun m => m.hom a) ((K.sc n).moduleCatCyclesIso_inv_iCycles)
  exact h₁.trans h₂.symm

theorem cycleClass_eq_homologyπ (n : ℕ) (a : Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hz : (K.d n j).hom a.val = 0) :
    cycleClass K n a = (K.homologyπ n).hom
      (K.cyclesMk a.val j hj hz) := by
  rw [cyclesMk_eq]
  exact (congrArg (fun m => m.hom a) ((K.sc n).moduleCatCyclesIso_inv_π)).symm

variable {S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)

/-- The native connecting map evaluated on an actual lift and its actual lifted boundary. -/
theorem connecting_cycleClass (n : ℕ) (a : Cycle S.X₃ (n + 1))
    (b : S.X₂.X (n + 1)) (hb : (S.g.f (n + 1)).hom b = a.val)
    (c : Cycle S.X₁ n) (hc : (S.f.f n).hom c.val = (S.X₂.d (n + 1) n).hom b) :
    connectingMap hS n (cycleClass S.X₃ (n + 1) a) = cycleClass S.X₁ n c := by
  have ha : (S.X₃.d (n + 1) n).hom a.val = 0 := by
    exact (congrArg (fun j => (S.X₃.d (n + 1) j).hom a.val = 0)
      (Nat.add_sub_cancel n 1)).mp (cycle_condition S.X₃ (n + 1) a)
  have hδ := hS.δ_apply (n + 1) n (by simp) a.val ha b hb c.val hc
    (n - 1) (next_nat n)
  exact (congrArg (connectingMap hS n) (cycleClass_eq_homologyπ S.X₃ (n + 1) a n
    ((ComplexShape.down ℕ).next_eq' (by simp)) ha)).trans
      (hδ.trans (cycleClass_eq_homologyπ S.X₁ n c (n - 1) (next_nat n)
        (cycle_condition S.X₁ n c)).symm)

end NoExoticSixSphere.ChainConnecting
