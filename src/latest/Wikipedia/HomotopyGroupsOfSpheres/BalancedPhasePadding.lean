import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBlocks
import Wikipedia.HomotopyGroupsOfSpheres.BalancedDiagonalPaths
import Mathlib.Topology.Homotopy.Basic

/-! # Four compensating phase directions for the balanced Clifford family -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePadding

open QuaternionicSymmetricMatrices

local notation "Core" => Fin 4 ⊕ Fin 4
local notation "Padded" => Fin 6 ⊕ Fin 6

def phasePair (θ : ℝ) : Space (Fin 2) :=
  reindex finSumFinEquiv (BalancedRealInvolutions.diagonalSpecial 1 (-θ)).val

theorem phasePair_val (θ : ℝ) :
    (phasePair θ).val.val = !![(Circle.exp (-θ) : ℂ), 0; 0, (Circle.exp θ : ℂ)] := by
  have h0 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 := rfl
  have h1 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = Sum.inr 0 := rfl
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [phasePair, reindex, BalancedRealInvolutions.diagonalSpecial,
      BalancedRealInvolutions.diagonalSymmetric, BalancedRealInvolutions.diagonalUnitary,
      BalancedRealInvolutions.diagonalPhase, BalancedRealInvolutions.phase,
      Matrix.reindex_apply, h0, h1]

theorem continuous_phasePair : Continuous phasePair :=
  (continuous_reindex finSumFinEquiv).comp
    (continuous_subtype_val.comp
      ((BalancedRealInvolutions.continuous_diagonalSpecial 1).comp continuous_neg))

theorem phasePair_zero : phasePair 0 = identity := by
  apply Subtype.ext
  apply Subtype.ext
  rw [phasePair_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [identity]

def paddingIndex : ((Fin 2 ⊕ Fin 2) ⊕ Core) ≃ Padded :=
  (Equiv.sumSumSumComm (Fin 2) (Fin 2) (Fin 4) (Fin 4)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

def padding : C(ℝ × Space Core, Space Padded) where
  toFun p := reindex paddingIndex (blockSum (blockSum (phasePair p.1) (phasePair p.1)) p.2)
  continuous_toFun := (continuous_reindex paddingIndex).comp
    (continuous_blockSum.comp
      ((continuous_blockSum.comp
        ((continuous_phasePair.comp continuous_fst).prodMk
          (continuous_phasePair.comp continuous_fst))).prodMk continuous_snd))

def identityPadding : C(Space Core, Space Padded) :=
  padding.comp ⟨fun B ↦ (0, B), continuous_const.prodMk continuous_id⟩

theorem identityPadding_val (B : Space Core) :
    (identityPadding B).val.val = Matrix.reindex paddingIndex paddingIndex
      (Matrix.fromBlocks 1 0 0 B.val.val) := by
  change (reindex paddingIndex (blockSum (blockSum (phasePair 0) (phasePair 0)) B)).val.val = _
  rw [phasePair_zero, blockSum_identity]
  rfl

theorem identityPadding_identity : identityPadding identity = identity := by
  change reindex paddingIndex (blockSum (blockSum (phasePair 0) (phasePair 0)) identity) = _
  rw [phasePair_zero, blockSum_identity, blockSum_identity, reindex_identity]

variable {X : Type*} [TopologicalSpace X]

def phasedMap (B : C(X, Space Core)) (a : C(X, ℝ)) : C(X, Space Padded) :=
  padding.comp ⟨fun x ↦ (a x, B x), a.continuous.prodMk B.continuous⟩

def paddingHomotopy (B : C(X, Space Core)) (a : C(X, ℝ)) (x : X) (ha : a x = 0) :
    (identityPadding.comp B).HomotopyRel (phasedMap B a) {x} where
  toFun p := padding ((p.1 : ℝ) * a p.2, B p.2)
  continuous_toFun := padding.continuous.comp
    (((continuous_subtype_val.comp continuous_fst).mul
      (a.continuous.comp continuous_snd)).prodMk (B.continuous.comp continuous_snd))
  map_zero_left y := by
    change padding ((0 : ℝ) * a y, B y) = padding (0, B y)
    rw [zero_mul]
  map_one_left y := by
    change padding ((1 : ℝ) * a y, B y) = padding (a y, B y)
    rw [one_mul]
  prop' t y hy := by
    have he : y = x := Set.mem_singleton_iff.mp hy
    subst y
    change padding ((t : ℝ) * a x, B x) = padding (0, B x)
    rw [ha, mul_zero]

end Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePadding
