import ErdosProblems.Erdos421.MixedCongruences
import ErdosProblems.Erdos421.PrimeResidueConcentration

/-! # A bounded code for shifted tuples with distinct prime residues -/

namespace Erdos421

def shiftedTupleResidues {n N : ℕ} (p d : ℕ) (a : ℤ) (x : Fin n → Fin N) :
    Fin n → ZMod (p ^ d) := fun i ↦ (x i : ZMod (p ^ d)) + 1 - a

def shiftedPowerCode (p k N : ℕ) (a : ℤ) (x : Fin k → Fin N) :
    (j : Fin k) → ZMod (p ^ ((j : ℕ) + 1)) :=
  fun j ↦ ∑ i : Fin k,
    ((x i : ZMod (p ^ ((j : ℕ) + 1))) + 1 - a) ^ ((j : ℕ) + 1)

theorem shiftedTupleResidues_injective {n N p d : ℕ} (a : ℤ) (hN : N ≤ p ^ d) :
    Function.Injective (shiftedTupleResidues (n := n) (N := N) p d a) := by
  intro x y h
  funext i
  have he := congrFun h i
  have he' := (Equiv.subRight (a : ZMod (p ^ d))).injective he
  have he'' := (Equiv.addRight (1 : ZMod (p ^ d))).injective he'
  have hv := congrArg ZMod.val he''
  rw [ZMod.val_natCast_of_lt ((x i).isLt.trans_le hN),
    ZMod.val_natCast_of_lt ((y i).isLt.trans_le hN)] at hv
  exact Fin.ext hv

theorem shiftedTupleResidues_reduction {n N p d : ℕ} (hd : 0 < d)
    (a : ℤ) (x : Fin n → Fin N) (i : Fin n) :
    primePowerReduction p d hd (shiftedTupleResidues p d a x i) =
      (x i : ZMod p) + 1 - a := by
  simp only [shiftedTupleResidues, map_sub, map_add, map_natCast, map_one, map_intCast]

theorem shiftedPowerCode_eq_cast {p k N : ℕ} (a : ℤ) (x : Fin k → Fin N) (j : Fin k) :
    shiftedPowerCode p k N a x j =
      primePowerCast p k ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
        (powerSumVector k (shiftedTupleResidues p k a x) j) := by
  simp only [shiftedPowerCode, powerSumVector, shiftedTupleResidues, map_sum, map_pow,
    map_sub, map_add, map_natCast, map_one, map_intCast]

theorem shiftedPowerCode_fiber_card_le {p k N : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hkp : k < p) (hN : N ≤ p ^ k) (a : ℤ)
    (w : (j : Fin k) → ZMod (p ^ ((j : ℕ) + 1))) :
    ((primeDistinctTuples k N p).filter (fun x ↦ shiftedPowerCode p k N a x = w)).card ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  let A := primeDistinctTuples k N p
  let S := A.image (shiftedTupleResidues p k a)
  have hS : ∀ y ∈ S, Function.Injective (fun i ↦ primePowerReduction p k hk (y i)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hinj := (Finset.mem_filter.mp hx).2
    intro i j he
    simp only [shiftedTupleResidues_reduction] at he
    apply hinj
    exact (Equiv.addRight (1 : ZMod p)).injective ((Equiv.subRight (a : ZMod p)).injective he)
  let U := S.filter (fun y ↦ ∀ j : Fin k,
    primePowerCast p k ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt) (powerSumVector k y j) = w j)
  have hU : U.card ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
    primePower_complete_congruence_card_le hp hk hkp S hS w
  apply le_trans _ hU
  apply Finset.card_le_card_of_injOn (shiftedTupleResidues p k a)
  · intro x hx
    obtain ⟨hxA, hxw⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxA, rfl⟩, fun j ↦ ?_⟩
    rw [← shiftedPowerCode_eq_cast]
    exact congrFun hxw j
  · exact (shiftedTupleResidues_injective a hN).injOn

end Erdos421
