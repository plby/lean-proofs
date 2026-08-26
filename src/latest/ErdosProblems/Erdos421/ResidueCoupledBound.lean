import ErdosProblems.Erdos421.ShiftedCodeCompatibility
import ErdosProblems.Erdos421.CoupledCounts

/-! # Bounding the concentrated system by a shorter free-variable count -/

namespace Erdos421

theorem vinogradovSums_append {r s k N : ℕ} (x : Fin r → Fin N) (y : Fin s → Fin N) :
    vinogradovSums k (Fin.append x y) = vinogradovSums k x + vinogradovSums k y := by
  funext j
  exact sum_comp_append (fun z : Fin N ↦ ((z : ℤ) + 1) ^ ((j : ℕ) + 1)) x y

def restrictedVinogradovCount {N : ℕ} (T : Finset (Fin N)) (s k : ℕ) : ℕ :=
  let U := Fintype.piFinset (fun _ : Fin s ↦ T)
  ((U ×ˢ U).filter (fun uv ↦ vinogradovSums k uv.1 = vinogradovSums k uv.2)).card

theorem primeDistinctTuples_card_le (k N p : ℕ) : (primeDistinctTuples k N p).card ≤ N ^ k := by
  have h := Finset.card_le_card (Finset.subset_univ (primeDistinctTuples k N p))
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using h

theorem mixedIntegerCount_residue_le (s k N p : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hkp : k < p) (hN : N ≤ p ^ k) (c : ZMod p) :
    mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k ≤
      N ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
        restrictedVinogradovCount (integerResidueClass N p c) s k := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let A := primeDistinctTuples k N p
  let U := Fintype.piFinset (fun _ : Fin s ↦ integerResidueClass N p c)
  have hc := coupled_count_le_compatible_fibers A U
    (vinogradovSums k) (vinogradovSums k) (shiftedPowerCode p k N c.val)
    (fun w ↦ shiftedPowerCode_fiber_card_le hp hk hkp hN c.val w)
    (by
      intro z _ w _ u hu v hv he
      apply shiftedPowerCode_compatible c z w u v
        (Fintype.mem_piFinset.mp hu) (Fintype.mem_piFinset.mp hv)
      rw [vinogradovSums_append, vinogradovSums_append]
      exact he)
  have hcount : mixedIntegerCount A (integerResidueClass N p c) s k ≤
      A.card * (k.factorial * p ^ (k * (k - 1) / 2)) *
        restrictedVinogradovCount (integerResidueClass N p c) s k := by
    simpa only [mixedIntegerCount, U, vinogradovSums_append, sub_eq_zero,
      restrictedVinogradovCount] using hc
  exact hcount.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (primeDistinctTuples_card_le k N p)))

end Erdos421
