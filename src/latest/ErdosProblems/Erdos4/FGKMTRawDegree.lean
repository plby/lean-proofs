import ErdosProblems.Erdos4.FGKMTIncidenceSize
import ErdosProblems.Erdos4.FGKMTConditionBounds

/-!
# Raw degrees as incidence normalizers

On survivor sets containing `v`, the raw degree at `v` is exactly its
model degree times the normalizer of the erased incidence law.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem normalizer_eq_mean (μ : FiniteLaw (Finset V)) (p : V → ℝ) (W : Finset V) :
    normalizer μ p W = μ.mean (fun e => if e ⊆ W then 1 / setProduct p e else 0) := by
  unfold normalizer FiniteLaw.mean
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hsub : e ⊆ W <;> simp [reweighted, hsub, div_eq_mul_inv]

theorem eventNumerator_eq_mean (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (W : Finset V) (E : Finset V → Prop) [DecidablePred E] :
    eventNumerator μ p W E =
      μ.mean (fun e => if E e ∧ e ⊆ W then 1 / setProduct p e else 0) := by
  unfold eventNumerator FiniteLaw.mean
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hE : E e <;> by_cases hsub : e ⊆ W <;>
    simp [reweighted, hE, hsub, div_eq_mul_inv]

noncomputable def rawDegree (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (W : Finset V) (v : V) : ℝ := ∑ i, eventNumerator (μ i) p W (fun e => v ∈ e)

theorem rawDegree_nonneg (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (W : Finset V) (v : V) : 0 ≤ rawDegree μ p W v :=
  Finset.sum_nonneg (fun i _hi => eventNumerator_nonneg (μ i) p hp W _)

theorem rawDegree_eq_incidence (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (W : Finset V) (v : V) (hvW : v ∈ W)
    (hd : vertexDegree μ v ≠ 0) :
    rawDegree μ p W v =
      (vertexDegree μ v / p v) * normalizer (erasedIncidence μ v) p W := by
  rw [normalizer_eq_mean, erasedIncidence_mean μ v hd]
  have hcancel (a : ℝ) : (vertexDegree μ v / p v) * (a / vertexDegree μ v) = a / p v := by
    field_simp
  rw [hcancel, Finset.sum_div]
  unfold rawDegree
  apply Finset.sum_congr rfl
  intro i _hi
  rw [eventNumerator_eq_mean]
  have hmean : (μ i).mean (fun e =>
      if v ∈ e then (if e.erase v ⊆ W then 1 / setProduct p (e.erase v) else 0) else 0) / p v =
      (μ i).mean (fun e =>
        (if v ∈ e then (if e.erase v ⊆ W then 1 / setProduct p (e.erase v) else 0) else 0) / p v) := by
    simp only [div_eq_mul_inv, FiniteLaw.mean_mul_const]
  rw [hmean]
  apply (μ i).mean_congr
  intro e
  by_cases hve : v ∈ e
  · have herase : e.erase v ⊆ W ↔ e ⊆ W := Finset.erase_subset_iff_of_mem hvW
    have hprod : setProduct p e = p v * setProduct p (e.erase v) :=
      (Finset.mul_prod_erase e p hve).symm
    by_cases hsub : e ⊆ W
    · simp only [hve, hsub, herase, and_self, if_true]
      rw [hprod]
      ring
    · simp only [hve, hsub, herase, and_false, if_false, if_true, zero_div]
  · simp [hve]

theorem rawDegree_le (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r) (W : Finset V) (v : V) :
    rawDegree μ p W v ≤ vertexDegree μ v / κ ^ r := by
  unfold rawDegree vertexDegree
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _hi => eventNumerator_le (μ i) p hκ0 hκ1 hp (hsize i) W _)

theorem rawDegree_zero (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r) (v : V)
    (hd : vertexDegree μ v = 0) (W : Finset V) : rawDegree μ p W v = 0 := by
  apply le_antisymm
  · simpa only [hd, zero_div] using rawDegree_le μ p hκ0 hκ1 hp hsize W v
  · exact rawDegree_nonneg μ p (fun v => hκ0.trans_le (hp v)) W v

end Erdos4.FGKMT
