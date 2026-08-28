import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyBasic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# The ordinary geometry of the flattened simplex

The flattened simplex is a compact convex subset of its actual ambient real
coordinate space. Its topological interior consists precisely of the vectors
with positive coordinates and coordinate sum strictly below one. These results
also include the zero-dimensional coordinate space.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.HigherHurewicz

theorem convex_flatSimplexSet (n : ℕ) : Convex ℝ (flatSimplexSet n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

theorem isClosed_flatSimplexSet (n : ℕ) : IsClosed (flatSimplexSet n) := by
  have he : flatSimplexSet n =
      (⋂ i : Fin n, {v : Fin n → ℝ | 0 ≤ v i}) ∩ {v | ∑ i, v i ≤ 1} := by
    ext v
    simp only [flatSimplexSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem flatSimplexSet_subset_Icc (n : ℕ) :
    flatSimplexSet n ⊆ Icc (0 : Fin n → ℝ) 1 := by
  intro v hv
  refine ⟨hv.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)).trans hv.2

theorem isCompact_flatSimplexSet (n : ℕ) : IsCompact (flatSimplexSet n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_flatSimplexSet n)
    (flatSimplexSet_subset_Icc n)

private def flatCoordinateSum (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  cont := by fun_prop

private theorem flatCoordinateSum_succ_ne_zero (n : ℕ) :
    flatCoordinateSum (n + 1) ≠ 0 := by
  intro h
  have he := congrArg (fun f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => f 1) h
  have hn : (n : ℝ) + 1 = 0 := by
    simpa [flatCoordinateSum] using he
  exact (ne_of_gt (Nat.cast_add_one_pos n)) hn

private theorem isOpen_flatSimplexStrict (n : ℕ) :
    IsOpen {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  have he : {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} =
      (⋂ i : Fin n, {v : Fin n → ℝ | 0 < v i}) ∩ {v | ∑ i, v i < 1} := by
    ext v
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (by fun_prop) continuous_const)

theorem interior_flatSimplexSet (n : ℕ) :
    interior (flatSimplexSet n) =
      {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  apply Subset.antisymm
  · intro v hv
    constructor
    · intro i
      have hi : v ∈ interior ((fun w : Fin n → ℝ => w i) ⁻¹' Ici 0) :=
        interior_mono (fun w hw => hw.1 i) hv
      have h := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa only [mem_preimage, interior_Ici, mem_Ioi] using h
    · cases n with
      | zero => simp
      | succ n =>
        have hs : v ∈ interior (flatCoordinateSum (n + 1) ⁻¹' Iic 1) :=
          interior_mono (fun w hw => hw.2) hv
        have h := ((flatCoordinateSum (n + 1)).isOpenMap_of_ne_zero
          (flatCoordinateSum_succ_ne_zero n)).interior_preimage_subset_preimage_interior hs
        simpa only [mem_preimage, interior_Iic, mem_Iio, flatCoordinateSum,
          ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using h
  · exact (isOpen_flatSimplexStrict n).subset_interior_iff.mpr
      (fun _ hv => ⟨fun i => (hv.1 i).le, hv.2.le⟩)

theorem interior_flatSimplexSet_nonempty (n : ℕ) :
    (interior (flatSimplexSet n)).Nonempty := by
  rw [interior_flatSimplexSet]
  have hn : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), fun _ => one_div_pos.mpr hn, ?_⟩
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one_div] using (div_lt_one hn).mpr (lt_add_one (n : ℝ))

end Wikipedia.HopfProblem.HigherHurewicz
