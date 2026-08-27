import Arxiv.Arxiv2411_18291.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting incidences and necessary divisibility conditions

The number of `r`-subsets of a `q`-set containing an `i`-set is
`(q - i).choose (r - i)`. Double counting gives the corresponding identity
for signed clique decompositions and hence the necessary degree divisibilities.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- Count fixed-size subsets of `T` that contain `I`. -/
theorem card_blocks_between (I T : Finset V) (hIT : I ⊆ T) (hIr : I.card ≤ r) :
    (univ.filter fun e : Block V r => I ⊆ e.val ∧ e.val ⊆ T).card =
      (T.card - I.card).choose (r - I.card) := by
  calc
    _ = ((T.powersetCard r).filter fun e => I ⊆ e).card := by
      apply card_bij (fun e _ => e.val)
      · intro e he
        simp only [mem_filter, mem_univ, true_and] at he
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨he.2, e.property⟩, he.1⟩
      · intro e _ f _ h
        exact Subtype.ext h
      · intro e he
        obtain ⟨⟨heT, her⟩, hIe⟩ := (by simpa only [mem_filter, mem_powersetCard] using he)
        exact ⟨⟨e, her⟩, by simp [hIe, heT], rfl⟩
    _ = _ := card_filter_powersetCard_subset I T r hIT hIr

/-- The signed degree at an arbitrary vertex subset. -/
def degree {R : Type*} [AddCommMonoid R] (J : Block V r → R) (I : Finset V) : R :=
  ∑ e, if I ⊆ e.val then J e else 0

theorem degree_boundary {R : Type*} [Semiring R]
    (Φ : Block V q → R) (I : Finset V) (hIr : I.card ≤ r) :
    degree (boundary r Φ) I =
      ((q - I.card).choose (r - I.card) : R) * degree Φ I := by
  unfold degree boundary
  simp only [Finset.ite_sum_zero]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro Q _
  by_cases hIQ : I ⊆ Q.val
  · rw [if_pos hIQ]
    calc
      (∑ e : Block V r, if I ⊆ e.val then
          if e.val ⊆ Q.val then Φ Q else 0 else 0) =
          ∑ e ∈ univ.filter (fun e : Block V r => I ⊆ e.val ∧ e.val ⊆ Q.val), Φ Q := by
        rw [sum_filter]
        apply sum_congr rfl
        intro e _
        split_ifs <;> simp_all
      _ = _ := by
        rw [sum_const, card_blocks_between I Q.val hIQ hIr, Q.property, nsmul_eq_mul]
  · rw [if_neg hIQ, mul_zero]
    apply sum_eq_zero
    intro e _
    by_cases hIe : I ⊆ e.val
    · have heQ : ¬e.val ⊆ Q.val := fun h => hIQ (hIe.trans h)
      simp [hIe, heQ]
    · simp [hIe]

/-- Every integral decomposition satisfies the usual local divisibility conditions. -/
theorem IntegrallyDecomposable.degree_dvd {J : Block V r → ℤ}
    (hJ : IntegrallyDecomposable q J) (I : Finset V) (hIr : I.card ≤ r) :
    ((q - I.card).choose (r - I.card) : ℤ) ∣ degree J I := by
  obtain ⟨Φ, rfl⟩ := hJ
  exact ⟨degree Φ I, degree_boundary Φ I hIr⟩

theorem degree_indicator (G : Hypergraph V r) (I : Finset V) :
    degree (indicator G) I = ((G.filter fun e => I ⊆ e.val).card : ℤ) := by
  simp only [degree, indicator, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext e
  simp [and_comm]

/-- The necessary binomial divisibility conditions for an actual design. -/
theorem HasDecomposition.degree_dvd {G : Hypergraph V r}
    (hG : HasDecomposition q G) (I : Finset V) (hIr : I.card ≤ r) :
    (q - I.card).choose (r - I.card) ∣ (G.filter fun e => I ⊆ e.val).card := by
  have h := hG.divisible.degree_dvd I hIr
  rw [degree_indicator] at h
  exact_mod_cast h

/-- For the complete hypergraph, these are the classical necessary conditions
`choose (q-i) (r-i) ∣ choose (n-i) (r-i)`. -/
theorem Divisible.complete_degree_dvd
    (hG : Divisible q (complete V r)) (I : Finset V) (hIr : I.card ≤ r) :
    (q - I.card).choose (r - I.card) ∣
      (Fintype.card V - I.card).choose (r - I.card) := by
  have h := hG.degree_dvd I hIr
  rw [degree_indicator] at h
  have hc : ((complete V r).filter fun e => I ⊆ e.val).card =
      (Fintype.card V - I.card).choose (r - I.card) := by
    simpa [complete] using card_blocks_between (r := r) I univ (subset_univ I) hIr
  rw [hc] at h
  exact_mod_cast h

end Arxiv2411_18291
