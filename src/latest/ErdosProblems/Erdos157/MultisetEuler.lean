import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-!
# An elementary nonvanishing lemma for a free commutative monoid

If the sum of all finite-multiset products is absolutely convergent, it is
nonzero. Finite sieving gives the Euler identity; dominated convergence
removes every nonempty multiset. No analytic continuation is involved.
-/

namespace Erdos157.Elementary.MultisetEuler

open Filter Topology
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

noncomputable def weight (w : α → ℂ) (s : Multiset α) : ℂ := (s.map w).prod

noncomputable def sievedWeight (w : α → ℂ) (A : Finset α) (s : Multiset α) : ℂ :=
  if ∀ a ∈ A, a ∉ s then weight w s else 0

noncomputable def tailSum (w : α → ℂ) (A : Finset α) : ℂ :=
  ∑' s : Multiset α, sievedWeight w A s

theorem norm_sievedWeight_le (w : α → ℂ) (A : Finset α) (s : Multiset α) :
    ‖sievedWeight w A s‖ ≤ ‖weight w s‖ := by
  unfold sievedWeight
  split_ifs <;> simp

theorem summable_sievedWeight (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) (A : Finset α) :
    Summable (sievedWeight w A) :=
  hw.of_norm_bounded (norm_sievedWeight_le w A)

/-- Consing a fixed element bijects all multisets with those containing it. -/
def consEquiv (a : α) : Multiset α ≃ {s : Multiset α // a ∈ s} where
  toFun s := ⟨a ::ₘ s, Multiset.mem_cons_self _ _⟩
  invFun s := s.1.erase a
  left_inv := Multiset.erase_cons_head a
  right_inv s := Subtype.ext (Multiset.cons_erase s.2)

theorem sievedWeight_cons (w : α → ℂ) (A : Finset α) {a : α} (ha : a ∉ A)
    (s : Multiset α) :
    sievedWeight w A (a ::ₘ s) = w a * sievedWeight w A s := by
  have hc : (∀ b ∈ A, b ∉ a ::ₘ s) ↔ ∀ b ∈ A, b ∉ s := by
    constructor
    · intro h b hb hs
      exact h b hb (Multiset.mem_cons_of_mem hs)
    · intro h b hb
      simp only [Multiset.mem_cons, not_or]
      exact ⟨fun heq => ha (heq ▸ hb), h b hb⟩
  simp only [sievedWeight, hc, weight, Multiset.map_cons, Multiset.prod_cons]
  split_ifs <;> simp

theorem tailSum_insert (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) (A : Finset α)
    {a : α} (ha : a ∉ A) :
    tailSum w (insert a A) = (1 - w a) * tailSum w A := by
  classical
  have hs := summable_sievedWeight w hw A
  have hsplit := (hs.subtype (fun s => a ∈ s)).tsum_add_tsum_compl
    (hs.subtype (fun s => a ∉ s))
  have hmem : (∑' s : {s : Multiset α // a ∈ s}, sievedWeight w A s.1) =
      w a * tailSum w A := by
    rw [← (consEquiv a).tsum_eq]
    simp only [consEquiv, Equiv.coe_fn_mk, sievedWeight_cons w A ha]
    exact tsum_mul_left
  have hnotmem : (∑' s : {s : Multiset α // a ∉ s}, sievedWeight w A s.1) =
      tailSum w (insert a A) := by
    calc
      _ = ∑' s : Multiset α, {s : Multiset α | a ∉ s}.indicator (sievedWeight w A) s :=
        tsum_subtype _ _
      _ = _ := by
        apply tsum_congr
        intro s
        by_cases hsa : a ∈ s
        · simp [Set.indicator, hsa, sievedWeight]
        · simp [Set.indicator, hsa, sievedWeight]
  change (∑' s : {s : Multiset α // a ∈ s}, sievedWeight w A s.1) +
    (∑' s : {s : Multiset α // a ∉ s}, sievedWeight w A s.1) = tailSum w A at hsplit
  rw [hmem, hnotmem] at hsplit
  linear_combination hsplit

/-- Finite Euler factors sieve out every multiset containing one of their indices. -/
theorem finite_euler_identity (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) (A : Finset α) :
    tailSum w A = (∏ a ∈ A, (1 - w a)) * ∑' s : Multiset α, weight w s := by
  induction A using Finset.induction with
  | empty => simp [tailSum, sievedWeight]
  | @insert a A ha ih =>
    rw [tailSum_insert w hw A ha, Finset.prod_insert ha, ih, mul_assoc]

/-- As the sieving set grows, only the empty multiset remains. -/
theorem tendsto_tailSum (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) :
    Tendsto (tailSum w) atTop (𝓝 1) := by
  classical
  have hp : ∀ s : Multiset α, Tendsto (fun A : Finset α => sievedWeight w A s)
      atTop (𝓝 (if s = 0 then (1 : ℂ) else 0)) := by
    intro s
    rcases s.empty_or_exists_mem with rfl | ⟨a, ha⟩
    · simpa [sievedWeight, weight] using
        (tendsto_const_nhds : Tendsto (fun _ : Finset α => (1 : ℂ)) atTop (𝓝 1))
    · have hs : s ≠ 0 := by intro h; simpa [h] using ha
      rw [if_neg hs]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({a} : Finset α)] with A hA
      have hamem : a ∈ A := hA (Finset.mem_singleton_self a)
      simp only [sievedWeight]
      rw [if_neg (fun h => h a hamem ha)]
  have ht := tendsto_tsum_of_dominated_convergence hw hp
    (Filter.Eventually.of_forall (fun A s => norm_sievedWeight_le w A s))
  change Tendsto (fun A => ∑' s : Multiset α, sievedWeight w A s) atTop (𝓝 1)
  simpa only [tsum_ite_eq, if_true] using ht

/-- Absolute convergence of the multiset expansion forces its sum to be nonzero. -/
theorem tsum_weight_ne_zero (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) :
    (∑' s : Multiset α, weight w s) ≠ 0 := by
  intro hz
  have hall : ∀ A, tailSum w A = 0 := by
    intro A
    rw [finite_euler_identity w hw A, hz, mul_zero]
  have ht : Tendsto (tailSum w) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall (fun A => (hall A).symm)
  exact zero_ne_one (tendsto_nhds_unique ht (tendsto_tailSum w hw))

/-- Absolute convergence over all multisets includes convergence over singleton factors. -/
theorem summable_norm_weight_singleton (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) : Summable (fun a => ‖w a‖) := by
  have hinj : Function.Injective (fun a : α => ({a} : Multiset α)) := by
    intro a b h
    simpa using h
  have h := hw.comp_injective hinj
  simpa only [Function.comp_def, weight, Multiset.map_singleton, Multiset.prod_singleton] using h

/-- The convergent Euler product is the reciprocal of the multiset expansion. -/
theorem tprod_mul_tsum_eq_one (w : α → ℂ)
    (hw : Summable (fun s : Multiset α => ‖weight w s‖)) :
    (∏' a, (1 - w a)) * (∑' s : Multiset α, weight w s) = 1 := by
  have hnorm : Summable (fun a => ‖-w a‖) := by
    simpa only [norm_neg] using summable_norm_weight_singleton w hw
  have hp : Multipliable (fun a => 1 - w a) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hnorm
  have hprod := hp.hasProd
  change Tendsto (fun A : Finset α => ∏ a ∈ A, (1 - w a)) atTop
    (𝓝 (∏' a, (1 - w a))) at hprod
  have htail := (tendsto_tailSum w hw).congr'
    (Filter.Eventually.of_forall (finite_euler_identity w hw))
  exact tendsto_nhds_unique (hprod.mul_const _) htail

end Erdos157.Elementary.MultisetEuler
