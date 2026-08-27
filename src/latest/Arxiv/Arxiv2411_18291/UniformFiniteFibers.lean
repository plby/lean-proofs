import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniform probabilities for maps with equal finite fibers

If all fibers have the same cardinality, a uniform input lands in a given
set of outputs with probability equal to that set's fraction of the codomain.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem card_preimage_of_equal_fibers (f : A → B) (b : B)
    (hf : ∀ c, (univ.filter fun a => f a = c).card = (univ.filter fun a => f a = b).card)
    (D : Finset B) :
    (univ.filter fun a => f a ∈ D).card = D.card * (univ.filter fun a => f a = b).card := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter univ D f]
  simp only [hf, sum_const, smul_eq_mul]

theorem uniform_equal_fibers_probability [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → B) (b : B)
    (hf : ∀ c, (univ.filter fun a => f a = c).card = (univ.filter fun a => f a = b).card)
    (D : Finset B) :
    (PMF.uniformOfFintype A).toMeasure.real {a | f a ∈ D} = D.card / (Fintype.card B : ℝ) := by
  classical
  let k := (univ.filter fun a => f a = b).card
  have htotal : Fintype.card A = Fintype.card B * k := by
    simpa only [mem_univ, filter_true, card_univ] using card_preimage_of_equal_fibers f b hf univ
  have hk : 0 < k := by
    have ha := Fintype.card_pos (α := A)
    rw [htotal] at ha
    apply Nat.pos_of_ne_zero
    intro hk
    simp only [hk, mul_zero, lt_self_iff_false] at ha
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hevent := card_preimage_of_equal_fibers f b hf D
  have hmeas : MeasurableSet {a | f a ∈ D} := (Set.toFinite _).measurableSet
  rw [PMF.uniformOfFintype, measureReal_def,
    PMF.toMeasure_uniformOfFinset_apply _ _ hmeas, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [Set.mem_ofPred_eq, card_univ]
  rw [hevent, htotal]
  change ((D.card * k : ℕ) : ℝ) / ((Fintype.card B * k : ℕ) : ℝ) = _
  push_cast
  exact mul_div_mul_right _ _ hkR.ne'

end Arxiv2411_18291
