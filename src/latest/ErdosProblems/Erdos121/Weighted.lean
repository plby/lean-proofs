import Mathlib

/-!
# Finite nonnegative weights for Erdős Problem 121

Tao's probabilistic proof only uses finite sample spaces.  This file records
the required probability bookkeeping as unnormalised nonnegative finite sums.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

/-- A finite sample space carrying a nonnegative real weight.  Normalisation
is deliberately not part of the structure: all extraction arguments are
homogeneous in the weights. -/
structure FiniteWeight (Ω : Type*) where
  support : Finset Ω
  weight : Ω → ℝ
  weight_nonneg : ∀ ω ∈ support, 0 ≤ weight ω

namespace FiniteWeight

variable {Ω : Type*}

/-- The weight of an event. -/
noncomputable def mass (W : FiniteWeight Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact (W.support.filter P).sum W.weight

theorem mass_nonneg (W : FiniteWeight Ω) (P : Ω → Prop) :
    0 ≤ W.mass P := by
  classical
  unfold mass
  exact Finset.sum_nonneg fun ω hω => W.weight_nonneg ω (Finset.mem_filter.mp hω).1

theorem mass_false (W : FiniteWeight Ω) :
    W.mass (fun _ => False) = 0 := by
  classical
  simp [mass]

theorem mass_true (W : FiniteWeight Ω) :
    W.mass (fun _ => True) = W.support.sum W.weight := by
  classical
  simp [mass]

theorem mass_mono {W : FiniteWeight Ω} {P Q : Ω → Prop}
    (hPQ : ∀ ω ∈ W.support, P ω → Q ω) :
    W.mass P ≤ W.mass Q := by
  classical
  unfold mass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    have hmem := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨hmem.1, hPQ ω hmem.1 hmem.2⟩
  · intro ω hωQ _hωP
    exact W.weight_nonneg ω (Finset.mem_filter.mp hωQ).1

theorem mass_congr {W : FiniteWeight Ω} {P Q : Ω → Prop}
    (hPQ : ∀ ω ∈ W.support, (P ω ↔ Q ω)) :
    W.mass P = W.mass Q := by
  apply le_antisymm
  · exact mass_mono fun ω hω hP => (hPQ ω hω).mp hP
  · exact mass_mono fun ω hω hQ => (hPQ ω hω).mpr hQ

theorem mass_or_le (W : FiniteWeight Ω) (P Q : Ω → Prop) :
    W.mass (fun ω => P ω ∨ Q ω) ≤ W.mass P + W.mass Q := by
  classical
  unfold mass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro ω hω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;>
    simp [hP, hQ, W.weight_nonneg ω hω]

theorem mass_biUnion_le {ι : Type*} (W : FiniteWeight Ω)
    (s : Finset ι) (P : ι → Ω → Prop) :
    W.mass (fun ω => ∃ i ∈ s, P i ω) ≤ s.sum (fun i => W.mass (P i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | @insert a s ha ih =>
      calc
        W.mass (fun ω => ∃ i ∈ insert a s, P i ω)
            = W.mass (fun ω => P a ω ∨ ∃ i ∈ s, P i ω) := by
                apply mass_congr
                intro ω _
                simp
        _ ≤ W.mass (P a) + W.mass (fun ω => ∃ i ∈ s, P i ω) :=
          mass_or_le W _ _
        _ ≤ W.mass (P a) + s.sum (fun i => W.mass (P i)) := by gcongr
        _ = (insert a s).sum (fun i => W.mass (P i)) := by simp [ha]

theorem exists_of_mass_pos {W : FiniteWeight Ω} {P : Ω → Prop}
    (hpos : 0 < W.mass P) : ∃ ω ∈ W.support, P ω := by
  classical
  by_contra hnone
  have hzero : W.mass P = 0 := by
    unfold mass
    apply Finset.sum_eq_zero
    intro ω hω
    have hP : P ω := (Finset.mem_filter.mp hω).2
    exact False.elim (hnone ⟨ω, (Finset.mem_filter.mp hω).1, hP⟩)
  linarith

/-- If the good event has more mass than a covering failure event, some good
outcome avoids the failure event. -/
theorem exists_good_not_failure {W : FiniteWeight Ω} {Good Failure : Ω → Prop}
    (hmore : W.mass Failure < W.mass Good) :
    ∃ ω ∈ W.support, Good ω ∧ ¬ Failure ω := by
  classical
  by_contra hnone
  have hsub : ∀ ω ∈ W.support, Good ω → Failure ω := by
    intro ω hω hGood
    by_contra hFailure
    exact hnone ⟨ω, hω, hGood, hFailure⟩
  exact (not_lt_of_ge (mass_mono hsub)) hmore

/-- Product of two finite weighted spaces. -/
noncomputable def prod {Ξ : Type*} (W : FiniteWeight Ω) (V : FiniteWeight Ξ) :
    FiniteWeight (Ω × Ξ) := by
  classical
  exact
    { support := W.support ×ˢ V.support
      weight := fun p => W.weight p.1 * V.weight p.2
      weight_nonneg := by
        intro p hp
        have hp' := Finset.mem_product.mp hp
        exact mul_nonneg (W.weight_nonneg p.1 hp'.1) (V.weight_nonneg p.2 hp'.2) }

theorem totalMass_prod {Ξ : Type*} (W : FiniteWeight Ω) (V : FiniteWeight Ξ) :
    (W.prod V).mass (fun _ => True) =
      W.mass (fun _ => True) * V.mass (fun _ => True) := by
  classical
  simp only [prod, mass, Finset.filter_true]
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- A finite family of independent identically weighted coordinates. -/
noncomputable def power (W : FiniteWeight Ω) (ι : Type*) [Fintype ι] :
    FiniteWeight (ι → Ω) := by
  classical
  exact
    { support := Fintype.piFinset fun _ : ι => W.support
      weight := fun f => ∏ i, W.weight (f i)
      weight_nonneg := by
        intro f hf
        refine Finset.prod_nonneg fun i _ => W.weight_nonneg (f i) ?_
        exact (Fintype.mem_piFinset.mp hf) i }

theorem totalMass_power (W : FiniteWeight Ω) (ι : Type*) [Fintype ι] :
    (W.power ι).mass (fun _ => True) = (W.mass (fun _ => True)) ^ Fintype.card ι := by
  classical
  simp only [power, mass, Finset.filter_true]
  rw [Finset.sum_prod_piFinset]
  simp [Finset.prod_const]

end FiniteWeight

end Erdos121
