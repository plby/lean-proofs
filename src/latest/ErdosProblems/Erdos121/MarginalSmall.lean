import ErdosProblems.Erdos121.MassBounds

/-!
# The small-prime cancellation in a marginal

After one output coordinate is fixed, a small prime dividing that output has
to be assigned to one of the four incident edges.  Multiplication by the
small vertex factor cancels its `1/q` weight.  Every other small prime has
only the six nonincident edge labels available.  The resulting Euler product
is bounded by `smallEuler 6`.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

def smallLabelIncident (v : Fin 5) (a : Fin 11) : Prop :=
  (![a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4,
      a = 1 ∨ a = 5 ∨ a = 6 ∨ a = 7,
      a = 2 ∨ a = 5 ∨ a = 8 ∨ a = 9,
      a = 3 ∨ a = 6 ∨ a = 8 ∨ a = 10,
      a = 4 ∨ a = 7 ∨ a = 9 ∨ a = 10] : Fin 5 → Prop) v

instance (v : Fin 5) (a : Fin 11) : Decidable (smallLabelIncident v a) :=
  Classical.propDecidable _

lemma smallLabelIncident_zero (v : Fin 5) : ¬ smallLabelIncident v 0 := by
  fin_cases v <;> simp [smallLabelIncident]

lemma prime_dvd_smallEdgeFactor_iff {Y : ℕ} (σ : SmallAssignment Y)
    (q : SmallPrime Y) (e : Fin 10) :
    (q : ℕ) ∣ smallEdgeFactor σ e ↔ σ q = e.succ := by
  have hqPrime := (Erdos469.mem_primesThrough.mp q.property).1
  rw [smallEdgeFactor, hqPrime.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨r, hr, hdiv⟩
    split at hdiv
    · rename_i ha
      have hrPrime := (Erdos469.mem_primesThrough.mp r.property).1
      rcases (Nat.dvd_prime hrPrime).mp hdiv with hqOne | hqr
      · exact (hqPrime.ne_one hqOne).elim
      · have hsub : q = r := Subtype.ext hqr
        simpa [hsub] using ha
    · have hqOne : (q : ℕ) = 1 := Nat.dvd_one.mp (by simpa using hdiv)
      exact (hqPrime.ne_one hqOne).elim
  · intro hlabel
    refine ⟨q, Finset.mem_univ _, ?_⟩
    simp [hlabel]

lemma prime_dvd_smallVertexFactor_iff {Y : ℕ} (σ : SmallAssignment Y)
    (q : SmallPrime Y) (v : Fin 5) :
    (q : ℕ) ∣ k5Tuple (smallEdgeFactor σ) v ↔
      smallLabelIncident v (σ q) := by
  have hqPrime := (Erdos469.mem_primesThrough.mp q.property).1
  fin_cases v <;>
    simp [k5Tuple, smallLabelIncident,
      hqPrime.dvd_mul, prime_dvd_smallEdgeFactor_iff] <;> tauto

lemma smallVertexFactor_eq_prod {Y : ℕ} (σ : SmallAssignment Y)
    (v : Fin 5) :
    k5Tuple (smallEdgeFactor σ) v =
      ∏ q : SmallPrime Y,
        if smallLabelIncident v (σ q) then (q : ℕ) else 1 := by
  fin_cases v <;>
    simp only [Fin.mk_one, Fin.isValue, Finset.univ_eq_attach, Fin.reduceFinMk, Fin.zero_eta] <;>
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib] <;>
    apply Finset.prod_congr rfl
  all_goals
    intro q hq
    generalize ha : σ q = a
    fin_cases a <;> simp [smallLabelIncident, ha]

def smallMarginalLocalWeight {Y : ℕ} (v : Fin 5) (q : SmallPrime Y)
    (a : Fin 11) : ℝ :=
  smallLocalWeight q a *
    (if smallLabelIncident v a then (q : ℕ) else 1)

lemma smallAssignment_mul_vertexFactor {Y : ℕ} (σ : SmallAssignment Y)
    (v : Fin 5) :
    smallAssignmentWeight σ * (k5Tuple (smallEdgeFactor σ) v : ℝ) =
      ∏ q, smallMarginalLocalWeight v q (σ q) := by
  rw [smallAssignmentWeight, smallVertexFactor_eq_prod, Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  simp [smallMarginalLocalWeight]

lemma sum_smallMarginalLocalWeight_restricted_le {Y : ℕ} (v : Fin 5)
    (q : SmallPrime Y) (n : ℕ) :
    (∑ a : Fin 11,
      if (smallLabelIncident v a ↔ (q : ℕ) ∣ n) then
        smallMarginalLocalWeight v q a else 0) ≤
      1 + (6 : ℝ) / (4 * (q : ℕ)) := by
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.ne_zero
  have hqpos : (0 : ℝ) < (q : ℕ) := by
    exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.pos
  by_cases hqn : (q : ℕ) ∣ n
  · fin_cases v <;>
      simp [hqn, smallMarginalLocalWeight, smallLocalWeight,
        smallLabelIncident, Fin.sum_univ_succ, hq0] <;>
      ring_nf
    all_goals
      rw [mul_inv_cancel₀ hq0]
      exact le_add_of_nonneg_right
        (mul_nonneg (inv_nonneg.mpr hqpos.le) (by norm_num))
  · fin_cases v <;>
      simp [hqn, smallMarginalLocalWeight, smallLocalWeight,
        smallLabelIncident, Fin.sum_univ_succ, hq0] <;>
      ring_nf <;> rfl

def SmallIncidentCondition {Y : ℕ} (v : Fin 5) (n : ℕ)
    (σ : SmallAssignment Y) : Prop :=
  ∀ q : SmallPrime Y,
    smallLabelIncident v (σ q) ↔ (q : ℕ) ∣ n

instance {Y : ℕ} (v : Fin 5) (n : ℕ) (σ : SmallAssignment Y) :
    Decidable (SmallIncidentCondition v n σ) := Classical.propDecidable _

/-- Exact finite Euler-product cancellation for the small part of one fixed
marginal. -/
theorem sum_small_marginal_le (Y n : ℕ) (v : Fin 5) :
    (∑ σ : SmallAssignment Y,
      if SmallIncidentCondition v n σ then
        smallAssignmentWeight σ * (k5Tuple (smallEdgeFactor σ) v : ℝ)
      else 0) ≤ smallEuler 6 Y := by
  calc
    _ = ∑ σ : SmallAssignment Y,
        ∏ q, if (smallLabelIncident v (σ q) ↔ (q : ℕ) ∣ n) then
          smallMarginalLocalWeight v q (σ q) else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases hcond : SmallIncidentCondition v n σ
      · rw [if_pos hcond]
        rw [smallAssignment_mul_vertexFactor]
        apply Finset.prod_congr rfl
        intro q hq
        rw [if_pos (hcond q)]
      · rw [if_neg hcond]
        obtain ⟨q, hq⟩ := Classical.not_forall.mp hcond
        have hzero :
            (if (smallLabelIncident v (σ q) ↔ (q : ℕ) ∣ n) then
              smallMarginalLocalWeight v q (σ q) else 0) = 0 :=
          if_neg hq
        exact (Finset.prod_eq_zero (Finset.mem_univ q) hzero).symm
    _ = ∏ q : SmallPrime Y,
        ∑ a : Fin 11,
          if (smallLabelIncident v a ↔ (q : ℕ) ∣ n) then
            smallMarginalLocalWeight v q a else 0 := by
      exact (Fintype.prod_sum fun (q : SmallPrime Y) (a : Fin 11) =>
        if (smallLabelIncident v a ↔ (q : ℕ) ∣ n) then
          smallMarginalLocalWeight v q a else 0).symm
    _ ≤ ∏ q : SmallPrime Y, (1 + (6 : ℝ) / (4 * (q : ℕ))) := by
      apply Finset.prod_le_prod
      · intro q hq
        apply Finset.sum_nonneg
        intro a ha
        split
        · exact mul_nonneg (smallLocalWeight_nonneg q a) (by positivity)
        · norm_num
      · intro q hq
        exact sum_smallMarginalLocalWeight_restricted_le v q n
    _ = smallEuler 6 Y := by
      rw [smallEuler]
      exact Finset.prod_attach (Erdos469.primesThrough Y)
        (fun p : ℕ => 1 + (6 : ℝ) / (4 * p))

end

end Erdos121
