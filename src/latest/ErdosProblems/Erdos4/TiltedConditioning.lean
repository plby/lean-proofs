import ErdosProblems.Erdos4.TiltedSieve

/-!
# Conditioning the tilted sieve

Root survival has strictly positive probability. Conditioning on it
preserves coordinate independence, and the conditional coordinate law is
computed by deleting the forbidden root residue. No independence between
different target integers is used.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

theorem prob_eq_weight {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (b : Ω) :
    ν.prob (fun a => a = b) = ν.weight b := by
  classical
  simp only [FiniteLaw.prob]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [hab]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

noncomputable def rootedLocalLaw (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) : FiniteLaw (ZMod s) :=
  (localLaw s hs u hu0.le hu1).condition (fun a => a ≠ v) 0

/-- Exact deletion and renormalization at one coordinate. -/
theorem rootedLocalLaw_prob_eq (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v b : ZMod s) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a = b) =
      (if b = v then 0 else localWeight s u b) /
        (if v = 0 then beta s u else baseline s u) := by
  rw [prob_eq_weight, rootedLocalLaw,
    FiniteLaw.condition_weight _ _ _ _ (localLaw_prob_ne_pos s hs u hu0 hu1 v).ne',
    localLaw_prob_ne]
  by_cases h : b = v <;> simp [h, localLaw]

theorem rootedLocalLaw_zero_root (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (b : ZMod s) (hb : b ≠ 0) :
    (rootedLocalLaw s hs u hu0 hu1 0).prob (fun a => a = b) =
      1 / ((s : ℝ) - 1) := by
  rw [rootedLocalLaw_prob_eq]
  simp only [if_neg hb, if_true, localWeight]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  unfold beta atom
  field_simp [hu0.ne', (denominator_pos hs hu0.le).ne',
    show (s : ℝ) - 1 ≠ 0 by linarith]

theorem rootedLocalLaw_nonzero_root (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v b : ZMod s)
    (hv : v ≠ 0) (hb : b ≠ 0) (hbv : b ≠ v) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a = b) =
      u / ((s : ℝ) - 1) := by
  rw [rootedLocalLaw_prob_eq]
  simp only [if_neg hbv, if_neg hv, localWeight, if_neg hb]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  unfold atom baseline
  field_simp [(denominator_pos hs hu0.le).ne',
    show (s : ℝ) - 1 ≠ 0 by linarith]

theorem rootedLocalLaw_zero_outcome (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) (hv : v ≠ 0) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a = 0) =
      (1 - beta s u) / baseline s u := by
  rw [rootedLocalLaw_prob_eq]
  simp [hv, Ne.symm hv, localWeight]

/-- The complete one-target formula in Appendix A. -/
theorem rootedLocalLaw_survival (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v n : ZMod s) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ≠ n) =
      if n = v then 1
      else if v = 0 then ((s : ℝ) - 2) / ((s : ℝ) - 1)
      else if n = 0 then u * ((s : ℝ) - 2) / ((s : ℝ) - 1)
      else 1 - u / ((s : ℝ) - 1) := by
  rw [FiniteLaw.prob_compl]
  by_cases hnv : n = v
  · rw [rootedLocalLaw_prob_eq]
    simp [hnv]
  simp only [if_neg hnv]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
  by_cases hv : v = 0
  · subst v
    rw [rootedLocalLaw_zero_root s hs u hu0 hu1 n hnv]
    simp only [if_true]
    field_simp
    ring
  simp only [if_neg hv]
  by_cases hn : n = 0
  · subst n
    rw [rootedLocalLaw_zero_outcome s hs u hu0 hu1 v hv]
    simp only [if_true]
    unfold beta baseline atom
    field_simp [(denominator_pos hs hu0.le).ne', hs1]
    ring
  · rw [rootedLocalLaw_nonzero_root s hs u hu0 hu1 v n hv hn hnv]
    simp only [if_neg hn]

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def rootedSieveLaw (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) :
    FiniteLaw (∀ l, ZMod (ell l)) := by
  classical
  exact (sieveLaw ell τ hτ).condition (fun a => Survives ell a {v}) (fun _ => 0)

/-- Equation (5.2): coordinate independence survives root conditioning. -/
theorem rootedSieveLaw_prob_all (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ)
    (E : ∀ l, ZMod (ell l) → Prop) :
    (rootedSieveLaw ell τ hτ v).prob (fun a => ∀ l, E l (a l)) =
      ∏ l, (rootedLocalLaw (ell l) (Fact.out : (ell l).Prime).two_le
        ((ell l : ℝ) ^ (-τ)) (rpow_tilt_pos (Fact.out : (ell l).Prime).two_le τ)
        (rpow_tilt_le_one (Fact.out : (ell l).Prime).two_le hτ) (v : ZMod (ell l))).prob
        (E l) := by
  classical
  rw [rootedSieveLaw,
    FiniteLaw.condition_prob _ _ _ _ (sieveLaw_singleton_pos ell τ hτ v).ne']
  have heq : (fun a : ∀ l, ZMod (ell l) => Survives ell a {v} ∧ ∀ l, E l (a l)) =
      (fun a => ∀ l, a l ≠ (v : ZMod (ell l)) ∧ E l (a l)) := by
    funext a
    apply propext
    simp only [Survives, residues, Finset.image_singleton, Finset.mem_singleton,
      forall_and]
  rw [heq, sieveLaw_prob_all ell τ hτ (fun l a => a ≠ (v : ZMod (ell l)) ∧ E l a),
    sieveLaw_survival_product]
  simp only [residues, Finset.image_singleton, Finset.mem_singleton]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro l _
  symm
  exact FiniteLaw.condition_prob _ _ _ _
    (residueLaw_survival_pos (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v).ne'

end Erdos4.Tilted
