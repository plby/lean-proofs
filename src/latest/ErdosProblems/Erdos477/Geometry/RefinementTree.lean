/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Pruning a finite refinement of plane auxiliary equations.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.TransitionBound

namespace Erdos477.Geometry

open scoped BigOperators

lemma exists_loss_step (P : ℕ → Prop) (r : ℕ) (h0 : P 0) (hr : ¬ P r) :
    ∃ t < r, P t ∧ ¬ P (t + 1) := by
  induction r with
  | zero => exact (hr h0).elim
  | succ r ih =>
      by_cases h : P r
      · exact ⟨r, Nat.lt_succ_self r, h, hr⟩
      · obtain ⟨t, ht, hyes, hno⟩ := ih h
        exact ⟨t, ht.trans (Nat.lt_succ_self r), hyes, hno⟩

variable {K X I : Type*} [Field K] [Infinite K] [DecidableEq I]

/-- A refining family of auxiliary equations leaves bounded-degree root
factors and an exceptional set controlled by the sum of the edge costs.
The projection is required to be injective only on the finite point set. -/
theorem exists_pruned_plane_cover (S : Finset X) (π : X → K × K)
    (hinj : Set.InjOn π S) (r : ℕ) (cls : ℕ → X → I) (parent : ℕ → I → I)
    (a0 : I) (hroot : ∀ z ∈ S, cls 0 z = a0)
    (hparent : ∀ t < r, ∀ z ∈ S, cls t z = parent t (cls (t + 1) z))
    (P : ℕ → I → MvPolynomial (Fin 2) K) (hroot0 : P 0 a0 ≠ 0)
    (d : ℕ → ℝ) (hd : ∀ t ≤ r, 0 ≤ d t)
    (hP : ∀ t ≤ r, ∀ z ∈ S, P t (cls t z) ≠ 0 ∧
      ((P t (cls t z)).totalDegree : ℝ) ≤ d t ∧
      MvPolynomial.eval ![(π z).1, (π z).2] (P t (cls t z)) = 0) :
    ∃ C : Finset (MvPolynomial (Fin 2) K), ∃ E : Finset X,
      (∀ F ∈ C, Irreducible F ∧ F ∣ P 0 a0 ∧ (F.totalDegree : ℝ) ≤ d r) ∧
      C.card ≤ (P 0 a0).totalDegree ∧ E ⊆ S ∧
      (∀ z ∈ S, z ∈ E ∨ ∃ F ∈ C, MvPolynomial.eval ![(π z).1, (π z).2] F = 0) ∧
      (E.card : ℝ) ≤ ∑ t ∈ Finset.range r,
        ((S.image (cls (t + 1))).card : ℝ) * d t * d (t + 1) := by
  classical
  obtain ⟨C0, hirr, hpair, _, hcard, hcover⟩ := exists_distinct_factor_cover (P 0 a0) hroot0
  let C := C0.filter (fun F => ∃ a ∈ S.image (cls r), F ∣ P r a)
  let T : ℕ → I → Finset (MvPolynomial (Fin 2) K) := fun t a =>
    C0.filter (fun F => F ∣ P t (parent t a) ∧ ¬ F ∣ P (t + 1) a)
  let D : ℕ → I → Finset X := fun t a =>
    S.filter (fun z => cls (t + 1) z = a ∧
      ∃ F ∈ T t a, MvPolynomial.eval ![(π z).1, (π z).2] F = 0)
  let E := (Finset.range r).biUnion (fun t => (S.image (cls (t + 1))).biUnion (D t))
  have hDsub (t a) : D t a ⊆ S := Finset.filter_subset _ _
  have hD (t) (ht : t < r) (a) (ha : a ∈ S.image (cls (t + 1))) :
      ((D t a).card : ℝ) ≤ d t * d (t + 1) := by
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
    have hpa : cls t z = parent t a := by rw [← hza]; exact hparent t ht z hz
    have hprev := hP t ht.le z hz
    have hnext := hP (t + 1) ht z hz
    rw [hpa] at hprev
    rw [hza] at hnext
    have hb := card_component_drop_le (P t (parent t a)) (P (t + 1) a) hprev.1
      (T t a) (fun F hF => (hirr F (Finset.mem_filter.mp hF).1).1)
      (hpair.mono (Finset.filter_subset _ _))
      (fun F hF => (Finset.mem_filter.mp hF).2.1)
      (fun F hF => (Finset.mem_filter.mp hF).2.2)
      ((D t a).image π) (by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have hv' := Finset.mem_filter.mp hv
        have heval := (hP (t + 1) ht v hv'.1).2.2
        rw [hv'.2.1] at heval
        exact ⟨heval, hv'.2.2⟩)
    rw [Finset.card_image_of_injOn (hinj.mono (hDsub t a))] at hb
    have hb' : ((D t a).card : ℝ) ≤
        (P t (parent t a)).totalDegree * (P (t + 1) a).totalDegree := by exact_mod_cast hb
    exact hb'.trans (mul_le_mul hprev.2.1 hnext.2.1 (Nat.cast_nonneg _) (hd t ht.le))
  refine ⟨C, E, ?_, (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨hF0, a, ha, hdiv⟩ := Finset.mem_filter.mp hF
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    have hp := hP r le_rfl z hz
    have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hp.1
    exact ⟨(hirr F hF0).1, (hirr F hF0).2, (Nat.cast_le.mpr hdeg).trans hp.2.1⟩
  · intro z hz
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp ht
    exact hDsub t a ha
  · intro z hz
    have hzero := (hP 0 (Nat.zero_le r) z hz).2.2
    rw [hroot z hz] at hzero
    obtain ⟨F, hF, hFz⟩ := hcover ![(π z).1, (π z).2] hzero
    by_cases hFC : F ∈ C
    · exact Or.inr ⟨F, hFC, hFz⟩
    · have hterminal : ¬ F ∣ P r (cls r z) := by
        intro h
        exact hFC (Finset.mem_filter.mpr ⟨hF, cls r z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, h⟩)
      have hinitial : F ∣ P 0 (cls 0 z) := by rw [hroot z hz]; exact (hirr F hF).2
      obtain ⟨t, ht, hyes, hno⟩ := exists_loss_step (fun t => F ∣ P t (cls t z)) r
        hinitial hterminal
      have hFT : F ∈ T t (cls (t + 1) z) := by
        apply Finset.mem_filter.mpr
        exact ⟨hF, (hparent t ht z hz) ▸ hyes, hno⟩
      apply Or.inl
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr ht,
        Finset.mem_biUnion.mpr ⟨cls (t + 1) z, Finset.mem_image.mpr ⟨z, hz, rfl⟩,
          Finset.mem_filter.mpr ⟨hz, rfl, F, hFT, hFz⟩⟩⟩
  · have hnat : E.card ≤ ∑ t ∈ Finset.range r,
        ∑ a ∈ S.image (cls (t + 1)), (D t a).card := by
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
    have hreal : (E.card : ℝ) ≤ ∑ t ∈ Finset.range r,
        ∑ a ∈ S.image (cls (t + 1)), ((D t a).card : ℝ) := by exact_mod_cast hnat
    apply hreal.trans
    apply Finset.sum_le_sum
    intro t ht
    calc
      _ ≤ ∑ _a ∈ S.image (cls (t + 1)), d t * d (t + 1) :=
        Finset.sum_le_sum (hD t (Finset.mem_range.mp ht))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]

#print axioms exists_pruned_plane_cover
-- 'Erdos477.Geometry.exists_pruned_plane_cover' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
