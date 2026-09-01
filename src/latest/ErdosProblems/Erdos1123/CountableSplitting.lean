import ErdosProblems.Erdos1123.Coupling
import ErdosProblems.Erdos1123.Diagonal

/-! # Simultaneously splitting all members of a countable coupling -/

namespace Erdos1123

open Filter
open scoped Topology

variable {α β : Type*} {W : WeightSequence α} {V : WeightSequence β}

/-- On disjoint finite blocks with vanishing atom sizes, one new source set can
be matched simultaneously against every member of a countable coupling. -/
theorem Coupling.exists_matching_intersections (C : Coupling W V) [Countable C.algebra]
    (hDisjoint : ∀ n m, n ≠ m → Disjoint (V.support n) (V.support m))
    (δ : ℕ → ℝ) (hδ₀ : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hAtom : ∀ n x, x ∈ V.support n → V.weight n x ≤ δ n) (A : Set α) :
    ∃ B : Set β, ∀ p : C.algebra,
      Tendsto (fun n => W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n) atTop (𝓝 0) := by
  classical
  obtain ⟨p, hp⟩ := exists_surjective_nat C.algebra
  let f (k : ℕ) : α → (Fin k → Bool) := jointLabel (fun i => (p i.val).val.1)
  let g (k : ℕ) : β → (Fin k → Bool) := jointLabel (fun i => (p i.val).val.2)
  let e (k n : ℕ) : ℝ := 2 * W.profileDistance V (f k) (g k) n +
    2 * (Fintype.card (Fin k → Bool) : ℝ) * δ n
  have he₀ (k n : ℕ) : 0 ≤ e k n := by
    have hdist : 0 ≤ W.profileDistance V (f k) (g k) n :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    exact add_nonneg (mul_nonneg htwo hdist)
      (mul_nonneg (mul_nonneg htwo (Nat.cast_nonneg _)) (hδ₀ n))
  have he (k : ℕ) : Tendsto (e k) atTop (𝓝 0) := by
    have h := C.profileDistance_tendsto (fun i : Fin k => p i.val)
    simpa only [e, f, g, mul_zero, zero_add] using
      (h.const_mul 2).add (hδ.const_mul (2 * (Fintype.card (Fin k → Bool) : ℝ)))
  have hex (k n : ℕ) : ∃ B : Set β,
      W.profileDistance V (WeightSequence.splitLabel (f k) A)
        (WeightSequence.splitLabel (g k) B) n ≤ e k n :=
    W.exists_profile_refinement V (f k) (g k) A n (hδ₀ n) (hAtom n)
  choose pieces hPieces using hex
  obtain ⟨k, hk, hek⟩ := exists_diagonal_zero e he₀ he
  let B : Set β := {x | ∃ n, x ∈ V.support n ∧ x ∈ pieces (k n) n}
  have hLocal (n : ℕ) {x : β} (hx : x ∈ V.support n) :
      x ∈ B ↔ x ∈ pieces (k n) n := by
    constructor
    · rintro ⟨m, hxm, hxp⟩
      by_cases hmn : m = n
      · simpa only [hmn] using hxp
      · exact False.elim ((Finset.disjoint_left.mp (hDisjoint m n hmn)) hxm hx)
    · intro hxp
      exact ⟨n, hx, hxp⟩
  refine ⟨B, ?_⟩
  intro r
  obtain ⟨i, hi⟩ := hp r
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) (g := fun n => e (k n) n)
  · filter_upwards [hk.eventually (eventually_gt_atTop i)] with n hin
    let event : Set ((Fin (k n) → Bool) × Bool) :=
      {z | z.1 ⟨i, hin⟩ = true ∧ z.2 = true}
    have hsource : (WeightSequence.splitLabel (f (k n)) A) ⁻¹' event = r.val.1 ∩ A := by
      ext x
      simp [event, f, jointLabel, WeightSequence.splitLabel, hi]
    have htarget : (WeightSequence.splitLabel (g (k n)) (pieces (k n) n)) ⁻¹' event =
        r.val.2 ∩ pieces (k n) n := by
      ext x
      simp [event, g, jointLabel, WeightSequence.splitLabel, hi]
    have hm : V.mass (r.val.2 ∩ B) n = V.mass (r.val.2 ∩ pieces (k n) n) n := by
      apply V.mass_congr
      intro x hx
      exact and_congr Iff.rfl (hLocal n hx)
    have hbound := W.abs_mass_preimage_sub_le V
      (WeightSequence.splitLabel (f (k n)) A)
      (WeightSequence.splitLabel (g (k n)) (pieces (k n) n)) event n
    rw [hsource, htarget, ← hm] at hbound
    exact hbound.trans (hPieces (k n) n)
  · exact hek

end Erdos1123
