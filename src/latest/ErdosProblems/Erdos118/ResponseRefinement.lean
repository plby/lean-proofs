import ErdosProblems.Erdos118.IntrinsicAnnotations
import ErdosProblems.Erdos118.LastMarkerRefinement

/-! Finite terminal-test refinement at a fixed response family.
The issued family and its state map stay unchanged; only the alphabet,
edge class, and universal response bound are refined. -/

namespace Erdos118.ResponseRefinement

open Negative Negative.Exact LabelledExtensions DecisionStates RamseyGame

noncomputable def front (F : ResponseFamily) (X : F.members → State × State)
    (p : Completed → Completed → Bool) : Game :=
  .response F (fun a ↦ AdaptiveGame.game p (X a))

theorem red_or {H : Set ℕ} (F : ResponseFamily) (X : F.members → State × State)
    (p q : Completed → Completed → Bool)
    (hp : Outcome H (front F X p) false) (hq : Outcome H (front F X q) false) :
    Outcome H (front F X (fun S T ↦ p S T || q S T)) false := by
  cases hp with
  | response _ _ bp _ hp =>
    cases hq with
    | response _ _ bq _ hq =>
      exact Outcome.response F _ (max bp bq) false (fun a ha hb ↦
        EdgeRefinement.red_or p q (X a)
          (hp a ha (fun x hx ↦ (le_max_left _ _).trans_lt (hb x hx)))
          (hq a ha (fun x hx ↦ (le_max_right _ _).trans_lt (hb x hx))))

theorem blue_summand {H : Set ℕ} (hH : H.Infinite)
    (F : ResponseFamily) (X : F.members → State × State)
    (p q : Completed → Completed → Bool)
    (hblue : Outcome H (front F X (fun S T ↦ p S T || q S T)) true) :
    ∃ K ⊆ H, K.Infinite ∧ (Outcome K (front F X p) true ∨ Outcome K (front F X q) true) := by
  obtain ⟨I, hIH, hI, value, hp⟩ := dichotomy (front F X p) H hH
  cases value with
  | true => exact ⟨I, hIH, hI, Or.inl hp⟩
  | false =>
    obtain ⟨K, hKI, hK, value, hq⟩ := dichotomy (front F X q) I hI
    have hKH := hKI.trans hIH
    cases value with
    | true => exact ⟨K, hKH, hK, Or.inr hq⟩
    | false =>
      have hred := red_or F X p q (hp.almost_mono (almostSubset_of_subset hKI)) hq
      have hblueK := hblue.almost_mono (almostSubset_of_subset hKH)
      exact (Outcome.not_both hK _ hblueK hred).elim

theorem refine_test {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (F : ResponseFamily) (X : F.members → State × State)
    (b : ℕ) (hcert : ∀ a : F.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      Outcome H (GraphPayoff.game B o (X a)) true)
    (test : Completed → Completed → Prop) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      ∃ value : Bool, ∃ d : ℕ,
        (∀ a : F.members, (↑a.1 : Set ℕ) ⊆ K → (∀ x ∈ a.1, d < x) →
          Outcome K (GraphPayoff.game C o (X a)) true) ∧
        (∀ S T : Completed, GraphPayoff.payoff C o S T = true →
          @decide (test S T) (Classical.propDecidable _) = value) := by
  let color := IntrinsicAnnotations.color test
  let symm := IntrinsicAnnotations.color_symm test
  let C₀ := EdgeRefinement.edgeClass B color symm false
  let C₁ := EdgeRefinement.edgeClass B color symm true
  have he : (fun S T ↦ GraphPayoff.payoff C₀ o S T || GraphPayoff.payoff C₁ o S T) =
      GraphPayoff.payoff B o := by
    funext S T
    exact EdgeRefinement.payoff_edgeClass_or B color symm o S T
  have hb : Outcome H (front F X
      (fun S T ↦ GraphPayoff.payoff C₀ o S T || GraphPayoff.payoff C₁ o S T)) true := by
    rw [he]
    exact Outcome.response F _ b true hcert
  obtain ⟨K, hKH, hK, hchoice⟩ := blue_summand hH F X _ _ hb
  have finish (value : Bool) (hc : Outcome K
      (front F X (GraphPayoff.payoff (EdgeRefinement.edgeClass B color symm value) o)) true) :
      ∃ d : ℕ, ∀ a : F.members, (↑a.1 : Set ℕ) ⊆ K → (∀ x ∈ a.1, d < x) →
        Outcome K (GraphPayoff.game
          (EdgeRefinement.edgeClass B color symm value) o (X a)) true := by
    cases hc with
    | response _ _ d _ hd => exact ⟨d, hd⟩
  rcases hchoice with hc | hc
  · obtain ⟨d, hd⟩ := finish false hc
    exact ⟨K, hKH, hK, C₀, fun _ _ h ↦ h.1,
      EdgeRefinement.edgeClass_cliqueFree B color symm false 3 hB, false, d, hd,
      IntrinsicAnnotations.class_test test B false o⟩
  · obtain ⟨d, hd⟩ := finish true hc
    exact ⟨K, hKH, hK, C₁, fun _ _ h ↦ h.1,
      EdgeRefinement.edgeClass_cliqueFree B color symm true 3 hB, true, d, hd,
      IntrinsicAnnotations.class_test test B true o⟩

theorem refine_nat (m : ℕ) {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (F : ResponseFamily) (X : F.members → State × State)
    (b : ℕ) (hcert : ∀ a : F.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      Outcome H (GraphPayoff.game B o (X a)) true)
    (test : Completed → Completed → ℕ)
    (hbound : ∀ S T : Completed, GraphPayoff.payoff B o S T = true → test S T ≤ m) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      ∃ value ≤ m, ∃ d : ℕ,
        (∀ a : F.members, (↑a.1 : Set ℕ) ⊆ K → (∀ x ∈ a.1, d < x) →
          Outcome K (GraphPayoff.game C o (X a)) true) ∧
        (∀ S T : Completed, GraphPayoff.payoff C o S T = true → test S T = value) := by
  induction m generalizing H B b with
  | zero =>
    exact ⟨H, Set.Subset.rfl, hH, B, le_rfl, hB, 0, le_rfl, b, hcert,
      fun S T hp ↦ Nat.eq_zero_of_le_zero (hbound S T hp)⟩
  | succ m ih =>
    obtain ⟨I, hIH, hI, D, hDB, hD, value, d, hd, htest⟩ :=
      refine_test hH B hB o F X b hcert (fun S T ↦ test S T = m + 1)
    cases value with
    | true =>
      exact ⟨I, hIH, hI, D, hDB, hD, m + 1, le_rfl, d, hd,
        fun S T hp ↦ @of_decide_eq_true _ (Classical.propDecidable _) (htest S T hp)⟩
    | false =>
      have hbound' : ∀ S T, GraphPayoff.payoff D o S T = true → test S T ≤ m := by
        intro S T hp
        have hold := hbound S T (LastMarkerRefinement.payoff_true_mono hDB o S T hp)
        have hn := @of_decide_eq_false _ (Classical.propDecidable _) (htest S T hp)
        omega
      obtain ⟨K, hKI, hK, C, hCD, hC, v, hv, e, he, hc⟩ := ih hI D hD d hd hbound'
      exact ⟨K, hKI.trans hIH, hK, C, hCD.trans hDB, hC, v, hv.trans (Nat.le_succ m), e, he, hc⟩

end Erdos118.ResponseRefinement
