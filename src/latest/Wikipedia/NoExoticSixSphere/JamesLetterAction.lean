import Wikipedia.NoExoticSixSphere.JamesWordTopology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.CompactOpen

/-!
# Joint continuity of the one-letter action

When the pointed base space is locally compact, adjoining one letter is
jointly continuous for its product with the actual James space. The proof
descends the finite-word formula through the presentation quotient. It
does not assume continuity of multiplication on an arbitrary James space.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.James

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

theorem continuous_word_cons_array (n : ℕ) :
    Continuous (fun p : (Fin n → X) × X ↦ letter x₀ p.2 * word x₀ (List.ofFn p.1)) := by
  have hc : Continuous (fun p : (Fin n → X) × X ↦ (Fin.cons p.2 p.1 : Fin (n + 1) → X)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  have h := (continuous_word_array x₀ (n + 1)).comp hc
  simpa only [Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, word_cons] using h

theorem continuous_word_cons_presentation :
    Continuous (fun p : (Σ n : ℕ, Fin n → X) × X ↦ letter x₀ p.2 * presentation x₀ p.1) := by
  let e : ((Σ n : ℕ, Fin n → X) × X) ≃ₜ (Σ n : ℕ, (Fin n → X) × X) :=
    Homeomorph.sigmaProdDistrib
  have hc : Continuous (fun p : Σ n : ℕ, (Fin n → X) × X ↦
      letter x₀ p.2.2 * word x₀ (List.ofFn p.2.1)) :=
    continuous_sigma_iff.mpr (continuous_word_cons_array x₀)
  exact hc.comp e.continuous

theorem continuous_letter_action [LocallyCompactSpace X] :
    Continuous (fun p : X × Space X x₀ ↦ letter x₀ p.1 * p.2) := by
  apply (isQuotientMap_presentation x₀).continuous_lift_prod_right
  exact (continuous_word_cons_presentation x₀).comp continuous_swap

def letterAction [LocallyCompactSpace X] : C(X × Space X x₀, Space X x₀) :=
  ⟨fun p ↦ letter x₀ p.1 * p.2, continuous_letter_action x₀⟩

theorem letterAction_basepoint [LocallyCompactSpace X] (w : Space X x₀) :
    letterAction x₀ (x₀, w) = w := by
  change letter x₀ x₀ * w = w
  rw [letter_basepoint, one_mul]

theorem letterAction_one [LocallyCompactSpace X] (x : X) :
    letterAction x₀ (x, 1) = letter x₀ x := mul_one _

end NoExoticSixSphere.James
