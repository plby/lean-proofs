import Wikipedia.NoExoticSixSphere.JamesReducedWords
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Monoid

/-!
# The actual final topology on reduced words

The topology is induced by all finite Cartesian powers of the original
pointed space. A function out of this space is continuous precisely when
it is continuous on every finite-word presentation. No global continuity
of multiplication, CW structure, or loop-space equivalence is assumed.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.James

variable {X : Type*} (x₀ : X)

def presentation (p : Σ n : ℕ, Fin n → X) : Space X x₀ := word x₀ (List.ofFn p.2)

theorem presentation_surjective : Function.Surjective (presentation x₀) := by
  intro w
  obtain ⟨l, hl⟩ := word_surjective x₀ w
  refine ⟨⟨l.length, l.get⟩, ?_⟩
  simpa only [presentation, List.ofFn_get] using hl

variable [TopologicalSpace X]

instance : TopologicalSpace (Space X x₀) :=
  TopologicalSpace.coinduced (presentation x₀) inferInstance

theorem isQuotientMap_presentation : IsQuotientMap (presentation x₀) :=
  ⟨⟨rfl⟩, presentation_surjective x₀⟩

theorem continuous_word_array (n : ℕ) :
    Continuous (fun v : Fin n → X ↦ word x₀ (List.ofFn v)) :=
  (isQuotientMap_presentation x₀).continuous.comp continuous_sigmaMk

theorem continuous_iff_on_words {Y : Type*} [TopologicalSpace Y] (f : Space X x₀ → Y) :
    Continuous f ↔ ∀ n : ℕ, Continuous (fun v : Fin n → X ↦ f (word x₀ (List.ofFn v))) := by
  change @Continuous (Space X x₀) Y
    (TopologicalSpace.coinduced (presentation x₀) inferInstance) _ f ↔ _
  rw [continuous_coinduced_dom, continuous_sigma_iff]
  rfl

theorem continuous_letter : Continuous (letter x₀) := by
  have h := (continuous_word_array x₀ 1).comp
    (continuous_pi (fun _ : Fin 1 ↦ continuous_id))
  simpa only [Function.comp_def, id_eq, List.ofFn_succ, List.ofFn_zero,
    word_cons, word_nil, mul_one] using h

theorem continuous_word_map {T α : Type*} [TopologicalSpace T]
    (l : List α) (f : T → α → X) (hf : ∀ a, Continuous (fun t ↦ f t a)) :
    Continuous (fun t ↦ word x₀ (l.map (f t))) := by
  have h := (continuous_word_array x₀ l.length).comp
    (continuous_pi (fun i : Fin l.length ↦ hf (l.get i)))
  have he : (fun t ↦ word x₀ (List.ofFn (fun i : Fin l.length ↦ f t (l.get i)))) =
      (fun t ↦ word x₀ (l.map (f t))) := by
    funext t
    rw [List.ofFn_comp', List.ofFn_get]
  exact he ▸ h

variable {N : Type*} [Monoid N] [TopologicalSpace N] [ContinuousMul N]

theorem continuous_lift (f : X → N) (hf : f x₀ = 1) (hc : Continuous f) :
    Continuous (lift x₀ f) := by
  apply (continuous_iff_on_words x₀ _).mpr
  intro n
  induction n with
  | zero =>
    simpa only [List.ofFn_zero, word_nil, map_one] using (continuous_const : Continuous
      (fun _ : Fin 0 → X ↦ (1 : N)))
  | succ n ih =>
    have ht : Continuous (fun v : Fin (n + 1) → X ↦ fun i : Fin n ↦ v i.succ) :=
      continuous_pi (fun i ↦ continuous_apply i.succ)
    have hh := (hc.comp (continuous_apply (0 : Fin (n + 1)))).mul (ih.comp ht)
    apply hh.congr
    intro v
    change f (v 0) * lift x₀ f (word x₀ (List.ofFn (fun i : Fin n ↦ v i.succ))) =
      lift x₀ f (word x₀ (List.ofFn v))
    rw [List.ofFn_succ, word_cons, map_mul, lift_letter x₀ f hf]

end NoExoticSixSphere.James
