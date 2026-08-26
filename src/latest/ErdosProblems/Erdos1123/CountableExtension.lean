import ErdosProblems.Erdos1123.CountableSplitting
import ErdosProblems.Erdos1123.SplitAlgebra

/-! # The countable extension theorem for atomless block couplings -/

namespace Erdos1123

open Filter
open scoped Topology

variable {α β : Type*}

theorem WeightSequence.mass_split_union (W : WeightSequence α) (P Q A : Set α) (n : ℕ) :
    W.mass ((P ∩ A) ∪ (Q ∩ Aᶜ)) n = W.mass (P ∩ A) n + W.mass (Q ∩ Aᶜ) n := by
  classical
  unfold WeightSequence.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hA : x ∈ A <;> by_cases hP : x ∈ P <;> by_cases hQ : x ∈ Q <;>
    simp [hA, hP, hQ]

namespace Coupling

variable {W : WeightSequence α} {V : WeightSequence β} (C : Coupling W V)
variable {A : Set α} {B : Set β}

theorem complementary_intersections_matching
    (h : ∀ p : C.algebra,
      Tendsto (fun n => W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n) atTop (𝓝 0))
    (p : C.algebra) :
    Tendsto (fun n => W.mass (p.val.1 ∩ Aᶜ) n - V.mass (p.val.2 ∩ Bᶜ) n) atTop (𝓝 0) := by
  have hlim := (C.matching p.val p.property).sub (h p)
  have heq : (fun n => W.mass p.val.1 n - V.mass p.val.2 n -
      (W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n)) =
      (fun n => W.mass (p.val.1 ∩ Aᶜ) n - V.mass (p.val.2 ∩ Bᶜ) n) := by
    funext n
    have hw := W.mass_inter_add_sdiff p.val.1 A n
    have hv := V.mass_inter_add_sdiff p.val.2 B n
    change W.mass (p.val.1 ∩ A) n + W.mass (p.val.1 ∩ Aᶜ) n = W.mass p.val.1 n at hw
    change V.mass (p.val.2 ∩ B) n + V.mass (p.val.2 ∩ Bᶜ) n = V.mass p.val.2 n at hv
    linarith
  simpa only [heq, sub_zero] using hlim

theorem mix_matching
    (h : ∀ p : C.algebra,
      Tendsto (fun n => W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n) atTop (𝓝 0))
    (p q : C.algebra) :
    Tendsto (fun n => W.mass (mix (A, B) p.val q.val).1 n -
      V.mass (mix (A, B) p.val q.val).2 n) atTop (𝓝 0) := by
  have hlim := (h p).add (C.complementary_intersections_matching h q)
  have heq : (fun n => (W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n) +
      (W.mass (q.val.1 ∩ Aᶜ) n - V.mass (q.val.2 ∩ Bᶜ) n)) =
      (fun n => W.mass (mix (A, B) p.val q.val).1 n -
        V.mass (mix (A, B) p.val q.val).2 n) := by
    funext n
    change _ = W.mass ((p.val.1 ∩ A) ∪ (q.val.1 ∩ Aᶜ)) n -
      V.mass ((p.val.2 ∩ B) ∪ (q.val.2 ∩ Bᶜ)) n
    rw [W.mass_split_union, V.mass_split_union]
    ring
  simpa only [heq, zero_add] using hlim

/-- Adjoin the new pair once all its intersections have been matched. -/
def extendBySplit
    (h : ∀ p : C.algebra,
      Tendsto (fun n => W.mass (p.val.1 ∩ A) n - V.mass (p.val.2 ∩ B) n) atTop (𝓝 0)) :
    Coupling W V where
  algebra := splitAlgebra C.algebra (A, B)
  matching := by
    rintro x ⟨p, hp, q, hq, rfl⟩
    exact C.mix_matching h ⟨p, hp⟩ ⟨q, hq⟩

/-- Extend a countable coupling to contain any prescribed source set. -/
theorem exists_countable_extension [Countable C.algebra]
    (hDisjoint : ∀ n m, n ≠ m → Disjoint (V.support n) (V.support m))
    (δ : ℕ → ℝ) (hδ₀ : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hAtom : ∀ n x, x ∈ V.support n → V.weight n x ≤ δ n) (A : Set α) :
    ∃ D : Coupling W V, Countable D.algebra ∧ C.algebra ≤ D.algebra ∧
      ∃ B : Set β, (A, B) ∈ D.algebra := by
  obtain ⟨B, hB⟩ := C.exists_matching_intersections hDisjoint δ hδ₀ hδ hAtom A
  let D := C.extendBySplit hB
  refine ⟨D, ?_, le_splitAlgebra C.algebra (A, B), B, mem_splitAlgebra C.algebra (A, B)⟩
  exact (splitAlgebra_countable C.algebra (A, B)).to_subtype

end Coupling
end Erdos1123
