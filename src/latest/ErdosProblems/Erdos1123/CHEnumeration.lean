import ErdosProblems.Erdos1123.DensityAlgebras
import ErdosProblems.Erdos1123.CountableRecursion
import Mathlib.SetTheory.Cardinal.Aleph

/-! # The precise use of CH: enumerating all subsets of `ℕ` in order type `ω₁` -/

namespace Erdos1123

open scoped Cardinal

/-- A small type representing the least uncountable ordinal. -/
abbrev OmegaOne := (Cardinal.aleph 1).ord.ToType

theorem omegaOne_initial_countable (i : OmegaOne) : (Set.Iio i).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt i (by simp [OmegaOne])
  simpa [OmegaOne] using h

/-- CH supplies an enumeration in which every strict initial segment is countable. -/
noncomputable def chEnumeration (hCH : ContinuumHypothesis) : OmegaOne ≃ Set ℕ :=
  Classical.choice (Cardinal.eq.mp (by
    calc
      Cardinal.mk OmegaOne = Cardinal.aleph 1 := by simp [OmegaOne]
      _ = Cardinal.mk (Set ℕ) := hCH.symm.trans Cardinal.mk_set_nat.symm))

theorem chEnumeration_surjective (hCH : ContinuumHypothesis) :
    Function.Surjective (chEnumeration hCH) := (chEnumeration hCH).surjective

/-- CH bookkeeping for one requirement per subset of `ℕ`. The countable
extension property remains an explicit obligation of every application. -/
theorem exists_good_meeting_all_sets {α : Type*} (hCH : ContinuumHypothesis)
    (Good : Set α → Prop) (Requirement : Set ℕ → Set α → Prop)
    (hStart : ∃ s, s.Countable ∧ Good s)
    (hUnion : ∀ {κ : Type} (f : κ → Set α), Directed (· ⊆ ·) f →
      (∀ i, Good (f i)) → Good (⋃ i, f i))
    (hReq : ∀ A {s t}, s ⊆ t → Requirement A s → Requirement A t)
    (hExtend : ∀ s, s.Countable → Good s → ∀ A,
      ∃ t, t.Countable ∧ Good t ∧ s ⊆ t ∧ Requirement A t) :
    ∃ s, Good s ∧ ∀ A, Requirement A s := by
  obtain ⟨s, hs, hreq⟩ := exists_good_meeting_all omegaOne_initial_countable
    Good (fun i => Requirement (chEnumeration hCH i)) hStart hUnion
    (fun i => hReq (chEnumeration hCH i))
    (fun s hc hg i => hExtend s hc hg (chEnumeration hCH i))
  refine ⟨s, hs, fun A => ?_⟩
  obtain ⟨i, rfl⟩ := chEnumeration_surjective hCH A
  exact hreq i

end Erdos1123
