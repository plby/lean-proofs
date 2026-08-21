import ErdosProblems.Erdos239.External.Erdos67.MRTMajorArc

/-!
# Uniformizing finitely many Matomäki--Radziwiłł thresholds

The analytic theorem naturally returns a threshold `X₀(H)` after `H` has
been fixed.  Downstream, `H` ranges over a fixed finite interval.  Taking the
finite supremum therefore produces a single threshold without changing the
source-level quantifier order.
-/

open scoped BigOperators
open Finset

namespace Erdos67

/-- A family of eventual natural-number statements indexed by a finite set
admits one common threshold. -/
theorem exists_uniform_nat_threshold_on_finset
    {α : Type*} [DecidableEq α] (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a ∈ s, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → P a X) :
    ∃ X₀ : ℕ, ∀ a ∈ s, ∀ X : ℕ, X₀ ≤ X → P a X := by
  classical
  let threshold : {a : α // a ∈ s} → ℕ := fun a =>
    Classical.choose (hP a.1 a.2)
  let X₀ : ℕ := s.attach.sup threshold
  refine ⟨X₀, ?_⟩
  intro a ha X hX
  let a' : {a : α // a ∈ s} := ⟨a, ha⟩
  have haMem : a' ∈ s.attach := by simp [a']
  have hthreshold : threshold a' ≤ X₀ := by
    exact Finset.le_sup haMem
  have hspec : ∀ Y : ℕ, threshold a' ≤ Y → P a'.1 Y := by
    exact Classical.choose_spec (hP a'.1 a'.2)
  exact hspec X (hthreshold.trans hX)

/-- In particular, pointwise thresholds on the natural interval
`[Hmin,Hmax]` can be replaced by one common threshold. -/
theorem exists_uniform_nat_threshold_on_Icc
    {Hmin Hmax : ℕ} (P : ℕ → ℕ → Prop)
    (hP : ∀ H ∈ Finset.Icc Hmin Hmax,
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → P H X) :
    ∃ X₀ : ℕ, ∀ H ∈ Finset.Icc Hmin Hmax,
      ∀ X : ℕ, X₀ ≤ X → P H X := by
  apply exists_uniform_nat_threshold_on_finset
    (Finset.Icc Hmin Hmax) P hP

end Erdos67
