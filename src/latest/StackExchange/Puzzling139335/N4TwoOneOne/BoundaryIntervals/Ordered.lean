import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

/-!
# Closed, ordered contacts partition an interval

The interval structure in this file is a conclusion.  The geometric input is
only the absence of four strictly alternating contacts along a parametrized
side.  No polygonal or interval-contact hypothesis is imposed on the pieces.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.BoundaryIntervals

variable {X : Type*}

/-- Four strictly alternating contacts do not occur along the unit parameter
interval. -/
def Noninterlacing (γ : ℝ → X) (P Q : Set X) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, 0 ≤ a → a < b → b < c → c < d → d ≤ 1 →
    γ a ∈ P → γ c ∈ P → γ b ∈ Q → γ d ∈ Q → False

/-- All contacts of the first piece precede all contacts of the second piece. -/
def OrderedContacts (γ : ℝ → X) (P Q : Set X) : Prop :=
  ∀ ⦃s t : ℝ⦄, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
    γ s ∈ P → γ t ∈ Q → s ≤ t

/-- Unique ownership of the two endpoints converts noninterlacing into an
ordering of every pair of contacts. -/
theorem ordered_contacts_of_noninterlacing {γ : ℝ → X} {P Q : Set X}
    (hNI : Noninterlacing γ P Q)
    (h0P : γ 0 ∈ P) (h0Q : γ 0 ∉ Q)
    (h1P : γ 1 ∉ P) (h1Q : γ 1 ∈ Q) : OrderedContacts γ P Q := by
  intro s t hs ht hsP htQ
  by_contra hst
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    exact h0Q (h ▸ htQ))
  have hs1 : s < 1 := lt_of_le_of_ne hs.2 (by
    intro h
    exact h1P (h ▸ hsP))
  exact hNI (by norm_num) ht0 (lt_of_not_ge hst) hs1 (by norm_num)
    h0P hsP htQ h1Q

/-- Two closed sets covering the unit interval and ordered from opposite
endpoints meet at a unique cutoff in the open interval. -/
theorem exists_cutoff_of_closed_ordered {A B : Set ℝ}
    (hA : IsClosed A) (hB : IsClosed B)
    (h0A : 0 ∈ A) (h0B : 0 ∉ B) (h1A : 1 ∉ A) (_h1B : 1 ∈ B)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ A ∨ t ∈ B)
    (horder : ∀ ⦃s t : ℝ⦄, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      s ∈ A → t ∈ B → s ≤ t) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (t ∈ A ↔ t ≤ l) ∧ (t ∈ B ↔ l ≤ t) := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ∩ A) := isCompact_Icc.inter_right hA
  obtain ⟨l, hl, hmax⟩ := hcompact.exists_isGreatest
    ⟨0, ⟨⟨by norm_num, by norm_num⟩, h0A⟩⟩
  have hl1 : l < 1 := lt_of_le_of_ne hl.1.2 (by
    intro h
    exact h1A (h ▸ hl.2))
  have htail : Ioc l 1 ⊆ B := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hl.1.1 ht.1.le, ht.2⟩
    rcases hcover t htI with htA | htB
    · exact False.elim ((not_le_of_gt ht.1) (hmax ⟨htI, htA⟩))
    · exact htB
  have hlB : l ∈ B := by
    have hcl := closure_minimal htail hB
    rw [closure_Ioc hl1.ne] at hcl
    exact hcl ⟨le_rfl, hl1.le⟩
  have hl0 : 0 < l := lt_of_le_of_ne hl.1.1 (by
    intro h
    exact h0B (h ▸ hlB))
  refine ⟨l, ⟨hl0, hl1⟩, ?_⟩
  intro t ht
  constructor
  · constructor
    · intro htA
      exact hmax ⟨ht, htA⟩
    · intro htl
      rcases hcover t ht with htA | htB
      · exact htA
      · have heq : t = l := le_antisymm htl (horder hl.1 ht hl.2 htB)
        exact heq.symm ▸ hl.2
  · constructor
    · intro htB
      exact horder hl.1 ht hl.2 htB
    · intro hlt
      rcases hcover t ht with htA | htB
      · have heq : t = l := le_antisymm (hmax ⟨ht, htA⟩) hlt
        exact heq.symm ▸ hlB
      · exact htB

/-- Increasing restrictions of a side preserve its noninterlacing property. -/
theorem Noninterlacing.comp {γ : ℝ → X} {P Q : Set X} {φ : ℝ → ℝ}
    (hNI : Noninterlacing γ P Q) (hφ : StrictMono φ)
    (hφ0 : 0 ≤ φ 0) (hφ1 : φ 1 ≤ 1) : Noninterlacing (γ ∘ φ) P Q := by
  intro a b c d ha hab hbc hcd hd haP hcP hbQ hdQ
  exact hNI (hφ0.trans (hφ.monotone ha)) (hφ hab) (hφ hbc) (hφ hcd)
    ((hφ.monotone hd).trans hφ1) haP hcP hbQ hdQ

/-- In particular, one can use any nondegenerate subinterval of a side. -/
theorem Noninterlacing.affine_restrict {γ : ℝ → X} {P Q : Set X}
    (hNI : Noninterlacing γ P Q) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Noninterlacing (fun t => γ (a + (b - a) * t)) P Q := by
  apply hNI.comp
  · intro s t hst
    dsimp
    linarith [mul_lt_mul_of_pos_left hst (sub_pos.mpr hab)]
  · simpa using ha
  · simpa using hb

variable [TopologicalSpace X]

/-- The cutoff theorem for any continuous parametrized side. -/
theorem exists_cutoff_of_noninterlacing {γ : ℝ → X} {P Q : Set X}
    (hγ : Continuous γ) (hP : IsClosed P) (hQ : IsClosed Q)
    (hNI : Noninterlacing γ P Q)
    (h0P : γ 0 ∈ P) (h0Q : γ 0 ∉ Q)
    (h1P : γ 1 ∉ P) (h1Q : γ 1 ∈ Q)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ Q) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (γ t ∈ P ↔ t ≤ l) ∧ (γ t ∈ Q ↔ l ≤ t) := by
  exact exists_cutoff_of_closed_ordered (hP.preimage hγ) (hQ.preimage hγ)
    h0P h0Q h1P h1Q hcover
    (ordered_contacts_of_noninterlacing hNI h0P h0Q h1P h1Q)

end Puzzling139335.N4TwoOneOne.BoundaryIntervals
