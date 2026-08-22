/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZPathEvents

/-!
# Routing the high HLOZ mesh to the transition estimate

Lemma 4.10 applies only when `α ≤ κ₂`.  This module records explicitly that
a proper mesh branch containing a high-scale gap is retained in the terminal
transition union used by Proposition 4.7.  It is not put into the summable
low-gap exceptional family.
-/

open Set

namespace Erdos1165.HLOZHighGapRouting

open HLOZPathEvents

/-- A high mesh scale cannot satisfy the low-scale deficit predicate. -/
lemma not_lowGapDeficitFailure_of_mem_highGapMesh
    {s : WalkPath} {m nOld nNew : ℕ}
    (hhigh : gapScaleOf m (s nOld) (s nNew) ∈ highGapMesh) :
    ¬lowGapDeficitFailure s m nOld nNew := by
  intro hlow
  have hle := (mem_lowGapMesh_iff.mp hlow.1).2
  have hlt := (mem_highGapMesh_iff.mp hhigh).2
  exact (not_lt_of_ge hle) hlt

lemma branch_subset_meshBranchUnion_of_mem
    {Ω Scale : Type*}
    (mesh : Finset Scale) (branch : ((Scale × Scale) × Scale) → Set Ω)
    (a : (Scale × Scale) × Scale)
    (ha₁ : a.1.1 ∈ mesh) (ha₂ : a.1.2 ∈ mesh) (ha₃ : a.2 ∈ mesh) :
    branch a ⊆ UpperAssembly.meshBranchUnion mesh branch := by
  classical
  intro x hx
  rw [UpperAssembly.mem_meshBranchUnion]
  refine ⟨a, ?_, hx⟩
  simpa only [UpperAssembly.meshTriples, Finset.mem_product] using
    And.intro (And.intro ha₁ ha₂) ha₃

lemma branch_subset_exceptional_union_screenedMesh_of_mem
    {Ω Scale : Type*}
    (mesh : Finset Scale) (branch : ((Scale × Scale) × Scale) → Set Ω)
    (exceptional : Set Ω) (a : (Scale × Scale) × Scale)
    (ha₁ : a.1.1 ∈ mesh) (ha₂ : a.1.2 ∈ mesh) (ha₃ : a.2 ∈ mesh) :
    branch a ⊆ exceptional ∪
      UpperAssembly.meshBranchUnion mesh (fun b ↦ branch b \ exceptional) := by
  classical
  intro x hx
  by_cases he : x ∈ exceptional
  · exact Or.inl he
  · right
    rw [UpperAssembly.mem_meshBranchUnion]
    refine ⟨a, ?_, ⟨hx, he⟩⟩
    simpa only [UpperAssembly.meshTriples, Finset.mem_product] using
      And.intro (And.intro ha₁ ha₂) ha₃

/-- Every proper high-scale terminal branch occurs in the same full mesh
union to which the three Proposition 4.7 transition bounds are applied. -/
theorem highGap_thirdTransitionEvent_subset_meshBranchUnion
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hproper₁ : a.1.1 ∈ properGapMesh)
    (hproper₂ : a.1.2 ∈ properGapMesh)
    (hproper₃ : a.2 ∈ properGapMesh)
    (_hhigh : HasHighGapScale a) :
    thirdTransitionEvent t m a ⊆
      UpperAssembly.meshBranchUnion properGapMesh
        (thirdTransitionEvent t m) := by
  exact branch_subset_meshBranchUnion_of_mem properGapMesh
    (thirdTransitionEvent t m) a hproper₁ hproper₂ hproper₃

/-- After the low exceptional family is removed, a high-scale branch is
still a screened terminal transition branch.  This is the exact path-cover
bridge charging high scales to Proposition 4.7 rather than Lemma 4.10. -/
theorem highGap_thirdTransitionEvent_subset_exceptional_union_screenedMesh
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hproper₁ : a.1.1 ∈ properGapMesh)
    (hproper₂ : a.1.2 ∈ properGapMesh)
    (hproper₃ : a.2 ∈ properGapMesh)
    (_hhigh : HasHighGapScale a) :
    thirdTransitionEvent t m a ⊆
      hlozExceptionalEvent t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (screenedThirdTransitionEvent t m) := by
  exact branch_subset_exceptional_union_screenedMesh_of_mem properGapMesh
    (thirdTransitionEvent t m) (hlozExceptionalEvent t m) a
      hproper₁ hproper₂ hproper₃

end Erdos1165.HLOZHighGapRouting
