import ErdosProblems.Erdos118.Imported591.ExactCanonicalSequence
import ErdosProblems.Erdos118.Imported591.OuterLevels

open Set Ordinal

namespace Erdos118.Negative.Exact.OuterLevels

/-- The part of a set of literal good sequences having root marker `m`. -/
def Fiber (W : Set G) (m : ℕ) : Set G :=
  {x | x ∈ W ∧ x.1.length = m}

@[simp] theorem mem_fiber {W : Set G} {m : ℕ} {x : G} :
    x ∈ Fiber W m ↔ x ∈ W ∧ x.1.length = m := Iff.rfl

/-- Forget source-goodness while retaining the underlying nested sequence. -/
def underlying (W : Set G) : Set OrderedG2 :=
  {s | ∃ x : G, x ∈ W ∧ s = x.1}

noncomputable def subtypeRelIso (W : Set G) :
    ((· < ·) : W → W → Prop) ≃r
      ((· < ·) : underlying W → underlying W → Prop) := by
  classical
  refine
    { toEquiv :=
        { toFun := fun x ↦ ⟨x.1.1, x.1, x.2, rfl⟩
          invFun := fun s ↦ ?_
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · let x : G := Classical.choose s.2
    have hx := Classical.choose_spec s.2
    exact ⟨x, hx.1⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec
      ((show underlying W from
        ⟨x.1.1, x.1, x.2, rfl⟩).2)).2.symm
  · intro s
    apply Subtype.ext
    exact (Classical.choose_spec s.2).2.symm
  · intro x y
    rfl

theorem type_underlying (W : Set G) :
    typeLT (underlying W) = typeLT W := by
  exact (subtypeRelIso W).ordinalType_congr.symm

noncomputable def fiberRelIso (W : Set G) (m : ℕ) :
    ((· < ·) : Fiber W m → Fiber W m → Prop) ≃r
      ((· < ·) : Erdos118.Negative.OuterLevels.Fiber (underlying W) m →
        Erdos118.Negative.OuterLevels.Fiber (underlying W) m → Prop) := by
  classical
  refine
    { toEquiv :=
        { toFun := fun x ↦ ⟨x.1.1, ⟨x.1, x.2.1, rfl⟩, x.2.2⟩
          invFun := fun s ↦ ?_
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · let x : G := Classical.choose s.2.1
    have hx := Classical.choose_spec s.2.1
    exact ⟨x, hx.1, hx.2 ▸ s.2.2⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec
      ((show Erdos118.Negative.OuterLevels.Fiber (underlying W) m from
        ⟨x.1.1, ⟨x.1, x.2.1, rfl⟩, x.2.2⟩).2.1)).2.symm
  · intro s
    apply Subtype.ext
    exact (Classical.choose_spec s.2.1).2.symm
  · intro x y
    rfl

theorem type_fiber (W : Set G) (m : ℕ) :
    typeLT (Fiber W m) =
      typeLT (Erdos118.Negative.OuterLevels.Fiber (underlying W) m) := by
  exact (fiberRelIso W m).ordinalType_congr

/-- The first selection in Handbook Lemma 9.31, now on the exact carrier. -/
theorem exists_large_fiber_above_pow (W : Set G)
    (hW : typeLT W = ω ^ (ω ^ 2)) (M k : ℕ) :
    ∃ m, M < m ∧ (ω ^ ω : Ordinal) ^ k ≤ typeLT (Fiber W m) := by
  have hU : typeLT (underlying W) = ω ^ (ω ^ 2) := by
    rw [type_underlying, hW]
  obtain ⟨m, hm, hlarge⟩ :=
    Erdos118.Negative.OuterLevels.exists_large_fiber_above_pow
      (underlying W) hU M k
  refine ⟨m, hm, ?_⟩
  rw [type_fiber]
  exact hlarge

theorem exists_large_fiber_above (W : Set G)
    (hW : typeLT W = ω ^ (ω ^ 2)) (M : ℕ) :
    ∃ m, M < m ∧ (ω ^ ω : Ordinal) ^ 4 ≤ typeLT (Fiber W m) :=
  exists_large_fiber_above_pow W hW M 4

end Erdos118.Negative.Exact.OuterLevels
