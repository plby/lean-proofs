import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneDomains

/-! # The actual punctured-product open used by the Dolbeault theorem -/

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

/-- The literal open submanifold `ℂ × ℂ*` inside `ℂ × ℂ`. -/
def puncturedOpen : Opens (ℂ × ℂ) :=
  ⟨PuncturedDbarOne.domain, PuncturedDbarOne.isOpen_domain⟩

@[simp] theorem mem_puncturedOpen (q : ℂ × ℂ) : q ∈ puncturedOpen ↔ q.2 ≠ 0 := Iff.rfl

theorem puncturedOpen_coe : (puncturedOpen : Set (ℂ × ℂ)) = {q | q.2 ≠ 0} := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
