import ErdosProblems.Erdos767.Build
import ErdosProblems.Erdos767.Case1
import ErdosProblems.Erdos767.Case2EqualA
import ErdosProblems.Erdos767.Case2Splice

open Finset Set
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two last cycle vertices of the aligned ears are distinct.  Equality
would put both at the fan root and the checked exceptional splice would make
a cycle longer than the chosen longest cycle. -/
lemma Case2FanData.a_ne {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length) :
    D.E₁.a ≠ D.E₂.a := by
  intro haa
  have hYtail : (B.tail.drop j₁).support.toFinset ⊆
      B.tail.support.toFinset := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    obtain ⟨i, hiw, _hi⟩ := Walk.mem_support_iff_exists_getVert.mp hw'
    rw [Walk.drop_getVert] at hiw
    exact List.mem_toFinset.mpr (hiw ▸ B.tail.getVert_mem_support (j₁ + i))
  obtain ⟨C, hC, hlong⟩ :=
    E767Case2EqualA.exists_longer_cycle_of_equal_blockEars B hpos
      D.F.toZ D.F.toY D.F.toZ_isPath D.F.toY_isPath D.F.meet_eq_start
      (B.tail.drop j₁).support.toFinset hYtail D.E₁ D.E₂ haa
  exact (Nat.not_lt_of_ge (B.cycle_maximal C hC)) hlong

end

end E767DiracBuild
