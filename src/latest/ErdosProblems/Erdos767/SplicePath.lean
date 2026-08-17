import ErdosProblems.Erdos767.Case2Splice
import ErdosProblems.Erdos767.Aligned

open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- A convenient qualitative constructor for the five-piece Case-2 body.
The geometric proof only has to establish the successive intersection
conditions; pathhood of the resulting nested append is then automatic. -/
lemma spliceBody_isPath_of_successive_meets
    {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂)
    (hR₁ : R₁.IsPath) (hA : A.IsPath) (hB : B.IsPath) (hR₂ : R₂.IsPath)
    (hR₁A : ∀ w, w ∈ R₁.support → w ∈ A.support → w = b₁)
    (hyR₁ : y ∉ R₁.support) (hyA : y ∉ A.support)
    (hpreB : ∀ w,
      w ∈ ((R₁.append A).concat hdy).support → w ∈ B.support → w = y)
    (hallR₂ : ∀ w,
      w ∈ (((R₁.append A).concat hdy).append B).support →
      w ∈ R₂.reverse.support → w = b₂) :
    (Erdos767DiracCase2.spliceBody R₁ A hdy B R₂).IsPath := by
  have hRA : (R₁.append A).IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hR₁ hA hR₁A
  have hyRA : y ∉ (R₁.append A).support := by
    intro hy
    rw [Walk.mem_support_append_iff] at hy
    exact hy.elim hyR₁ hyA
  have hRAy : ((R₁.append A).concat hdy).IsPath := hRA.concat hyRA hdy
  have hRAB : (((R₁.append A).concat hdy).append B).IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hRAy hB hpreB
  exact E767AlignedAlt.isPath_append_of_meet_eq_end hRAB hR₂.reverse hallR₂

end E767DiracBuild

