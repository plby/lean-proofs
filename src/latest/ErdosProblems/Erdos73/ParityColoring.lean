import ErdosProblems.Erdos73.ParityPaths

/-! A proper Boolean colouring controls the parity of every supported walk. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem BipartiteColoringOn.even_walk {T : Finset V} (c : BipartiteColoringOn G T)
    {x y : V} (w : G.Walk x y) (hw : ∀ v ∈ w.support, v ∈ T) :
    Even (w.length + (c.color x).toNat + (c.color y).toNat) := by
  induction w with
  | @nil z => exact ⟨(c.color z).toNat, by simp⟩
  | @cons x z y hxz w ih =>
    have hx : x ∈ T := hw x (by simp)
    have hz : z ∈ T := hw z (by simp)
    have hne := c.valid x hx z hz hxz
    have hcolors : (c.color x).toNat + (c.color z).toNat = 1 := by
      cases hcx : c.color x <;> cases hcz : c.color z <;> simp_all
    have ht := ih (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    rw [Nat.even_iff] at ht ⊢
    simp only [Walk.length_cons]
    omega

theorem BipartiteColoringOn.not_parityBreaking_of_subset {T : Finset V}
    (c : BipartiteColoringOn G T) (P : GraphPath G) (hP : P.vertexSet ⊆ T) :
    ¬ ParityBreaking c.color P := by
  have he := c.even_walk P.walk (fun v hv => hP (List.mem_toFinset.mpr hv))
  exact Nat.not_odd_iff_even.mpr he

theorem IsParityBreakingPath.not_subset {T : Finset V} (c : BipartiteColoringOn G T)
    {P : GraphPath G} (hP : IsParityBreakingPath c.color T P) : ¬ P.vertexSet ⊆ T := by
  intro hsub
  exact c.not_parityBreaking_of_subset P hsub hP.breaking

theorem ParityBreaking.source_ne_target {c : V → Bool} {P : GraphPath G}
    (hP : ParityBreaking c P) : P.source ≠ P.target := by
  intro he
  have hnil := P.isPath.nil_iff_eq.mpr he
  have hlen : P.walk.length = 0 := hnil.length_eq_zero
  rw [ParityBreaking, hlen, he, Nat.odd_iff] at hP
  omega

end
end Erdos73
