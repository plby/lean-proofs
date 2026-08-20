/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Transporting prescribed linkages through induced-subgraph inclusions. -/

import ErdosProblems.Erdos717.DenseNeighborhood

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

universe u v

variable {V : Type u} {ι : Type v}

/-- Restrict a terminal embedding to an induced vertex set known to contain
all of its values. -/
def terminalIntoSet (A : Set V) (terminal : Sum ι ι ↪ V)
    (hA : Set.range terminal ⊆ A) : Sum ι ι ↪ A where
  toFun z := ⟨terminal z, hA ⟨z, rfl⟩⟩
  inj' := fun _ _ h => terminal.injective (congrArg Subtype.val h)

@[simp] lemma terminalIntoSet_coe (A : Set V)
    (terminal : Sum ι ι ↪ V) (hA : Set.range terminal ⊆ A)
    (z : Sum ι ι) :
    ((terminalIntoSet A terminal hA z : A) : V) = terminal z := rfl

/-- A linkage in an induced graph maps to the host graph. -/
noncomputable def Erdos718.PairLinkage.liftInduce
    {G : SimpleGraph V} {A X : Set V}
    {terminal : Sum ι ι ↪ V} (hA : Set.range terminal ⊆ A)
    (L : Erdos718.PairLinkage (G.induce A)
      {a : A | (a : V) ∈ X} (terminalIntoSet A terminal hA)) :
    Erdos718.PairLinkage G X terminal := by
  let inclusion : G.induce A →g G :=
    (SimpleGraph.Embedding.induce A).toHom
  let q (i : ι) := (L.path i).map inclusion
  have hqstart (i : ι) : inclusion (terminalIntoSet A terminal hA (.inl i)) =
      terminal (.inl i) := by
    change ((terminalIntoSet A terminal hA (.inl i) : A) : V) = _
    rfl
  have hqend (i : ι) : inclusion (terminalIntoSet A terminal hA (.inr i)) =
      terminal (.inr i) := by
    change ((terminalIntoSet A terminal hA (.inr i) : A) : V) = _
    rfl
  refine {
    path := fun i => (q i).copy (hqstart i) (hqend i)
    isPath := fun i => ?_
    avoids := fun i => ?_
    disjoint := fun i j hij => ?_
  }
  · apply ((q i).isPath_copy (hqstart i) (hqend i)).mpr
    exact (L.isPath i).map Subtype.val_injective
  · rw [Set.disjoint_left]
    intro x hx hXx
    have hxsupp : x ∈ (q i).support := by
      simpa only [Erdos718.walkInteriorSet, Set.mem_ofPred_eq,
        Walk.support_copy] using hx.1
    rw [Walk.support_map] at hxsupp
    obtain ⟨y, hysupp, hyx⟩ := List.mem_map.mp hxsupp
    have hyval : (y : V) = x := by
      change (y : V) = x at hyx
      exact hyx
    have hystart : y ≠ terminalIntoSet A terminal hA (.inl i) := by
      intro hy
      apply hx.2.1
      rw [← hyval]
      exact congrArg Subtype.val hy
    have hyend : y ≠ terminalIntoSet A terminal hA (.inr i) := by
      intro hy
      apply hx.2.2
      rw [← hyval]
      exact congrArg Subtype.val hy
    exact (Set.disjoint_left.mp (L.avoids i))
      ⟨hysupp, hystart, hyend⟩ (by simpa [hyval] using hXx)
  · change Disjoint
      {v | v ∈ ((q i).copy (hqstart i) (hqend i)).support}
      {v | v ∈ ((q j).copy (hqstart j) (hqend j)).support}
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hxi' : x ∈ (q i).support := by simpa using hxi
    have hxj' : x ∈ (q j).support := by simpa using hxj
    rw [Walk.support_map] at hxi' hxj'
    obtain ⟨y, hyi, hyx⟩ := List.mem_map.mp hxi'
    obtain ⟨z, hzj, hzx⟩ := List.mem_map.mp hxj'
    have hyz : y = z := by
      apply Subtype.val_injective
      simpa [inclusion] using hyx.trans hzx.symm
    subst z
    exact (Set.disjoint_left.mp (L.disjoint hij)) hyi hzj

/-- If an induced vertex set contains `X`, linkedness of its copy of `X`
implies linkedness of `X` in the host. -/
theorem isLinkedSet_of_induce {G : SimpleGraph V} {A X : Set V}
    (hXA : X ⊆ A)
    (hlinked : Erdos718.IsLinkedSet (G.induce A)
      {a : A | (a : V) ∈ X}) :
    Erdos718.IsLinkedSet G X := by
  intro ι _ terminal hrange
  let hA : Set.range terminal ⊆ A := hrange.trans hXA
  have hrangeSub : Set.range (terminalIntoSet A terminal hA) ⊆
      {a : A | (a : V) ∈ X} := by
    rintro _ ⟨z, rfl⟩
    exact hrange ⟨z, rfl⟩
  exact (hlinked ι (terminalIntoSet A terminal hA) hrangeSub).map
    (Erdos718.PairLinkage.liftInduce hA)

end ThomasWollanMassed
end Erdos717
