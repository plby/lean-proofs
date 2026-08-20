/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Transport of prescribed linkages through graph embeddings. -/

import ErdosProblems.Erdos717.NoSmallRigid

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

variable {U V I : Type} [Fintype I]

/-- Map a prescribed linkage through a graph embedding. -/
noncomputable def Erdos718.PairLinkage.mapEmbedding
    {H : SimpleGraph U} {G : SimpleGraph V} {X : Set U}
    {terminal : Sum I I ↪ U}
    (L : Erdos718.PairLinkage H X terminal) (f : H ↪g G) :
    Erdos718.PairLinkage G (f '' X) (terminal.trans f.toEmbedding) := by
  let hom : H →g G := f.toHom
  have hstart (i : I) : hom (terminal (.inl i)) =
      (terminal.trans f.toEmbedding) (.inl i) := by rfl
  have hend (i : I) : hom (terminal (.inr i)) =
      (terminal.trans f.toEmbedding) (.inr i) := by rfl
  refine {
    path := fun i => ((L.path i).map hom).copy (hstart i) (hend i)
    isPath := fun i => by
      rw [Walk.isPath_copy]
      exact (L.isPath i).map f.injective
    avoids := ?_
    disjoint := ?_
  }
  · intro i
    rw [Set.disjoint_left]
    intro x hx hxImage
    rcases hxImage with ⟨y, hyX, hyx⟩
    rcases hx with ⟨hxSupp, hxStart, hxEnd⟩
    have hxSupp' : x ∈ ((L.path i).map hom).support := by
      simpa only [Walk.support_copy] using hxSupp
    rw [Walk.support_map] at hxSupp'
    obtain ⟨z, hzSupp, hzx⟩ := List.mem_map.mp hxSupp'
    have hzy : z = y := f.injective (hzx.trans hyx.symm)
    have hzStart : z ≠ terminal (.inl i) := by
      intro h
      apply hxStart
      change x = f (terminal (.inl i))
      rw [← hyx, ← hzy, h]
    have hzEnd : z ≠ terminal (.inr i) := by
      intro h
      apply hxEnd
      change x = f (terminal (.inr i))
      rw [← hyx, ← hzy, h]
    exact (Set.disjoint_left.mp (L.avoids i))
      ⟨hzSupp, hzStart, hzEnd⟩ (hzy ▸ hyX)
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    change x ∈ (((L.path i).map hom).copy (hstart i) (hend i)).support at hxi
    change x ∈ (((L.path j).map hom).copy (hstart j) (hend j)).support at hxj
    have hxi' : x ∈ ((L.path i).map hom).support := by
      simpa only [Walk.support_copy] using hxi
    have hxj' : x ∈ ((L.path j).map hom).support := by
      simpa only [Walk.support_copy] using hxj
    rw [Walk.support_map] at hxi' hxj'
    obtain ⟨y, hyi, hyx⟩ := List.mem_map.mp hxi'
    obtain ⟨z, hzj, hzx⟩ := List.mem_map.mp hxj'
    have hyz : y = z := f.injective (hyx.trans hzx.symm)
    exact (Set.disjoint_left.mp (L.disjoint hij)) hyi (hyz ▸ hzj)

/-- The range of a `k`-linked graph embedded in an ambient graph is
`k`-linked with paths lying in the induced range. -/
theorem isKLinked_induce_range_of_embedding
    [Fintype U] [Fintype V] [DecidableEq V]
    {H : SimpleGraph U} {G : SimpleGraph V} (f : H ↪g G) {k : ℕ}
    (hlinked : Erdos718.IsKLinked H k) :
    Erdos718.IsKLinked (G.induce (Set.range f)) k := by
  intro X hXfinite hXcard I _ terminal hterminal
  let e : U ≃ Set.range f := f.toEmbedding.toEquivRange
  let terminalU : Sum I I ↪ U := terminal.trans e.symm.toEmbedding
  let XU : Set U := e.symm '' X
  have hXUfinite : XU.Finite := hXfinite.image e.symm
  have hXUncard : XU.ncard = X.ncard := by
    exact Set.ncard_image_of_injective X e.symm.injective
  have hterminalU : Set.range terminalU ⊆ XU := by
    rintro _ ⟨z, rfl⟩
    exact ⟨terminal z, hterminal ⟨z, rfl⟩, rfl⟩
  obtain ⟨L⟩ := hlinked XU hXUfinite (hXUncard.trans_le hXcard)
    I terminalU hterminalU
  let fRange : H ↪g (G.induce (Set.range f)) := {
    toFun := e
    inj' := e.injective
    map_rel_iff' := by
      intro a b
      change G.Adj (f a) (f b) ↔ H.Adj a b
      exact f.map_rel_iff
  }
  have hterm : terminalU.trans fRange.toEmbedding = terminal := by
    apply Function.Embedding.ext
    intro z
    apply Subtype.ext
    change f (e.symm (terminal z)) = (terminal z : V)
    have he := e.apply_symm_apply (terminal z)
    exact congrArg Subtype.val he
  have hset : fRange '' XU = X := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzX, hzy⟩, hyx⟩
      have hzEq : z = x := by
        rw [← hyx, ← hzy]
        exact (e.apply_symm_apply z).symm
      exact hzEq ▸ hzX
    · intro hx
      refine ⟨e.symm x, ⟨x, hx, rfl⟩, ?_⟩
      exact e.apply_symm_apply x
  exact ⟨by simpa only [hterm, hset] using
    Erdos718.PairLinkage.mapEmbedding L fRange⟩

end ThomasWollanMassed
end Erdos717
