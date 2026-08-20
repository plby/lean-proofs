/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Restrict walks and linkages whose supports lie in an induced set. -/

import ErdosProblems.Erdos717.InduceLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

universe u v

variable {V : Type u} {G : SimpleGraph V} {A : Set V}

/-- Regard a walk all of whose vertices lie in `A` as a walk in the graph
induced on `A`. -/
def walkRestrictInduce : ∀ {x y : V} (p : G.Walk x y)
    (h : ∀ z ∈ p.support, z ∈ A),
    (G.induce A).Walk
      ⟨x, h x p.start_mem_support⟩
      ⟨y, h y p.end_mem_support⟩
  | _, _, .nil, h => .nil
  | x, y, .cons (v := w) hxw p, h => by
      let hxA : x ∈ A := h x (by simp)
      let hwA : w ∈ A := h w (by simp)
      have hpA : ∀ z ∈ p.support, z ∈ A := by
        intro z hz
        exact h z (by simp [hz])
      let q := walkRestrictInduce p hpA
      let hadj : (G.induce A).Adj ⟨x, hxA⟩ ⟨w, hwA⟩ := hxw
      exact (q.cons hadj).copy (by apply Subtype.ext; rfl)
        (by apply Subtype.ext; rfl)

@[simp] lemma map_val_support_walkRestrictInduce
    {x y : V} (p : G.Walk x y) (h : ∀ z ∈ p.support, z ∈ A) :
    (walkRestrictInduce p h).support.map Subtype.val = p.support := by
  induction p with
  | nil => rfl
  | @cons x w y hxw p ih =>
      change x :: (walkRestrictInduce p _).support.map Subtype.val =
        x :: p.support
      rw [ih]

lemma mem_support_walkRestrictInduce_iff
    {x y : V} (p : G.Walk x y) (h : ∀ z ∈ p.support, z ∈ A)
    (z : A) : z ∈ (walkRestrictInduce p h).support ↔
      (z : V) ∈ p.support := by
  have hm := map_val_support_walkRestrictInduce p h
  constructor
  · intro hz
    rw [← hm]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  · intro hz
    rw [← hm] at hz
    obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hz
    have : w = z := Subtype.ext hwz
    simpa [this] using hw

lemma isPath_walkRestrictInduce
    {x y : V} (p : G.Walk x y) (h : ∀ z ∈ p.support, z ∈ A)
    (hp : p.IsPath) : (walkRestrictInduce p h).IsPath := by
  apply Walk.IsPath.mk'
  apply List.Nodup.of_map Subtype.val
  rw [map_val_support_walkRestrictInduce p h]
  exact hp.support_nodup

/-- Every vertex of a linkage lifted from an induced graph remains in the
inducing set. -/
lemma Erdos718.PairLinkage.support_liftInduce_subset
    {I : Type v} [Fintype I] {X : Set V}
    {terminal : Sum I I ↪ V} (hA : Set.range terminal ⊆ A)
    (L : Erdos718.PairLinkage (G.induce A)
      {a : A | (a : V) ∈ X} (terminalIntoSet A terminal hA))
    (i : I) {z : V}
    (hz : z ∈ ((Erdos718.PairLinkage.liftInduce hA L).path i).support) :
    z ∈ A := by
  dsimp only [Erdos718.PairLinkage.liftInduce] at hz
  rw [Walk.support_copy, Walk.support_map] at hz
  obtain ⟨w, _hw, hwz⟩ := List.mem_map.mp hz
  have : (w : V) = z := by
    change (w : V) = z at hwz
    exact hwz
  exact this ▸ w.property

/-- Restrict a linkage to an induced graph when all its path supports lie in
the inducing set. -/
noncomputable def Erdos718.PairLinkage.restrictInduce
    {I : Type v} [Fintype I] {X : Set V}
    {terminal : Sum I I ↪ V} (L : Erdos718.PairLinkage G X terminal)
    (hA : ∀ i z, z ∈ (L.path i).support → z ∈ A)
    (hterminal : Set.range terminal ⊆ A) :
    Erdos718.PairLinkage (G.induce A) {z : A | (z : V) ∈ X}
      (terminalIntoSet A terminal hterminal) := by
  let q (i : I) := walkRestrictInduce (L.path i) (hA i)
  have hstart (i : I) :
      (⟨terminal (.inl i), hA i _ (L.path i).start_mem_support⟩ : A) =
        terminalIntoSet A terminal hterminal (.inl i) := by
    apply Subtype.ext
    rfl
  have hend (i : I) :
      (⟨terminal (.inr i), hA i _ (L.path i).end_mem_support⟩ : A) =
        terminalIntoSet A terminal hterminal (.inr i) := by
    apply Subtype.ext
    rfl
  refine {
    path := fun i => (q i).copy (hstart i) (hend i)
    isPath := fun i => ?_
    avoids := fun i => ?_
    disjoint := fun i j hij => ?_
  }
  · simpa only [Walk.isPath_copy] using
      isPath_walkRestrictInduce (L.path i) (hA i) (L.isPath i)
  · rw [Set.disjoint_left]
    intro z hz hzX
    have hzSupp : (z : V) ∈ (L.path i).support := by
      apply (mem_support_walkRestrictInduce_iff (L.path i) (hA i) z).mp
      simpa only [Walk.support_copy] using hz.1
    have hzStart : (z : V) ≠ terminal (.inl i) := by
      intro heq
      apply hz.2.1
      apply Subtype.ext
      simpa only [terminalIntoSet_coe] using heq
    have hzEnd : (z : V) ≠ terminal (.inr i) := by
      intro heq
      apply hz.2.2
      apply Subtype.ext
      simpa only [terminalIntoSet_coe] using heq
    exact (Set.disjoint_left.mp (L.avoids i))
      ⟨hzSupp, hzStart, hzEnd⟩ hzX
  · apply Set.disjoint_left.mpr
    intro z hzi hzj
    change z ∈ (walkRestrictInduce (L.path i) (hA i)).support at hzi
    change z ∈ (walkRestrictInduce (L.path j) (hA j)).support at hzj
    have hzi' : (z : V) ∈ (L.path i).support := by
      exact (mem_support_walkRestrictInduce_iff (L.path i) (hA i) z).mp hzi
    have hzj' : (z : V) ∈ (L.path j).support := by
      exact (mem_support_walkRestrictInduce_iff (L.path j) (hA j) z).mp hzj
    exact (Set.disjoint_left.mp (L.disjoint hij)) hzi' hzj'

end ThomasWollanMassed
end Erdos717
