import ErdosProblems.Erdos547.ShrubIndex
import ErdosProblems.Erdos547.ShrubEmbedding

/-!
# Translating a regular-pair shrub copy to its partition interface
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V : Type*} [Fintype U] [DecidableEq U]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

theorem shrub_copy_near_far (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val)
    {G : SimpleGraph V} (f : (T.induce (S.val : Set U)).Copy G) (X Y : Finset V)
    (hroot : f D.root ∈ X)
    (hsecond : ∀ u, D.second.map Prod.snd = some u → f u ∈ X)
    (hrest : ∀ u, u ≠ D.root → D.second.map Prod.snd ≠ some u →
      ((T.induce (S.val : Set U)).dist D.root u % 2 = 0 → f u ∈ X) ∧
      ((T.induce (S.val : Set U)).dist D.root u % 2 ≠ 0 → f u ∈ Y)) :
    (∀ u : ↥S.val, col u.val ≠ P.shrubColour S → f u ∈ X) ∧
    (∀ u : ↥S.val, col u.val = P.shrubColour S → f u ∈ Y) := by
  have hpar (u : ↥S.val) := P.shrub_root_even_iff_near _ _ (P.mem_shrubsOfColour S) D u
  constructor
  · intro u hu
    by_cases hur : u = D.root
    · exact hur ▸ hroot
    · by_cases hus : D.second.map Prod.snd = some u
      · exact hsecond u hus
      · exact (hrest u hur hus).1 ((hpar u).mpr hu)
  · intro u hu
    have heven : (T.induce (S.val : Set U)).dist D.root u % 2 ≠ 0 := by
      intro h
      exact (hpar u).mp h hu
    have hur : u ≠ D.root := by
      intro h
      subst u
      exact P.shrub_root_colour_ne _ _ (P.mem_shrubsOfColour S) D hu
    have hus : D.second.map Prod.snd ≠ some u := by
      intro h
      exact heven (D.rooted.even_distance u h)
    exact (hrest u hur hus).2 heven

end Erdos547.FineTreePartition

namespace Erdos547

open Finset SimpleGraph

theorem shrub_copy_avoids {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}
    (f : T.Copy G) (r : U) (s : Option U) (A B P bad : Finset V)
    (hroot : f r ∉ bad) (hA : Disjoint A bad) (hB : Disjoint B bad)
    (hP : Disjoint P bad) (hsecond : ∀ u, s = some u → f u ∈ P)
    (hrest : ∀ u, u ≠ r → s ≠ some u → f u ∈ A ∨ f u ∈ B) :
    ∀ u, f u ∉ bad := by
  intro u hu
  by_cases hur : u = r
  · exact hroot (hur ▸ hu)
  · by_cases hus : s = some u
    · exact Finset.disjoint_left.mp hP (hsecond u hus) hu
    · rcases hrest u hur hus with h | h
      · exact Finset.disjoint_left.mp hA h hu
      · exact Finset.disjoint_left.mp hB h hu

theorem shrub_reservoir_only_roots {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}
    (f : T.Copy G) (r : U) (s : Option U) (A B Q : Finset V)
    (hA : Disjoint A Q) (hB : Disjoint B Q)
    (hrest : ∀ u, u ≠ r → s ≠ some u → f u ∈ A ∨ f u ∈ B) :
    ∀ u, f u ∈ Q → u = r ∨ s = some u := by
  intro u hu
  by_cases hur : u = r
  · exact Or.inl hur
  · by_cases hus : s = some u
    · exact Or.inr hus
    · exfalso
      rcases hrest u hur hus with h | h
      · exact Finset.disjoint_left.mp hA h hu
      · exact Finset.disjoint_left.mp hB h hu

end Erdos547

#print axioms Erdos547.FineTreePartition.shrub_copy_near_far
