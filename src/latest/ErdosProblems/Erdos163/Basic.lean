/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Erdős Problem 163: elementary graph interface

This file fixes the two notions which are easiest to state incorrectly:
degeneracy is tested on every nonempty induced vertex set, and a graph copy
is an ordinary subgraph copy, not an induced copy.
-/

open Finset

namespace Erdos163

universe u v w

/-- Every nonempty induced vertex set contains a vertex of degree at most `d`. -/
def IsDegenerateAtMost {α : Type u} [Fintype α]
    (H : SimpleGraph α) (d : ℕ) : Prop := by
  classical
  exact ∀ S : Finset α, S.Nonempty →
    ∃ x ∈ S, (S.filter fun y => H.Adj x y).card ≤ d

/-- An ordinary graph copy: injective on vertices and preserving every edge.
Nonedges need not be preserved. -/
structure CopyEmbedding {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) where
  toFun : α → β
  injective' : Function.Injective toFun
  map_adj' : ∀ ⦃x y : α⦄, H.Adj x y → G.Adj (toFun x) (toFun y)

namespace CopyEmbedding

instance {α : Type u} {β : Type v} {H : SimpleGraph α} {G : SimpleGraph β} :
    CoeFun (CopyEmbedding H G) fun _ => α → β := ⟨toFun⟩

theorem injective {α : Type u} {β : Type v} {H : SimpleGraph α} {G : SimpleGraph β}
    (f : CopyEmbedding H G) : Function.Injective f :=
  f.injective'

theorem map_adj {α : Type u} {β : Type v} {H : SimpleGraph α} {G : SimpleGraph β}
    (f : CopyEmbedding H G) {x y : α} (hxy : H.Adj x y) : G.Adj (f x) (f y) :=
  f.map_adj' hxy

def refl {α : Type u} (H : SimpleGraph α) : CopyEmbedding H H where
  toFun := id
  injective' := Function.injective_id
  map_adj' := fun {_ _} h => h

def comp {α : Type u} {β : Type v} {γ : Type w}
    {H : SimpleGraph α} {G : SimpleGraph β} {F : SimpleGraph γ}
    (g : CopyEmbedding G F) (f : CopyEmbedding H G) : CopyEmbedding H F where
  toFun := g ∘ f
  injective' := g.injective'.comp f.injective'
  map_adj' := fun {_ _} h => g.map_adj' (f.map_adj' h)

/-- Every injection into a complete graph is an ordinary graph copy. -/
def intoComplete {α : Type u} {β : Type v} {H : SimpleGraph α}
    (f : α → β) (hf : Function.Injective f) :
    CopyEmbedding H (⊤ : SimpleGraph β) where
  toFun := f
  injective' := hf
  map_adj' := fun {_ _} hxy => by
    simpa using hf.ne (H.ne_of_adj hxy)

end CopyEmbedding

/-- The host contains an ordinary copy of the target. -/
def HasCopy {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  Nonempty (CopyEmbedding H G)

/-- Every red/blue coloring of `K_N` contains a monochromatic copy of `H`. -/
def RamseyFor {α : Type u} (H : SimpleGraph α) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCopy H G ∨ HasCopy H Gᶜ

theorem HasCopy.mono {α : Type u} {β : Type v}
    {H : SimpleGraph α} {G G' : SimpleGraph β} (hGG' : G ≤ G') :
    HasCopy H G → HasCopy H G' := by
  rintro ⟨f⟩
  exact ⟨{
    toFun := f
    injective' := f.injective'
    map_adj' := fun {_ _} h => hGG' (f.map_adj' h)
  }⟩

theorem HasCopy.trans {α : Type u} {β : Type v} {γ : Type w}
    {H : SimpleGraph α} {G : SimpleGraph β} {F : SimpleGraph γ} :
    HasCopy H G → HasCopy G F → HasCopy H F := by
  rintro ⟨f⟩ ⟨g⟩
  exact ⟨g.comp f⟩

theorem hasCopy_complete_of_injective {α : Type u} {β : Type v}
    {H : SimpleGraph α} {f : α → β} (hf : Function.Injective f) :
    HasCopy H (⊤ : SimpleGraph β) :=
  ⟨CopyEmbedding.intoComplete f hf⟩

/-- A monochromatic clique of the target order contains every target graph. -/
theorem hasCopy_of_isNClique {n N : ℕ} (H : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin N)) {S : Finset (Fin N)} (hS : G.IsNClique n S) :
    HasCopy H G := by
  classical
  let e : Fin n ≃ S :=
    (Fintype.equivFinOfCardEq (by simpa using hS.card_eq)).symm
  refine ⟨{
    toFun := fun i => (e i : Fin N)
    injective' := fun i j hij => e.injective (Subtype.ext hij)
    map_adj' := ?_
  }⟩
  intro i j hij
  exact hS.1 (e i).property (e j).property fun hval =>
    H.ne_of_adj hij (e.injective (Subtype.ext hval))

theorem ramseyFor_of_ramseyProperty {n N : ℕ} (H : SimpleGraph (Fin n))
    (hR : Ramsey.RamseyProperty n n N) : RamseyFor H N := by
  intro G
  classical
  by_cases hclique : G.CliqueFree n
  · right
    have hindep : ¬G.IndepSetFree n := fun h => hR G ⟨hclique, h⟩
    have hcompl : ¬Gᶜ.CliqueFree n := by
      simpa [SimpleGraph.indepSetFree_compl] using hindep
    have : ∃ S : Finset (Fin N), Gᶜ.IsNClique n S := by
      simpa [SimpleGraph.CliqueFree] using hcompl
    obtain ⟨S, hS⟩ := this
    exact hasCopy_of_isNClique H Gᶜ hS
  · left
    have : ∃ S : Finset (Fin N), G.IsNClique n S := by
      simpa [SimpleGraph.CliqueFree] using hclique
    obtain ⟨S, hS⟩ := this
    exact hasCopy_of_isNClique H G hS

theorem ramseyFor_exists (n : ℕ) (H : SimpleGraph (Fin n)) :
    ∃ N, RamseyFor H N := by
  obtain ⟨N, hN⟩ := Ramsey.ramseyProperty_exists n n
  exact ⟨N, ramseyFor_of_ramseyProperty H hN⟩

/-! ## Elementary consequences of degeneracy -/

/-- A `d`-degenerate finite graph is colorable with `d+1` colors. -/
theorem colorable_succ_of_degenerate {α : Type u} [Finite α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (d : ℕ)
    (hdeg : ∀ S : Finset α, S.Nonempty →
      ∃ x ∈ S, (S.filter fun y => H.Adj x y).card ≤ d) :
    H.Colorable (d + 1) := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨c, hc⟩ : ∃ c : α → Fin (d + 1),
      ∀ x y : α, H.Adj x y → c x ≠ c y := by
    suffices hcolor : ∀ S : Finset α,
        ∃ c : α → Fin (d + 1),
          ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → c x ≠ c y by
      simpa only [mem_univ, forall_const] using hcolor univ
    intro S
    exact Finset.strongInduction
      (p := fun S => ∃ c : α → Fin (d + 1),
        ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → c x ≠ c y)
      (fun S ih => by
        by_cases hS : S.Nonempty
        · obtain ⟨x, hxS, hx⟩ := hdeg S hS
          obtain ⟨c, hc⟩ := ih (S.erase x) (Finset.erase_ssubset hxS)
          have hcard :
              (Finset.image c (S.filter fun y => H.Adj x y)).card < d + 1 :=
            lt_of_le_of_lt Finset.card_image_le (Nat.lt_succ_of_le hx)
          obtain ⟨cx, hcx⟩ :
              ∃ cx : Fin (d + 1),
                cx ∉ Finset.image c (S.filter fun y => H.Adj x y) := by
            by_contra h
            push_neg at h
            have hall : Finset.image c (S.filter fun y => H.Adj x y) = univ :=
              eq_univ_of_forall h
            simpa [hall] using hcard
          refine ⟨fun y => if y = x then cx else c y, ?_⟩
          intro u hu v hv huv
          by_cases hu' : u = x <;> by_cases hv' : v = x
          · subst u; subst v
            exact (H.irrefl huv).elim
          · subst u
            simp only [if_pos, hv', if_false]
            exact fun heq => hcx (mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, huv⟩, heq.symm⟩)
          · subst v
            simp only [hu', if_false, if_pos]
            exact fun heq => hcx (mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, huv.symm⟩, heq⟩)
          · simp only [hu', hv', if_false]
            exact hc u (mem_erase.mpr ⟨hu', hu⟩) v (mem_erase.mpr ⟨hv', hv⟩) huv
        · exact ⟨fun _ => 0, fun _ hx => (hS ⟨_, hx⟩).elim⟩) S
  exact ⟨c, fun {_ _} h => by simpa using hc _ _ h⟩

theorem colorable_succ {α : Type u} [Fintype α]
    (H : SimpleGraph α) (d : ℕ) (hdeg : IsDegenerateAtMost H d) :
    H.Colorable (d + 1) := by
  classical
  exact colorable_succ_of_degenerate H d hdeg

end Erdos163
