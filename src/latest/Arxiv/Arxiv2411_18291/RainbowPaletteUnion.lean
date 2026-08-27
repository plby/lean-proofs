import Arxiv.Arxiv2411_18291.RainbowColourAvoidance

/-!
# Joining rainbow families with disjoint colour assignments

An extension which avoids all labels used on its root can be joined to
that root without colour collisions. The statement allows the edge
families themselves to overlap; their assigned label ranges are disjoint.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [DecidableEq V] {r : ℕ}

theorem isRainbow_union_of_disjoint_colours (colour : I → Hypergraph V r)
    (H K : Hypergraph V r) (c : H ↪ I) (d : K ↪ I)
    (hc : ∀ e : H, e.val ∈ colour (c e)) (hd : ∀ e : K, e.val ∈ colour (d e))
    (hsep : ∀ e : H, ∀ f : K, c e ≠ d f) : IsRainbow colour (H ∪ K) := by
  classical
  let f (e : ↥(H ∪ K)) : I := if he : e.val ∈ H then c ⟨e.val, he⟩
    else d ⟨e.val, (mem_union.mp e.property).resolve_left he⟩
  have hinj : Function.Injective f := by
    intro e g heg
    by_cases he : e.val ∈ H
    · by_cases hg : g.val ∈ H
      · have hcg : c ⟨e.val, he⟩ = c ⟨g.val, hg⟩ := by
          simpa only [f, dif_pos he, dif_pos hg] using heg
        exact Subtype.ext (congrArg (fun x : H => x.val) (c.injective hcg))
      · have hcg : c ⟨e.val, he⟩ = d ⟨g.val, (mem_union.mp g.property).resolve_left hg⟩ := by
          simpa only [f, dif_pos he, dif_neg hg] using heg
        exact (hsep _ _ hcg).elim
    · by_cases hg : g.val ∈ H
      · have hcg : d ⟨e.val, (mem_union.mp e.property).resolve_left he⟩ = c ⟨g.val, hg⟩ := by
          simpa only [f, dif_neg he, dif_pos hg] using heg
        exact (hsep _ _ hcg.symm).elim
      · have hdg : d ⟨e.val, (mem_union.mp e.property).resolve_left he⟩ =
            d ⟨g.val, (mem_union.mp g.property).resolve_left hg⟩ := by
          simpa only [f, dif_neg he, dif_neg hg] using heg
        exact Subtype.ext (congrArg (fun x : K => x.val) (d.injective hdg))
  refine ⟨⟨f, hinj⟩, fun e => ?_⟩
  by_cases he : e.val ∈ H
  · simpa only [Function.Embedding.coeFn_mk, f, dif_pos he] using hc ⟨e.val, he⟩
  · simpa only [Function.Embedding.coeFn_mk, f, dif_neg he] using
      hd ⟨e.val, (mem_union.mp e.property).resolve_left he⟩

theorem IsRainbowAvoiding.union_left {colour : I → Hypergraph V r}
    {H K : Hypergraph V r} {B : Finset I} (hK : IsRainbowAvoiding colour K B)
    (c : H ↪ I) (hc : ∀ e : H, e.val ∈ colour (c e)) (hB : ∀ e : H, c e ∈ B) :
    IsRainbow colour (H ∪ K) := by
  obtain ⟨d, hd⟩ := hK
  exact isRainbow_union_of_disjoint_colours colour H K c d hc (fun e => (hd e).2)
    (fun e f hef => (hd f).1 (hef ▸ hB e))

theorem IsRainbowAvoiding.insert {colour : I → Hypergraph V r} {H : Hypergraph V r}
    {B : Finset I} (hH : IsRainbowAvoiding colour H B) {i : I} (hi : i ∈ B)
    {e : Block V r} (he : e ∈ colour i) : IsRainbow colour (insert e H) := by
  classical
  let c : ({e} : Hypergraph V r) ↪ I := ⟨fun _ => i, fun x y _ => Subtype.ext
    ((mem_singleton.mp x.property).trans (mem_singleton.mp y.property).symm)⟩
  have hc : ∀ x : ({e} : Hypergraph V r), x.val ∈ colour (c x) := by
    intro x
    change x.val ∈ colour i
    rw [mem_singleton.mp x.property]
    exact he
  simpa only [singleton_union] using hH.union_left c hc (fun _ => hi)

end Arxiv2411_18291
