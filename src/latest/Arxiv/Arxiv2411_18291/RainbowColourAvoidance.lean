import Arxiv.Arxiv2411_18291.RainbowColourRelabeling

/-!
# Rainbow witnesses avoiding prescribed colours

Duplicating a palette with distinct colour labels allows a bounded set of
forbidden labels to be avoided. This is a deterministic relabelling step;
the duplicated permutations need not be independent.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I J V : Type*} {r : ℕ}

def IsRainbowAvoiding (colour : J → Hypergraph V r) (H : Hypergraph V r)
    (B : Finset J) : Prop :=
  ∃ c : H ↪ J, ∀ e : H, c e ∉ B ∧ e.val ∈ colour (c e)

theorem IsRainbowAvoiding.isRainbow {colour : J → Hypergraph V r} {H : Hypergraph V r}
    {B : Finset J} (hH : IsRainbowAvoiding colour H B) : IsRainbow colour H := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, fun e => (hc e).2⟩

theorem IsRainbowAvoiding.mono {colour : J → Hypergraph V r} {H H' : Hypergraph V r}
    {B : Finset J} (hH : IsRainbowAvoiding colour H B) (hsub : H' ⊆ H) :
    IsRainbowAvoiding colour H' B := by
  obtain ⟨c, hc⟩ := hH
  let e : H' ↪ H := ⟨fun x => ⟨x.val, hsub x.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : H => z.val) h)⟩
  exact ⟨e.trans c, fun x => hc (e x)⟩

theorem exists_unused_colour_group [Fintype I] (B : Finset (I × J))
    (hB : B.card < Fintype.card I) : ∃ i : I, ∀ j : J, (i, j) ∉ B := by
  classical
  have hc : (B.image Prod.fst).card < (univ : Finset I).card :=
    (card_image_le.trans_lt hB).trans_eq card_univ.symm
  obtain ⟨i, _, hi⟩ := exists_mem_notMem_of_card_lt_card hc
  exact ⟨i, fun j hj => hi (mem_image.mpr ⟨(i, j), hj, rfl⟩)⟩

theorem IsRainbow.avoiding_copies [Fintype I] {colour : J → Hypergraph V r}
    {H : Hypergraph V r} (hH : IsRainbow colour H) (B : Finset (I × J))
    (hB : B.card < Fintype.card I) :
    IsRainbowAvoiding (fun p : I × J => colour p.2) H B := by
  obtain ⟨i, hi⟩ := exists_unused_colour_group B hB
  obtain ⟨c, hc⟩ := hH
  let d : H ↪ I × J := ⟨fun e => (i, c e),
    fun e f hef => c.injective (congrArg Prod.snd hef)⟩
  exact ⟨d, fun e => ⟨hi (c e), hc e⟩⟩

end Arxiv2411_18291
