import ErdosProblems.Erdos73.PureEndpointPairs
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.Pigeonhole

/-! Select fixed-size, rank-ordered families and homogeneous finite fibres. -/

namespace Erdos73
noncomputable section
open scoped Classical

open Finset

theorem exists_rank_ordered_selection {I : Type*} (s : Finset I) (rank : I → ℕ)
    (hrank : Set.InjOn rank (s : Set I)) (k : ℕ) (hsize : k ≤ s.card) :
    ∃ f : Fin k → I, Function.Injective f ∧ (∀ i, f i ∈ s) ∧ StrictMono (rank ∘ f) := by
  obtain ⟨t, hts, htcard⟩ := exists_subset_card_eq hsize
  have htinj : Set.InjOn rank (t : Set I) := hrank.mono hts
  have himage : (t.image rank).card = k := (card_image_iff.mpr htinj).trans htcard
  let e := (t.image rank).orderEmbOfFin himage
  have hex (i : Fin k) : ∃ x ∈ t, rank x = e i := mem_image.mp
    ((t.image rank).orderEmbOfFin_mem himage i)
  choose f hf he using hex
  refine ⟨f, ?_, fun i => hts (hf i), ?_⟩
  · intro i j hij
    apply e.injective
    exact (he i).symm.trans ((congrArg rank hij).trans (he j))
  · intro i j hij
    change rank (f i) < rank (f j)
    rw [he i, he j]
    exact e.strictMono hij

theorem exists_large_finite_fiber {I B : Type*} [Fintype B] [Nonempty B]
    (s : Finset I) (f : I → B) (k : ℕ) (hsize : Fintype.card B * k ≤ s.card) :
    ∃ b : B, ∃ t : Finset I, t ⊆ s ∧ k ≤ t.card ∧ ∀ i ∈ t, f i = b := by
  obtain ⟨b, _, hb⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := s) (t := (univ : Finset B)) (f := f) (fun _ _ => mem_univ _) univ_nonempty
    (by simpa only [card_univ] using hsize)
  exact ⟨b, s.filter (fun i => f i = b), filter_subset _ _, hb,
    fun _ hi => (mem_filter.mp hi).2⟩

end
end Erdos73
