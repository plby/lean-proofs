import StackExchange.Puzzling139335.JordanRegion
import Wikipedia.SchoenfliesTheorem.Inversion

/-!
# Connected complements after inversion

The inversion center is a limit of the image of every unbounded set.  Thus,
if that set is connected and misses the center, adjoining the center to its
inverted image preserves connectedness.  The complement of a bounded plane
set is unbounded, so this applies to complements of compact regions.
-/

open Set Metric Bornology

namespace Puzzling139335.HalfTurnRemainder

theorem center_mem_closure_invert_image {S : Set Plane} {a : Plane}
    (hS : ¬ IsBounded S) :
    a ∈ closure (Schoenflies.invert a '' S) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hzS, hzfar⟩ : ∃ z ∈ S, ε⁻¹ < dist z a := by
    by_contra hcon
    push Not at hcon
    exact hS ((isBounded_iff_subset_closedBall a).2
      ⟨ε⁻¹, fun z hz => hcon z hz⟩)
  refine ⟨Schoenflies.invert a z, ⟨z, hzS, rfl⟩, ?_⟩
  rw [dist_comm, Schoenflies.dist_invert_center]
  exact inv_lt_of_inv_lt₀ hε hzfar

theorem isConnected_invert_image_union_singleton {S : Set Plane} {a : Plane}
    (hconn : IsConnected S) (ha : a ∉ S) (hS : ¬ IsBounded S) :
    IsConnected (Schoenflies.invert a '' S ∪ {a}) := by
  have havoid : S ⊆ ({a}ᶜ : Set Plane) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact ha hx
  apply (hconn.image _ ((Schoenflies.continuousOn_invert a).mono havoid)).subset_closure
    subset_union_left
  apply union_subset subset_closure
  rintro x rfl
  exact center_mem_closure_invert_image hS

theorem not_isBounded_compl_of_isBounded {U : Set Plane} (hU : IsBounded U) :
    ¬ IsBounded Uᶜ := by
  intro hcomp
  apply NormedSpace.unbounded_univ ℝ Plane
  simpa only [union_compl_self] using hU.union hcomp

theorem isConnected_invert_compl_union_singleton_of_isBounded
    {U : Set Plane} {a : Plane} (hU : IsBounded U) (ha : a ∈ U)
    (hconn : IsConnected Uᶜ) :
    IsConnected (Schoenflies.invert a '' Uᶜ ∪ {a}) :=
  isConnected_invert_image_union_singleton hconn (fun h => h ha)
    (not_isBounded_compl_of_isBounded hU)

theorem isConnected_invert_compl_union_singleton {U : Set Plane} {a : Plane}
    (hU : IsCompact U) (ha : a ∈ U) (hconn : IsConnected Uᶜ) :
    IsConnected (Schoenflies.invert a '' Uᶜ ∪ {a}) :=
  isConnected_invert_compl_union_singleton_of_isBounded hU.isBounded ha hconn

end Puzzling139335.HalfTurnRemainder
