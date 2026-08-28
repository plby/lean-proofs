import Wikipedia.HopfProblem.FundamentalGroupVanKampenSquareCell
import Wikipedia.HopfProblem.FundamentalGroupVanKampenSquareGrid

/-!
# Local-to-global homotopy invariance of path values

A continuous homotopy square has a finite rectangular subdivision
subordinate to any open cover.  Local homotopy invariance proves the
boundary equation of each rectangle, and cancellation along the rows
proves that the values of its two boundary paths agree.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
variable {G : Type*} [Group G] {U : ι → Set X}

namespace PathValue

variable (V : PathValue X G)

/-- The actual finite subdivision of a homotopy square transfers local
homotopy invariance to its two boundary paths. -/
theorem value_eq_of_homotopy_of_open_cover (L : LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hExt : V.Extends L) (hL : L.HomotopyInvariant)
    {x y : X} (p q : Path x y) (H : Path.Homotopy p q) :
    V.value p = V.value q := by
  have hpre : univ ⊆ ⋃ i, H ⁻¹' U i := by
    rw [← preimage_iUnion, hcover, preimage_univ]
  obtain ⟨d, hd0, hdmono, ⟨n, hn⟩, hrect⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => (hopen i).preimage (map_continuous H)) hpre
  have hstep (k : ℕ) : V.value (H.eval (d k)) = V.value (H.eval (d (k + 1))) := by
    have hstrip := V.square_strip H.toContinuousMap (d k) (d (k + 1)) d hdmono n
      (fun m _ => by
        obtain ⟨i, hi⟩ := hrect k m
        exact V.square_cell_of_local L hExt hL i H.toContinuousMap
          (d k) (d (k + 1)) (d m) (d (m + 1))
          (hdmono (Nat.le_succ k)) (hdmono (Nat.le_succ m)) hi)
    rw [hd0, hn n le_rfl] at hstrip
    simpa only [V.value_subpath_zero_one, V.value_squareVertical_homotopy_zero,
      V.value_squareVertical_homotopy_one, V.value_squareHorizontal_homotopy,
      mul_one, one_mul] using hstrip
  have hwalk : ∀ k, V.value (H.eval (d 0)) = V.value (H.eval (d k)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact ih.trans (hstep k)
  have hfinish := hwalk n
  simpa only [hd0, hn n le_rfl, Path.Homotopy.eval_zero, Path.Homotopy.eval_one] using hfinish

/-- Multiplicative path values that extend locally homotopy-invariant
values on an open cover are globally homotopy invariant. -/
theorem homotopyInvariant_of_open_cover (L : LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hExt : V.Extends L) (hL : L.HomotopyInvariant) : V.HomotopyInvariant := by
  intro x y p q h
  obtain ⟨H⟩ := h
  exact V.value_eq_of_homotopy_of_open_cover L hopen hcover hExt hL p q H

end PathValue

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
