import ErdosProblems.Erdos587.HooleyCoordinateBlocks
import ErdosProblems.Erdos587.PolynomialDenseBoxes

/-! # A coarse seed inside genuine coefficient-vector subset sums -/

open scoped Pointwise

namespace Erdos587.CFP

theorem delta_exists_coarse_coordinate_seed {d : ℕ} (A : Finset (Fin d → ℤ))
    (L : Fin d → ℕ) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (nvCoordBox (fun i => 2 * (h * L i))).card < M * (h • insert 0 D).card) :
    let T := (nvCoordBox (fun i => 2 * (h * L i))).card
    let c := 2 * (Nat.log 2 T + 1)
    let D := M * c ^ d
    let q := denseBoxCount D d
    q * (c * h) ≤ r →
    ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ z : Fin d → ℤ, ∃ P : NVFullGAP d,
      P.Proper ∧ P.AxisAligned ∧ ({z} : Finset (Fin d → ℤ)) + P.carrier ⊆ U.subsetSum ∧
      T ≤ nvDenseFactor D d * P.carrier.card ∧
      ∀ i j, |(P.length i : ℤ) * P.step i j| ≤ (q : ℤ) * (2 * (h * L j) : ℕ) := by
  let T := (nvCoordBox (fun i => 2 * (h * L i))).card
  let c := 2 * (Nat.log 2 T + 1)
  let D := M * c ^ d
  let q := denseBoxCount D d
  dsimp only
  intro hbudget
  have hD : 0 < D := by dsimp [D, c]; positivity
  obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ :=
    delta_exists_disjoint_coordinate_fibers A L hA h M r q hh hM hdense hbudget
  obtain ⟨P, hproper, haxis, hsub, hcard⟩ := exists_large_coordinate_GAP_of_dense_summands
    D hD (fun i => 2 * (h * L i)) Xs hlen (fun X hX => (hXs X hX).1)
      (fun X hX => (hXs X hX).2.le)
  refine ⟨U, hUA, hUcard, z, P, hproper, haxis,
    (Finset.add_subset_add (Finset.Subset.refl _) hsub).trans hsum, hcard, ?_⟩
  intro i j
  exact GeneralizedAP.nvFullGAP_generator_excursion_le P hlen
    (fun X hX => (hXs X hX).1) hsub i j

end Erdos587.CFP
