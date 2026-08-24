import ErdosProblems.Erdos587.StableCoordinateModel

/-!
Stabilize the coordinate subgroup while retaining the same multiscale
density targets. The targets refer to the original stable set, so no new
doubling assumption is required after this deletion.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem exists_subgroupStable_multiscale_subset
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h n F r d₀ : ℕ) (T : ℕ → ℕ)
    (hF : 0 < F) (hdim : P.rank ≤ d₀) (hpos : ∀ i, 0 < P.length i)
    (hscale : 4 * F ≤ 2 ^ n * h)
    (hmodel : (P.dilate (2 ^ n * h)).boxCard ≤ F * T n)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + ((4 * F) ^ d₀ + 1) * r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card) :
    ∃ B ⊆ A, A.card ≤ B.card + (4 * F) ^ d₀ * r ∧
      (generatedSubgroup P.centeredCoordinates B).FiniteIndex ∧
      (generatedSubgroup P.centeredCoordinates B).index ≤ (4 * F) ^ d₀ ∧
      (∀ D ⊆ B, B.card ≤ D.card + r →
        generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates B) ∧
      ∀ D ⊆ B, B.card ≤ D.card + r → ∀ j ≤ n,
        2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card := by
  have hwidth (i : Fin P.rank) : 4 * F ≤ (2 ^ n * h) * P.length i + 1 := by
    have hm : 2 ^ n * h ≤ (2 ^ n * h) * P.length i := by
      simpa using Nat.mul_le_mul_left (2 ^ n * h) (hpos i)
    omega
  have hdense' : ∀ D ⊆ A, A.card ≤ D.card + ((4 * F) ^ d₀ + 1) * r →
      2 * (P.dilate (2 ^ n * h)).boxCard < (4 * F) *
        ((2 ^ n * h) • insert 0 D).card := by
    intro D hDA hcost
    have ht := Nat.mul_lt_mul_of_pos_left (hdense D hDA hcost n (le_refl _)) hF
    nlinarith
  obtain ⟨B, hBA, hcost, hfinite, hindex, hstable⟩ :=
    exists_subset_stable_centeredCoordinates P A hzero hA (2 ^ n * h) r (4 * F) d₀
      (by omega) hdim hwidth hdense'
  refine ⟨B, hBA, hcost, hfinite, hindex, hstable, ?_⟩
  intro D hDB hremove j hj
  apply hdense D (hDB.trans hBA) _ j hj
  calc
    A.card ≤ B.card + (4 * F) ^ d₀ * r := hcost
    _ ≤ (D.card + r) + (4 * F) ^ d₀ * r := Nat.add_le_add_right hremove _
    _ = D.card + ((4 * F) ^ d₀ + 1) * r := by ring

end Erdos587.CFP
