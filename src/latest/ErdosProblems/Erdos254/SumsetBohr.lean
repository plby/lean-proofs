/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.IntersectionDensity
import ErdosProblems.Erdos254.PiecewiseEmbedding

namespace Erdos254

open Filter Set
open scoped BigOperators

def natSumset (A B : Set ℕ) : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

lemma PositiveBinaryDensity.exists_true {c : BinarySequence} (hc : PositiveBinaryDensity c) :
    ∃ k : ℤ, c k = true := by
  by_contra h
  have hfalse (k : ℤ) : c k = false := by
    cases hk : c k with
    | false => rfl
    | true => exact False.elim (h ⟨k, hk⟩)
  obtain ⟨δ, hδ, hdensity⟩ := hc
  obtain ⟨N, hN⟩ := hdensity.exists
  simp only [hfalse, Bool.toNat_false, Nat.cast_zero, Finset.sum_const_zero, mul_zero] at hN
  exact (not_le_of_gt hδ) hN

/-- Common finite patterns of a configuration and a reflected configuration
embed their differences into the sumset. One common point ensures that the
translating integer is nonnegative. -/
lemma intersection_differences_finiteEmbeds {A B : Set ℕ}
    (x : binaryOrbitClosure (natConfiguration A)) (y : binaryOrbitClosure (natConfiguration B))
    (hc : ∃ k : ℤ, (x.val k && y.val (-k)) = true) :
    FiniteEmbeds (configurationDifferences (fun k : ℤ ↦ x.val k && y.val (-k)))
      (natSumset A B) := by
  classical
  intro F hF
  obtain ⟨k₀, hk₀⟩ := hc
  choose k hk using fun n : F ↦ hF n.property
  let K : Finset ℤ := insert k₀
    ((Finset.univ.image k) ∪ (Finset.univ.image (fun n : F ↦ k n + n.val)))
  have hK₀ : k₀ ∈ K := Finset.mem_insert_self _ _
  have hK₁ (n : F) : k n ∈ K := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, by simp, rfl⟩))
  have hK₂ (n : F) : k n + n.val ∈ K := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, by simp, rfl⟩))
  obtain ⟨u, hu⟩ := orbitClosure_finite_pattern x.property K
  obtain ⟨v, hv⟩ := orbitClosure_finite_pattern y.property (K.image (fun k ↦ -k))
  have hA (j : ℤ) (hj : j ∈ K) (htrue : (x.val j && y.val (-j)) = true) :
      ∃ a ∈ A, j + u = (a : ℤ) := by
    apply (natConfiguration_eq_true A (j + u)).mp
    exact (hu j hj).symm.trans (Bool.and_eq_true_iff.mp htrue).1
  have hB (j : ℤ) (hj : j ∈ K) (htrue : (x.val j && y.val (-j)) = true) :
      ∃ b ∈ B, -j + v = (b : ℤ) := by
    apply (natConfiguration_eq_true B (-j + v)).mp
    exact (hv (-j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).symm.trans
      (Bool.and_eq_true_iff.mp htrue).2
  obtain ⟨a₀, _, ha₀⟩ := hA k₀ hK₀ hk₀
  obtain ⟨b₀, _, hb₀⟩ := hB k₀ hK₀ hk₀
  have htpos : 0 ≤ u + v := by omega
  let t := (u + v).toNat
  have ht : (t : ℤ) = u + v := by dsimp [t]; omega
  refine ⟨t, fun n hn ↦ ?_⟩
  let i : F := ⟨n, hn⟩
  obtain ⟨a, ha, heqa⟩ := hA (k i + i.val) (hK₂ i) (hk i).2
  obtain ⟨b, hb, heqb⟩ := hB (k i) (hK₁ i) (hk i).1
  refine ⟨a, ha, b, hb, ?_⟩
  have hi : i.val = n := rfl
  have heq : (a : ℤ) + (b : ℤ) = (t : ℤ) + (n : ℤ) := by omega
  exact_mod_cast heq

/-- The Bergelson--Furstenberg--Weiss sumset input, in the syndetic case used
by Bergelson--Simmons and Fan. All density, spectral, and compactness inputs
are proved in the preceding modules. -/
theorem syndetic_sumset_piecewiseBohr {A B : Set ℕ} (hA : IsSyndetic A) (hB : IsSyndetic B) :
    ContainsPiecewiseBohr (natSumset A B) := by
  obtain ⟨x, y, hc⟩ := exists_positive_intersection_configuration
    (natConfiguration A) (natConfiguration B) hA.positiveBinaryDensity hB.positiveBinaryDensity
  exact (configuration_differences_piecewiseBohr _ hc).of_finiteEmbeds
    (intersection_differences_finiteEmbeds x y hc.exists_true)

end Erdos254
