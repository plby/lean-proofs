import Wikipedia.NoExoticSixSphere.ComplexStructureColumnFiber
import Wikipedia.NoExoticSixSphere.ComplexStructureColumnHomotopy

/-!
# Rank reduction for sphere families of orthogonal complex structures

The exact relative column lift and the actual column-fiber homeomorphism
reduce the rank by two when the source sphere is smaller than the column
sphere. A vanishing theorem at the lower rank propagates upwards; the
rank-six vanishing input is not assumed to have been proved.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization ComplexStructureColumnFiber

theorem exists_based_rankReduction {m n : ℕ} (hmn : m < n)
    (v : UnitSphere (Vector (n + 2))) (f : C(Sphere m, Space (n + 2))) (p : Sphere m) :
    ∃ q : C(Sphere m, Space n),
      q p = residual v (column v (f p)) (f p) rfl ∧
      Nonempty (f.HomotopyRel (reconstructMap v (column v (f p)) q) {p}) := by
  obtain ⟨g, hgp, ⟨H⟩, hcol⟩ := exists_based_constant_column hmn v f p
  let q := residualMap v (column v (f p)) g hcol
  have hrec : reconstructMap v (column v (f p)) q = g :=
    reconstructMap_residualMap v (column v (f p)) g hcol
  refine ⟨q, ?_, ⟨H.cast rfl hrec.symm⟩⟩
  change residual v (column v (f p)) (g p) (hcol p) =
    residual v (column v (f p)) (f p) rfl
  congr 1

theorem exists_rankReduction {m n : ℕ} (hmn : m < n)
    (v : UnitSphere (Vector (n + 2))) (f : C(Sphere m, Space (n + 2))) :
    ∃ c : Sphere n, ∃ q : C(Sphere m, Space n), f.Homotopic (reconstructMap v c q) := by
  obtain ⟨p⟩ : Nonempty (Sphere m) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  obtain ⟨q, -, ⟨H⟩⟩ := exists_based_rankReduction hmn v f p
  exact ⟨column v (f p), q, ⟨H.toHomotopy⟩⟩

theorem sphereVanishing_add_two {m n : ℕ} (hmn : m < n)
    (hn : ∀ f : C(Sphere m, Space n), ∃ K, f.Homotopic (ContinuousMap.const _ K)) :
    ∀ f : C(Sphere m, Space (n + 2)), ∃ J, f.Homotopic (ContinuousMap.const _ J) := by
  intro f
  obtain ⟨v⟩ : Nonempty (UnitSphere (Vector (n + 2))) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  obtain ⟨c, q, hfq⟩ := exists_rankReduction hmn v f
  obtain ⟨K, hqK⟩ := hn q
  refine ⟨reconstruct v c K, hfq.trans ?_⟩
  simpa only [reconstructMap_const] using homotopic_reconstructMap v c hqK

theorem sphereVanishing_add_even {m n : ℕ} (hmn : m < n)
    (hn : ∀ f : C(Sphere m, Space n), ∃ K, f.Homotopic (ContinuousMap.const _ K)) (r : ℕ) :
    ∀ f : C(Sphere m, Space (n + 2 * r)), ∃ J, f.Homotopic (ContinuousMap.const _ J) := by
  induction r with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero] using hn
  | succ r ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact sphereVanishing_add_two (show m < n + 2 * r by omega) ih

/-- The rank-six vanishing theorem, once proved, suffices at the rank used in
the checked first Bott comparison. -/
theorem fourthSphereVanishing_sixteen_of_six
    (h6 : ∀ f : C(Sphere 4, Space 6), ∃ K, f.Homotopic (ContinuousMap.const _ K)) :
    ∀ f : C(Sphere 4, Space 16), ∃ J, f.Homotopic (ContinuousMap.const _ J) :=
  sphereVanishing_add_even (by omega : 4 < 6) h6 5

/-- The concrete complex-structure spaces used in the comparisons are nonempty
in every even rank, by repeated reconstruction starting in rank zero. -/
theorem nonempty_even (r : ℕ) : Nonempty (Space (2 * r)) := by
  induction r with
  | zero =>
    have h : Nonempty (Space 0) := ⟨⟨0, Subsingleton.elim _ _⟩⟩
    simpa only [Nat.mul_zero] using h
  | succ r ih =>
    rw [Nat.mul_succ]
    obtain ⟨K⟩ := ih
    obtain ⟨v⟩ : Nonempty (UnitSphere (Vector (2 * r + 2))) :=
      NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
    obtain ⟨c⟩ : Nonempty (Sphere (2 * r)) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
    exact ⟨reconstruct v c K⟩

end NoExoticSixSphere.OrthogonalComplexStructures
