import Wikipedia.HopfProblem.OrbitPairRealizationQuotient
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Nondegenerate representatives in the actual realization

The characteristic maps of nondegenerate simplices still detect the
topology. Removing degeneracies and zero coordinates decreases dimension,
so every point has a representative with all coordinates positive in a
nondegenerate simplex. Uniqueness of this representative is a separate
claim and is not assumed here.
-/

noncomputable section

open CategoryTheory Simplicial Topology

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz SecondHurewicz.SimplyConnected

variable (S : SSet)

theorem continuous_iff_nonDegenerate {Y : Type*} [TopologicalSpace Y]
    (f : SSet.toTop.obj S → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : S.nonDegenerate n),
      Continuous (f ∘ characteristic S n x.val) := by
  rw [continuous_iff_characteristic]
  constructor
  · intro hf n x
    exact hf n x.val
  · intro hf n x
    obtain ⟨m, g, _, y, rfl⟩ := S.exists_nonDegenerate x
    rw [characteristic_map]
    exact (hf m y).comp (SimplexCategory.toTop₀.map g).hom.continuous

theorem isOpen_iff_nonDegenerate (U : Set (SSet.toTop.obj S)) :
    IsOpen U ↔ ∀ (n : ℕ) (x : S.nonDegenerate n),
      IsOpen (characteristic S n x.val ⁻¹' U) := by
  rw [isOpen_iff_characteristic]
  constructor
  · intro hU n x
    exact hU n x.val
  · intro hU n x
    obtain ⟨m, g, _, y, rfl⟩ := S.exists_nonDegenerate x
    rw [characteristic_map]
    exact (hU m y).preimage (SimplexCategory.toTop₀.map g).hom.continuous

theorem isClosed_iff_nonDegenerate (U : Set (SSet.toTop.obj S)) :
    IsClosed U ↔ ∀ (n : ℕ) (x : S.nonDegenerate n),
      IsClosed (characteristic S n x.val ⁻¹' U) := by
  simp only [← isOpen_compl_iff, isOpen_iff_nonDegenerate, Set.preimage_compl]

theorem exists_positive_nonDegenerate_representative (n : ℕ) (x : S _⦋n⦌)
    (t : Simplex n) :
    ∃ (m : ℕ) (_ : m ≤ n) (y : S.nonDegenerate m) (v : Simplex m),
      (∀ i, 0 < v i) ∧ characteristic S m y.val v = characteristic S n x t := by
  classical
  induction n with
  | zero =>
      let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
      refine ⟨0, le_rfl, ⟨x, by simp⟩, t, ?_, rfl⟩
      intro i
      have hi : t i = 1 := stdSimplex.eq_one_of_unique t i
      rw [hi]
      exact zero_lt_one
  | succ n ih =>
      by_cases hx : x ∈ S.nonDegenerate (n + 1)
      · by_cases ht : ∀ i, 0 < t i
        · exact ⟨n + 1, le_rfl, ⟨x, hx⟩, t, ht, rfl⟩
        · push Not at ht
          obtain ⟨i, hi⟩ := ht
          have hzero : t i = 0 := le_antisymm hi (stdSimplex.zero_le t i)
          let s := simplexFaceInverse n i ⟨t, hzero⟩
          have hs : simplexFace n i s = t := simplexFace_inverse n i ⟨t, hzero⟩
          obtain ⟨m, hm, y, v, hv, hchar⟩ := ih (S.δ i x) s
          refine ⟨m, hm.trans (Nat.le_succ n), y, v, hv, hchar.trans ?_⟩
          have hface := congrArg (fun f : C(Simplex n, SSet.toTop.obj S) ↦ f s)
            (characteristic_face S n i x)
          exact hface.trans (congrArg (characteristic S (n + 1) x) hs)
      · have hd : x ∈ S.degenerate (n + 1) :=
          (S.mem_degenerate_iff_notMem_nonDegenerate x).mpr hx
        rw [S.degenerate_eq_iUnion_range_σ] at hd
        obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.mp hd
        obtain ⟨m, hm, y, v, hv, hchar⟩ :=
          ih a ((SimplexCategory.toTop₀.map (SimplexCategory.σ i)).hom t)
        refine ⟨m, hm.trans (Nat.le_succ n), y, v, hv, hchar.trans ?_⟩
        exact (congrArg (fun f : C(Simplex (n + 1), SSet.toTop.obj S) ↦ f t)
          (characteristic_map S (n + 1) n (SimplexCategory.σ i) a)).symm

theorem exists_positive_nonDegenerate (z : SSet.toTop.obj S) :
    ∃ (n : ℕ) (x : S.nonDegenerate n) (t : Simplex n),
      (∀ i, 0 < t i) ∧ characteristic S n x.val t = z := by
  obtain ⟨n, x, t, rfl⟩ := exists_characteristic S z
  obtain ⟨m, _, y, v, hv, hchar⟩ := exists_positive_nonDegenerate_representative S n x t
  exact ⟨m, y, v, hv, hchar⟩

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
