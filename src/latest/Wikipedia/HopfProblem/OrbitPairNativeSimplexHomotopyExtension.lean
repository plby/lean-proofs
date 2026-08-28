import Wikipedia.HopfProblem.OrbitPairSimplexHomotopyExtension

/-!
# Homotopy extension for the actual realized boundary inclusion

The native boundary homeomorphism commutes exactly with the original
inclusion and the standard-coordinate homeomorphism. Transporting the
literal simplex extension therefore gives the homotopy-extension property
for the actual map `|boundary n| → |standardSimplex n|`.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.NativeSimplexHomotopyExtension

open FirstHurewicz SecondHurewicz.SimplyConnected Subdivision

theorem boundary_symm_inclusion (n : ℕ) (q : ↥(simplexBoundary n)) :
    (SSet.toTop.map (SSet.boundary.{u} n).ι) ((RealizedSimplexBoundary.homeomorph n).symm q) =
      (standardCoordinates n).symm q.val := by
  apply (standardCoordinates n).injective
  rw [Homeomorph.apply_symm_apply]
  simpa only [Homeomorph.apply_symm_apply] using
    (RealizedSimplexBoundary.homeomorph_inclusion n
      ((RealizedSimplexBoundary.homeomorph n).symm q)).symm

theorem exists_extension (n : ℕ) {Z : Type v} [TopologicalSpace Z]
    (f : C(SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n⦌), Z))
    (G : C(I × SSet.toTop.obj (SSet.boundary n : SSet), Z))
    (h0 : ∀ a, G (0, a) = f ((SSet.toTop.map (SSet.boundary n).ι) a)) :
    ∃ H : C(I × SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌), Z),
      (∀ x, H (0, x) = f x) ∧
        ∀ t a, H (t, (SSet.toTop.map (SSet.boundary n).ι) a) = G (t, a) := by
  let e := standardCoordinates.{u} n
  let b := RealizedSimplexBoundary.homeomorph.{u} n
  let f' : C(Simplex n, Z) := f.comp ⟨e.symm, e.symm.continuous⟩
  let G' : C(I × ↥(simplexBoundary n), Z) :=
    G.comp ((ContinuousMap.id I).prodMap ⟨b.symm, b.symm.continuous⟩)
  have h0' : ∀ q, G' (0, q) = f' q.val := fun q ↦
    (h0 (b.symm q)).trans (congrArg f (boundary_symm_inclusion n q))
  obtain ⟨K, hK0, hKb⟩ := SimplexHomotopyExtension.exists_extension n f' G' h0'
  let H := K.comp ((ContinuousMap.id I).prodMap ⟨e, e.continuous⟩)
  refine ⟨H, ?_, ?_⟩
  · intro x
    change K (0, e x) = f x
    exact (hK0 (e x)).trans (congrArg f (e.symm_apply_apply x))
  · intro t a
    change K (t, e ((SSet.toTop.map (SSet.boundary n).ι) a)) = G (t, a)
    rw [← RealizedSimplexBoundary.homeomorph_inclusion n a]
    exact (hKb t (b a)).trans (congrArg (fun q ↦ G (t, q)) (b.symm_apply_apply a))

end Wikipedia.HopfProblem.OrbitPair.NativeSimplexHomotopyExtension

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

def HasHomotopyExtension {A B : TopCat.{u}} (i : A ⟶ B) : Prop :=
  ∀ (Z : TopCat.{u}) (f : C(B, Z)) (G : C(I × A, Z)),
    (∀ a, G (0, a) = f (i a)) →
      ∃ H : C(I × B, Z), (∀ b, H (0, b) = f b) ∧ ∀ t a, H (t, i a) = G (t, a)

theorem realized_boundary_hasHomotopyExtension (n : ℕ) :
    HasHomotopyExtension (SSet.toTop.map (SSet.boundary.{u} n).ι) := by
  intro Z f G h0
  exact NativeSimplexHomotopyExtension.exists_extension n f G h0

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
