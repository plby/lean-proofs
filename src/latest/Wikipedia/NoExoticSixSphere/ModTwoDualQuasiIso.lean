import Wikipedia.NoExoticSixSphere.ModTwoDualHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Mod-two duals of quasi-isomorphisms between projective chain complexes

A quasi-isomorphism between the actual bounded-below projective chain
complexes is a genuine chain homotopy equivalence. Its original dual
therefore remains a quasi-isomorphism. This does not assume exactness
of mod-two duality on arbitrary integer modules.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.ModTwoDualComplex

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Actual precomposition preserves quasi-isomorphisms of projective chain complexes. -/
theorem map_quasiIso_of_projective [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (map f) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  rw [← he]
  exact (mapHomotopyEquiv e).quasiIso_hom

end NoExoticSixSphere.ModTwoDualComplex
