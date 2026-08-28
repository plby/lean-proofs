import Wikipedia.HopfProblem.OrbitPairRealizationNormalForm

/-!
# The actual unique normal parameters and continuous core-coordinate maps

The normal-parameter selection is set-theoretic. In contrast, for a fixed
simplex its core-coordinate map into the disjoint union of parameters is
continuous: only the barycentric coordinates vary.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

def normalParameters (z : SSet.toTop.obj S) : Parameters S :=
  (Classical.choose (existsUnique_normal S z)).val

theorem normalParameters_isNormal (z : SSet.toTop.obj S) :
    IsNormal S (normalParameters S z) :=
  (Classical.choose (existsUnique_normal S z)).property

theorem projection_normalParameters (z : SSet.toTop.obj S) :
    projection S (normalParameters S z) = z :=
  (Classical.choose_spec (existsUnique_normal S z)).1

theorem normalize_eq_normalParameters (p : Parameters S) :
    normalize S p = normalParameters S (projection S p) :=
  normal_injective S (normalize_isNormal S p)
    (normalParameters_isNormal S (projection S p))
    ((normalize_projection S p).trans (projection_normalParameters S (projection S p)).symm)

theorem normalParameters_injective : Function.Injective (normalParameters S) := by
  intro x y h
  have hp := congrArg (projection S) h
  simpa only [projection_normalParameters] using hp

def coreParameterMap (n : ℕ) (x : S _⦋n⦌) : C(Simplex n, Parameters S) where
  toFun := coreParameters S n x
  continuous_toFun := by
    change Continuous (fun t : Simplex n ↦
      (⟨⟨(core S n x).dim, (core S n x).simplex.val⟩,
        stdSimplex.map (core S n x).collapse.toOrderHom t⟩ : Parameters S))
    exact continuous_sigmaMk.comp (stdSimplex.continuous_map (core S n x).collapse.toOrderHom)

theorem coreParameterMap_apply (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) :
    coreParameterMap S n x t = coreParameters S n x t := rfl

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
