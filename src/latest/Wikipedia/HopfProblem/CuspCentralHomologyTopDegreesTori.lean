import Wikipedia.HopfProblem.CuspCentralHomologyPhaseTori
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups

/-!
# Actual homology of the compact phases in the central open cover

The original compact fibre phases form the literal two-circle torus.
Adding the radial boundary circle gives a literal three-circle torus.
The actual coordinate homeomorphisms transfer the already proved
integral singular homology of finite circle products to these spaces.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

def compactFibreTorusHomologyEquiv (n : ℕ) :
    SingularHomology CompactFibreTorus n ≃ₗ[ℤ] binomialModule 2 n :=
  (homeomorphHomologyEquiv compactFibreTorusHomeomorph n).trans
    (productTorusHomologyEquiv 2 n)

def fibreTorusCircleHomologyEquiv (n : ℕ) :
    SingularHomology (CompactFibreTorus × Circle) n ≃ₗ[ℤ] binomialModule 3 n :=
  (homeomorphHomologyEquiv fibreTorusCircleHomeomorph n).trans
    (productTorusHomologyEquiv 3 n)

/-- The actual top class of the overlap's phase-circle model has one
integral coordinate. -/
def fibreTorusCircleHomologyThreeEquiv :
    SingularHomology (CompactFibreTorus × Circle) 3 ≃ₗ[ℤ] ℤ :=
  (fibreTorusCircleHomologyEquiv 3).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

theorem compactFibreTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 2 < n) :
    Subsingleton (SingularHomology CompactFibreTorus n) := by
  let := productTorus_homology_subsingleton_of_lt hn
  exact (homeomorphHomologyEquiv compactFibreTorusHomeomorph n).injective.subsingleton

theorem compactFibreTorus_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology CompactFibreTorus (n + 3)) :=
  compactFibreTorus_homology_subsingleton_of_lt (by omega)

theorem fibreTorusCircle_homology_subsingleton_of_lt {n : ℕ} (hn : 3 < n) :
    Subsingleton (SingularHomology (CompactFibreTorus × Circle) n) := by
  let := productTorus_homology_subsingleton_of_lt hn
  exact (homeomorphHomologyEquiv fibreTorusCircleHomeomorph n).injective.subsingleton

theorem fibreTorusCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (CompactFibreTorus × Circle) (n + 4)) :=
  fibreTorusCircle_homology_subsingleton_of_lt (by omega)

theorem compactFibreTorus_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology CompactFibreTorus n) = Nat.choose 2 n := by
  rw [(compactFibreTorusHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 2 n

theorem fibreTorusCircle_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (CompactFibreTorus × Circle) n) = Nat.choose 3 n := by
  rw [(fibreTorusCircleHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 3 n

theorem compactFibreTorus_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology CompactFibreTorus n) :=
  Module.Free.of_equiv (compactFibreTorusHomologyEquiv n).symm

theorem fibreTorusCircle_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (CompactFibreTorus × Circle) n) :=
  Module.Free.of_equiv (fibreTorusCircleHomologyEquiv n).symm

theorem compactFibreTorus_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology CompactFibreTorus n) := by
  let := compactFibreTorus_homology_free n
  infer_instance

theorem fibreTorusCircle_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (CompactFibreTorus × Circle) n) := by
  let := fibreTorusCircle_homology_free n
  infer_instance

end Wikipedia.HopfProblem.CuspCentralHomology
