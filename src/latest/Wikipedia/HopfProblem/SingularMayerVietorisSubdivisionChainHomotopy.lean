import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionHomotopy
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Subdivision as an actual chain homotopy equivalence

The degreewise, explicitly constructed subdivision homotopy is packaged as
Mathlib's `Homotopy` between actual singular chain maps. Consequently every
subdivision induces the identity on actual singular homology in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz CategoryTheory HomologicalComplex

/-- The degree-raising components of the actual subdivision homotopy. -/
def subdivisionHomotopyComponent (X : Type) [TopologicalSpace X] (k : ℕ)
    (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) : Chains X i ⟶ Chains X j := by
  change i + 1 = j at h
  subst j
  exact ModuleCat.ofHom (subdivisionHomotopy X k i)

/-- The null-homotopic chain map given by these concrete homotopy components. -/
def subdivisionNullMap (X : Type) [TopologicalSpace X] (k : ℕ) :
    singularComplex X ⟶ singularComplex X :=
  Homotopy.nullHomotopicMap' (subdivisionHomotopyComponent X k)

/-- The tautological null-homotopic map is exactly identity minus subdivision. -/
theorem subdivisionNullMap_eq (X : Type) [TopologicalSpace X] (k : ℕ) :
    subdivisionNullMap X k = 𝟙 (singularComplex X) - subdivisionChainMap X k := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change (Homotopy.nullHomotopicMap' (subdivisionHomotopyComponent X k)).f 0 = _
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (k₁ := 1) (k₀ := 0) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
        (fun l hl => Nat.succ_ne_zero l hl)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change ((singularComplex X).d 1 0).hom (subdivisionHomotopy X k 0 c) =
        c - subdivision X k 0 c
      exact subdivisionHomotopy_boundary_zero k c
  | succ n =>
      change (Homotopy.nullHomotopicMap' (subdivisionHomotopyComponent X k)).f (n + 1) = _
      rw [Homotopy.nullHomotopicMap'_f (k₂ := n + 2) (k₁ := n + 1) (k₀ := n)
        (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)
        (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change subdivisionHomotopy X k n (((singularComplex X).d (n + 1) n).hom c) +
          ((singularComplex X).d (n + 2) (n + 1)).hom
            (subdivisionHomotopy X k (n + 1) c) =
        c - subdivision X k (n + 1) c
      exact (add_comm _ _).trans (subdivisionHomotopy_boundary k n c)

/-- The explicit singular-chain homotopy from the identity to subdivision. -/
def subdivisionChainHomotopy (X : Type) [TopologicalSpace X] (k : ℕ) :
    Homotopy (𝟙 (singularComplex X)) (subdivisionChainMap X k) := by
  refine Homotopy.equivSubZero.symm ?_
  have h : Homotopy (subdivisionNullMap X k) 0 :=
    Homotopy.nullHomotopy' (subdivisionHomotopyComponent X k)
  rw [subdivisionNullMap_eq] at h
  exact h

/-- Every subdivision induces the identity on actual singular homology. -/
theorem subdivision_homologyMap (X : Type) [TopologicalSpace X] (k n : ℕ) :
    HomologicalComplex.homologyMap (subdivisionChainMap X k) n =
      𝟙 ((singularComplex X).homology n) := by
  have h := (subdivisionChainHomotopy X k).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_id] at h
  exact h.symm

/-- Actual subdivision is a chain homotopy equivalence, with identity as inverse. -/
def subdivisionHomotopyEquiv (X : Type) [TopologicalSpace X] (k : ℕ) :
    HomotopyEquiv (singularComplex X) (singularComplex X) where
  hom := subdivisionChainMap X k
  inv := 𝟙 (singularComplex X)
  homotopyHomInvId := by simpa using (subdivisionChainHomotopy X k).symm
  homotopyInvHomId := by simpa using (subdivisionChainHomotopy X k).symm

/-- In particular every actual subdivision is an unconditional quasi-isomorphism. -/
theorem subdivision_quasiIso (X : Type) [TopologicalSpace X] (k : ℕ) :
    QuasiIso (subdivisionChainMap X k) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, subdivision_homologyMap]
  infer_instance

end Wikipedia.HopfProblem.SingularMayerVietoris
