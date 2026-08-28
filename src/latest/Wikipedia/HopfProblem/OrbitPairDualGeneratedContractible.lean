import Wikipedia.HopfProblem.OrbitPairGeneratedSimplexDeformation

/-!
# Contractibility of generated cells in native dual subdivision

Strong induction on simplex dimension uses the actual zeroth-face
deformation for a nondegenerate simplex. A degenerate simplex generates
the same subcomplex as a lower-dimensional simplex. The base case is
the native realization of the standard zero-simplex.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.InitialFace

theorem zero_characteristic_mono {X : SSet.{u}} (z : X _⦋0⦌) :
    Mono (SSet.yonedaEquiv.symm z) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply ConcreteCategory.mono_of_injective
  intro a b _
  apply SSet.stdSimplex.objEquiv.injective
  exact Subsingleton.elim _ _

theorem generated_zero_contractible {X : SSet.{u}} (z : X _⦋0⦌) :
    ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet)) := by
  let : Mono (SSet.yonedaEquiv.symm z) := zero_characteristic_mono z
  let : IsIso (SSet.Subcomplex.toOfSimplex z) :=
    (SSet.Subcomplex.isIso_toOfSimplex_iff z).mpr inferInstance
  let : ContractibleSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋0⦌)) := standard_contractible 0
  exact (TopCat.homeoOfIso
    (SSet.toTop.mapIso (asIso (SSet.Subcomplex.toOfSimplex z)))).symm.contractibleSpace

theorem generated_contractible_of_initialInjective (X : SSet.{u})
    (hX : ∀ (n : ℕ) (z : X _⦋n⦌), z ∈ X.nonDegenerate n → InitialInjective z)
    (n : ℕ) (z : X _⦋n⦌) :
    ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet)) := by
  revert z
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z
    cases n with
    | zero => exact generated_zero_contractible z
    | succ n =>
      by_cases hz : z ∈ X.nonDegenerate (n + 1)
      · let : ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex (X.δ 0 z) : SSet)) :=
          ih n (Nat.lt_succ_self n) (X.δ 0 z)
        exact generated_contractible_of_face z (hX (n + 1) z hz)
      · have hd : z ∈ X.degenerate (n + 1) :=
          (X.mem_degenerate_iff_notMem_nonDegenerate z).mpr hz
        obtain ⟨m, hm, f, hf, y, hy⟩ := (X.mem_degenerate_iff z).mp hd
        let : Epi f := hf
        have heq : SSet.Subcomplex.ofSimplex z = SSet.Subcomplex.ofSimplex y :=
          (congrArg SSet.Subcomplex.ofSimplex hy).symm.trans
            (SSet.Subcomplex.ofSimplex_map_of_epi f y)
        exact Eq.mpr (congrArg (fun A : X.Subcomplex ↦
          ContractibleSpace (SSet.toTop.obj (A : SSet))) heq) (ih m hm y)

end Wikipedia.HopfProblem.OrbitPair.InitialFace

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

theorem dual_generated_contractible (X : SSet.{u}) (n : ℕ) (z : (dualSd.obj X) _⦋n⦌) :
    ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet)) :=
  InitialFace.generated_contractible_of_initialInjective (dualSd.obj X)
    (fun _ z hz ↦ dual_initialInjective X z hz) n z

end Wikipedia.HopfProblem.OrbitPair.Subdivision
