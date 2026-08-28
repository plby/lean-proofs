import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopy

/-!
# Lifting actual based simplices from native homotopy-map surjectivity

The boundary-preserving simplex-cube homeomorphism turns the given
simplex into its native generalized loop. A preimage in the actual
homotopy quotient supplies an actual source loop and a boundary-fixed
homotopy. Pulling both back gives a source simplex with its full boundary
based and a homotopy fixing every original simplex boundary point.
-/

noncomputable section

open scoped unitInterval Topology
open Wikipedia.HopfProblem FirstHurewicz HigherHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.BasedSimplexLifting

variable {A X : Type} [TopologicalSpace A] [TopologicalSpace X]

theorem exists_lift (n : ℕ) (f : C(A, X)) (a : A)
    (hs : Function.Surjective (HigherHomotopy.map (N := Fin n) f (y := a) rfl))
    (τ : BasedSimplex n (f a)) :
    ∃ ρ : BasedSimplex n a,
      Nonempty (τ.val.HomotopyRel (f.comp ρ.val) (simplexBoundary n)) := by
  obtain ⟨q, hq⟩ := hs (Quotient.mk' (basedSimplexNativeLoop τ))
  revert hq
  refine Quotient.inductionOn q ?_
  intro q hq
  have h : GenLoop.Homotopic (HigherHomotopy.genLoopMap f rfl q) (basedSimplexNativeLoop τ) :=
    Quotient.exact hq
  obtain ⟨H⟩ := h
  let e : C(Simplex n, Fin n → I) :=
    ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
  let ρ : BasedSimplex n a :=
    ⟨q.val.comp e, fun s hs ↦ q.property (e s) ((simplexCubeHomeomorph_boundary_iff n s).mpr hs)⟩
  have hp : (basedSimplexNativeLoop τ).val.comp e = τ.val :=
    basedSimplexNativeLoop_comp_homeomorph τ
  refine ⟨ρ, ⟨{
    toHomotopy := (H.symm.toHomotopy.compContinuousMap e).cast hp rfl
    prop' := ?_ }⟩⟩
  intro t s hs
  exact (H.symm.eq_fst t ((simplexCubeHomeomorph_boundary_iff n s).mpr hs)).trans
    (ContinuousMap.congr_fun hp s)

end NoExoticSixSphere.BasedSimplexLifting
