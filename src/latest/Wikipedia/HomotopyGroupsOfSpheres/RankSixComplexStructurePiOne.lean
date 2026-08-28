import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorInterval
import Wikipedia.NoExoticSixSphere.RankSixPfaffianSign
import Wikipedia.NoExoticSixSphere.RankSixSpinorNullhomotopy
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# The first rank-six complex-structure homotopy group vanishes

Lift a loop to a closed unit-spinor path, contract it on the actual
seven-sphere, and reconstruct with its constant Pfaffian sign. The
contraction fixes the full boundary of the native one-cube.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix

theorem complexStructure_genLoop_one_nullhomotopic (J₀ : OrthogonalComplexStructures.Space 6)
    (p : GenLoop (Fin 1) (OrthogonalComplexStructures.Space 6) J₀) :
    GenLoop.Homotopic p GenLoop.const := by
  let J : C(I, OrthogonalComplexStructures.Space 6) :=
    ⟨fun t ↦ p (fun _ ↦ t), p.val.continuous.comp (continuous_pi fun _ ↦ continuous_id)⟩
  have hJ₀ : J 0 = J₀ := p.property _ ⟨0, Or.inl rfl⟩
  have hJ₁ : J 1 = J₀ := p.property _ ⟨0, Or.inr rfl⟩
  obtain ⟨q, hq, hclose⟩ := exists_closed_interval_unitSection J (hJ₁.trans hJ₀.symm)
  let Q : GenLoop (Fin 1) UnitSpinor (q 0) :=
    ⟨q.comp ⟨fun u ↦ u 0, continuous_apply 0⟩, by
      intro u hu
      change q (u 0) = q 0
      obtain ⟨i, hi⟩ := hu
      have he : i = 0 := Subsingleton.elim _ _
      rw [he] at hi
      rcases hi with hi | hi
      · rw [hi]
      · rw [hi, hclose]⟩
  have hJ (u : Fin 1 → I) : J (u 0) = p u := by
    change p (fun _ ↦ u 0) = p u
    apply congrArg p
    funext i
    exact congrArg u (Subsingleton.elim 0 i)
  have hQ (u : Fin 1 → I) : projection (p u) (Q u) = (Q u : Spinor) := by
    change projection (p u) (q (u 0)) = (q (u 0) : Spinor)
    rw [← hJ u]
    exact hq (u 0)
  have hp₀ : p 0 = J₀ := p.property 0 ⟨0, Or.inl rfl⟩
  let c : ℝ := -pfaffian (matrix J₀)
  have hc : c ^ 2 = 1 := by
    dsimp only [c]
    rw [neg_sq]
    exact pfaffian_sq_one _ (matrix_transpose _) (matrix_square _)
  let R : C(UnitSpinor, OrthogonalComplexStructures.Space 6) :=
    ⟨fun q ↦ signScale c hc (fromSpinor q),
      (continuous_signScale c hc).comp continuous_fromSpinor⟩
  have hR (u : Fin 1 → I) : R (Q u) = p u := by
    apply matrix_injective
    change matrix (signScale c hc (fromSpinor (Q u))) = matrix (p u)
    rw [matrix_signScale, fromSpinor_recovers_of_fixed (p u) (Q u) (hQ u)]
    have hs : pfaffian (matrix (p u)) = pfaffian (matrix J₀) :=
      (pfaffian_constant p.val u 0).trans (congrArg (fun K ↦ pfaffian (matrix K)) hp₀)
    rw [hs]
    change c • (c • matrix (p u)) = matrix (p u)
    rw [smul_smul, ← pow_two, hc, one_smul]
  have hR₀ : R (q 0) = J₀ := (hR 0).trans hp₀
  have hnull := genLoop_homotopic_const_of_homeomorph_sphere (by decide : 1 < 7)
    unitSpinorHomeomorph (q 0) Q
  have hh := HigherHomotopy.genLoopMap_homotopic R hR₀ hnull
  have hmap : HigherHomotopy.genLoopMap R hR₀ Q = p := by
    apply GenLoop.ext
    exact hR
  rw [hmap, HigherHomotopy.genLoopMap_const] at hh
  exact hh

theorem complexStructure_piOne_subsingleton (J₀ : OrthogonalComplexStructures.Space 6) :
    Subsingleton (HomotopyGroup (Fin 1) (OrthogonalComplexStructures.Space 6) J₀) := by
  refine ⟨fun a b ↦ Quotient.inductionOn₂ a b fun p q ↦ ?_⟩
  exact Quotient.sound ((complexStructure_genLoop_one_nullhomotopic J₀ p).trans
    (complexStructure_genLoop_one_nullhomotopic J₀ q).symm)

end NoExoticSixSphere.RankSixComplexProjection
