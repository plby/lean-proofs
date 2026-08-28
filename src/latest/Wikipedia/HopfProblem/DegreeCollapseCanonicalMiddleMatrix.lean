import Wikipedia.HopfProblem.DegreeCollapseMiddleClassSpanning

/-!
# The matrix of the actual canonical section classes is surjective

Its entries are the coordinates of the geometric sphere classes in the
given free basis of the common sublevel. Matrix multiplication maps back
to their actual integral linear combination. The native finite spanning
theorem therefore proves surjectivity of this specific matrix.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

def classCoordinateMatrix {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ :=
  fun i j => B.symm (v j) i

theorem classCoordinateMatrix_mulVec {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) (z : Fin n → ℤ) :
    B ((classCoordinateMatrix B v).mulVec z) = ∑ j, z j • v j := by
  have hvec : (classCoordinateMatrix B v).mulVec z = ∑ j, z j • B.symm (v j) := by
    funext i
    simp [classCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, LinearEquiv.apply_symm_apply]

theorem classCoordinateMatrix_surjective {A : Type} [AddCommGroup A] [hA : Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A)
    (hspan : Submodule.span ℤ (range v) = ⊤) :
    Surjective (classCoordinateMatrix B v).mulVec := by
  intro w
  have hw : B w ∈ Submodule.span ℤ (range v) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  refine ⟨z, B.injective ?_⟩
  rw [classCoordinateMatrix_mulVec]
  have hsum : (∑ j, z j • v j) = ∑ j, hA.smul (z j) (v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (int_smul_eq_zsmul hA (z j) (v j)).symm
  exact hsum.trans hz

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

def canonicalMiddleMatrix {r n : ℕ} {a : ℝ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a})) : Matrix (Fin r) (Fin n) ℤ :=
  classCoordinateMatrix B (fun j => middleSectionClass (γ j))

theorem canonical_middle_matrix_surjective
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hrc <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology
      {y : M // f y ≤ nativeMiddleBaseCut S r n hrc} 2)
    (γ : Fin n → C(S₂, {y : M // f y = nativeMiddleBaseCut S r n hrc}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j) x).val =
        (γ j x).val) : Surjective (canonicalMiddleMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (middle_section_classes_span S T hf hdim e horder hzero hone r n hr hn hrc hp hbefore γ horbit)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
