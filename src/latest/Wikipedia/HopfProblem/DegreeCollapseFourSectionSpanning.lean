import Wikipedia.HopfProblem.DegreeCollapseFiniteFourInclusion
import Wikipedia.HopfProblem.DegreeCollapseCanonicalMiddleMatrix

/-!
# The actual index-four sphere classes span below the original terminal cut

The actual critical enumeration determines the last below-cut point.
The final regular band identifies its sublevel homology with the original
cut sublevel. Vanishing there and the finite literal-inclusion kernel
formula prove spanning by the transported three-spheres themselves.
Their coordinate matrix is therefore surjective in the original H3 basis.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def canonicalFourMatrix {r n : ℕ} {a : ℝ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = a})) : Matrix (Fin r) (Fin n) ℤ :=
  classCoordinateMatrix B (fun j => threeSectionClass (γ j))

theorem four_section_classes_span_below_cut
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 3)]
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hwhich : ∀ i : Fin S.toSurgeryWindows.count,
      f (S.toSurgeryWindows.point i) < b ↔ i.val ≤ r + n)
    (hupperS : ∀ p : criticalPoints E f, f p < b → S.toSurgeryWindows.upper p < b)
    (hupperT : ∀ p : criticalPoints E f, f p < b → T.toSurgeryWindows.upper p < b)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 4)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hn <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = nativeMiddleBaseCut S r n hn}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexFourAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j) x).val =
        (γ j x).val) :
    Submodule.span ℤ (range (fun j => threeSectionClass (γ j))) = ⊤ := by
  let W := S.toSurgeryWindows
  let q : criticalPoints E f := W.point ⟨r + n, hn⟩
  let a := nativeMiddleCutSequence S T r n hn (Fin.last n)
  have hqb : f q < b := (hwhich ⟨r + n, hn⟩).mpr le_rfl
  have hqa : f q < a := by
    cases n with
    | zero => exact S.toSurgeryWindows.value_lt_upper q
    | succ n => exact T.toSurgeryWindows.value_lt_upper q
  have hab : a < b := by
    cases n with
    | zero => exact hupperS q hqb
    | succ n => exact hupperT q hqb
  have hband : ∀ y, f y ∈ Icc a b → y ∉ criticalPoints E f := by
    intro y hy hcrit
    have hyb : f y < b := lt_of_le_of_ne hy.2 (fun he => hb y he hcrit)
    obtain ⟨i, hi⟩ := W.point.surjective ⟨y, hcrit⟩
    have hib : f (W.point i) < b := by rw [hi]; exact hyb
    have hiq : i ≤ (⟨r + n, hn⟩ : Fin W.count) := (hwhich i).mp hib
    have hyq : f y ≤ f q := by simpa only [hi] using W.point_strictMono.monotone hiq
    exact (hyq.trans_lt hqa).not_ge hy.1
  let : Subsingleton (SingularHomology {y : M // f y ≤ a} 3) :=
    (regular_sublevel_inclusion_bijective hf hab.le hband 3).injective.subsingleton
  obtain ⟨h, _, hker⟩ := ordered_four_inclusion_relations S T hf r n hn hp hbefore γ horbit
  apply top_unique
  intro v hv
  rw [← hker]
  exact Subsingleton.elim _ _

theorem canonical_four_matrix_surjective_below_cut
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 3)]
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hwhich : ∀ i : Fin S.toSurgeryWindows.count,
      f (S.toSurgeryWindows.point i) < b ↔ i.val ≤ r + n)
    (hupperS : ∀ p : criticalPoints E f, f p < b → S.toSurgeryWindows.upper p < b)
    (hupperT : ∀ p : criticalPoints E f, f p < b → T.toSurgeryWindows.upper p < b)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 4)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hn <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology
      {y : M // f y ≤ nativeMiddleBaseCut S r n hn} 3)
    (γ : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = nativeMiddleBaseCut S r n hn}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexFourAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j) x).val =
        (γ j x).val) : Surjective (canonicalFourMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (four_section_classes_span_below_cut S T hf hb r n hn hwhich hupperS hupperT
      hp hbefore γ horbit)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
