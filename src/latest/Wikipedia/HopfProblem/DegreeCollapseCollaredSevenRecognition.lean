import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFreeIteration
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenReversal
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenSmoothRecognition

/-!

# Smooth recognition of a supplied collared state without finite third homology

Remove all free H3 summands by actual positive surgeries. Reverse the
actual regular time and remove the free summands of the opposite half;
the first cleared half is unchanged by the second sequence. The genuine
Mayer--Vietoris sum gives finite ambient H3. Compose both native boundary
surgery identifications and the actual time-reversal identification with
the proved finite-homology recognition theorem.

No finite-H3 hypothesis remains. The initial compact framed collared state,
including its simple connectivity and zero H2, is still required data.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B]

theorem exists_finite_ambient_after_both_halves (S : CollaredSevenState B)
    [SimplyConnectedSpace B]
    [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
    [Subsingleton (SingularHomology B 4)] :
    ∃ U V : CollaredSevenState B, S.Reachable U ∧ U.reverse.Reachable V ∧
      Finite (SingularHomology V.Space 3) := by
  obtain ⟨U, hSU, hU⟩ := S.exists_finite_half
  let : Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p => -U.reverse.time p)) 3) := by
    change Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p : U.Space => - -U.time p)) 3)
    let _ : Finite (SingularHomology {p : U.Space // 0 ≤ U.time p} 3) := hU
    let E := Homeomorph.setCongr
      (show {p : U.Space | 0 ≤ - -U.time p} = {p : U.Space | 0 ≤ U.time p} by
        ext p
        change 0 ≤ - -U.time p ↔ 0 ≤ U.time p
        rw [neg_neg])
    exact @Finite.of_injective _ _ hU _ (homeomorphHomologyEquiv E 3).injective
  obtain ⟨V, hUV, hV⟩ := U.reverse.exists_finite_half
  let _ : Finite (SingularHomology (TimeCollar.NonnegativeHalf V.time) 3) := hV
  let _ : Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p => -V.time p)) 3) :=
    hUV.negative_half_homology_finite 3
  exact ⟨U, V, hSU, hUV, Finite.of_surjective _ (V.collar.halvesHomologySum_bijective 2).2⟩

theorem nonempty_zero_sphere_diffeomorph (S : CollaredSevenState B)
    (eBoundary : B ≃ₜ Sphere 6) :
    letI := S.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let _ : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  have hB (j : ℕ) (hj : j ≠ 0) (h6 : j ≠ 6) : Subsingleton (SingularHomology B j) := by
    let : Subsingleton (SingularHomology (Sphere 6) j) :=
      SphereHomology.unitSphere_homology_subsingleton 5 j hj h6
    exact (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv j).injective.subsingleton
  let _ := hB 2 (by decide) (by decide)
  let _ := hB 3 (by decide) (by decide)
  let _ := hB 4 (by decide) (by decide)
  obtain ⟨U, V, hSU, hUV, hV⟩ := S.exists_finite_ambient_after_both_halves
  let _ := hV
  let _ := S.zeroAtlas
  let _ := U.zeroAtlas
  let _ := U.reverse.zeroAtlas
  let _ := V.zeroAtlas
  obtain ⟨D⟩ := hSU.zero_diffeomorphic
  obtain ⟨E⟩ := hUV.zero_diffeomorphic
  obtain ⟨F⟩ := V.nonempty_zero_sphere_diffeomorph_of_finite_third eBoundary
  exact ⟨D.trans (U.reverseZeroDiffeomorph.trans (E.trans F))⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
