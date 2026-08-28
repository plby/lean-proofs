import Wikipedia.HopfProblem.DegreeCollapseRegularCutMatrixTransport
import Wikipedia.HopfProblem.DegreeCollapseLastTwoPrimitiveCoordinate

/-!
# Put the entire middle family on the last index-two handle's actual belt level

The family construction has smaller windows than the chronological system.
The intervening band is regular by the original last index-two isolation.
Transport by the family's own flow therefore moves all actual sphere maps
to its native belt level, with the exact same matrix and a primitive
collapse coordinate belonging to that same field and surgery system.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem exists_native_belt_cut_family
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrpos : 0 < r) (hrc : r + n < S.toSurgeryWindows.count)
    (hradii : ∀ z, (T.data z).radius < (S.data z).radius) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let a := nativeMiddleBaseCut S r n hrc
    let p := nativeMiddleBlockPoint S r n hrc
    ∀ (hlower : ∀ j, a < T.toSurgeryWindows.lower (p j))
      (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
      (γ : Fin n → C(S₂, {y : M // f y = a})),
      IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
      Surjective (canonicalMiddleMatrix B γ).mulVec →
      ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2,
        Surjective ((T.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
        (∀ δ : C(Hemisphere.Sphere 1, (T.data q).LowerLevel),
          ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
        (∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 →
          f z < T.toSurgeryWindows.upper q) ∧
        (∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 → ∃ j, p j = z) ∧
        (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
        ∃ β : Fin n → C(S₂, (T.data q).UpperLevel),
          IsNativeMiddleBasinFamily T hf (T.data q).upper_regular p (fun j => β j) ∧
          (∀ j x, ∃ t : ℝ, T.flow t (γ j x).val = (β j x).val) ∧
          ∃ B' : (Fin r → ℤ) ≃ₗ[ℤ]
              SingularHomology {y : M // f y ≤ T.toSurgeryWindows.upper q} 2,
            canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ ∧
            Surjective (canonicalMiddleMatrix B' β).mulVec := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := nativeMiddleBaseCut S r n hrc
  let p := nativeMiddleBlockPoint S r n hrc
  dsimp only
  intro hlower B γ hγ hsurj
  have hrcT : r + n < T.toSurgeryWindows.count := hrc
  obtain ⟨hindex, hprimitive, hnull⟩ :=
    last_index_two_collapse_is_primitive T hf hdim horder hzero hone r n hr hrpos hrcT
  obtain ⟨hcomplete, hcut⟩ :=
    native_middle_block_complete_and_cut T hf hdim horder hzero hone r n hr hn hrcT
  have hba : T.toSurgeryWindows.upper q < a := by
    change f q + (T.data q).radius ^ 2 < f q + (S.data q).radius ^ 2
    have hh := hradii q
    nlinarith [(T.data q).radius_pos, (S.data q).radius_pos]
  have hband : ∀ y, f y ∈ Icc (T.toSurgeryWindows.upper q) a → y ∉ criticalPoints E f := by
    intro y hy hcrit
    have hqy : f q < f y := (T.toSurgeryWindows.value_lt_upper q).trans_le hy.1
    have heq : y = q.val := S.isolated q y hcrit
      ⟨((S.toSurgeryWindows.lower_lt_value q).trans hqy).le, hy.2⟩
    exact hqy.ne (congrArg f heq).symm
  have hnpos : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    obtain ⟨x, hx⟩ := hsurj 1
    have hh := congrFun hx ⟨0, hrpos⟩
    let _ : IsEmpty (Fin n) := ⟨fun j => by have hj := j.isLt; omega⟩
    simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, Pi.one_apply] at hh
    exact zero_ne_one hh
  let za := γ ⟨0, hnpos⟩ (Hemisphere.point true ⟨0, by simp⟩)
  obtain ⟨β, hβ, horbit, -, hmatrix, hsurj'⟩ := T.exists_lower_cut_geometric_matrix hf hba
    (S.data q).upper_regular (T.data q).upper_regular hband za p
      (fun j => (hlower j).trans (T.toSurgeryWindows.lower_lt_value (p j))) B γ hγ hsurj
  exact ⟨hindex, hprimitive, hnull, hcut, hcomplete, fun j => hba.trans (hlower j),
    β, hβ, horbit, B.trans (regularCutHomologyEquiv hf hba.le hband).symm, hmatrix, hsurj'⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
