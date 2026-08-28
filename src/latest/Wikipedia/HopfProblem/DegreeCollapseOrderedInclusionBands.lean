import Wikipedia.HopfProblem.DegreeCollapseFiniteMiddleInclusion

/-!
# Construct every regular band in the original chronological middle block

The common cut comes from the original surgery system. Later cuts use
the actual new flow's upper windows. The original critical enumeration
and separated windows prove all regular-band hypotheses of the finite
inclusion induction, without identifying any chosen ambient band maps.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def nativeMiddleBaseCut (S : AdaptedSurgeryWindows E f) (r n : ℕ)
    (hn : r + n < S.toSurgeryWindows.count) : ℝ :=
  S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r, by omega⟩)

def nativeMiddleCutSequence (S T : AdaptedSurgeryWindows E f) (r n : ℕ)
    (hn : r + n < S.toSurgeryWindows.count) : Fin (n + 1) → ℝ :=
  Fin.cases (nativeMiddleBaseCut S r n hn)
    (fun j => T.toSurgeryWindows.upper (nativeMiddleBlockPoint S r n hn j))

theorem nativeMiddleCutSequence_bands
    (S T : AdaptedSurgeryWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hn <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j)) :
    let p := nativeMiddleBlockPoint S r n hn
    let cut := nativeMiddleCutSequence S T r n hn
    (∀ i, cut 0 ≤ cut i) ∧
      (∀ j, cut j.succ = T.toSurgeryWindows.upper (p j)) ∧
      (∀ j, cut j.castSucc < T.toSurgeryWindows.lower (p j)) ∧
      ∀ j y, f y ∈ Icc (cut j.castSucc) (T.toSurgeryWindows.lower (p j)) →
        y ∉ criticalPoints E f := by
  let p := nativeMiddleBlockPoint S r n hn
  let cut := nativeMiddleCutSequence S T r n hn
  have hbase (i : Fin (n + 1)) : cut 0 ≤ cut i := by
    cases i using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact ((hbefore j).trans
        ((T.toSurgeryWindows.lower_lt_value (p j)).trans
          (T.toSurgeryWindows.value_lt_upper (p j)))).le
  have hstep (j : Fin n) : cut j.castSucc < T.toSurgeryWindows.lower (p j) := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact hbefore 0
      | succ j =>
        change T.toSurgeryWindows.upper (p j.castSucc) < T.toSurgeryWindows.lower (p j.succ)
        apply T.separated
        apply S.toSurgeryWindows.point_strictMono
        change r + j.val + 1 < r + (j.val + 1) + 1
        omega
  have hpred (j : Fin n) :
      f (S.toSurgeryWindows.point ⟨r + j.val, by omega⟩) < cut j.castSucc := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact S.toSurgeryWindows.value_lt_upper _
      | succ j => exact T.toSurgeryWindows.value_lt_upper (p j.castSucc)
  refine ⟨hbase, fun _ => rfl, hstep, ?_⟩
  intro j y hy hcrit
  have hconsecutive := S.toSurgeryWindows.point_consecutive
    ⟨r + j.val, by omega⟩ ⟨r + j.val + 1, by omega⟩ rfl
  exact hconsecutive ⟨y, hcrit⟩ ⟨(hpred j).trans_le hy.1,
    hy.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p j))⟩

theorem ordered_middle_inclusion_relations
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 3)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hn <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C(S₂, {y : M // f y = nativeMiddleBaseCut S r n hn}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j) x).val =
        (γ j x).val) :
    ∃ h : nativeMiddleBaseCut S r n hn ≤ nativeMiddleCutSequence S T r n hn (Fin.last n),
      Surjective (singularHomologyMap (sublevelMap f h) 2) ∧
        LinearMap.ker (singularHomologyMap (sublevelMap f h) 2) =
          Submodule.span ℤ (range (fun j => middleSectionClass (γ j))) := by
  obtain ⟨hbase, hnext, hlower, hband⟩ := nativeMiddleCutSequence_bands S T r n hn hbefore
  refine ⟨hbase (Fin.last n), ?_⟩
  exact T.finite_middle_inclusion_relations hf n (nativeMiddleBlockPoint S r n hn) hp
    (nativeMiddleCutSequence S T r n hn) (S.data (S.toSurgeryWindows.point ⟨r, by omega⟩)).upper_regular
    hbase hnext hlower hband γ horbit

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
