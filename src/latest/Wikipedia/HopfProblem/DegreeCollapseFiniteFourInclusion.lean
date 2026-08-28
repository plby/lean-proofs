import Wikipedia.HopfProblem.DegreeCollapseOrderedInclusionBands
import Wikipedia.HopfProblem.DegreeCollapseIndexFourInclusionStep

/-!
# The finite index-four inclusion kernel is spanned by the actual sphere classes

Induct through the actual regular bands and native four-handle windows.
Every map is the literal sublevel inclusion. Its final kernel is exactly
the span of the given transported attaching three-spheres. The actual
chronological block supplies all regular-band hypotheses independently
of any chosen ambient band homeomorphism or arbitrary relation lifts.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.finite_four_inclusion_relations
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n : ℕ) (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4) (cut : Fin (n + 1) → ℝ)
    (ha : ∀ y, f y = cut 0 → y ∉ criticalPoints E f)
    (hbase : ∀ i, cut 0 ≤ cut i)
    (hnext : ∀ j, cut j.succ = S.toSurgeryWindows.upper (p j))
    (hlower : ∀ j, cut j.castSucc < S.toSurgeryWindows.lower (p j))
    (hband : ∀ j y, f y ∈ Icc (cut j.castSucc) (S.toSurgeryWindows.lower (p j)) →
      y ∉ criticalPoints E f)
    (γ : Fin n → C(S₃, {y : M // f y = cut 0}))
    (horbit : ∀ j x, ∃ t : ℝ,
      S.flow t (nativeIndexFourAttachingSphere S (p j) (hp j) x).val = (γ j x).val) :
    Surjective (singularHomologyMap (sublevelMap f (hbase (Fin.last n))) 3) ∧
      LinearMap.ker (singularHomologyMap (sublevelMap f (hbase (Fin.last n))) 3) =
        Submodule.span ℤ (range (fun j => threeSectionClass (γ j))) := by
  have hprefix (k : ℕ) : ∀ hk : k ≤ n,
      Surjective (singularHomologyMap (sublevelMap f (hbase ⟨k, by omega⟩)) 3) ∧
        LinearMap.ker (singularHomologyMap (sublevelMap f (hbase ⟨k, by omega⟩)) 3) =
          Submodule.span ℤ (range (fun j : Fin k =>
            threeSectionClass (γ ⟨j.val, j.isLt.trans_le hk⟩))) := by
    induction k with
    | zero =>
      intro hk
      have hid : singularHomologyMap (sublevelMap f (hbase ⟨0, by omega⟩)) 3 =
          LinearMap.id := by
        change singularHomologyMap (ContinuousMap.id {y : M // f y ≤ cut 0}) 3 = _
        exact singularHomologyMap_id _ _
      constructor
      · rw [hid]
        exact Function.surjective_id
      · rw [hid]
        simp only [Fin.zero_eta, Matrix.range_empty, Submodule.span_empty]
        ext v
        rfl
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      let j : Fin n := ⟨k, hkn⟩
      obtain ⟨hprev, hkernel⟩ := ih (by omega)
      have hstep := S.index_four_inclusion_step hf (p j) (hp j) (hbase j.castSucc) ha
        (hlower j) (hband j) (γ j) (horbit j) hprev
      have hstep' :
          Surjective (singularHomologyMap (sublevelMap f (hbase ⟨k + 1, by omega⟩)) 3) ∧
          LinearMap.ker (singularHomologyMap (sublevelMap f (hbase ⟨k + 1, by omega⟩)) 3) =
            LinearMap.ker (singularHomologyMap (sublevelMap f (hbase j.castSucc)) 3) ⊔
              Submodule.span ℤ {threeSectionClass (γ j)} := by
        have heq : cut ⟨k + 1, by omega⟩ = S.toSurgeryWindows.upper (p j) := hnext j
        have aux (b : ℝ) (hb : cut 0 ≤ b) (he : b = S.toSurgeryWindows.upper (p j)) :
            Surjective (singularHomologyMap (sublevelMap f hb) 3) ∧
              LinearMap.ker (singularHomologyMap (sublevelMap f hb) 3) =
                LinearMap.ker (singularHomologyMap (sublevelMap f (hbase j.castSucc)) 3) ⊔
                  Submodule.span ℤ {threeSectionClass (γ j)} := by
          subst b
          exact hstep
        exact aux _ _ heq
      refine ⟨hstep'.1, ?_⟩
      rw [hstep'.2, hkernel]
      exact span_prefix_succ (fun i => threeSectionClass (γ i)) hkn
  simpa only using hprefix n le_rfl

theorem ordered_four_inclusion_relations
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 4)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hn <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C(S₃, {y : M // f y = nativeMiddleBaseCut S r n hn}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexFourAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j) x).val =
        (γ j x).val) :
    ∃ h : nativeMiddleBaseCut S r n hn ≤ nativeMiddleCutSequence S T r n hn (Fin.last n),
      Surjective (singularHomologyMap (sublevelMap f h) 3) ∧
        LinearMap.ker (singularHomologyMap (sublevelMap f h) 3) =
          Submodule.span ℤ (range (fun j => threeSectionClass (γ j))) := by
  obtain ⟨hbase, hnext, hlower, hband⟩ := nativeMiddleCutSequence_bands S T r n hn hbefore
  refine ⟨hbase (Fin.last n), ?_⟩
  exact T.finite_four_inclusion_relations hf n (nativeMiddleBlockPoint S r n hn) hp
    (nativeMiddleCutSequence S T r n hn)
    (S.data (S.toSurgeryWindows.point ⟨r, by omega⟩)).upper_regular
    hbase hnext hlower hband γ horbit


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
