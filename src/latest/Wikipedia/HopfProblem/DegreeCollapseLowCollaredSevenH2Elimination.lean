import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenH2Successor
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenFiniteHomology

/-!

# Finite native surgery eliminates the actual positive half's H2

Choose finitely many generators from native compact Morse theory and the
actual collar inclusion. Kill the first by a constructed positive framed
two-sphere surgery. Surjectivity and the exact kernel show that the images
of the remaining generators span the next half. Induction gives a finite
actual surgery path with zero H2, retaining simple connectivity and the
original zero-boundary smooth structure. No finite-H2-cardinality assumption,
primitivity condition or supplied sequence is used.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open SingularMayerVietoris

theorem span_tail_of_surjective_killing_first {G H : Type*}
    [AddCommGroup G] [Module ℤ G] [AddCommGroup H] [Module ℤ H]
    {n : ℕ} (g : Fin (n + 1) → G) (hg : Submodule.span ℤ (range g) = ⊤)
    (φ : G →ₗ[ℤ] H) (hφ : Surjective φ) (hk : φ (g 0) = 0) :
    Submodule.span ℤ (range (fun i : Fin n ↦ φ (g i.succ))) = ⊤ := by
  let K : Submodule ℤ H := Submodule.span ℤ (range (fun i : Fin n ↦ φ (g i.succ)))
  have hall : ∀ i, φ (g i) ∈ K := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [hk]
      exact K.zero_mem
    · exact Submodule.subset_span (mem_range_self j)
  have hle : Submodule.span ℤ (range g) ≤ K.comap φ := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hall i
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨x, rfl⟩ := hφ y
  exact hle (by rw [hg]; trivial)

variable {B : Type} [TopologicalSpace B]

theorem exists_h2_zero_of_generators (n : ℕ) :
    ∀ (S : LowCollaredSevenState B), SimplyConnectedSpace S.PositiveHalf →
      ∀ g : Fin n → SingularHomology S.PositiveHalf 2,
        Submodule.span ℤ (range g) = ⊤ →
          ∃ U : LowCollaredSevenState B, S.Reachable U ∧
            SimplyConnectedSpace U.PositiveHalf ∧
              Subsingleton (SingularHomology U.PositiveHalf 2) := by
  induction n with
  | zero =>
    intro S hS g hg
    have hr : range g = ∅ := by ext x; simp
    have hz : (⊥ : Submodule ℤ (SingularHomology S.PositiveHalf 2)) = ⊤ := by
      simpa only [hr, Submodule.span_empty] using hg
    have hzero (x : SingularHomology S.PositiveHalf 2) : x = 0 := by
      have hx : x ∈ (⊥ : Submodule ℤ (SingularHomology S.PositiveHalf 2)) := by
        rw [hz]
        trivial
      simpa using hx
    exact ⟨S, Relation.ReflTransGen.refl, hS, ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩⟩
  | succ n ih =>
    intro S hS g hg
    let := hS
    obtain ⟨U, hSU, hU, φ, hφ, hker⟩ := S.exists_h2_killing_step (g 0)
    have hk : φ (g 0) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact Submodule.subset_span (mem_singleton _)
    have hspan := span_tail_of_surjective_killing_first g hg φ hφ hk
    obtain ⟨V, hUV, hV, hzero⟩ := ih U hU (fun i : Fin n ↦ φ (g i.succ)) hspan
    exact ⟨V, (Relation.ReflTransGen.single hSU).trans hUV, hV, hzero⟩

theorem exists_h2_zero (S : LowCollaredSevenState B) [SimplyConnectedSpace S.PositiveHalf]
    [Subsingleton (SingularHomology B 2)] :
    ∃ U : LowCollaredSevenState B, S.Reachable U ∧
      SimplyConnectedSpace U.PositiveHalf ∧ Subsingleton (SingularHomology U.PositiveHalf 2) := by
  let : Module.Finite ℤ (SingularHomology S.PositiveHalf 2) :=
    S.half_secondHomology_finitely_generated
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin
    (R := ℤ) (M := SingularHomology S.PositiveHalf 2)
  exact exists_h2_zero_of_generators n S inferInstance g hg

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
