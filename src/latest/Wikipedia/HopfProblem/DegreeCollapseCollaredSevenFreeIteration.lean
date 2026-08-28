import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFreeReduction
import Wikipedia.HopfProblem.DegreeCollapseFiniteFreeSplitting

/-!

# Actual finite surgery removes all free positive-half third homology

Finite generation follows from the original compact smooth manifold and
the genuine collar inclusion. Decompose its positive-half H3 into a finite
free product, realize each primitive coordinate by an actual surgery, and
induct on the number of integer factors. The endpoint has finite H3.
The actual unchanged negative half also retains any supplied finite homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open SingularMayerVietoris SevenSurgery.FramedAttachingProduct.UnitSurgery

variable {B : Type} [TopologicalSpace B]

theorem Step.negative_half_homology_finite {S U : CollaredSevenState B}
    (h : S.Step U) (k : ℕ)
    [Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p => -S.time p)) k)] :
    Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p => -U.time p)) k) := by
  obtain ⟨f, A, hA, T, hT, rfl⟩ := h
  let : Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p => -T.time p)) k) := by
    rw [hT]
    infer_instance
  exact negativeHalf_homology_finite A hA T k

theorem Reachable.negative_half_homology_finite {S U : CollaredSevenState B}
    (h : S.Reachable U) (k : ℕ)
    [Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p => -S.time p)) k)] :
    Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p => -U.time p)) k) := by
  induction h with
  | refl => infer_instance
  | @tail U V hSU hUV ih =>
    let _ := ih
    exact hUV.negative_half_homology_finite k

variable [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

theorem exists_finite_half_from_free_product (n : ℕ) {T : Type} [AddCommGroup T] [Finite T]
    (S : CollaredSevenState B)
    (e : SingularHomology (TimeCollar.NonnegativeHalf S.time) 3 ≃+ (Fin n → ℤ) × T) :
    ∃ U : CollaredSevenState B, S.Reachable U ∧
      Finite (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3) := by
  induction n generalizing S with
  | zero =>
    exact ⟨S, Relation.ReflTransGen.refl, Finite.of_injective e e.injective⟩
  | succ n ih =>
    obtain ⟨σ, c, hc, ⟨E⟩⟩ :=
      IntegerSplit.exists_primitive_coordinate_with_smaller_free_product e
    obtain ⟨U, hSU, ⟨F⟩⟩ := S.successor_of_primitive_coordinate σ c hc
    obtain ⟨V, hUV, hV⟩ := ih U (F.trans E)
    exact ⟨V, (Relation.ReflTransGen.single hSU).trans hUV, hV⟩

theorem exists_finite_half (S : CollaredSevenState B) :
    ∃ U : CollaredSevenState B, S.Reachable U ∧
      Finite (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3) := by
  let _ : AddGroup.FG (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3) := by
    apply Module.Finite.iff_addGroup_fg.mp
    convert! S.half_third_homology_finitely_generated using 1
    exact Subsingleton.elim _ _
  obtain ⟨n, T, hT, hfinite, ⟨e⟩⟩ :=
    IntegerSplit.exists_finite_free_product (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3)
  let _ := hT
  let _ := hfinite
  exact exists_finite_half_from_free_product n S e

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
