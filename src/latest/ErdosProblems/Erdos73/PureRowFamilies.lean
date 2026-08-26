import ErdosProblems.Erdos73.HandleFamilySelection

/-! Ramsey selection of row-ordered pure families with all geometric data retained. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem exists_pure_row_ordered_selection (F : ColumnHandleFamily S col I)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (hrow : ∀ i, (F.sourceNail i).val.1.val < (F.targetNail i).val.1.val)
    (s : Finset I) (k : ℕ) (hsize : pureEndpointPairBound k ≤ s.card) :
    ∃ f : Fin k → I, Function.Injective f ∧ (∀ i, f i ∈ s) ∧
      StrictMono (fun i => (F.sourceNail (f i)).val.1.val) ∧
      ∃ shape : EndpointPairShape, ∀ i j, i < j →
        shape.Rel (F.sourceNail (f i)).val.1.val (F.targetNail (f i)).val.1.val
          (F.sourceNail (f j)).val.1.val (F.targetNail (f j)).val.1.val := by
  have hneq {i j : I} (hij : i ≠ j) :
      (F.sourceNail i).val.1.val ≠ (F.sourceNail j).val.1.val ∧
      (F.sourceNail i).val.1.val ≠ (F.targetNail j).val.1.val ∧
      (F.targetNail i).val.1.val ≠ (F.sourceNail j).val.1.val ∧
      (F.targetNail i).val.1.val ≠ (F.targetNail j).val.1.val :=
    ⟨F.endpoint_row_ne hdis hij false false, F.endpoint_row_ne hdis hij false true,
      F.endpoint_row_ne hdis hij true false, F.endpoint_row_ne hdis hij true true⟩
  obtain ⟨t, hts, htcard, shape, hshape⟩ := exists_pure_endpoint_pairs s
    (fun i => (F.sourceNail i).val.1.val) (fun i => (F.targetNail i).val.1.val)
    (fun i _ => hrow i) (fun _ _ _ _ hij => hneq hij) k hsize
  obtain ⟨f, hf, hft, hmono⟩ := exists_rank_ordered_selection t
    (fun i => (F.sourceNail i).val.1.val) (F.sourceRow_injective hdis).injOn k htcard
  exact ⟨f, hf, fun i => hts (hft i), hmono, shape,
    fun i j hij => hshape (hft i) (hft j) (hf.ne hij.ne)⟩

end
end Erdos73.ColumnHandleFamily
