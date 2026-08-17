import ErdosProblems.Erdos215.Global

/-!
# The outer well-founded recursion for Erdős Problem 215

This file packages the purely order-theoretic assembly of the birth blocks
used in `Global.BlockFamily`.  A stage constructor is allowed to inspect all
strictly earlier blocks together with proofs of all invariants already
established there.  The construction uses well-founded recursion and makes
no countability assumption about initial segments of the stage order.
-/

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace OuterRecursion

variable {I : Type} (r : I → I → Prop) [IsWellOrder I r]
    (layer : I → TerminalLayer) (Located : I → Point → Prop)

/-- The union of the blocks in a proof-indexed strict prefix. -/
def priorUnion (i : I) (prev : (j : I) → r j i → Set Point) : Set Point :=
  {x | ∃ (j : I) (hji : r j i), x ∈ prev j hji}

/-- All global invariants restricted to the strict prefix below `i`.

The proof arguments in `prev` are harmless: proof irrelevance makes the
chosen set independent of the particular proof of `r j i`.  Keeping them in
the type is what lets a `WellFounded.fix` body access exactly, and only, its
recursive predecessors. -/
structure PrefixGood (i : I) (prev : (j : I) → r j i → Set Point) : Prop where
  block_partial : ∀ j (hji : r j i), IsPartialSteinhaus (prev j hji)
  earlier_separated : ∀ j (hji : r j i) k (hki : r k i), r j k →
    ∀ x ∈ prev j hji, ∀ y ∈ prev k hki, Separated x y
  hits_up_to : ∀ j (hji : r j i), (layer j).Hits
    ({x | ∃ (k : I) (hkj : r k j),
      x ∈ prev k (IsTrans.trans k j i hkj hji)} ∪
      prev j hji)
  first_added_located : ∀ j (hji : r j i) x, x ∈ prev j hji → Located j x
  old_new_explained : ∀ j (hji : r j i) k (hki : r k i), r j k →
    ∀ x ∈ prev j hji, ∀ y ∈ prev k hki,
      RationalSqDist x y → (layer k).Explains x y

/-- The exact certificate returned by one outer stage. -/
structure StageFacts (i : I) (prev : (j : I) → r j i → Set Point)
    (newBlock : Set Point) : Prop where
  block_partial : IsPartialSteinhaus newBlock
  earlier_separated : ∀ j (hji : r j i),
    ∀ x ∈ prev j hji, ∀ y ∈ newBlock, Separated x y
  hits_up_to : (layer i).Hits (priorUnion r i prev ∪ newBlock)
  first_added_located : ∀ x, x ∈ newBlock → Located i x
  old_new_explained : ∀ j (hji : r j i),
    ∀ x ∈ prev j hji, ∀ y ∈ newBlock,
      RationalSqDist x y → (layer i).Explains x y

/-- The obligation discharged by the concrete terminal-layer construction.
It is only requested on prefixes which already carry all global invariants. -/
abbrev StageExtension : Prop :=
  ∀ (i : I) (prev : (j : I) → r j i → Set Point),
    PrefixGood r layer Located i prev →
      ∃ newBlock : Set Point, StageFacts r layer Located i prev newBlock

variable (extend : StageExtension r layer Located)

private noncomputable def nextBlock (i : I)
    (prev : (j : I) → r j i → Set Point) : Set Point := by
  classical
  exact if h : PrefixGood r layer Located i prev then
    Classical.choose (extend i prev h)
  else ∅

private theorem nextBlock_stageFacts (i : I)
    (prev : (j : I) → r j i → Set Point)
    (hgood : PrefixGood r layer Located i prev) :
    StageFacts r layer Located i prev
      (nextBlock r layer Located extend i prev) := by
  rw [nextBlock, dif_pos hgood]
  exact Classical.choose_spec (extend i prev hgood)

/-- Birth blocks selected by well-founded recursion.  The empty fallback is
never used: `blocks_prefixGood` proves inductively that the recursive prefix
always satisfies the stage constructor's premise. -/
noncomputable def blocks : I → Set Point :=
  WellFounded.fix (IsWellFounded.wf : WellFounded r) fun i rec ↦
    nextBlock r layer Located extend i rec

private theorem blocks_stageFacts_of_prefixGood (i : I)
    (hgood : PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)) :
    StageFacts r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)
      (blocks (r := r) (layer := layer) (Located := Located) extend i) := by
  have hunfold :
      blocks (r := r) (layer := layer) (Located := Located) extend i =
        nextBlock r layer Located extend i
          (fun j (_ : r j i) ↦
            blocks (r := r) (layer := layer) (Located := Located) extend j) := by
    unfold blocks
    rw [WellFounded.fix_eq]
  rw [hunfold]
  exact nextBlock_stageFacts r layer Located extend i _ hgood

/-- Every recursive prefix is good.  This is the induction which guarantees
that the fallback branch in `blocks` is unreachable. -/
theorem blocks_prefixGood (i : I) :
    PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j) := by
  refine @IsWellFounded.induction I r _
    (fun i ↦ PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)) i ?_
  intro i ih
  let facts : ∀ j (hji : r j i),
      StageFacts r layer Located j
        (fun k (_ : r k j) ↦
          blocks (r := r) (layer := layer) (Located := Located) extend k)
        (blocks (r := r) (layer := layer) (Located := Located) extend j) :=
    fun j hji ↦
      blocks_stageFacts_of_prefixGood r layer Located extend j (ih j hji)
  refine
    { block_partial := ?_
      earlier_separated := ?_
      hits_up_to := ?_
      first_added_located := ?_
      old_new_explained := ?_ }
  · intro j hji
    exact (facts j hji).block_partial
  · intro j hji k hki hjk x hx y hy
    exact (facts k hki).earlier_separated j hjk x hx y hy
  · intro j hji
    exact (facts j hji).hits_up_to
  · intro j hji x hx
    exact (facts j hji).first_added_located x hx
  · intro j hji k hki hjk x hx y hy hr
    exact (facts k hki).old_new_explained j hjk x hx y hy hr

/-- The selected block at every stage satisfies its exact stage certificate. -/
theorem blocks_stageFacts (i : I) :
    StageFacts r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)
      (blocks (r := r) (layer := layer) (Located := Located) extend i) :=
  blocks_stageFacts_of_prefixGood r layer Located extend i
    (blocks_prefixGood (r := r) (layer := layer) (Located := Located) extend i)

include Located extend

/-- Generic outer-recursion theorem.  It assembles an exact
`Global.BlockFamily` from the one-stage extension hypothesis, without any
countability requirement on `I` or its initial segments. -/
theorem exists_blockFamily :
    Nonempty (BlockFamily I r layer) := by
  let B : I → Set Point :=
    blocks (r := r) (layer := layer) (Located := Located) extend
  refine ⟨
    { block := B
      block_partial := fun i ↦
        (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend i).block_partial
      earlier_separated := ?_
      hits_up_to := ?_
      located := Located
      first_added_located := ?_
      old_new_explained := ?_ }⟩
  · intro i j hij x hx y hy
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend j).earlier_separated i hij x hx y hy
  · intro i n hn K hK
    obtain ⟨p, hp, hpK⟩ :=
      (blocks_stageFacts (r := r) (layer := layer)
        (Located := Located) extend i).hits_up_to n hn K hK
    refine ⟨p, ?_, hpK⟩
    rcases hp with hp | hp
    · rcases hp with ⟨j, hji, hpj⟩
      exact Or.inl ⟨j, hji, hpj⟩
    · exact Or.inr hp
  · intro i x hx
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend i).first_added_located x hx
  · intro i j hij x hx y hy hr
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend j).old_new_explained i hij x hx y hy hr

end OuterRecursion
end Global

end

end Erdos215
