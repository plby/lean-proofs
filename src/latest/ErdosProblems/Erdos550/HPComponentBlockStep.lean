import Mathlib
import ErdosProblems.Erdos550.HPRestrictedPairEmbedding
import ErdosProblems.Erdos550.ParityContactColor
import ErdosProblems.Erdos550.RootedComponentLocal

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# One parity-refined component block

This is the local graph-theoretic extension used by the stateful matching
algorithm.  The component is rebased so its root has local colour `false` and
is embedded on the selected root endpoint.  Every vertex which is the parent
of a deferred boundary seed has that same local colour, hence also lands in
the retained root-side pool.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

theorem hp_component_block_step
    (T : SimpleGraph A) (Sseed : Finset A)
    {parent : A → Option A} {rank : A → ℕ}
    (D : RootedSeedComponentData T Sseed parent)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : NonseedComponent T Sseed)
    (hboundary : ∀ a ∈ componentSeeds T Sseed c.1,
      ∀ b ∈ componentSeeds T Sseed c.1, col a = col b)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    {rootSide otherSide freeRoot freeOther rootPool : Finset V}
    (hrootSide : rootSide.Nonempty) (hotherSide : otherSide.Nonempty)
    (huni : G.IsUniform ε rootSide otherSide)
    (hdens : d ≤ (G.edgeDensity rootSide otherSide : ℝ))
    (hfreeRoot : freeRoot ⊆ rootSide)
    (hfreeOther : freeOther ⊆ otherSide)
    (hrootPool : rootPool ⊆ freeRoot)
    (anchor : V)
    (hrootAdj : ∀ v ∈ rootPool, G.Adj anchor v)
    (L : ℕ)
    (hLfree : L ≤ freeRoot.card)
    (hOfree : L ≤ freeOther.card)
    (hrootCard : L ≤ rootPool.card)
    (hLsig : ε * (rootSide.card : ℝ) ≤ (L : ℝ))
    (hOsig : ε * (otherSide.card : ℝ) ≤ (L : ℝ))
    (hroom :
      ε * (max rootSide.card otherSide.card : ℝ) +
          (Fintype.card (RootedComponentVertex T Sseed c) : ℝ)
        ≤ (d - 2 * ε) * (L : ℝ)) :
    ∃ f : RootedComponentVertex T Sseed c → V,
      Function.Injective f ∧
      G.Adj anchor (f (componentLocalRoot T Sseed D c)) ∧
      (∀ x, f x ∈
        (if relativeComponentColor col (D.root c) x.1
          then freeOther else freeRoot)) ∧
      (∀ x y, componentLocalParent T Sseed D c x = some y →
        G.Adj (f x) (f y)) ∧
      (∀ s ∈ componentSeeds T Sseed c.1,
        ∀ x : RootedComponentVertex T Sseed c,
          parent s = some x.1 → f x ∈ freeRoot) := by
  let localParent := componentLocalParent T Sseed D c
  let localRank : RootedComponentVertex T Sseed c → ℕ :=
    fun x => rank x.1
  let localRoot := componentLocalRoot T Sseed D c
  let localCol : RootedComponentVertex T Sseed c → Bool :=
    fun x => relativeComponentColor col (D.root c) x.1
  have hlocalRank : ∀ x y, localParent x = some y →
      localRank y < localRank x := by
    intro x y hxy
    exact componentLocalParent_rank T Sseed D rank hrank c hxy
  have hlocalRoot : localParent localRoot = none := by
    exact componentLocalParent_root T Sseed D c
  have hlocalUnique : ∀ x, localParent x = none → x = localRoot := by
    intro x hx
    exact componentLocalParent_none_unique T Sseed D c x hx
  have hlocalRootCol : localCol localRoot = false := by
    simp [localCol, localRoot, componentLocalRoot]
  have hlocalCol : ∀ x y, localParent x = some y →
      localCol x ≠ localCol y := by
    intro x y hxy
    apply relativeComponentColor_parent col (D.root c) hcol
    exact componentLocalParent_some_global T Sseed D c hxy
  obtain ⟨f, hfinj, hfroot, hfside, hfadj⟩ :=
    hp_restricted_pair_step_left G hε0 hε1 hd1
      hrootSide hotherSide huni hdens
      hfreeRoot hfreeOther hrootPool
      L hLfree hOfree hrootCard hLsig hOsig
      localParent localRank hlocalRank localRoot hlocalRoot
      hlocalUnique localCol hlocalRootCol hlocalCol hroom
  refine ⟨f, hfinj, hrootAdj _ hfroot, hfside, hfadj, ?_⟩
  intro s hs x hsx
  have hxColour :
      col x.1 = col (D.root c) :=
    component_contact_colour_eq_root T Sseed D hparentAdj col hcol
      c hboundary hs x.2 hsx
  have hxLocal : localCol x = false := by
    simp [localCol, relativeComponentColor, hxColour]
  simpa [hxLocal] using! hfside x

end Erdos550
