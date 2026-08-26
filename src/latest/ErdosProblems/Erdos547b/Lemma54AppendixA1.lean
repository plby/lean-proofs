/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma51DynamicRootPool
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest
import Mathlib.Tactic

/-!
# Zhao Appendix Corollary A.1: adaptive regular-pair realization

This file implements the graph-realization half of Corollary A.1.  The
orientation is fixed.  At every step the exact image of the preceding trees
is deleted from the two live endpoint sets and from the two live root
reservoirs.  On a physical side `c`, nonroot vertices use

* `live c \ roots c` when that complement has cardinality at least `gamma*N`;
* all of `live c` otherwise.

The second case is safe because the side-capacity inequality then forces the
live root reservoir itself to have more than `3*epsilon*N` vertices.  Once a
complement becomes small it remains small after further deletions.  Before
that happens, nonroots avoid the root reservoir, so the exact root-count
capacity is preserved.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma54AppendixA1

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma51DynamicRootPool
open Erdos547b.ZhaoLemma58GroupedSmallForest

universe v

/-! ## Source root counts and their tail identities -/

/-- Number of component roots assigned to physical side `c`. -/
def rootSideLoad {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) : ℕ :=
  #((Finset.univ : Finset (Fin b)).filter fun i ↦
    branchRootSide F orient i = c)

theorem one_le_rootSideLoad_head {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) :
    1 ≤ rootSideLoad F orient (branchRootSide F orient 0) := by
  apply Finset.one_le_card.mpr
  exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem rootSideLoad_tail_add_head {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) (c : Fin 2) :
    rootSideLoad F.tail (tailOrient orient) c +
        (if branchRootSide F orient 0 = c then 1 else 0) =
      rootSideLoad F orient c := by
  classical
  unfold rootSideLoad
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [branchRootSide, tailOrient]
  exact Nat.add_comm _ _

theorem rootSideLoad_le_sideLoad {b : ℕ}
    (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) :
    rootSideLoad F orient c ≤ sideLoad F orient c := by
  classical
  unfold rootSideLoad sideLoad
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : branchRootSide F orient i = c
  · simp only [hi, if_pos]
    subst c
    exact one_le_orientedClassSize_root F orient i
  · simp [hi]

/-! ## Adaptive live-state invariant -/

/-- The nonroot candidate used on one physical side at the current step. -/
def adaptiveInterior {B : Type v} [DecidableEq B]
    (gamma N : ℝ) (live roots : Fin 2 → Finset B) (c : Fin 2) : Finset B :=
  if gamma * N ≤ (#(live c \ roots c) : ℝ) then
    live c \ roots c
  else
    live c

theorem adaptiveInterior_subset_live
    {B : Type v} [DecidableEq B]
    (gamma N : ℝ) (live roots : Fin 2 → Finset B) (c : Fin 2) :
    adaptiveInterior gamma N live roots c ⊆ live c := by
  classical
  unfold adaptiveInterior
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.rfl

/-- The exact invariant propagated by the Appendix-A.1 recursion.

The disjunction in `root_or_small` records the two phases of the proof.  In
the first phase the root reservoir has only lost preceding roots.  In the
second phase the complement is small; this remains true forever and the side
capacity itself supplies the root reservoir. -/
structure AppendixLiveCapacity {b : ℕ} {B : Type v} [DecidableEq B]
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (live roots : Fin 2 → Finset B)
    (gamma epsilon N : ℝ) : Prop where
  roots_subset : ∀ c, roots c ⊆ live c
  side_capacity : ∀ c,
    (sideLoad F orient c : ℝ) + (gamma + 3 * epsilon) * N ≤
      (#(live c) : ℝ)
  root_or_small : ∀ c,
    ((rootSideLoad F orient c : ℝ) + 3 * epsilon * N ≤
        (#(roots c) : ℝ)) ∨
      (#(live c \ roots c) : ℝ) < gamma * N

/-- `AppendixOneCapacity` is exactly the initial, first-phase instance of
`AppendixLiveCapacity`; no adaptive-state premise remains in the public
embedding theorem. -/
theorem appendixLiveCapacity_of_appendixOneCapacity
    {b : ℕ} {B : Type v} [DecidableEq B]
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (live roots : Fin 2 → Finset B)
    (gamma epsilon N : ℝ)
    (hroots : ∀ c, roots c ⊆ live c)
    (C : AppendixOneCapacity
      (sideLoad F orient 0) (sideLoad F orient 1)
      (rootSideLoad F orient 0) (rootSideLoad F orient 1)
      #(live 0) #(live 1) #(roots 0) #(roots 1)
      gamma epsilon N) :
    AppendixLiveCapacity F orient live roots gamma epsilon N := by
  refine {
    roots_subset := hroots
    side_capacity := ?_
    root_or_small := ?_
  }
  · intro c
    fin_cases c
    · simpa using C.side_zero
    · simpa using C.side_one
  · intro c
    left
    fin_cases c
    · simpa using C.root_zero
    · simpa using C.root_one

theorem card_adaptiveInterior_ge
    {b : ℕ} {B : Type v} [DecidableEq B]
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (live roots : Fin 2 → Finset B)
    (gamma epsilon N : ℝ)
    (L : AppendixLiveCapacity F orient live roots gamma epsilon N)
    (hepsilonN : 0 ≤ epsilon * N) (c : Fin 2) :
    gamma * N ≤ (#(adaptiveInterior gamma N live roots c) : ℝ) := by
  classical
  unfold adaptiveInterior
  split_ifs with hlarge
  · exact hlarge
  · have hcap := L.side_capacity c
    have hload : (0 : ℝ) ≤ sideLoad F orient c := by positivity
    have hthree : (0 : ℝ) ≤ 3 * epsilon * N := by linarith
    linarith

theorem card_liveRoots_gt_regularLoss
    {b : ℕ} {B : Type v} [DecidableEq B]
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2)
    (whole live roots : Fin 2 → Finset B)
    (rho gamma epsilon N : ℝ)
    (L : AppendixLiveCapacity F orient live roots gamma epsilon N)
    (hregularRoot : ∀ c,
      rho * (#(whole c) : ℝ) < 3 * epsilon * N) :
    rho * (#(whole (branchRootSide F orient 0)) : ℝ) <
      (#(roots (branchRootSide F orient 0)) : ℝ) := by
  classical
  let c := branchRootSide F orient 0
  rcases L.root_or_small c with hroot | hsmall
  · have hone : (1 : ℝ) ≤ rootSideLoad F orient c := by
      exact_mod_cast one_le_rootSideLoad_head F orient
    have hr := hregularRoot c
    linarith
  · have hsubset := L.roots_subset c
    have hrootsLe : #(roots c) ≤ #(live c) :=
      Finset.card_le_card hsubset
    have hcard : #(live c) = #(live c \ roots c) + #(roots c) := by
      rw [Finset.card_sdiff_of_subset hsubset]
      omega
    have hcardReal : (#(live c) : ℝ) =
        #(live c \ roots c) + #(roots c) := by exact_mod_cast hcard
    have hcap := L.side_capacity c
    have hload : (0 : ℝ) ≤ sideLoad F orient c := by positivity
    have hr := hregularRoot c
    linarith

/-! ## One exact-image transition -/

private theorem adaptiveInterior_eq_sdiff_of_large
    {B : Type v} [DecidableEq B]
    (gamma N : ℝ) (live roots : Fin 2 → Finset B) (c : Fin 2)
    (hlarge : gamma * N ≤ (#(live c \ roots c) : ℝ)) :
    adaptiveInterior gamma N live roots c = live c \ roots c := by
  simp [adaptiveInterior, hlarge]

private theorem sdiff_sdiff_subset_sdiff
    {B : Type v} [DecidableEq B] (live roots used : Finset B) :
    (live \ used) \ (roots \ used) ⊆ live \ roots := by
  intro x hx
  have hxLive : x ∈ live := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  have hxUsed : x ∉ used := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2
  have hxNotRoot : x ∉ roots := by
    intro hxRoot
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mpr ⟨hxRoot, hxUsed⟩)
  exact Finset.mem_sdiff.mpr ⟨hxLive, hxNotRoot⟩

/-! ## Sequential graph realization -/

/-- Internal recursive engine.  Its live-state premise is constructed from
`AppendixOneCapacity` by the public theorem below and then maintained from
the exact images chosen by the recursion itself. -/
theorem exists_adaptiveAppendixEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole live roots : Fin 2 → Finset B)
    (rho density gamma epsilon N : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hliveWhole : ∀ c, live c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hepsilonN : 0 ≤ epsilon * N)
    (hregularRoot : ∀ c,
      rho * (#(whole c) : ℝ) < 3 * epsilon * N)
    (hregularInterior : ∀ c,
      rho * (#(whole c) : ℝ) ≤ gamma * N)
    (hcomponentMargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) ≤
        (density - rho) * (gamma * N))
    (hattach : ∀ i w,
      w ∈ roots (branchRootSide F orient i) →
        G.Adj (externalParent i) w)
    (L : AppendixLiveCapacity F orient live roots gamma epsilon N) :
    Nonempty (DynamicAttachedForestEmbedding
      F G externalParent orient live) := by
  classical
  induction b generalizing live roots with
  | zero =>
      let copies : ∀ i : Fin 0, (F.tree i).Copy G := fun i ↦ Fin.elim0 i
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩
        exact Fin.elim0 i
      exact ⟨{
        embedding := ⟨copies, hinjective⟩
        attach := fun i ↦ Fin.elim0 i
        map_side := fun i ↦ Fin.elim0 i
      }⟩
  | succ b ih =>
      let rootSide := branchRootSide F orient 0
      let interior : Fin 2 → Finset B :=
        adaptiveInterior gamma N live roots
      have hinteriorSubset (c : Fin 2) : interior c ⊆ whole c :=
        (adaptiveInterior_subset_live gamma N live roots c).trans
          (hliveWhole c)
      have hinteriorLarge : ∀ c,
          rho * (#(whole c) : ℝ) ≤ (#(interior c) : ℝ) := by
        intro c
        exact (hregularInterior c).trans
          (card_adaptiveInterior_ge F orient live roots gamma epsilon N
            L hepsilonN c)
      have hrootPool : roots rootSide ⊆ whole (orient 0 0) := by
        simpa [rootSide, branchRootSide] using
          (L.roots_subset rootSide).trans (hliveWhole rootSide)
      have hrootPoolLarge :
          rho * (#(whole (orient 0 0)) : ℝ) < (#(roots rootSide) : ℝ) := by
        simpa [rootSide, branchRootSide] using
          card_liveRoots_gt_regularLoss F orient whole live roots rho gamma
            epsilon N L hregularRoot
      have hheadMargin : ∀ c,
          (F.size 0 : ℝ) + rho * (#(whole c) : ℝ) ≤
            (density - rho) * (#(interior c) : ℝ) := by
        intro c
        exact (hcomponentMargin 0 c).trans (mul_le_mul_of_nonneg_left
          (card_adaptiveInterior_ge F orient live roots gamma epsilon N
            L hepsilonN c) hfactor)
      obtain ⟨fhead, hfheadRoot, hfheadInterior⟩ :=
        exists_dynamic_rooted_tree_copy_with_root_pool
          (F.tree 0) (F.isTree 0) (F.root 0) G (orient 0)
          whole interior (roots rootSide) rho density hunif
          hinteriorSubset hrootPool hinteriorLarge hrootPoolLarge
          hdensity (by
            intro c
            simpa using hheadMargin c)
      have hfheadAttach : G.Adj (externalParent 0) (fhead (F.root 0)) :=
        hattach 0 _ (by simpa [rootSide] using hfheadRoot)
      have hfheadMem (a : Fin (F.size 0)) :
          fhead a ∈
            live (orient 0 ((F.isTree 0).coloringTwoOfVert (F.root 0) a)) := by
        by_cases ha : a = F.root 0
        · subst a
          rw [coloringTwoOfVert_root]
          exact L.roots_subset rootSide (by simpa [rootSide] using hfheadRoot)
        · exact adaptiveInterior_subset_live gamma N live roots _
            (hfheadInterior a ha)
      let used : Fin 2 → Finset B := fun c ↦
        orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead c
      have husedSubset (c : Fin 2) : used c ⊆ live c := by
        exact orientedCopyImage_subset (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead live hfheadMem c
      have husedCard (c : Fin 2) :
          #(used c) = orientedClassSize F orient 0 c := by
        exact card_orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead c
      let liveTail : Fin 2 → Finset B := fun c ↦ live c \ used c
      let rootsTail : Fin 2 → Finset B := fun c ↦ roots c \ used c
      let Ftail : OrderedRootedForest b := F.tail
      let orientTail : Fin b → Fin 2 ≃ Fin 2 := tailOrient orient
      let parentTail : Fin b → B := fun i ↦ externalParent i.succ

      have husedInterRoots (c : Fin 2)
          (hlarge : gamma * N ≤ (#(live c \ roots c) : ℝ)) :
          used c ∩ roots c =
            if c = rootSide then {fhead (F.root 0)} else ∅ := by
        have hinteriorEq : interior c = live c \ roots c := by
          exact adaptiveInterior_eq_sdiff_of_large gamma N live roots c hlarge
        by_cases hc : c = rootSide
        · subst c
          rw [if_pos rfl]
          ext x
          constructor
          · intro hx
            have hxUsed := (Finset.mem_inter.mp hx).1
            have hxRoot := (Finset.mem_inter.mp hx).2
            obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxUsed
            have haSide := (Finset.mem_filter.mp ha).2
            by_cases haroot : a = F.root 0
            · subst a
              simpa [hax]
            · have haInterior := hfheadInterior a haroot
              rw [haSide, hinteriorEq] at haInterior
              exact False.elim
                ((Finset.mem_sdiff.mp haInterior).2 (hax ▸ hxRoot))
          · intro hx
            have hxEq := Finset.mem_singleton.mp hx
            subst x
            apply Finset.mem_inter.mpr
            constructor
            · change fhead (F.root 0) ∈ used ((orient 0) 0)
              simpa only [used, coloringTwoOfVert_root] using
                (copy_mem_orientedCopyImage
                  (F.tree 0) (F.isTree 0) (F.root 0) (orient 0) G fhead
                  (F.root 0))
            · exact hfheadRoot
        · rw [if_neg hc]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxUsed := (Finset.mem_inter.mp hx).1
          have hxRoot := (Finset.mem_inter.mp hx).2
          obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxUsed
          have haSide := (Finset.mem_filter.mp ha).2
          by_cases haroot : a = F.root 0
          · subst a
            have : rootSide = c := by
              simpa [rootSide, branchRootSide] using haSide
            exact hc this.symm
          · have haInterior := hfheadInterior a haroot
            rw [haSide, hinteriorEq] at haInterior
            exact (Finset.mem_sdiff.mp haInterior).2 (hax ▸ hxRoot)

      have hrootsTailCard (c : Fin 2)
          (hlarge : gamma * N ≤ (#(live c \ roots c) : ℝ)) :
          (#(rootsTail c) : ℝ) = (#(roots c) : ℝ) -
            (if rootSide = c then 1 else 0) := by
        have hset : rootsTail c = roots c \ (used c ∩ roots c) := by
          ext x
          simp [rootsTail, and_assoc, and_left_comm, and_comm]
        rw [hset, show #(roots c \ (used c ∩ roots c)) =
            #(roots c) - #(used c ∩ roots c) by
          exact Finset.card_sdiff_of_subset Finset.inter_subset_right]
        rw [husedInterRoots c hlarge]
        by_cases hc : rootSide = c
        · have hc' : c = rootSide := hc.symm
          have hrootMem : fhead (F.root 0) ∈ roots c := by
            simpa [hc] using hfheadRoot
          have hrootPos : 1 ≤ #(roots c) :=
            Finset.one_le_card.mpr ⟨fhead (F.root 0), hrootMem⟩
          rw [if_pos hc', if_pos hc, Finset.card_singleton]
          rw [Nat.cast_sub hrootPos]
          norm_num
        · have hc' : c ≠ rootSide := Ne.symm hc
          rw [if_neg hc', if_neg hc, Finset.card_empty]
          norm_num

      have htailLiveWhole (c : Fin 2) : liveTail c ⊆ whole c :=
        Finset.sdiff_subset.trans (hliveWhole c)
      have htailRootsSubset (c : Fin 2) : rootsTail c ⊆ liveTail c := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨
          L.roots_subset c (Finset.mem_sdiff.mp hx).1,
          (Finset.mem_sdiff.mp hx).2⟩
      have htailSideCapacity (c : Fin 2) :
          (sideLoad Ftail orientTail c : ℝ) +
              (gamma + 3 * epsilon) * N ≤ (#(liveTail c) : ℝ) := by
        have husedLe : #(used c) ≤ #(live c) :=
          Finset.card_le_card (husedSubset c)
        have hcardNat : #(liveTail c) = #(live c) - #(used c) := by
          exact Finset.card_sdiff_of_subset (husedSubset c)
        have hcardReal : (#(liveTail c) : ℝ) =
            (#(live c) : ℝ) - #(used c) := by
          rw [hcardNat]
          exact Nat.cast_sub husedLe
        have hload := sideLoad_tail_add_head F orient c
        have hloadReal : (sideLoad Ftail orientTail c : ℝ) +
            orientedClassSize F orient 0 c = sideLoad F orient c := by
          exact_mod_cast hload
        rw [hcardReal, husedCard]
        linarith [L.side_capacity c]
      have htailRootOrSmall (c : Fin 2) :
          ((rootSideLoad Ftail orientTail c : ℝ) + 3 * epsilon * N ≤
              (#(rootsTail c) : ℝ)) ∨
            (#(liveTail c \ rootsTail c) : ℝ) < gamma * N := by
        by_cases hlarge : gamma * N ≤ (#(live c \ roots c) : ℝ)
        · rcases L.root_or_small c with hroot | hsmall
          · left
            have hcount := rootSideLoad_tail_add_head F orient c
            have hcountReal : (rootSideLoad Ftail orientTail c : ℝ) +
                (if rootSide = c then 1 else 0) =
                  rootSideLoad F orient c := by
              have hcount' :
                  ((rootSideLoad Ftail orientTail c +
                    (if rootSide = c then 1 else 0) : ℕ) : ℝ) =
                    (rootSideLoad F orient c : ℝ) := by
                exact_mod_cast (by simpa [rootSide] using hcount)
              simpa using hcount'
            rw [hrootsTailCard c hlarge]
            linarith
          · exact False.elim ((not_lt_of_ge hlarge) hsmall)
        · right
          have hsub : liveTail c \ rootsTail c ⊆ live c \ roots c := by
            exact sdiff_sdiff_subset_sdiff (live c) (roots c) (used c)
          have hcardLe : (#(liveTail c \ rootsTail c) : ℝ) ≤
              #(live c \ roots c) := by
            exact_mod_cast Finset.card_le_card hsub
          exact hcardLe.trans_lt (lt_of_not_ge hlarge)
      let Ltail : AppendixLiveCapacity Ftail orientTail liveTail rootsTail
          gamma epsilon N := {
        roots_subset := htailRootsSubset
        side_capacity := htailSideCapacity
        root_or_small := htailRootOrSmall
      }
      have htailMargin : ∀ i c,
          (Ftail.size i : ℝ) + rho * (#(whole c) : ℝ) ≤
            (density - rho) * (gamma * N) := by
        intro i c
        exact hcomponentMargin i.succ c
      have htailAttach : ∀ i w,
          w ∈ rootsTail (branchRootSide Ftail orientTail i) →
            G.Adj (parentTail i) w := by
        intro i w hw
        exact hattach i.succ w (Finset.mem_sdiff.mp hw).1
      obtain ⟨Etail⟩ := ih Ftail parentTail orientTail liveTail
        rootsTail htailLiveWhole htailMargin htailAttach Ltail

      have hwholeDisjoint' : ∀ c d, c ≠ d → Disjoint (whole c) (whole d) := by
        intro c d hcd
        fin_cases c <;> fin_cases d
        · exact False.elim (hcd rfl)
        · exact hwholeDisjoint
        · exact hwholeDisjoint.symm
        · exact False.elim (hcd rfl)
      have hheadTailDisjoint : ∀ a i d,
          fhead a ≠ Etail.embedding.copy i d := by
        intro a i d had
        let ca := orient 0 ((F.isTree 0).coloringTwoOfVert (F.root 0) a)
        let cd := orientTail i
          ((Ftail.isTree i).coloringTwoOfVert (Ftail.root i) d)
        have haUsed : fhead a ∈ used ca :=
          copy_mem_orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
            (orient 0) G fhead a
        have hdTail : Etail.embedding.copy i d ∈ liveTail cd :=
          Etail.map_side i d
        by_cases hside : ca = cd
        · have hdTail' : Etail.embedding.copy i d ∈ liveTail ca := by
            simpa only [hside] using hdTail
          exact (Finset.mem_sdiff.mp hdTail').2 (had ▸ haUsed)
        · have haWhole : fhead a ∈ whole ca :=
            hliveWhole ca (husedSubset ca haUsed)
          have hdWhole : Etail.embedding.copy i d ∈ whole cd :=
            hliveWhole cd (Finset.mem_sdiff.mp hdTail).1
          exact (Finset.disjoint_left.mp (hwholeDisjoint' ca cd hside)
            haWhole) (had ▸ hdWhole)
      let copies : ∀ i, (F.tree i).Copy G :=
        Fin.cases fhead (fun i ↦ Etail.embedding.copy i)
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩ ⟨k, d⟩ hik
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change fhead a = fhead d at hik
            have : a = d := fhead.injective hik
            subst d
            rfl
          · change fhead a = Etail.embedding.copy k d at hik
            exact False.elim (hheadTailDisjoint a k d hik)
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change Etail.embedding.copy i a = fhead d at hik
            exact False.elim (hheadTailDisjoint d i a hik.symm)
          · have htail :
                (⟨i, a⟩ : Σ i, Fin (Ftail.size i)) = ⟨k, d⟩ := by
                apply Etail.embedding.injective
                change Etail.embedding.copy i a = Etail.embedding.copy k d at hik
                exact hik
            cases htail
            rfl
      let E : F.Embedding G := ⟨copies, hinjective⟩
      exact ⟨{
        embedding := E
        attach := by
          intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · exact hfheadAttach
          · exact Etail.attach i
        map_side := by
          intro i a
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · exact hfheadMem a
          · exact (Finset.mem_sdiff.mp (Etail.map_side i a)).1
      }⟩

/-! ## Public Corollary-A.1 graph endpoint -/

/-- Sequentially realize a fixed oriented forest from the four cardinal
inequalities of `AppendixOneCapacity`.

The three additional scalar hypotheses are the parameter hierarchy used in
the Appendix proof: `3*epsilon*N` dominates one regularity exceptional set,
`gamma*N` is a legal uniformity test set, and every component fits the
regular-pair tree margin at that minimum interior size.  They follow in the
source application from the small-component bound and the displayed
relations between `epsilon`, `gamma`, and the pair density; they contain no
embedding or continuation data. -/
theorem exists_dynamicAttachedForestEmbedding_of_appendixOneCapacity
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available rootReserve : Fin 2 → Finset B)
    (rho density gamma epsilon N : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hrootReserve : ∀ c, rootReserve c ⊆ available c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hepsilonN : 0 ≤ epsilon * N)
    (hregularRoot : ∀ c,
      rho * (#(whole c) : ℝ) < 3 * epsilon * N)
    (hregularInterior : ∀ c,
      rho * (#(whole c) : ℝ) ≤ gamma * N)
    (hcomponentMargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) ≤
        (density - rho) * (gamma * N))
    (hattach : ∀ i w,
      w ∈ rootReserve (branchRootSide F orient i) →
        G.Adj (externalParent i) w)
    (C : AppendixOneCapacity
      (sideLoad F orient 0) (sideLoad F orient 1)
      (rootSideLoad F orient 0) (rootSideLoad F orient 1)
      #(available 0) #(available 1)
      #(rootReserve 0) #(rootReserve 1)
      gamma epsilon N) :
    Nonempty (DynamicAttachedForestEmbedding
      F G externalParent orient available) := by
  let L := appendixLiveCapacity_of_appendixOneCapacity F orient available
    rootReserve gamma epsilon N hrootReserve C
  exact exists_adaptiveAppendixEmbedding F G externalParent orient whole
    available rootReserve rho density gamma epsilon N hunif havailable
    hwholeDisjoint hdensity hfactor hepsilonN hregularRoot hregularInterior
    hcomponentMargin hattach L

end Erdos547b.ZhaoLemma54AppendixA1

#print axioms Erdos547b.ZhaoLemma54AppendixA1.exists_dynamicAttachedForestEmbedding_of_appendixOneCapacity
