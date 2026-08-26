/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Partite
import ErdosProblems.Erdos547b.RegularPair
import Mathlib.Combinatorics.Hall.Basic

/-!
# The Hall core of Zhao's Lemma 7.8

The last branch of Lemma 7.8 in Zhao (2011) has two equally large sets of
vertices. Every vertex misses at most `l` vertices on the opposite side,
and both sides have size at least `2*l`. The proof invokes the marriage
theorem. This file isolates and proves exactly that finite combinatorial
step, first for an arbitrary relation and then for two finite vertex sets of
a graph.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma78

open Finset Function SimpleGraph

private theorem card_filter_finset_subtype
    {A : Type*} [DecidableEq A] (S : Finset A) (p : A → Prop)
    [DecidablePred p] :
    #{x : S | p x} = #{x ∈ S | p x} := by
  have huniv : (univ : Finset S) = S.attach := by
    ext x
    simp
  rw [huniv, filter_attach, card_map, card_attach]

/-- A balanced bipartite relation in which every element misses at most `l`
elements on the other side has a perfect transversal as soon as both sides
have size at least `2*l`.

This is the precise Hall-theorem calculation used in the matching branch of
Zhao's Lemma 7.8. -/
theorem exists_bijective_of_balanced_minDegree
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r] (l : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hlarge : 2 * l ≤ Fintype.card A)
    (hdegA : ∀ a, Fintype.card B - l ≤ #{b | r a b})
    (hdegB : ∀ b, Fintype.card A - l ≤ #{a | r a b}) :
    ∃ f : A → B, Function.Bijective f ∧ ∀ a, r a (f a) := by
  classical
  have hHall : ∀ S : Finset A, #S ≤ #{b | ∃ a ∈ S, r a b} := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    by_cases hsmall : #S ≤ l
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hsubset : ({b | r a b} : Finset B) ⊆
          ({b | ∃ a ∈ S, r a b} : Finset B) := by
        intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨a, ha, hb⟩
      calc
        #S ≤ l := hsmall
        _ ≤ Fintype.card B - l := by omega
        _ ≤ #{b | r a b} := hdegA a
        _ ≤ #{b | ∃ a ∈ S, r a b} := card_le_card hsubset
    · have hfull : ({b | ∃ a ∈ S, r a b} : Finset B) = univ := by
        apply eq_univ_of_forall
        intro b
        simp only [mem_filter, mem_univ, true_and]
        by_contra hnone
        push Not at hnone
        have hsubset : ({a | r a b} : Finset A) ⊆ univ \ S := by
          intro a ha
          rw [mem_sdiff]
          refine ⟨mem_univ a, ?_⟩
          intro haS
          exact hnone a haS ((mem_filter.mp ha).2)
        have hupper := card_le_card hsubset
        rw [card_sdiff_of_subset (subset_univ S), card_univ] at hupper
        have hlS : l < #S := Nat.lt_of_not_ge hsmall
        have hlower := hdegB b
        have hSle : #S ≤ Fintype.card A := card_le_univ S
        have hlcard : l < Fintype.card A := by omega
        have hstrict : Fintype.card A - #S < Fintype.card A - l :=
          Nat.sub_lt_sub_left hlcard hlS
        omega
      rw [hfull, card_univ, ← hcard]
      exact card_le_univ S
  obtain ⟨f, hfinj, hfrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hHall
  refine ⟨f, ?_, hfrel⟩
  exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩

/-- If at most `l` elements of `S` fail a predicate, the same is true
after restricting to any subset `T`.  This is the degree-loss calculation
used when Zhao passes from the ambient pair `X,Y` to `X',Y'`. -/
private theorem restricted_minDegree
    {A : Type*} [DecidableEq A] (S T : Finset A) (p : A → Prop)
    [DecidablePred p] (l : ℕ) (hTS : T ⊆ S)
    (hdeg : #S - l ≤ #(S.filter p)) :
    #T - l ≤ #(T.filter p) := by
  classical
  have hpartS := card_filter_add_card_filter_not (s := S) p
  have hmissS : #(S.filter fun a ↦ ¬p a) ≤ l := by omega
  have hmissSubset :
      T.filter (fun a ↦ ¬p a) ⊆ S.filter (fun a ↦ ¬p a) := by
    intro a ha
    rw [mem_filter] at ha ⊢
    exact ⟨hTS ha.1, ha.2⟩
  have hmissT : #(T.filter fun a ↦ ¬p a) ≤ l :=
    (card_le_card hmissSubset).trans hmissS
  have hpartT := card_filter_add_card_filter_not (s := T) p
  omega

/-- Graph-theoretic specialization of the balanced Hall core. It produces
a bijection from `P` to `Q` made entirely of host edges. -/
theorem exists_bijective_adj_on_finsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) (l : ℕ)
    (hcard : #P = #Q) (hlarge : 2 * l ≤ #P)
    (hdegP : ∀ p ∈ P, #Q - l ≤ #{q ∈ Q | G.Adj p q})
    (hdegQ : ∀ q ∈ Q, #P - l ≤ #{p ∈ P | G.Adj p q}) :
    ∃ f : P → Q, Function.Bijective f ∧ ∀ p : P, G.Adj p (f p) := by
  let r : P → Q → Prop := fun p q ↦ G.Adj p q
  have hdegP' : ∀ p : P, Fintype.card Q - l ≤ #{q : Q | r p q} := by
    intro p
    change Fintype.card Q - l ≤ #{q : Q | G.Adj p q}
    rw [Fintype.card_coe,
      card_filter_finset_subtype Q (fun q : V ↦ G.Adj p q)]
    exact hdegP p p.property
  have hdegQ' : ∀ q : Q, Fintype.card P - l ≤ #{p : P | r p q} := by
    intro q
    change Fintype.card P - l ≤ #{p : P | G.Adj p q}
    rw [Fintype.card_coe,
      card_filter_finset_subtype P (fun p : V ↦ G.Adj p q)]
    exact hdegQ q q.property
  exact exists_bijective_of_balanced_minDegree r l
    (by simpa only [Fintype.card_coe] using hcard)
    (by simpa only [Fintype.card_coe] using hlarge) hdegP' hdegQ'

/-- Source-facing subset form.  The semidegree assumptions are stated on
ambient sides `X,Y`, while the resulting perfect matching is between any
equal subpair `P ⊆ Y`, `Q ⊆ X` of size at least `2*l`. -/
theorem exists_bijective_adj_on_subsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y P Q : Finset V) (l : ℕ)
    (hPY : P ⊆ Y) (hQX : Q ⊆ X)
    (hcard : #P = #Q) (hlarge : 2 * l ≤ #P)
    (hdegX : ∀ x ∈ X, #Y - l ≤ #{y ∈ Y | G.Adj x y})
    (hdegY : ∀ y ∈ Y, #X - l ≤ #{x ∈ X | G.Adj y x}) :
    ∃ f : P → Q, Function.Bijective f ∧ ∀ p : P, G.Adj p (f p) := by
  apply exists_bijective_adj_on_finsets G P Q l hcard hlarge
  · intro p hp
    exact restricted_minDegree X Q (G.Adj p) l hQX (hdegY p (hPY hp))
  · intro q hq
    have h := restricted_minDegree Y P (G.Adj q) l hPY (hdegX q (hQX hq))
    simpa only [G.adj_comm] using h

/-- A source-shaped version of the Hall branch in Zhao's proof. Distinct
target leaves have distinct already embedded parents. If the remaining
host vertices and the parent images form a balanced high-semidegree pair,
then all leaves can be added simultaneously and injectively. -/
theorem exists_injective_leaf_images
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parentImage : W → V) (_hparent_inj : Function.Injective parentImage)
    (free : Finset V) (l : ℕ)
    (hcard : Fintype.card W = #free)
    (hlarge : 2 * l ≤ Fintype.card W)
    (hdegParent : ∀ w, #free - l ≤ #{q ∈ free | G.Adj (parentImage w) q})
    (hdegFree : ∀ q ∈ free,
      Fintype.card W - l ≤ #{w : W | G.Adj (parentImage w) q}) :
    ∃ leafImage : W → V,
      Function.Injective leafImage ∧
      (∀ w, leafImage w ∈ free) ∧
      ∀ w, G.Adj (parentImage w) (leafImage w) := by
  let r : W → free → Prop := fun w q ↦ G.Adj (parentImage w) q
  have hdegParent' : ∀ w, Fintype.card free - l ≤ #{q : free | r w q} := by
    intro w
    change Fintype.card free - l ≤ #{q : free | G.Adj (parentImage w) q}
    rw [Fintype.card_coe,
      card_filter_finset_subtype free (fun q : V ↦ G.Adj (parentImage w) q)]
    exact hdegParent w
  have hdegFree' : ∀ q : free, Fintype.card W - l ≤ #{w : W | r w q} := by
    intro q
    dsimp only [r]
    exact hdegFree q q.property
  obtain ⟨f, hfbij, hfadj⟩ :=
    exists_bijective_of_balanced_minDegree r l
      (by simpa only [Fintype.card_coe] using hcard)
      hlarge hdegParent' hdegFree'
  refine ⟨fun w ↦ f w, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp hfbij.injective
  · exact fun w ↦ (f w).property
  · exact hfadj

/-- Exact ambient-pair formulation of the simultaneous leaf-attachment
step in Zhao's Lemma 7.8.  The already embedded parents lie in `Y`, the
chosen free vertices lie in `X`, and the ambient pair has deficiency at
most `l` in both directions. -/
theorem exists_injective_leaf_images_of_ambient
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parentImage : W → V) (hparent_inj : Function.Injective parentImage)
    (X Y free : Finset V) (l : ℕ)
    (hparent_mem : ∀ w, parentImage w ∈ Y)
    (hfreeX : free ⊆ X)
    (hcard : Fintype.card W = #free)
    (hlarge : 2 * l ≤ Fintype.card W)
    (hdegX : ∀ x ∈ X, #Y - l ≤ #{y ∈ Y | G.Adj x y})
    (hdegY : ∀ y ∈ Y, #X - l ≤ #{x ∈ X | G.Adj y x}) :
    ∃ leafImage : W → V,
      Function.Injective leafImage ∧
      (∀ w, leafImage w ∈ free) ∧
      ∀ w, G.Adj (parentImage w) (leafImage w) := by
  classical
  let parents : Finset V := univ.image parentImage
  have hparentsCard : #parents = Fintype.card W := by
    dsimp only [parents]
    exact card_image_iff.mpr fun _ _ _ _ h ↦ hparent_inj h
  have hparentsY : parents ⊆ Y := by
    intro p hp
    rcases mem_image.mp hp with ⟨w, -, rfl⟩
    exact hparent_mem w
  have hparentsFree : #parents = #free := hparentsCard.trans hcard
  obtain ⟨f, hfbij, hfadj⟩ :=
    exists_bijective_adj_on_subsets G X Y parents free l
      hparentsY hfreeX hparentsFree
      (by simpa only [hparentsCard] using hlarge) hdegX hdegY
  let toParents : W → parents := fun w ↦
    ⟨parentImage w, by
      apply mem_image.mpr
      exact ⟨w, mem_univ w, rfl⟩⟩
  have htoParents_inj : Function.Injective toParents := by
    intro w w' h
    apply hparent_inj
    exact Subtype.ext_iff.mp h
  refine ⟨fun w ↦ f (toParents w), ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp (hfbij.injective.comp htoParents_inj)
  · exact fun w ↦ (f (toParents w)).property
  · intro w
    simpa [toParents] using hfadj (toParents w)

/-- Elements of `W` that are the unique element of their parent fiber.
For Zhao's `Ŵ₁`, this is exactly the set `W'₁` of leaves that are the
unique selected leaf child of their parent. -/
def uniqueParentFiber
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) : Finset A :=
  W.filter fun w ↦ #(W.filter fun z ↦ parent z = parent w) = 1

/-- The complementary set of elements lying in a parent fiber of size at
least two; this is Zhao's `W''₁`. -/
def repeatedParentFiber
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) : Finset A :=
  W \ uniqueParentFiber W parent

private theorem card_unique_add_card_repeated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) :
    #(uniqueParentFiber W parent) + #(repeatedParentFiber W parent) = #W := by
  have hsub : uniqueParentFiber W parent ⊆ W := filter_subset _ _
  have hcardSub := card_le_card hsub
  rw [repeatedParentFiber, card_sdiff_of_subset hsub]
  omega

/-- Arithmetic behind the first claim in Zhao's proof.  From at least
`5*l-1` available leaves, if fewer than `l` belong to the easy movable
class, at least `4*l` remain for the parent-fiber dichotomy. -/
theorem four_mul_le_card_sdiff
    {A : Type*} [DecidableEq A] (W movable : Finset A) (l : ℕ)
    (hmovable : movable ⊆ W)
    (hW : 5 * l - 1 ≤ #W) (hsmall : #movable < l) :
    4 * l ≤ #(W \ movable) := by
  have hcard := card_le_card hmovable
  rw [card_sdiff_of_subset hmovable]
  omega

private theorem uniqueParentFiber_injOn
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) :
    Set.InjOn parent (uniqueParentFiber W parent : Set A) := by
  intro x hx y hy hxy
  have hxone :
      #(W.filter fun z ↦ parent z = parent x) = 1 :=
    (mem_filter.mp hx).2
  have hxin : x ∈ W.filter fun z ↦ parent z = parent x := by
    rw [mem_filter]
    exact ⟨(mem_filter.mp hx).1, rfl⟩
  have hyin : y ∈ W.filter fun z ↦ parent z = parent x := by
    rw [mem_filter]
    exact ⟨(mem_filter.mp hy).1, hxy.symm⟩
  exact (card_le_one.mp hxone.le) x hxin y hyin

private theorem two_mul_card_parent_image_le_repeated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) :
    2 * #((repeatedParentFiber W parent).image parent) ≤
      #(repeatedParentFiber W parent) := by
  classical
  let R := repeatedParentFiber W parent
  have hfiber : ∀ b ∈ R.image parent, 2 ≤ #(R.filter fun z ↦ parent z = b) := by
    intro b hb
    rcases mem_image.mp hb with ⟨w, hwR, hwb⟩
    have hwR' : w ∈ W \ uniqueParentFiber W parent := by
      simpa [R, repeatedParentFiber] using hwR
    have hwW : w ∈ W := (mem_sdiff.mp hwR').1
    have hwNotUnique : w ∉ uniqueParentFiber W parent := (mem_sdiff.mp hwR').2
    have hfiberWpos : 0 < #(W.filter fun z ↦ parent z = parent w) := by
      rw [card_pos]
      exact ⟨w, by simp [hwW]⟩
    have hfiberWne : #(W.filter fun z ↦ parent z = parent w) ≠ 1 := by
      intro h
      apply hwNotUnique
      rw [uniqueParentFiber, mem_filter]
      exact ⟨hwW, h⟩
    have hfiberW : 2 ≤ #(W.filter fun z ↦ parent z = parent w) := by omega
    have heq :
        R.filter (fun z ↦ parent z = b) =
          W.filter (fun z ↦ parent z = parent w) := by
      ext z
      simp only [mem_filter]
      constructor
      · rintro ⟨hzR, hzb⟩
        have hzR' : z ∈ W \ uniqueParentFiber W parent := by
          simpa [R, repeatedParentFiber] using hzR
        exact ⟨(mem_sdiff.mp hzR').1, hzb.trans hwb.symm⟩
      · rintro ⟨hzW, hzw⟩
        have hzNotUnique : z ∉ uniqueParentFiber W parent := by
          intro hzUnique
          have hzone :=
            (mem_filter.mp hzUnique).2
          have hfilters :
              W.filter (fun u ↦ parent u = parent z) =
                W.filter (fun u ↦ parent u = parent w) := by
            ext u
            simp [hzw]
          rw [hfilters] at hzone
          exact hfiberWne hzone
        have hzRmem : z ∈ R := by
          dsimp only [R]
          rw [repeatedParentFiber, mem_sdiff]
          exact ⟨hzW, hzNotUnique⟩
        exact ⟨hzRmem, hzw.trans hwb⟩
    rw [heq]
    exact hfiberW
  have hsum :
      #(R.image parent) * 2 ≤
        ∑ b ∈ R.image parent, #(R.filter fun z ↦ parent z = b) := by
    rw [← sum_const_nat (s := R.image parent) (m := 2) (fun _ _ ↦ rfl)]
    exact sum_le_sum fun b hb ↦ hfiber b hb
  rw [← card_eq_sum_card_image parent R] at hsum
  simpa [R, mul_comm] using hsum

/-- The exact finite-fiber dichotomy in the hard branch of Zhao's Lemma
7.8.  Among at least `4*l` leaves, either at least `2*l` have distinct
parents, or the remaining repeated-parent leaves number more than `2*l`
and moving them together with their parents decreases the first side by
more than `l`. -/
theorem parentFiber_dichotomy
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (parent : A → B) (l : ℕ)
    (hW : 4 * l ≤ #W) :
    (2 * l ≤ #(uniqueParentFiber W parent) ∧
      Set.InjOn parent (uniqueParentFiber W parent : Set A)) ∨
    (2 * l < #(repeatedParentFiber W parent) ∧
      2 * #((repeatedParentFiber W parent).image parent) ≤
        #(repeatedParentFiber W parent) ∧
      l < #(repeatedParentFiber W parent) -
        #((repeatedParentFiber W parent).image parent)) := by
  by_cases hlarge : 2 * l ≤ #(uniqueParentFiber W parent)
  · exact Or.inl ⟨hlarge, uniqueParentFiber_injOn W parent⟩
  · right
    have hsplit := card_unique_add_card_repeated W parent
    have himage := two_mul_card_parent_image_le_repeated W parent
    constructor
    · omega
    constructor
    · exact himage
    · omega

/-- Assemble a full graph copy from a copy on the complement of a set of
leaves and simultaneous, pairwise distinct images for those leaves.  The
parent interface records the degree-one fact in the exact form needed by
the construction. -/
theorem extend_copy_by_distinct_leaves
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (leaves : Finset A)
    (parent : leaves → {a : A // a ∉ leaves})
    (hparent_edge : ∀ w : leaves, ∀ a : A, T.Adj w a → a = parent w)
    (core : Copy (T.induce ({a : A | a ∉ leaves} : Set A)) G)
    (free : Finset V) (hpartial_avoids : ∀ a, core a ∉ free)
    (leafImage : leaves → V) (hleaf_inj : Function.Injective leafImage)
    (hleaf_free : ∀ w, leafImage w ∈ free)
    (hleaf_adj : ∀ w, G.Adj (leafImage w) (core (parent w))) :
    ∃ f : Copy T G,
      (∀ w : leaves, f w = leafImage w) ∧
      ∀ a : {a : A // a ∉ leaves}, f a = core a := by
  classical
  let F : A → V := fun a ↦
    if h : a ∈ leaves then leafImage ⟨a, h⟩ else core ⟨a, h⟩
  have hF_adj : ∀ ⦃a b⦄, T.Adj a b → G.Adj (F a) (F b) := by
    intro a b hab
    by_cases ha : a ∈ leaves
    · let w : leaves := ⟨a, ha⟩
      have hb : b = parent w := hparent_edge w b hab
      have hbnot : b ∉ leaves := by simpa [hb] using (parent w).property
      have hFa : F a = leafImage w := by simp [F, ha, w]
      have hFb : F b = core (parent w) := by
        rw [hb]
        simp [F, (parent w).property]
      rw [hFa, hFb]
      exact hleaf_adj w
    · by_cases hb : b ∈ leaves
      · let w : leaves := ⟨b, hb⟩
        have ha' : a = parent w := hparent_edge w a hab.symm
        have hanot : a ∉ leaves := by simpa [ha'] using (parent w).property
        have hFa : F a = core (parent w) := by
          rw [ha']
          simp [F, (parent w).property]
        have hFb : F b = leafImage w := by simp [F, hb, w]
        rw [hFa, hFb]
        exact (hleaf_adj w).symm
      · have hab' :
          (T.induce ({a : A | a ∉ leaves} : Set A)).Adj
            (⟨a, ha⟩ : {a : A // a ∉ leaves}) ⟨b, hb⟩ := by
          simpa using hab
        simpa [F, ha, hb] using core.toHom.map_adj hab'
  have hF_inj : Function.Injective F := by
    intro a b hab
    by_cases ha : a ∈ leaves
    · by_cases hb : b ∈ leaves
      · have hw : (⟨a, ha⟩ : leaves) = ⟨b, hb⟩ := by
          apply hleaf_inj
          simpa [F, ha, hb] using hab
        exact congrArg Subtype.val hw
      · have heq :
          leafImage (⟨a, ha⟩ : leaves) =
            core (⟨b, hb⟩ : {a : A // a ∉ leaves}) := by
          simpa [F, ha, hb] using hab
        exfalso
        exact hpartial_avoids ⟨b, hb⟩ (by
          rw [← heq]
          exact hleaf_free ⟨a, ha⟩)
    · by_cases hb : b ∈ leaves
      · have heq :
          core (⟨a, ha⟩ : {a : A // a ∉ leaves}) =
            leafImage (⟨b, hb⟩ : leaves) := by
          simpa [F, ha, hb] using hab
        exfalso
        exact hpartial_avoids ⟨a, ha⟩ (by
          rw [heq]
          exact hleaf_free ⟨b, hb⟩)
      · have hw :
            (⟨a, ha⟩ : {a : A // a ∉ leaves}) =
              ⟨b, hb⟩ := by
          apply core.injective
          simpa [F, ha, hb] using hab
        exact congrArg Subtype.val hw
  let f : Copy T G :=
    ⟨⟨F, fun {a b} hab ↦ hF_adj hab⟩, hF_inj⟩
  refine ⟨f, ?_, ?_⟩
  · intro w
    simp [f, F, w.property]
  · intro a
    simp [f, F, a.property]

/-- End-to-end Hall branch: a partial embedding of the nonleaves extends to
a full copy whenever the parents and a free host set sit in the ambient
high-semidegree pair from Lemma 7.8. -/
theorem exists_copy_extending_leaves_of_ambient
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (leaves : Finset A)
    (parent : leaves → {a : A // a ∉ leaves})
    (hparent_inj : Function.Injective parent)
    (hparent_edge : ∀ w : leaves, ∀ a : A, T.Adj w a → a = parent w)
    (core : Copy (T.induce ({a : A | a ∉ leaves} : Set A)) G)
    (X Y free : Finset V) (l : ℕ)
    (hparentY : ∀ w, core (parent w) ∈ Y)
    (hfreeX : free ⊆ X)
    (hpartial_avoids : ∀ a, core a ∉ free)
    (hcard : Fintype.card leaves = #free)
    (hlarge : 2 * l ≤ Fintype.card leaves)
    (hdegX : ∀ x ∈ X, #Y - l ≤ #{y ∈ Y | G.Adj x y})
    (hdegY : ∀ y ∈ Y, #X - l ≤ #{x ∈ X | G.Adj y x}) :
    ∃ f : Copy T G,
      (∀ w : leaves, f w ∈ free) ∧
      ∀ a : {a : A // a ∉ leaves}, f a = core a := by
  have hparentImage_inj :
      Function.Injective (fun w ↦ core (parent w)) :=
    core.injective.comp hparent_inj
  obtain ⟨leafImage, hleaf_inj, hleaf_free, hleaf_adj⟩ :=
    exists_injective_leaf_images_of_ambient G
      (fun w ↦ core (parent w)) hparentImage_inj X Y free l
      hparentY hfreeX hcard hlarge hdegX hdegY
  obtain ⟨f, hfleaf, hfpartial⟩ :=
    extend_copy_by_distinct_leaves T G leaves parent hparent_edge core free
      hpartial_avoids leafImage hleaf_inj hleaf_free (fun w ↦ (hleaf_adj w).symm)
  exact ⟨f, fun w ↦ hfleaf w ▸ hleaf_free w, hfpartial⟩

end Erdos547b.ZhaoLemma78

#print axioms Erdos547b.ZhaoLemma78.exists_bijective_of_balanced_minDegree
#print axioms Erdos547b.ZhaoLemma78.exists_bijective_adj_on_finsets
#print axioms Erdos547b.ZhaoLemma78.exists_injective_leaf_images
#print axioms Erdos547b.ZhaoLemma78.exists_bijective_adj_on_subsets
#print axioms Erdos547b.ZhaoLemma78.exists_injective_leaf_images_of_ambient
#print axioms Erdos547b.ZhaoLemma78.extend_copy_by_distinct_leaves
#print axioms Erdos547b.ZhaoLemma78.exists_copy_extending_leaves_of_ambient
#print axioms Erdos547b.ZhaoLemma78.parentFiber_dichotomy
#print axioms Erdos547b.ZhaoLemma78.four_mul_le_card_sdiff
