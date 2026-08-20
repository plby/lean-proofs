/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.PredecessorClique
import ErdosProblems.Erdos518.CliqueExtension
import ErdosProblems.Erdos518.Intersection

/-!
# The clique-extension obstruction

This file formalizes Chen--Chen's Lemma 3.4.  For an outside vertex `y`, its predecessor
clique has `blueDegreeToX y + 1` vertices of the distinguished blue path.  If an alternating
red tail supplies another `r - blueDegreeToX y` vertices of `X`, appending that tail to a
Hamilton ordering of the clique produces a red path containing `r + 1` vertices of `X`.
This contradicts the opposite-colour intersection bound.

Both a list interface and an interface indexed by `Fin` are provided.  The latter is suited
to the representative-selection arguments used later in the proof.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance extensionObstructionDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance extensionObstructionDecidableAdj : DecidableRel C.G.Adj := Classical.decRel _
noncomputable local instance extensionObstructionDecidableComplAdj : DecidableRel C.Gᶜ.Adj := Classical.decRel _

/-- Chen's predecessor clique `S_y` for the distinguished blue path `Q`. -/
noncomputable def extensionPredecessorSet (y : V) : Finset V :=
  predecessorClique C.G C.Q C.q_isPath.1 y

/-- The last vertex of `Q`, used as the endpoint of a Hamilton path through `S_y`. -/
noncomputable def extensionPredecessorEnd : V :=
  C.Q.getLast C.q_isPath.1

/-- The reservoir `W = X \ S_y`. -/
noncomputable def extensionReservoir (y : V) : Finset V :=
  C.X \ C.extensionPredecessorSet y

/-- The number `a = r - blueDegreeToX y` of outside and reservoir vertices in the tail. -/
noncomputable def extensionCount (y : V) : ℕ :=
  C.r - C.blueDegreeToX y

lemma extensionPredecessorSet_subset_X (y : V) :
    C.extensionPredecessorSet y ⊆ C.X := by
  classical
  simpa only [extensionPredecessorSet, X] using
    predecessorClique_subset_toFinset C.G C.Q C.q_isPath.1 y

@[simp] lemma extensionPredecessorEnd_mem (y : V) :
    C.extensionPredecessorEnd ∈ C.extensionPredecessorSet y := by
  classical
  simp [extensionPredecessorEnd, extensionPredecessorSet, predecessorClique]

lemma extensionPredecessorSet_isClique {y : V} (hy : y ∈ C.Y) :
    C.G.IsClique (C.extensionPredecessorSet y : Set V) := by
  classical
  apply predecessorClique_isClique C.q_isPath C.q_isGloballyLongest
  simpa [C.mem_X] using C.mem_Y.mp hy

lemma extensionPredecessorSet_card {y : V} (hy : y ∈ C.Y) :
    (C.extensionPredecessorSet y).card = C.blueDegreeToX y + 1 := by
  classical
  have hyQ : y ∉ C.Q := by
    simpa [C.mem_X] using C.mem_Y.mp hy
  simpa [extensionPredecessorSet, blueDegreeOnPath, blueNeighborsOnPath,
    blueDegreeToX, X] using
    predecessorClique_card_eq_blueDegree_add_one
      C.q_isPath C.q_isGloballyLongest hyQ

lemma extensionReservoir_subset_X (y : V) :
    C.extensionReservoir y ⊆ C.X := by
  classical
  exact Finset.sdiff_subset

@[simp] lemma mem_extensionReservoir {y x : V} :
    x ∈ C.extensionReservoir y ↔
      x ∈ C.X ∧ x ∉ C.extensionPredecessorSet y := by
  classical
  simp [extensionReservoir]

lemma extensionReservoir_disjoint_predecessorSet (y : V) :
    Disjoint (C.extensionReservoir y) (C.extensionPredecessorSet y) := by
  classical
  rw [Finset.disjoint_left]
  simp [extensionReservoir]

/-- The endpoint of the predecessor clique is red-adjacent to every vertex outside `Q`.
Otherwise that vertex extends the reversed blue path. -/
lemma extensionPredecessorEnd_adj_Y {z : V} (hz : z ∈ C.Y) :
    C.G.Adj C.extensionPredecessorEnd z := by
  classical
  have hQrev : IsPath C.Gᶜ C.Q.reverse := isPath_reverse C.q_isPath
  have hlongRev : IsGloballyLongestMonoPath C.G C.Q.reverse := by
    refine ⟨Or.inr hQrev, ?_⟩
    intro p hp
    simpa using C.q_isGloballyLongest.2 p hp
  have hzQ : z ∉ C.Q := by
    simpa [C.mem_X] using C.mem_Y.mp hz
  have hzRev : z ∉ C.Q.reverse := by simpa using hzQ
  have hnblue := not_compl_adj_head_of_globally_longest hQrev hlongRev hzRev
  have hhead : C.Q.reverse.head hQrev.1 = C.extensionPredecessorEnd := by
    simpa [extensionPredecessorEnd] using List.head_reverse C.q_isPath.1
  rw [hhead] at hnblue
  by_contra hred
  have hne : z ≠ C.extensionPredecessorEnd := by
    intro heq
    apply hzQ
    simpa [extensionPredecessorEnd, heq] using List.getLast_mem C.q_isPath.1
  exact hnblue ((SimpleGraph.compl_adj C.G z C.extensionPredecessorEnd).2
    ⟨hne, fun h ↦ hred h.symm⟩)

/-- A general predecessor-clique extension is impossible as soon as its alternating tail
contains enough vertices of `X` to make the total intersection with `Q` at least `r + 1`.

The first outside vertex is not prescribed: the terminal vertex of `Q` is red-adjacent to
every member of `Y`. -/
theorem predecessor_clique_extension_impossible
    {y : V} (hy : y ∈ C.Y) {ys xs : List V}
    (hys0 : ys ≠ []) (hysN : ys.Nodup) (hxsN : xs.Nodup)
    (hysY : ∀ z ∈ ys, z ∈ C.Y)
    (hxsX : ∀ x ∈ xs, x ∈ C.X)
    (hxsOut : ∀ x ∈ xs, x ∉ C.extensionPredecessorSet y)
    (hyx : List.Forall₂ C.G.Adj ys xs)
    (hxy : List.Forall₂ C.G.Adj xs.dropLast ys.tail)
    (hlarge : C.r + 1 ≤ (C.extensionPredecessorSet y).card + xs.length) : False := by
  classical
  have hSX := C.extensionPredecessorSet_subset_X y
  have hyxDisj : List.Disjoint ys xs := by
    rw [List.disjoint_left]
    intro v hvys hvxs
    exact Finset.disjoint_left.mp C.X_disjoint_Y (hxsX v hvxs) (hysY v hvys)
  have hysOut : ∀ z ∈ ys, z ∉ C.extensionPredecessorSet y := by
    intro z hz hzs
    exact Finset.disjoint_left.mp C.X_disjoint_Y (hSX hzs) (hysY z hz)
  let p := cliqueExtension (C.extensionPredecessorSet y)
    C.extensionPredecessorEnd ys xs
  have hp : IsPath C.G p := by
    apply isPath_cliqueExtension
      (C.extensionPredecessorSet_isClique hy) (C.extensionPredecessorEnd_mem y)
      hys0 hysN hxsN hyxDisj hysOut hxsOut hyx hxy
    exact C.extensionPredecessorEnd_adj_Y (hysY _ (List.head_mem hys0))
  have hinter :
      (p.toFinset ∩ C.X).card =
        (C.extensionPredecessorSet y).card + xs.length := by
    exact cliqueExtension_inter_card (C.extensionPredecessorEnd_mem y)
      hxsN hxsOut hSX hxsX (fun z hz ↦ C.mem_Y.mp (hysY z hz))
  have hbound := C.path_inter_Q_card_le hp
  have hinterQ :
      (pathSupport p ∩ pathSupport C.Q).card =
        (C.extensionPredecessorSet y).card + xs.length := by
    simpa [pathSupport, X, p] using hinter
  rw [hinterQ] at hbound
  omega

/-- **Chen--Chen Lemma 3.4, list form.**

Let `sigma = blueDegreeToX y`, `S_y` be the predecessor clique,
`W = X \ S_y`, and `a = r - sigma`.  Distinct lists
`y₁,...,yₐ ∈ Y` and `x₁,...,xₐ ∈ W` whose paired and successive cross
edges are red would extend `S_y` to a red path containing exactly `r + 1` vertices of `X`.
The strict degree bound is the only numerical hypothesis needed; in the application one has
the stronger `sigma ≤ r - 2`. -/
theorem clique_extension_obstruction_list
    {y : V} (hy : y ∈ C.Y1) (hdeg : C.blueDegreeToX y < C.r)
    {ys xs : List V}
    (hysLen : ys.length = C.extensionCount y)
    (hxsLen : xs.length = C.extensionCount y)
    (hysN : ys.Nodup) (hxsN : xs.Nodup)
    (hysY : ∀ z ∈ ys, z ∈ C.Y)
    (hxsW : ∀ x ∈ xs, x ∈ C.extensionReservoir y)
    (hyx : List.Forall₂ C.G.Adj ys xs)
    (hxy : List.Forall₂ C.G.Adj xs.dropLast ys.tail) : False := by
  classical
  have hyY : y ∈ C.Y := C.Y1_subset_Y hy
  have haPos : 0 < C.extensionCount y := by
    simp only [extensionCount]
    omega
  have hys0 : ys ≠ [] := by
    intro h
    subst ys
    simp at hysLen
    omega
  have hxsX : ∀ x ∈ xs, x ∈ C.X := by
    intro x hx
    exact (C.mem_extensionReservoir.mp (hxsW x hx)).1
  have hxsOut : ∀ x ∈ xs, x ∉ C.extensionPredecessorSet y := by
    intro x hx
    exact (C.mem_extensionReservoir.mp (hxsW x hx)).2
  apply C.predecessor_clique_extension_impossible hyY hys0 hysN hxsN
    hysY hxsX hxsOut hyx hxy
  rw [C.extensionPredecessorSet_card hyY, hxsLen]
  simp only [extensionCount]
  omega

/-- Initial-position embedding used in the indexed version of the obstruction. -/
def extensionInitIndex (a : ℕ) (i : Fin (a - 1)) : Fin a :=
  ⟨i.1, by omega⟩

/-- Successor-position embedding used in the indexed version of the obstruction. -/
def extensionTailIndex (a : ℕ) (i : Fin (a - 1)) : Fin a :=
  ⟨i.1 + 1, by omega⟩

private lemma forall₂_ofFn
    {n : ℕ} {f g : Fin n → V} {R : V → V → Prop}
    (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  rw [List.forall₂_iff_get]
  constructor
  · simp
  · intro i hi hj
    simpa using h ⟨i, by simpa using hi⟩

private lemma forall₂_dropLast_tail_ofFn
    {n : ℕ} {f g : Fin n → V} {R : V → V → Prop}
    (h : ∀ i : Fin (n - 1),
      R (f (extensionInitIndex n i)) (g (extensionTailIndex n i))) :
    List.Forall₂ R (List.ofFn f).dropLast (List.ofFn g).tail := by
  rw [List.forall₂_iff_get]
  constructor
  · simp
  · intro i hi hj
    have hin : i < n - 1 := by simpa using hi
    have hia : i < n := by omega
    have his : i + 1 < n := by omega
    have hrel := h ⟨i, hin⟩
    simpa [List.get_eq_getElem, extensionInitIndex, extensionTailIndex] using hrel

/-- **Chen--Chen Lemma 3.4, `Fin`-indexed form.**

This is the form consumed by greedy representative selections.  `yv i` and `xv i` are the
ordered vertices `yᵢ₊₁` and `xᵢ₊₁`; `extensionInitIndex` and
`extensionTailIndex` name the two embeddings of the `a - 1` successive gaps into `Fin a`. -/
theorem clique_extension_obstruction_fin
    {y : V} (hy : y ∈ C.Y1) (hdeg : C.blueDegreeToX y < C.r)
    (yv xv : Fin (C.extensionCount y) → V)
    (hyv : Function.Injective yv) (hxv : Function.Injective xv)
    (hyY : ∀ i, yv i ∈ C.Y)
    (hxW : ∀ i, xv i ∈ C.extensionReservoir y)
    (hpair : ∀ i, C.G.Adj (yv i) (xv i))
    (hnext : ∀ i : Fin (C.extensionCount y - 1),
      C.G.Adj (xv (extensionInitIndex (C.extensionCount y) i))
        (yv (extensionTailIndex (C.extensionCount y) i))) : False := by
  classical
  let ys := List.ofFn yv
  let xs := List.ofFn xv
  apply C.clique_extension_obstruction_list hy hdeg
      (ys := ys) (xs := xs)
  · simp [ys]
  · simp [xs]
  · exact List.nodup_ofFn.mpr hyv
  · exact List.nodup_ofFn.mpr hxv
  · intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hyY i
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hxW i
  · exact forall₂_ofFn hpair
  · exact forall₂_dropLast_tail_ofFn hnext

end Configuration
end Erdos518
