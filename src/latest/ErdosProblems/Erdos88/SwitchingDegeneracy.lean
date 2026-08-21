import ErdosProblems.Erdos88.SwitchingLocal
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Rank

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos88.Switching

universe u v w

section TupleGeometry

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- All endpoint vertices of an ordered tuple of switches. -/
noncomputable def switchingEndpointFinset (p : I → V × V) : Finset V :=
  (Finset.univ.image fun i ↦ (p i).1) ∪
    (Finset.univ.image fun i ↦ (p i).2)

@[simp] lemma mem_switchingEndpointFinset {p : I → V × V} {w : V} :
    w ∈ switchingEndpointFinset p ↔
      (∃ i, (p i).1 = w) ∨ ∃ i, (p i).2 = w := by
  simp [switchingEndpointFinset]

lemma card_switchingEndpointFinset_le (p : I → V × V) :
    (switchingEndpointFinset p).card ≤ 2 * Fintype.card I := by
  unfold switchingEndpointFinset
  calc
    _ ≤ (Finset.univ.image fun i ↦ (p i).1).card +
        (Finset.univ.image fun i ↦ (p i).2).card := Finset.card_union_le _ _
    _ ≤ Finset.univ.card + Finset.univ.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * Fintype.card I := by simp; omega

/-- The vertices in `S₀` which avoid every vertex in `A`, both as vertices
and as neighbours.  This is the paper's `N(v₁, ..., vₛ) ∩ S₀`. -/
noncomputable def nonneighborsOf (G : SimpleGraph V) (A S₀ : Finset V) : Finset V :=
  S₀.filter fun w ↦ w ∉ A ∧ ∀ v ∈ A, ¬G.Adj v w

@[simp] lemma mem_nonneighborsOf {G : SimpleGraph V} {A S₀ : Finset V} {w : V} :
    w ∈ nonneighborsOf G A S₀ ↔
      w ∈ S₀ ∧ w ∉ A ∧ ∀ v ∈ A, ¬G.Adj v w := by
  simp [nonneighborsOf]

/-- Common nonneighbours of all endpoints of a switch tuple. -/
noncomputable def switchingCommonNonneighbors (G : SimpleGraph V)
    (p : I → V × V) (S₀ : Finset V) : Finset V :=
  nonneighborsOf G (switchingEndpointFinset p) S₀

/-- All endpoint occurrences other than the right endpoint at coordinate
`i`.  This occurrence-sensitive formulation agrees with deleting `zᵢ` when
the endpoints are distinct, and remains faithful to the paper when a value is
repeated at another endpoint. -/
noncomputable def switchingOtherEndpoints (p : I → V × V) (i : I) : Finset V :=
  insert (p i).1
    (((Finset.univ.erase i).image fun j ↦ (p j).1) ∪
      ((Finset.univ.erase i).image fun j ↦ (p j).2))

lemma card_switchingOtherEndpoints_le (p : I → V × V) (i : I) :
    (switchingOtherEndpoints p i).card ≤ 2 * Fintype.card I := by
  have hIpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have herase : (Finset.univ.erase i).card = Fintype.card I - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  unfold switchingOtherEndpoints
  calc
    _ ≤ ((((Finset.univ.erase i).image fun j ↦ (p j).1) ∪
          ((Finset.univ.erase i).image fun j ↦ (p j).2)).card) + 1 :=
      Finset.card_insert_le _ _
    _ ≤ ((Finset.univ.erase i).card +
        (Finset.univ.erase i).card) + 1 := by
      gcongr
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    _ = 2 * Fintype.card I - 1 := by rw [herase]; omega
    _ ≤ 2 * Fintype.card I := Nat.sub_le _ _

lemma switchingOtherEndpoints_subset {S : Finset V} {p : I → V × V}
    (hp : ∀ j, p j ∈ S ×ˢ S) (i : I) :
    switchingOtherEndpoints p i ⊆ S := by
  intro w hw
  simp only [switchingOtherEndpoints, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image] at hw
  rcases hw with h | ⟨j, _hj, h⟩ | ⟨j, _hj, h⟩
  · simpa [h] using (Finset.mem_product.mp (hp i)).1
  · simpa [← h] using (Finset.mem_product.mp (hp j)).1
  · simpa [← h] using (Finset.mem_product.mp (hp j)).2

/-- Property (2) of KSSS Lemma 13.1: every set of at most `D` vertices in
`S` has many common nonneighbors in `S₀`. -/
def HasLargeCommonNonneighbors (G : SimpleGraph V) (S S₀ : Finset V)
    (δ : ℝ) (D : ℕ) : Prop :=
  ∀ A ⊆ S, A.card ≤ D →
    δ * S₀.card ≤ ((nonneighborsOf G A S₀).card : ℝ)

/-- Property (2) of KSSS Lemma 13.1 applied simultaneously to every
endpoint of a switching tuple. -/
lemma HasLargeCommonNonneighbors.on_switchingEndpointFinset
    {G : SimpleGraph V} {S S₀ : Finset V} {δ : ℝ} {D : ℕ}
    (h : HasLargeCommonNonneighbors G S S₀ δ D)
    (hI : 2 * Fintype.card I ≤ D) (p : I → V × V)
    (hp : ∀ j, p j ∈ S ×ˢ S) :
    δ * S₀.card ≤
      ((switchingCommonNonneighbors G p S₀).card : ℝ) := by
  apply h (switchingEndpointFinset p)
  · intro w hw
    rcases mem_switchingEndpointFinset.mp hw with ⟨j, hj⟩ | ⟨j, hj⟩
    · simpa [← hj] using (Finset.mem_product.mp (hp j)).1
    · simpa [← hj] using (Finset.mem_product.mp (hp j)).2
  · exact (card_switchingEndpointFinset_le p).trans hI

lemma HasLargeCommonNonneighbors.on_switchingOtherEndpoints
    {G : SimpleGraph V} {S S₀ : Finset V} {δ : ℝ} {D : ℕ}
    (h : HasLargeCommonNonneighbors G S S₀ δ D)
    (hI : 2 * Fintype.card I ≤ D) (p : I → V × V)
    (hp : ∀ j, p j ∈ S ×ˢ S) (i : I) :
    δ * S₀.card ≤
      ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ) := by
  exact h (Erdos88.Switching.switchingOtherEndpoints p i)
    (switchingOtherEndpoints_subset hp i)
    ((card_switchingOtherEndpoints_le p i).trans hI)

/-- The private neighbourhood `Nᵢ` from KSSS Section 13: vertices adjacent
to `zᵢ` and avoiding every endpoint other than `zᵢ`. -/
noncomputable def switchingPrivateNeighbors (G : SimpleGraph V)
    (p : I → V × V) (i : I) (S₀ : Finset V) : Finset V :=
  neighborsIn G (p i).2
    (nonneighborsOf G (switchingOtherEndpoints p i) S₀)

@[simp] lemma mem_switchingPrivateNeighbors {G : SimpleGraph V}
    {p : I → V × V} {i : I} {S₀ : Finset V} {w : V} :
    w ∈ switchingPrivateNeighbors G p i S₀ ↔
      w ∈ S₀ ∧ G.Adj (p i).2 w ∧
        w ∉ switchingOtherEndpoints p i ∧
        ∀ v ∈ switchingOtherEndpoints p i, ¬G.Adj v w := by
  simp only [switchingPrivateNeighbors, mem_neighborsIn, mem_nonneighborsOf]
  aesop

/-- The endpoint map used to state that all `2s` tuple coordinates are
distinct. -/
def switchingEndpointMap (p : I → V × V) : I ⊕ I → V
  | Sum.inl i => (p i).1
  | Sum.inr i => (p i).2

def PairEndpointsDistinct (p : I → V × V) : Prop :=
  Function.Injective (switchingEndpointMap p)

lemma switchingEndpointFinset_eq_image (p : I → V × V) :
    switchingEndpointFinset p =
      Finset.univ.image (switchingEndpointMap p) := by
  ext w
  simp [switchingEndpointMap]

lemma card_switchingEndpointFinset_eq (p : I → V × V)
    (hp : PairEndpointsDistinct p) :
    (switchingEndpointFinset p).card = 2 * Fintype.card I := by
  rw [switchingEndpointFinset_eq_image,
    Finset.card_image_iff.mpr hp.injOn]
  simp only [Finset.card_univ, Fintype.card_sum]
  omega

lemma right_endpoint_mem_switchingOtherEndpoints {p : I → V × V}
    {i j : I} (hij : i ≠ j) :
    (p i).2 ∈ switchingOtherEndpoints p j := by
  unfold switchingOtherEndpoints
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, rfl⟩

lemma left_endpoint_mem_switchingOtherEndpoints {p : I → V × V}
    {i j : I} (hij : i ≠ j) :
    (p i).1 ∈ switchingOtherEndpoints p j := by
  unfold switchingOtherEndpoints
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, rfl⟩

lemma switchingPrivateNeighbors_pairwise_disjoint
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p) {i j : I} (hij : i ≠ j) :
    Disjoint (switchingPrivateNeighbors G p i S₀)
      (switchingPrivateNeighbors G p j S₀) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  have hadj : G.Adj (p i).2 w :=
    (mem_switchingPrivateNeighbors.mp hwi).2.1
  have hnot : ¬G.Adj (p i).2 w :=
    (mem_switchingPrivateNeighbors.mp hwj).2.2.2 _
      (right_endpoint_mem_switchingOtherEndpoints hij)
  exact hnot hadj

/-- No tuple endpoint belongs to any private-neighbour block. -/
lemma switchingEndpointFinset_disjoint_privateUnion
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    Disjoint (switchingEndpointFinset p)
      (Finset.univ.biUnion fun i ↦ switchingPrivateNeighbors G p i S₀) := by
  rw [Finset.disjoint_left]
  intro w hwEndpoint hwPrivate
  obtain ⟨i, _hi, hwi⟩ := Finset.mem_biUnion.mp hwPrivate
  have hwi' := mem_switchingPrivateNeighbors.mp hwi
  rcases mem_switchingEndpointFinset.mp hwEndpoint with
      ⟨j, hj⟩ | ⟨j, hj⟩
  · by_cases hji : j = i
    · subst j
      have hyMem : (p i).1 ∈ switchingOtherEndpoints p i := by
        simp [switchingOtherEndpoints]
      exact hwi'.2.2.1 (by simpa [hj] using hyMem)
    · have hyMem : (p j).1 ∈ switchingOtherEndpoints p i :=
        left_endpoint_mem_switchingOtherEndpoints hji
      exact hwi'.2.2.1 (by simpa [hj] using hyMem)
  · by_cases hji : j = i
    · subst j
      have : G.Adj w w := by simpa [hj] using hwi'.2.1
      simpa using this
    · have hzMem : (p j).2 ∈ switchingOtherEndpoints p i :=
        right_endpoint_mem_switchingOtherEndpoints hji
      exact hwi'.2.2.1 (by simpa [hj] using hzMem)

lemma switchingCommonNonneighbors_disjoint_private
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) (i : I) :
    Disjoint (switchingCommonNonneighbors G p S₀)
      (switchingPrivateNeighbors G p i S₀) := by
  rw [Finset.disjoint_left]
  intro w hwN hwi
  have hnot : ¬G.Adj (p i).2 w := by
    have hmem : (p i).2 ∈ switchingEndpointFinset p := by simp
    exact (mem_nonneighborsOf.mp hwN).2.2 _ hmem
  exact hnot (mem_switchingPrivateNeighbors.mp hwi).2.1

lemma switchingOtherEndpoints_update_same_left (p : I → V × V) (i : I)
    (y z z' : V) :
    switchingOtherEndpoints (Function.update p i (y, z)) i =
      switchingOtherEndpoints (Function.update p i (y, z')) i := by
  classical
  have hleft :
      (Finset.univ.erase i).image
          (fun j ↦ (Function.update p i (y, z) j).1) =
        (Finset.univ.erase i).image
          (fun j ↦ (Function.update p i (y, z') j).1) := by
    apply Finset.image_congr
    intro j hj
    change (Function.update p i (y, z) j).1 =
      (Function.update p i (y, z') j).1
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1,
      Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hright :
      (Finset.univ.erase i).image
          (fun j ↦ (Function.update p i (y, z) j).2) =
        (Finset.univ.erase i).image
          (fun j ↦ (Function.update p i (y, z') j).2) := by
    apply Finset.image_congr
    intro j hj
    change (Function.update p i (y, z) j).2 =
      (Function.update p i (y, z') j).2
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1,
      Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [switchingOtherEndpoints]
  rw [show (Function.update p i (y, z) i).1 = y by simp,
    show (Function.update p i (y, z') i).1 = y by simp, hleft, hright]

/-- Richness bounds the possible right endpoints which make one fixed
private neighborhood too small.  The other tuple coordinates and the left
endpoint are fixed; the occurrence-sensitive endpoint definition makes the
ambient common-nonneighbor set independent of the right endpoint. -/
lemma card_bad_private_right_endpoints_le
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ) (b : ℕ)
    (i : I) (p : I → V × V) (y : V)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀) (hρ : 0 ≤ ρ)
    (hcommon : δ * S₀.card ≤
      ((nonneighborsOf G
        (switchingOtherEndpoints (Function.update p i (y, y)) i)
        S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    (S.filter fun z ↦
      ((switchingPrivateNeighbors G (Function.update p i (y, z)) i S₀).card : ℝ) <
        ρ * δ * S₀.card).card ≤ b := by
  classical
  let W := nonneighborsOf G
    (switchingOtherEndpoints (Function.update p i (y, y)) i) S₀
  have hWsub : W ⊆ S₀ := by
    intro w hw
    exact (mem_nonneighborsOf.mp hw).1
  have hrichW := hrich W hWsub (by simpa only [W] using hcommon)
  have hsub :
      (S.filter fun z ↦
        ((switchingPrivateNeighbors G
          (Function.update p i (y, z)) i S₀).card : ℝ) <
            ρ * δ * S₀.card) ⊆
        lowExceptionalVertices G W ρ ∩ S₀ := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hprivate :
        switchingPrivateNeighbors G (Function.update p i (y, z)) i S₀ =
          neighborsIn G z W := by
      simp only [switchingPrivateNeighbors]
      rw [show (Function.update p i (y, z) i).2 = z by simp]
      congr 1
      simpa only [W] using congrArg
        (fun A ↦ nonneighborsOf G A S₀)
        (switchingOtherEndpoints_update_same_left p i y z y)
    have hsmall : ((neighborsIn G z W).card : ℝ) ≤ ρ * W.card := by
      rw [← hprivate]
      calc
        ((switchingPrivateNeighbors G
          (Function.update p i (y, z)) i S₀).card : ℝ)
            ≤ ρ * δ * S₀.card := hz'.2.le
        _ ≤ ρ * W.card := by
          have := mul_le_mul_of_nonneg_left hcommon hρ
          simpa only [W, mul_assoc] using this
    apply Finset.mem_inter.mpr
    refine ⟨?_, hSS₀ hz'.1⟩
    simpa only [lowExceptionalVertices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hsmall
  have hcardReal :
      (((S.filter fun z ↦
        ((switchingPrivateNeighbors G
          (Function.update p i (y, z)) i S₀).card : ℝ) <
            ρ * δ * S₀.card).card : ℕ) : ℝ) ≤ b := by
    calc
      (((S.filter fun z ↦
        ((switchingPrivateNeighbors G
          (Function.update p i (y, z)) i S₀).card : ℝ) <
            ρ * δ * S₀.card).card : ℕ) : ℝ)
          ≤ ((lowExceptionalVertices G W ρ ∩ S₀).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((exceptionalVertices G W ρ ∩ S₀).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro z hz
          have hz' := Finset.mem_inter.mp hz
          exact Finset.mem_inter.mpr ⟨by
            rw [exceptionalVertices_eq_union]
            exact Finset.mem_union_left _ hz'.1, hz'.2⟩)
      _ ≤ (S₀.card : ℝ) ^ α := hrichW
      _ ≤ b := hbudget
  exact_mod_cast hcardReal

end TupleGeometry

section TupleMatrix


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I]

/-- The signed neighbourhood-difference matrix of KSSS Definition 13.7. -/
noncomputable def switchingDifferenceMatrix (G : SimpleGraph V)
    (p : I → V × V) : Matrix I V ℝ := fun i w ↦
  (if G.Adj (p i).2 w ∧ w ≠ (p i).1 then 1 else 0) -
    (if G.Adj (p i).1 w ∧ w ≠ (p i).2 then 1 else 0)

/-- Every vertex in the `i`th private-neighbour block contributes the
`i`th coordinate vector to the switching-difference matrix. -/
lemma switchingDifferenceMatrix_apply_of_mem_private
    [DecidableEq I] (G : SimpleGraph V) (p : I → V × V)
    (i j : I) (S₀ : Finset V) {w : V}
    (hw : w ∈ switchingPrivateNeighbors G p i S₀) :
    switchingDifferenceMatrix G p j w = if j = i then 1 else 0 := by
  have hw' := mem_switchingPrivateNeighbors.mp hw
  by_cases hji : j = i
  · subst j
    have hyMem : (p i).1 ∈ switchingOtherEndpoints p i := by
      simp [switchingOtherEndpoints]
    have hwy : w ≠ (p i).1 := by
      intro h
      apply hw'.2.2.1
      simpa [h] using hyMem
    have hyNot : ¬G.Adj (p i).1 w := hw'.2.2.2 _ hyMem
    unfold switchingDifferenceMatrix
    simp [hw'.2.1, hwy, hyNot]
  · have hyMem : (p j).1 ∈ switchingOtherEndpoints p i :=
      left_endpoint_mem_switchingOtherEndpoints hji
    have hzMem : (p j).2 ∈ switchingOtherEndpoints p i :=
      right_endpoint_mem_switchingOtherEndpoints hji
    have hyNot : ¬G.Adj (p j).1 w := hw'.2.2.2 _ hyMem
    have hzNot : ¬G.Adj (p j).2 w := hw'.2.2.2 _ hzMem
    simp only [if_neg hji]
    unfold switchingDifferenceMatrix
    simp [hyNot, hzNot]

lemma switchingDifferenceMatrix_ternary (G : SimpleGraph V)
    (p : I → V × V) (i : I) (w : V) :
    switchingDifferenceMatrix G p i w = -1 ∨
      switchingDifferenceMatrix G p i w = 0 ∨
        switchingDifferenceMatrix G p i w = 1 := by
  unfold switchingDifferenceMatrix
  split_ifs <;> norm_num

/-- A concrete code for the three possible matrix entries `-1,0,1`. -/
noncomputable def ternaryEncode (x : ℝ) : Fin 3 :=
  if x = -1 then 0 else if x = 0 then 1 else 2

lemma ternaryEncode_injective_of_ternary {x y : ℝ}
    (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (hy : y = -1 ∨ y = 0 ∨ y = 1)
    (h : ternaryEncode x = ternaryEncode y) : x = y := by
  rcases hx with hx | hx | hx
  · rcases hy with hy | hy | hy
    · exact hx.trans hy.symm
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
      have hv := congrArg Fin.val h
      omega
  · rcases hy with hy | hy | hy
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
    · exact hx.trans hy.symm
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
      have hv := congrArg Fin.val h
      omega
  · rcases hy with hy | hy | hy
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
      have hv := congrArg Fin.val h
      omega
    · exfalso
      rw [hx, hy] at h
      norm_num [ternaryEncode] at h
      have hv := congrArg Fin.val h
      omega
    · exact hx.trans hy.symm

/-- The ternary column type on a selected set of rows. -/
noncomputable def switchingColumnCode (G : SimpleGraph V)
    (p : I → V × V) (B : Finset I) (w : V) : B → Fin 3 := fun i ↦
  ternaryEncode (switchingDifferenceMatrix G p i.1 w)

lemma switchingColumnCode_eq_iff (G : SimpleGraph V)
    (p : I → V × V) (B : Finset I) (x y : V) :
    switchingColumnCode G p B x = switchingColumnCode G p B y ↔
      ∀ i ∈ B,
        switchingDifferenceMatrix G p i x =
          switchingDifferenceMatrix G p i y := by
  constructor
  · intro h i hi
    apply ternaryEncode_injective_of_ternary
      (switchingDifferenceMatrix_ternary G p i x)
      (switchingDifferenceMatrix_ternary G p i y)
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact congrArg ternaryEncode (h i.1 i.2)

/-- A fiber of the selected-row ternary column code. -/
noncomputable def switchingColumnFiber (G : SimpleGraph V)
    (p : I → V × V) (B : Finset I) (A : Finset V)
    (t : B → Fin 3) : Finset V :=
  A.filter fun w ↦ switchingColumnCode G p B w = t

@[simp] lemma mem_switchingColumnFiber {G : SimpleGraph V}
    {p : I → V × V} {B : Finset I} {A : Finset V}
    {t : B → Fin 3} {w : V} :
    w ∈ switchingColumnFiber G p B A t ↔
      w ∈ A ∧ switchingColumnCode G p B w = t := by
  simp [switchingColumnFiber]

/-- Pigeonhole among the `3^|B|` selected-row column types. -/
lemma exists_large_switchingColumnFiber (G : SimpleGraph V)
    (p : I → V × V) (B : Finset I) (A : Finset V) (m : ℕ)
    (hsize : 3 ^ B.card * m ≤ A.card) :
    ∃ t : B → Fin 3,
      m ≤ (switchingColumnFiber G p B A t).card := by
  classical
  obtain ⟨t, _ht, ht⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := A) (t := Finset.univ)
      (f := switchingColumnCode G p B)
      (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty (by
        simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe] using hsize)
  exact ⟨t, by simpa only [switchingColumnFiber] using ht⟩

/-- The real characteristic vector of a finite vertex set. -/
noncomputable def finsetIndicator (U : Finset V) : V → ℝ := fun w ↦
  if w ∈ U then 1 else 0

lemma switchingDifferenceMatrix_mulVec (G : SimpleGraph V)
    (p : I → V × V) (U : Finset V) (i : I) :
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) i =
      (AKSGraph.degreeInto G (p i).2 (U.erase (p i).1) : ℝ) -
        (AKSGraph.degreeInto G (p i).1 (U.erase (p i).2) : ℝ) := by
  simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply,
    switchingDifferenceMatrix, finsetIndicator, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [AKSGraph.degreeInto_eq_sum]
    push_cast
    rw [← Finset.sum_subset (Finset.subset_univ (U.erase (p i).1))]
    · apply Finset.sum_congr rfl
      intro w hw
      simp only [Finset.mem_erase] at hw
      simp [hw.1, hw.2]
    · intro w hw _hwErase
      simp only [Finset.mem_erase, not_and_or, not_not] at _hwErase
      rcases _hwErase with hwy | hwU
      · simp [hwy]
      · simp [hwU]

  · rw [AKSGraph.degreeInto_eq_sum]
    push_cast
    rw [← Finset.sum_subset (Finset.subset_univ (U.erase (p i).2))]
    · apply Finset.sum_congr rfl
      intro w hw
      simp only [Finset.mem_erase] at hw
      simp [hw.1, hw.2]
    · intro w hw _hwErase
      simp only [Finset.mem_erase, not_and_or, not_not] at _hwErase
      rcases _hwErase with hwz | hwU
      · simp [hwz]
      · simp [hwU]

/-- Removing one vertex from the full ambient set subtracts exactly its
adjacency indicator from the real degree. -/
lemma degreeInto_erase_univ_real (G : SimpleGraph V) (x y : V) :
    (AKSGraph.degreeInto G x ((Finset.univ : Finset V).erase y) : ℝ) =
      (FiniteES.vertexDegree G x : ℝ) -
        if G.Adj x y then 1 else 0 := by
  by_cases hxy : G.Adj x y
  · have hy : y ∈ G.neighborFinset x := by simpa using hxy
    have hinter :
        G.neighborFinset x ∩ ((Finset.univ : Finset V).erase y) =
          (G.neighborFinset x).erase y := by
      ext z
      simp [and_comm]
    rw [AKSGraph.degreeInto, hinter, Finset.card_erase_of_mem hy,
      if_pos hxy]
    rw [FiniteES.vertexDegree_eq_degree, ← G.card_neighborFinset_eq_degree]
    rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨y, hy⟩)]
    norm_num
  · have hy : y ∉ G.neighborFinset x := by simpa using hxy
    have hinter :
        G.neighborFinset x ∩ ((Finset.univ : Finset V).erase y) =
          G.neighborFinset x := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · exact And.left
      · intro hz
        exact ⟨hz, fun hzy ↦ hy (hzy ▸ hz)⟩
    rw [AKSGraph.degreeInto, hinter, if_neg hxy,
      FiniteES.vertexDegree_eq_degree, ← G.card_neighborFinset_eq_degree]
    simp

/-- The sum of a row of the switching-difference matrix is the difference
of the endpoint degrees.  The possible edge between the two endpoints is
deleted from both sides and therefore cancels. -/
lemma sum_switchingDifferenceMatrix_row (G : SimpleGraph V)
    (p : I → V × V) (i : I) :
    (∑ w : V, switchingDifferenceMatrix G p i w) =
      (FiniteES.vertexDegree G (p i).2 : ℝ) -
        (FiniteES.vertexDegree G (p i).1 : ℝ) := by
  have hmul := switchingDifferenceMatrix_mulVec G p
    (Finset.univ : Finset V) i
  have hind : finsetIndicator (Finset.univ : Finset V) = fun _ ↦ (1 : ℝ) := by
    funext w
    simp [finsetIndicator]
  rw [hind] at hmul
  simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply, mul_one] at hmul
  rw [degreeInto_erase_univ_real, degreeInto_erase_univ_real] at hmul
  by_cases h : G.Adj (p i).2 (p i).1
  · rw [if_pos h,
      if_pos ((G.adj_comm (p i).2 (p i).1).mp h)] at hmul
    linarith
  · rw [if_neg h, if_neg (fun h' ↦
      h ((G.adj_comm (p i).1 (p i).2).mp h'))] at hmul
    linarith

/-- Under the unbiased product measure, a switching row evaluated on the
random indicator vector has mean one half of the endpoint-degree
difference. -/
lemma expectation_switchingDifferenceMatrix_mulVec_half
    (G : SimpleGraph V) (p : I → V × V) (i : I) :
    Probability.expectation (1 / 2 : ℝ)
        (fun U ↦ (switchingDifferenceMatrix G p).mulVec
          (finsetIndicator U) i) =
      ((FiniteES.vertexDegree G (p i).2 : ℝ) -
        (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2 := by
  simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply,
    finsetIndicator]
  change Probability.expectation (1 / 2 : ℝ)
      (fun U ↦ ∑ w : V,
        switchingDifferenceMatrix G p i w * Probability.bit w U) = _
  rw [show (fun U ↦ ∑ w : V,
      switchingDifferenceMatrix G p i w * Probability.bit w U) =
      (fun U ↦ ∑ w ∈ (Finset.univ : Finset V),
        switchingDifferenceMatrix G p i w * Probability.bit w U) by
    funext U
    simp]
  rw [Probability.expectation_sum]
  simp_rw [Probability.expectation_smul,
    Probability.expectation_bit (p := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)]
  rw [← Finset.sum_mul, sum_switchingDifferenceMatrix_row]
  ring

lemma switchingDifferenceMatrix_eq_one_iff (G : SimpleGraph V)
    (p : I → V × V) (i : I) {w : V}
    (hwy : w ≠ (p i).1) (hwz : w ≠ (p i).2) :
    switchingDifferenceMatrix G p i w = 1 ↔
      G.Adj (p i).2 w ∧ ¬G.Adj (p i).1 w := by
  by_cases hz : G.Adj (p i).2 w <;>
    by_cases hy : G.Adj (p i).1 w <;>
    simp [switchingDifferenceMatrix, hwy, hwz, hz, hy] <;> norm_num

/-- KSSS Definition 13.7 with an explicit integral deletion budget. -/
def IsKDegenerate (G : SimpleGraph V) (p : I → V × V)
    (budget k : ℕ) : Prop :=
  ∃ Q : Finset V, Q.card ≤ budget ∧
    Matrix.rank ((switchingDifferenceMatrix G p).submatrix id
      (fun w : {w : V // w ∉ Q} ↦ w.1)) ≤ Fintype.card I - k

/-- The integer version of the deletion budget `δ^(3/ρ) n` in KSSS
Definition 13.7. -/
noncomputable def switchingDegeneracyBudget (delta rho : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (delta ^ (3 / rho) * (n : ℝ))

lemma card_le_switchingDegeneracyBudget_iff {Q : Finset V}
    {delta rho : ℝ} {n : ℕ} (hdelta : 0 ≤ delta) :
    Q.card ≤ switchingDegeneracyBudget delta rho n ↔
      (Q.card : ℝ) ≤ delta ^ (3 / rho) * (n : ℝ) := by
  have hnonneg : 0 ≤ delta ^ (3 / rho) * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hdelta _) (Nat.cast_nonneg _)
  constructor
  · intro h
    have hcast : (Q.card : ℝ) ≤
        (switchingDegeneracyBudget delta rho n : ℝ) := by
      exact_mod_cast h
    have hfloor : (switchingDegeneracyBudget delta rho n : ℝ) ≤
        delta ^ (3 / rho) * (n : ℝ) := by
      exact Nat.floor_le hnonneg
    exact hcast.trans hfloor
  · exact Nat.le_floor

lemma isKDegenerate_zero (G : SimpleGraph V) (p : I → V × V)
    (budget : ℕ) : IsKDegenerate G p budget 0 := by
  classical
  refine ⟨∅, by simp, ?_⟩
  simpa using Matrix.rank_le_card_height
    ((switchingDifferenceMatrix G p).submatrix id
      (fun w : {w : V // w ∉ (∅ : Finset V)} ↦ w.1))

lemma IsKDegenerate.mono {G : SimpleGraph V} {p : I → V × V}
    {budget k₁ k₂ : ℕ} (h : IsKDegenerate G p budget k₂)
    (hk : k₁ ≤ k₂) : IsKDegenerate G p budget k₁ := by
  obtain ⟨Q, hQ, hrank⟩ := h
  exact ⟨Q, hQ, hrank.trans (by omega)⟩

/-- The maximum degeneracy in KSSS Definition 13.7. -/
noncomputable def switchingDegeneracy (G : SimpleGraph V)
    (p : I → V × V) (budget : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ IsKDegenerate G p budget k)
    (Fintype.card I)

lemma switchingDegeneracy_le (G : SimpleGraph V) (p : I → V × V)
    (budget : ℕ) :
    switchingDegeneracy G p budget ≤ Fintype.card I := by
  exact Nat.findGreatest_le _

lemma isKDegenerate_switchingDegeneracy (G : SimpleGraph V)
    (p : I → V × V) (budget : ℕ) :
    IsKDegenerate G p budget (switchingDegeneracy G p budget) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (isKDegenerate_zero G p budget)

lemma le_switchingDegeneracy_of_isKDegenerate
    {G : SimpleGraph V} {p : I → V × V} {budget k : ℕ}
    (hk : k ≤ Fintype.card I) (h : IsKDegenerate G p budget k) :
    k ≤ switchingDegeneracy G p budget := by
  classical
  exact Nat.le_findGreatest hk h

/-- A matrix of rank at most `r` has at most `r` actual rows spanning all of
its rows.  This is the row-selection step used in KSSS Lemma 13.9. -/
lemma exists_spanning_rows {J : Type w} [Fintype J]
    (A : Matrix I J ℝ) (r : ℕ) (hrank : A.rank ≤ r) :
    ∃ B : Finset I, B.card ≤ r ∧
      ∀ i, A i ∈ Submodule.span ℝ (A '' (B : Set I)) := by
  classical
  let rows : Set (J → ℝ) := Set.range A.row
  obtain ⟨T, hTsub, hTcard, hTspan, _hTind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ rows
  choose idx hidx using fun f : T ↦ hTsub f.2
  let B : Finset I := T.attach.image idx
  have hBcard : B.card ≤ r := by
    calc
      B.card ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
      _ = A.rank := by
        rw [Matrix.rank_eq_finrank_span_row]
        simpa only [rows] using hTcard
      _ ≤ r := hrank
  have himage : A '' (B : Set I) = (T : Set (J → ℝ)) := by
    ext x
    constructor
    · rintro ⟨i, hiB, rfl⟩
      simp only [B, Finset.mem_coe, Finset.mem_image] at hiB
      obtain ⟨f, hf, hfi⟩ := hiB
      subst i
      have hrow : A (idx f) = f.1 := by
        funext j
        simpa only [Matrix.row_apply] using congrFun (hidx f) j
      rw [hrow]
      exact f.2
    · intro hxT
      let f : T := ⟨x, hxT⟩
      have hidxB : idx f ∈ B := by
        simp [B]
      refine ⟨idx f, hidxB, ?_⟩
      funext j
      simpa only [Matrix.row_apply, f] using congrFun (hidx f) j
  refine ⟨B, hBcard, ?_⟩
  intro i
  rw [himage]
  rw [hTspan]
  exact Submodule.subset_span ⟨i, rfl⟩

lemma eq_on_spanning_rows_imp_all {J : Type w}
    (A : Matrix I J ℝ) (B : Finset I)
    (hspan : ∀ i, A i ∈ Submodule.span ℝ (A '' (B : Set I)))
    {x y : J} (hxy : ∀ i ∈ B, A i x = A i y) :
    ∀ i, A i x = A i y := by
  have hall : ∀ f : J → ℝ,
      f ∈ Submodule.span ℝ (A '' (B : Set I)) → f x = f y := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨i, hi, rfl⟩ := hf
        exact hxy i hi
    | zero => rfl
    | add f g hf hg ihf ihg => simp [ihf, ihg]
    | smul c f hf ih => simp [ih]
  intro i
  exact hall (A i) (hspan i)

/-- Column equality on at most `r` selected rows forces column equality on
all rows of a rank-at-most-`r` matrix. -/
lemma exists_rows_determining_columns {J : Type w} [Fintype J]
    (A : Matrix I J ℝ) (r : ℕ) (hrank : A.rank ≤ r) :
    ∃ B : Finset I, B.card ≤ r ∧
      ∀ x y : J, (∀ i ∈ B, A i x = A i y) →
        ∀ i, A i x = A i y := by
  obtain ⟨B, hBcard, hspan⟩ := exists_spanning_rows A r hrank
  exact ⟨B, hBcard, fun x y hxy ↦
    eq_on_spanning_rows_imp_all A B hspan hxy⟩

/-- The rank part of KSSS Lemma 13.9: after deleting the exceptional
columns, a `k`-degenerate `s`-tuple has at most `s-k` rows whose ternary
values determine every remaining row. -/
lemma IsKDegenerate.exists_determining_rows
    {G : SimpleGraph V} {p : I → V × V} {budget k : ℕ}
    (h : IsKDegenerate G p budget k) :
    ∃ (Q : Finset V) (B : Finset I),
      Q.card ≤ budget ∧ B.card ≤ Fintype.card I - k ∧
        ∀ x y : {w : V // w ∉ Q},
          (∀ i ∈ B,
            switchingDifferenceMatrix G p i x.1 =
              switchingDifferenceMatrix G p i y.1) →
            ∀ i,
              switchingDifferenceMatrix G p i x.1 =
                switchingDifferenceMatrix G p i y.1 := by
  classical
  obtain ⟨Q, hQ, hrank⟩ := h
  let A := (switchingDifferenceMatrix G p).submatrix id
    (fun w : {w : V // w ∉ Q} ↦ w.1)
  obtain ⟨B, hBcard, hB⟩ :=
    exists_rows_determining_columns A (Fintype.card I - k) hrank
  refine ⟨Q, B, hQ, hBcard, ?_⟩
  intro x y hxy
  exact hB x y hxy

/-- Once the determining rows are fixed, a value on any remaining row is
constant throughout each column-code fiber away from the deleted columns. -/
lemma row_eq_one_on_switchingColumnFiber
    {G : SimpleGraph V} {p : I → V × V}
    {Q : Finset V} {B : Finset I}
    (hdet : ∀ x y : {w : V // w ∉ Q},
      (∀ i ∈ B,
        switchingDifferenceMatrix G p i x.1 =
          switchingDifferenceMatrix G p i y.1) →
        ∀ i,
          switchingDifferenceMatrix G p i x.1 =
            switchingDifferenceMatrix G p i y.1)
    {A : Finset V} {t : B → Fin 3} {j : I} {x : V}
    (hx : x ∈ switchingColumnFiber G p B A t)
    (hxQ : x ∉ Q) (hxone : switchingDifferenceMatrix G p j x = 1) :
    ∀ y ∈ switchingColumnFiber G p B A t, y ∉ Q →
      switchingDifferenceMatrix G p j y = 1 := by
  intro y hy hyQ
  have hcode : switchingColumnCode G p B x =
      switchingColumnCode G p B y :=
    (mem_switchingColumnFiber.mp hx).2.trans
      (mem_switchingColumnFiber.mp hy).2.symm
  have hrows := hdet ⟨x, hxQ⟩ ⟨y, hyQ⟩
    ((switchingColumnCode_eq_iff G p B x y).mp hcode) j
  exact hrows ▸ hxone

/-- If a row equals `1` away from the deleted columns and its two endpoint
vertices, then the first endpoint has few neighbours and the second endpoint
has few nonneighbours in the set. -/
lemma row_eq_one_degree_bounds
    {G : SimpleGraph V} {p : I → V × V} {j : I}
    (W Q : Finset V)
    (hrow : ∀ w ∈ W, w ∉ Q → w ≠ (p j).1 → w ≠ (p j).2 →
      switchingDifferenceMatrix G p j w = 1) :
    (neighborsIn G (p j).1 W).card ≤ Q.card + 2 ∧
      (W \ neighborsIn G (p j).2 W).card ≤ Q.card + 2 := by
  classical
  let E : Finset V := Q ∪ {(p j).1, (p j).2}
  have hEcard : E.card ≤ Q.card + 2 := by
    have hpair : ({(p j).1, (p j).2} : Finset V).card ≤ 2 := by
      calc
        _ ≤ ({(p j).2} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    calc
      E.card ≤ Q.card + ({(p j).1, (p j).2} : Finset V).card :=
        Finset.card_union_le _ _
      _ ≤ Q.card + 2 := Nat.add_le_add_left hpair _
  constructor
  · refine (Finset.card_le_card ?_).trans hEcard
    intro w hw
    by_contra hwE
    have hout : w ∉ Q ∧ w ≠ (p j).1 ∧ w ≠ (p j).2 := by
      simpa only [E, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or] using hwE
    have hM := hrow w (mem_neighborsIn.mp hw).1 hout.1 hout.2.1 hout.2.2
    have hnotAdj :=
      (switchingDifferenceMatrix_eq_one_iff G p j hout.2.1 hout.2.2).mp hM
    exact hnotAdj.2 (mem_neighborsIn.mp hw).2
  · refine (Finset.card_le_card ?_).trans hEcard
    intro w hw
    by_contra hwE
    have hout : w ∉ Q ∧ w ≠ (p j).1 ∧ w ≠ (p j).2 := by
      simpa only [E, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or] using hwE
    have hw' := Finset.mem_sdiff.mp hw
    have hM := hrow w hw'.1 hout.1 hout.2.1 hout.2.2
    have hadj :=
      (switchingDifferenceMatrix_eq_one_iff G p j hout.2.1 hout.2.2).mp hM
    exact hw'.2 (mem_neighborsIn.mpr ⟨hw'.1, hadj.1⟩)

/-- The selected-row certificate turns one `+1` witness in a fiber into the
two exceptional-neighbourhood bounds used in KSSS Lemma 13.9. -/
lemma switchingColumnFiber_degree_bounds
    {G : SimpleGraph V} {p : I → V × V}
    {Q : Finset V} {B : Finset I}
    (hdet : ∀ x y : {w : V // w ∉ Q},
      (∀ i ∈ B,
        switchingDifferenceMatrix G p i x.1 =
          switchingDifferenceMatrix G p i y.1) →
        ∀ i,
          switchingDifferenceMatrix G p i x.1 =
            switchingDifferenceMatrix G p i y.1)
    {A : Finset V} {t : B → Fin 3} {j : I} {x : V}
    (hx : x ∈ switchingColumnFiber G p B A t)
    (hxQ : x ∉ Q) (hxone : switchingDifferenceMatrix G p j x = 1) :
    (neighborsIn G (p j).1 (switchingColumnFiber G p B A t)).card ≤
        Q.card + 2 ∧
      (switchingColumnFiber G p B A t \
          neighborsIn G (p j).2 (switchingColumnFiber G p B A t)).card ≤
        Q.card + 2 := by
  apply row_eq_one_degree_bounds
  intro w hw hwQ _hwy _hwz
  exact row_eq_one_on_switchingColumnFiber hdet hx hxQ hxone w hw hwQ

/-- The undeleted columns on which row `j` is visibly `+1`; this is the
exclusive neighbourhood of `zⱼ` over `yⱼ`, with the deleted columns and the
two endpoint vertices removed. -/
noncomputable def positiveDifferenceColumns (G : SimpleGraph V)
    (p : I → V × V) (j : I) (S₀ Q : Finset V) : Finset V :=
  (S₀.filter fun w ↦ G.Adj (p j).2 w ∧ ¬G.Adj (p j).1 w) \
    (Q ∪ {(p j).1, (p j).2})

@[simp] lemma mem_positiveDifferenceColumns {G : SimpleGraph V}
    {p : I → V × V} {j : I} {S₀ Q : Finset V} {w : V} :
    w ∈ positiveDifferenceColumns G p j S₀ Q ↔
      w ∈ S₀ ∧ G.Adj (p j).2 w ∧ ¬G.Adj (p j).1 w ∧
        w ∉ Q ∧ w ≠ (p j).1 ∧ w ≠ (p j).2 := by
  simp only [positiveDifferenceColumns, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
  aesop

lemma positiveDifferenceColumns_subset (G : SimpleGraph V)
    (p : I → V × V) (j : I) (S₀ Q : Finset V) :
    positiveDifferenceColumns G p j S₀ Q ⊆ S₀ := by
  intro w hw
  exact (mem_positiveDifferenceColumns.mp hw).1

lemma positiveDifferenceColumns_row_eq_one (G : SimpleGraph V)
    (p : I → V × V) (j : I) (S₀ Q : Finset V) :
    ∀ w ∈ positiveDifferenceColumns G p j S₀ Q,
      w ∉ Q ∧ switchingDifferenceMatrix G p j w = 1 := by
  intro w hw
  have h := mem_positiveDifferenceColumns.mp hw
  refine ⟨h.2.2.2.1, ?_⟩
  exact (switchingDifferenceMatrix_eq_one_iff G p j h.2.2.2.2.1
    h.2.2.2.2.2).mpr ⟨h.2.1, h.2.2.1⟩

lemma positiveDifferenceColumns_card_lower
    (G : SimpleGraph V) (p : I → V × V) (j : I)
    (S S₀ Q : Finset V) (q budget k m : ℕ)
    (hp : p j ∈ switchingPairs G S S₀ q)
    (hQ : Q.card ≤ budget)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q) :
    3 ^ (Fintype.card I - k) * m ≤
      (positiveDifferenceColumns G p j S₀ Q).card := by
  classical
  let A := S₀.filter fun w ↦ G.Adj (p j).2 w ∧ ¬G.Adj (p j).1 w
  let R : Finset V := Q ∪ {(p j).1, (p j).2}
  have hAcard : q ≤ A.card := by
    have hp' := (mem_switchingPairs_iff G S S₀ q (p j).1 (p j).2).mp hp
    simpa only [A, exclusiveNeighborCount] using hp'.2.2.1
  have hpair : ({(p j).1, (p j).2} : Finset V).card ≤ 2 := by
    calc
      _ ≤ ({(p j).2} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hRcard : R.card ≤ budget + 2 := by
    calc
      R.card ≤ Q.card + ({(p j).1, (p j).2} : Finset V).card :=
        Finset.card_union_le _ _
      _ ≤ budget + 2 := Nat.add_le_add hQ hpair
  have hdiff : A.card - R.card ≤ (A \ R).card :=
    Finset.le_card_sdiff R A
  change 3 ^ (Fintype.card I - k) * m ≤ (A \ R).card
  omega

/-- Finite core of KSSS Lemma 13.9.  If every row has a sufficiently large
set of undeleted `+1` columns, then a `k`-degenerate tuple admits at most
`s-k` determining rows, and every row has a large ternary code fiber on
which its two endpoints have the required low/high degree bounds. -/
lemma IsKDegenerate.exists_large_fibers_with_degree_bounds
    {G : SimpleGraph V} {p : I → V × V}
    {budget k m : ℕ} (hdeg : IsKDegenerate G p budget k)
    (hm : 0 < m) (S₀ : Finset V)
    (hlarge : ∀ Q : Finset V, Q.card ≤ budget → ∀ j : I,
      ∃ E : Finset V,
        E ⊆ S₀ ∧
          (∀ w ∈ E,
            w ∉ Q ∧ switchingDifferenceMatrix G p j w = 1) ∧
          3 ^ (Fintype.card I - k) * m ≤ E.card) :
    ∃ (Q : Finset V) (B : Finset I),
      Q.card ≤ budget ∧ B.card ≤ Fintype.card I - k ∧
        ∀ j : I, ∃ t : B → Fin 3,
          m ≤ (switchingColumnFiber G p B S₀ t).card ∧
            (neighborsIn G (p j).1
                (switchingColumnFiber G p B S₀ t)).card ≤ Q.card + 2 ∧
            (switchingColumnFiber G p B S₀ t \
                neighborsIn G (p j).2
                  (switchingColumnFiber G p B S₀ t)).card ≤ Q.card + 2 := by
  classical
  obtain ⟨Q, B, hQ, hBcard, hdet⟩ := hdeg.exists_determining_rows
  refine ⟨Q, B, hQ, hBcard, ?_⟩
  intro j
  obtain ⟨E, hES₀, hE, hEcard⟩ := hlarge Q hQ j
  have hpow : 3 ^ B.card * m ≤
      3 ^ (Fintype.card I - k) * m :=
    Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by omega) hBcard)
  obtain ⟨t, htE⟩ :=
    exists_large_switchingColumnFiber G p B E m (hpow.trans hEcard)
  have htENonempty : (switchingColumnFiber G p B E t).Nonempty :=
    Finset.card_pos.mp (hm.trans_le htE)
  obtain ⟨x, hxE⟩ := htENonempty
  have hxData := mem_switchingColumnFiber.mp hxE
  have hxQ : x ∉ Q := (hE x hxData.1).1
  have hxone : switchingDifferenceMatrix G p j x = 1 :=
    (hE x hxData.1).2
  have hxS₀ : x ∈ switchingColumnFiber G p B S₀ t :=
    mem_switchingColumnFiber.mpr ⟨hES₀ hxData.1, hxData.2⟩
  have hfiberSub : switchingColumnFiber G p B E t ⊆
      switchingColumnFiber G p B S₀ t := by
    intro w hw
    have hwData := mem_switchingColumnFiber.mp hw
    exact mem_switchingColumnFiber.mpr ⟨hES₀ hwData.1, hwData.2⟩
  have hfullCard : m ≤ (switchingColumnFiber G p B S₀ t).card :=
    htE.trans (Finset.card_le_card hfiberSub)
  obtain ⟨hy, hz⟩ :=
    switchingColumnFiber_degree_bounds hdet hxS₀ hxQ hxone
  exact ⟨t, hfullCard, hy, hz⟩

/-- Source-shaped finite Lemma 13.9 consequence for a tuple of pairs in the
switching reservoir.  The displayed supply inequality is the exact integer
arithmetic needed after removing the deleted columns and two endpoints. -/
lemma IsKDegenerate.exists_switching_fibers_with_degree_bounds
    {G : SimpleGraph V} {p : I → V × V}
    {S S₀ : Finset V} {q budget k m : ℕ}
    (hdeg : IsKDegenerate G p budget k)
    (hm : 0 < m) (hp : ∀ j, p j ∈ switchingPairs G S S₀ q)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q) :
    ∃ (Q : Finset V) (B : Finset I),
      Q.card ≤ budget ∧ B.card ≤ Fintype.card I - k ∧
        ∀ j : I, ∃ t : B → Fin 3,
          m ≤ (switchingColumnFiber G p B S₀ t).card ∧
            (neighborsIn G (p j).1
                (switchingColumnFiber G p B S₀ t)).card ≤ Q.card + 2 ∧
            (switchingColumnFiber G p B S₀ t \
                neighborsIn G (p j).2
                  (switchingColumnFiber G p B S₀ t)).card ≤ Q.card + 2 := by
  apply hdeg.exists_large_fibers_with_degree_bounds hm S₀
  intro Q hQ j
  let E := positiveDifferenceColumns G p j S₀ Q
  refine ⟨E, positiveDifferenceColumns_subset G p j S₀ Q,
    positiveDifferenceColumns_row_eq_one G p j S₀ Q, ?_⟩
  exact positiveDifferenceColumns_card_lower G p j S S₀ Q q budget k m
    (hp j) hQ hsupply

/-- Source-shaped exceptional-vertex conclusion of KSSS Lemma 13.9.  The
integer supply condition produces the large ternary fiber, while `hscale`
converts the deleted-column bound into the richness threshold on that
fiber. -/
lemma IsKDegenerate.exists_switching_fibers_with_exceptional_endpoints
    {G : SimpleGraph V} {p : I → V × V}
    {S S₀ : Finset V} {q budget k m : ℕ} {ρ : ℝ}
    (hdeg : IsKDegenerate G p budget k)
    (hm : 0 < m) (hρ : 0 ≤ ρ)
    (hp : ∀ j, p j ∈ switchingPairs G S S₀ q)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q)
    (hscale : ((budget + 2 : ℕ) : ℝ) ≤ ρ * m) :
    ∃ (Q : Finset V) (B : Finset I),
      Q.card ≤ budget ∧ B.card ≤ Fintype.card I - k ∧
        ∀ j : I, ∃ t : B → Fin 3,
          m ≤ (switchingColumnFiber G p B S₀ t).card ∧
            (p j).1 ∈ lowExceptionalVertices G
              (switchingColumnFiber G p B S₀ t) ρ ∧
            (p j).2 ∈ highExceptionalVertices G
              (switchingColumnFiber G p B S₀ t) ρ := by
  obtain ⟨Q, B, hQ, hB, hfibers⟩ :=
    hdeg.exists_switching_fibers_with_degree_bounds hm hp hsupply
  refine ⟨Q, B, hQ, hB, ?_⟩
  intro j
  obtain ⟨t, ht, hy, hz⟩ := hfibers j
  refine ⟨t, ht, ?_, ?_⟩
  · simp only [lowExceptionalVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    calc
      ((neighborsIn G (p j).1
          (switchingColumnFiber G p B S₀ t)).card : ℝ)
          ≤ (Q.card + 2 : ℕ) := by exact_mod_cast hy
      _ ≤ (budget + 2 : ℕ) := by exact_mod_cast Nat.add_le_add_right hQ 2
      _ ≤ ρ * m := hscale
      _ ≤ ρ * (switchingColumnFiber G p B S₀ t).card := by
        gcongr
  · simp only [highExceptionalVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    calc
      (((switchingColumnFiber G p B S₀ t) \
          neighborsIn G (p j).2
            (switchingColumnFiber G p B S₀ t)).card : ℝ)
          ≤ (Q.card + 2 : ℕ) := by exact_mod_cast hz
      _ ≤ (budget + 2 : ℕ) := by exact_mod_cast Nat.add_le_add_right hQ 2
      _ ≤ ρ * m := hscale
      _ ≤ ρ * (switchingColumnFiber G p B S₀ t).card := by
        gcongr

/-- The counting step in KSSS Lemma 13.10(b), for one fixed choice of the
determining rows.  Each large ternary fiber contributes at most `b` choices
for either exceptional endpoint, so the union over all codes contributes at
most `|C| b²` ordered pairs. -/
lemma card_pairs_with_large_exceptional_fiber_le
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (m b : ℕ) (W : C → Finset V)
    (hrich : RichOn G S₀ δ ρ α)
    (hSS₀ : S ⊆ S₀) (hW : ∀ c, W c ⊆ S₀)
    (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    ((S ×ˢ S).filter fun yz ↦
      ∃ c : C,
        m ≤ (W c).card ∧
          yz.1 ∈ lowExceptionalVertices G (W c) ρ ∧
          yz.2 ∈ highExceptionalVertices G (W c) ρ).card ≤
      Fintype.card C * (b * b) := by
  classical
  let P : C → Finset (V × V) := fun c ↦
    if m ≤ (W c).card then
      (lowExceptionalVertices G (W c) ρ ∩ S) ×ˢ
        (highExceptionalVertices G (W c) ρ ∩ S)
    else ∅
  have hPcard : ∀ c, (P c).card ≤ b * b := by
    intro c
    by_cases hc : m ≤ (W c).card
    · have hcReal : δ * S₀.card ≤ (W c).card := by
        exact hsize.trans (by exact_mod_cast hc)
      have hrichc := hrich (W c) (hW c) hcReal
      have hexcard :
          (exceptionalVertices G (W c) ρ ∩ S₀).card ≤ b := by
        exact_mod_cast hrichc.trans hbudget
      have hlowSub :
          lowExceptionalVertices G (W c) ρ ∩ S ⊆
            exceptionalVertices G (W c) ρ ∩ S₀ := by
        intro v hv
        refine Finset.mem_inter.mpr ⟨?_, hSS₀ (Finset.mem_inter.mp hv).2⟩
        rw [exceptionalVertices_eq_union]
        exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).1
      have hhighSub :
          highExceptionalVertices G (W c) ρ ∩ S ⊆
            exceptionalVertices G (W c) ρ ∩ S₀ := by
        intro v hv
        refine Finset.mem_inter.mpr ⟨?_, hSS₀ (Finset.mem_inter.mp hv).2⟩
        rw [exceptionalVertices_eq_union]
        exact Finset.mem_union_right _ (Finset.mem_inter.mp hv).1
      have hlow : (lowExceptionalVertices G (W c) ρ ∩ S).card ≤ b :=
        (Finset.card_le_card hlowSub).trans hexcard
      have hhigh : (highExceptionalVertices G (W c) ρ ∩ S).card ≤ b :=
        (Finset.card_le_card hhighSub).trans hexcard
      simp only [P, if_pos hc, Finset.card_product]
      exact Nat.mul_le_mul hlow hhigh
    · simp [P, hc]
  have hsub :
      (S ×ˢ S).filter (fun yz ↦
        ∃ c : C,
          m ≤ (W c).card ∧
            yz.1 ∈ lowExceptionalVertices G (W c) ρ ∧
            yz.2 ∈ highExceptionalVertices G (W c) ρ) ⊆
        Finset.univ.biUnion P := by
    intro yz hyz
    have hyz' := Finset.mem_filter.mp hyz
    have hyzS : yz.1 ∈ S ∧ yz.2 ∈ S := by
      simpa only [Finset.mem_product] using hyz'.1
    obtain ⟨c, hc, hy, hz⟩ := hyz'.2
    rw [Finset.mem_biUnion]
    refine ⟨c, Finset.mem_univ c, ?_⟩
    simp only [P, if_pos hc, Finset.mem_product, Finset.mem_inter]
    exact ⟨⟨hy, hyzS.1⟩, hz, hyzS.2⟩
  calc
    ((S ×ˢ S).filter fun yz ↦
        ∃ c : C,
          m ≤ (W c).card ∧
            yz.1 ∈ lowExceptionalVertices G (W c) ρ ∧
            yz.2 ∈ highExceptionalVertices G (W c) ρ).card
        ≤ (Finset.univ.biUnion P).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ Finset.univ, (P c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c : C, b * b :=
      Finset.sum_le_sum fun c _hc ↦ hPcard c
    _ = Fintype.card C * (b * b) := by simp

/-- A finite Cartesian-product bound used to iterate the one-coordinate
estimate in Lemma 13.10(b).  Values on `B` are fixed, while every remaining
coordinate has at most `b` choices. -/
lemma card_functions_fixed_on_subset_with_choices_le
    {J β : Type*} [Fintype J] [DecidableEq J]
    [Fintype β] [DecidableEq β]
    (B : Finset J) (r : J → β) (choices : J → Finset β) (b : ℕ)
    (hchoices : ∀ j, j ∉ B → (choices j).card ≤ b) :
    ((Finset.univ : Finset (J → β)).filter fun f ↦
      (∀ j ∈ B, f j = r j) ∧
        ∀ j, j ∉ B → f j ∈ choices j).card ≤
      b ^ (Fintype.card J - B.card) := by
  classical
  let D : J → Finset β := fun j ↦
    if j ∈ B then {r j} else choices j
  have hsub :
      (Finset.univ : Finset (J → β)).filter (fun f ↦
        (∀ j ∈ B, f j = r j) ∧
          ∀ j, j ∉ B → f j ∈ choices j) ⊆
        Fintype.piFinset D := by
    intro f hf
    have hf' := (Finset.mem_filter.mp hf).2
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hj : j ∈ B
    · simp only [D, if_pos hj, Finset.mem_singleton]
      exact hf'.1 j hj
    · simp only [D, if_neg hj]
      exact hf'.2 j hj
  calc
    ((Finset.univ : Finset (J → β)).filter fun f ↦
        (∀ j ∈ B, f j = r j) ∧
          ∀ j, j ∉ B → f j ∈ choices j).card
        ≤ (Fintype.piFinset D).card := Finset.card_le_card hsub
    _ = ∏ j : J, (D j).card := Fintype.card_piFinset D
    _ ≤ ∏ j : J, if j ∈ B then 1 else b := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact Nat.zero_le _
      · intro j _hj
        by_cases hj : j ∈ B
        · simp [D, hj]
        · simpa [D, hj] using hchoices j hj
    _ = ∏ j ∈ (Finset.univ \ B), b := by
      calc
        (∏ j : J, if j ∈ B then 1 else b) =
            ∏ j : J, if j ∈ (Finset.univ \ B) then b else 1 := by
          congr 1 with j
          by_cases hj : j ∈ B <;> simp [hj]
        _ = ∏ j ∈ (Finset.univ \ B), b :=
          Finset.prod_ite_mem_eq _ _
    _ = b ^ (Finset.univ \ B).card := by simp
    _ = b ^ (Fintype.card J - B.card) := by
      simp [Finset.card_sdiff]

/-- Column fibers depend only on the rows indexed by `B`. -/
lemma switchingColumnFiber_eq_of_eq_on
    {G : SimpleGraph V} {p r : I → V × V} {B : Finset I}
    {A : Finset V} {t : B → Fin 3}
    (hpr : ∀ i ∈ B, p i = r i) :
    switchingColumnFiber G p B A t =
      switchingColumnFiber G r B A t := by
  classical
  ext w
  simp only [mem_switchingColumnFiber]
  apply and_congr_right
  intro _hw
  have hcode : switchingColumnCode G p B w =
      switchingColumnCode G r B w := by
    funext i
    simp only [switchingColumnCode, switchingDifferenceMatrix,
      hpr i.1 i.2]
  rw [hcode]

/-- Fixed-basis form of the tuple count in KSSS Lemma 13.10(b).  Once the
values on the determining set `B` are fixed, every remaining coordinate has
at most `3^|B| b²` choices, hence the displayed Cartesian-product bound. -/
lemma card_fixed_basis_exceptional_tuples_le
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (m b : ℕ) (B : Finset I) (r : I → V × V)
    (hrich : RichOn G S₀ δ ρ α)
    (hSS₀ : S ⊆ S₀) (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ S ×ˢ S) ∧
        (∀ j ∈ B, p j = r j) ∧
          ∀ j, j ∉ B →
            ∃ t : B → Fin 3,
              m ≤ (switchingColumnFiber G r B S₀ t).card ∧
                (p j).1 ∈ lowExceptionalVertices G
                  (switchingColumnFiber G r B S₀ t) ρ ∧
                (p j).2 ∈ highExceptionalVertices G
                  (switchingColumnFiber G r B S₀ t) ρ).card ≤
      (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) := by
  classical
  let W : (B → Fin 3) → Finset V := fun t ↦
    switchingColumnFiber G r B S₀ t
  let choices : I → Finset (V × V) := fun _j ↦
    (S ×ˢ S).filter fun yz ↦
      ∃ t : B → Fin 3,
        m ≤ (W t).card ∧
          yz.1 ∈ lowExceptionalVertices G (W t) ρ ∧
          yz.2 ∈ highExceptionalVertices G (W t) ρ
  have hW : ∀ t, W t ⊆ S₀ := by
    intro t w hw
    exact (mem_switchingColumnFiber.mp hw).1
  have hchoiceCard : ∀ j, (choices j).card ≤ 3 ^ B.card * (b * b) := by
    intro j
    have h := card_pairs_with_large_exceptional_fiber_le
      (C := B → Fin 3) G S S₀ δ ρ α m b W
      hrich hSS₀ hW hsize hbudget
    simpa only [choices, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe] using h
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ S ×ˢ S) ∧
          (∀ j ∈ B, p j = r j) ∧
            ∀ j, j ∉ B →
              ∃ t : B → Fin 3,
                m ≤ (switchingColumnFiber G r B S₀ t).card ∧
                  (p j).1 ∈ lowExceptionalVertices G
                    (switchingColumnFiber G r B S₀ t) ρ ∧
                  (p j).2 ∈ highExceptionalVertices G
                    (switchingColumnFiber G r B S₀ t) ρ) ⊆
        (Finset.univ : Finset (I → V × V)).filter (fun p ↦
          (∀ j ∈ B, p j = r j) ∧
            ∀ j, j ∉ B → p j ∈ choices j) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, hp'.2.1, ?_⟩
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨hp'.1 j, ?_⟩
    simpa only [choices, W] using hp'.2.2 j hj
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ S ×ˢ S) ∧
          (∀ j ∈ B, p j = r j) ∧
            ∀ j, j ∉ B →
              ∃ t : B → Fin 3,
                m ≤ (switchingColumnFiber G r B S₀ t).card ∧
                  (p j).1 ∈ lowExceptionalVertices G
                    (switchingColumnFiber G r B S₀ t) ρ ∧
                  (p j).2 ∈ highExceptionalVertices G
                    (switchingColumnFiber G r B S₀ t) ρ).card
        ≤ ((Finset.univ : Finset (I → V × V)).filter fun p ↦
          (∀ j ∈ B, p j = r j) ∧
            ∀ j, j ∉ B → p j ∈ choices j).card :=
      Finset.card_le_card hsub
    _ ≤ (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) :=
      card_functions_fixed_on_subset_with_choices_le B r choices
        (3 ^ B.card * (b * b)) (fun j _hj ↦ hchoiceCard j)

/-- Extend an assignment on a finite set of coordinates by a fixed default
value. -/
noncomputable def extendFinsetAssignment
    {J β : Type*} (B : Finset J) (default : β) (a : B → β) : J → β := by
  classical
  exact fun j ↦ if hj : j ∈ B then a ⟨j, hj⟩ else default

@[simp] lemma extendFinsetAssignment_apply_mem
    {J β : Type*} {B : Finset J} {default : β} (a : B → β)
    {j : J} (hj : j ∈ B) :
    extendFinsetAssignment B default a j = a ⟨j, hj⟩ := by
  classical
  simp [extendFinsetAssignment, hj]

lemma extendFinsetAssignment_erase_eq_update
    {J β : Type*} [Fintype J] [DecidableEq J]
    (i : J) (default x : β)
    (a : {j : J // j ∈ (Finset.univ.erase i : Finset J)} → β) :
    extendFinsetAssignment (Finset.univ.erase i) x a =
      Function.update
        (extendFinsetAssignment (Finset.univ.erase i) default a) i x := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [extendFinsetAssignment]
  · have hj : j ∈ (Finset.univ.erase i : Finset J) := by simp [hji]
    rw [Function.update_of_ne hji]
    simp only [extendFinsetAssignment_apply_mem a hj]

/-- Count a filtered Cartesian product from uniform bounds on its right
fibers. -/
lemma card_filter_product_le_mul_of_right_fiber_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (X : Finset A) (Y : Finset B) (P : A → B → Prop)
    [DecidablePred fun xy : A × B ↦ P xy.1 xy.2]
    [∀ x, DecidablePred (P x)] (b : ℕ)
    (h : ∀ x ∈ X, (Y.filter (P x)).card ≤ b) :
    ((X ×ˢ Y).filter fun xy ↦ P xy.1 xy.2).card ≤ X.card * b := by
  rw [Finset.card_filter]
  calc
    _ = ∑ x ∈ X, ∑ y ∈ Y, if P x y then 1 else 0 := by
      exact Finset.sum_product X Y
        (fun xy ↦ if P xy.1 xy.2 then 1 else 0)
    _ = ∑ x ∈ X, (Y.filter (P x)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.card_filter]
    _ ≤ ∑ _x ∈ X, b := Finset.sum_le_sum fun x hx ↦ h x hx
    _ = X.card * b := by simp

/-- A one-coordinate fiber bound for a predicate on a finite Cartesian
power.  This is the reusable counting form of "fix all other coordinates". -/
lemma card_functions_property_le_of_update_fiber_le
    {J β : Type*} [Fintype J] [DecidableEq J]
    [Fintype β] [DecidableEq β]
    (T : Finset β) (i : J) (default : β) (P : (J → β) → Prop)
    [DecidablePred P] (b : ℕ)
    (hfiber : ∀ r : J → β, (∀ j, j ≠ i → r j ∈ T) →
      (T.filter fun x ↦ P (Function.update r i x)).card ≤ b) :
    ((Finset.univ : Finset (J → β)).filter fun p ↦
      (∀ j, p j ∈ T) ∧ P p).card ≤
      T.card ^ (Fintype.card J - 1) * b := by
  classical
  let B : Finset J := Finset.univ.erase i
  let assignments : Finset (B → β) := Fintype.piFinset fun _j : B ↦ T
  let full : (B → β) → β → J → β := fun a x ↦
    extendFinsetAssignment B x a
  let Q : (B → β) → Finset (J → β) := fun a ↦
    (T.filter fun x ↦ P (full a x)).image (full a)
  have hQcard : ∀ a ∈ assignments, (Q a).card ≤ b := by
    intro a ha
    let r : J → β := extendFinsetAssignment B default a
    have hr : ∀ j, j ≠ i → r j ∈ T := by
      intro j hji
      have hjB : j ∈ B := by simp [B, hji]
      have haj : a ⟨j, hjB⟩ ∈ T :=
        Fintype.mem_piFinset.mp ha ⟨j, hjB⟩
      simpa only [r, extendFinsetAssignment_apply_mem a hjB] using haj
    have hfull : ∀ x, full a x = Function.update r i x := by
      intro x
      simpa only [full, r, B] using
        extendFinsetAssignment_erase_eq_update i default x a
    exact Finset.card_image_le.trans (by
      simpa only [hfull] using hfiber r hr)
  have hsub :
      (Finset.univ : Finset (J → β)).filter (fun p ↦
        (∀ j, p j ∈ T) ∧ P p) ⊆ assignments.biUnion Q := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    let a : B → β := fun j ↦ p j.1
    have ha : a ∈ assignments := by
      apply Fintype.mem_piFinset.mpr
      intro j
      exact hp'.1 j.1
    have hfullp : full a (p i) = p := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [full, B, extendFinsetAssignment]
      · have hjB : j ∈ B := by simp [B, hji]
        simpa only [full, a, extendFinsetAssignment_apply_mem a hjB]
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, Finset.mem_image.mpr ⟨p i, ?_, hfullp⟩⟩
    apply Finset.mem_filter.mpr
    exact ⟨hp'.1 i, by simpa only [hfullp] using hp'.2⟩
  have hassignments : assignments.card = T.card ^ (Fintype.card J - 1) := by
    have hBcard : B.card = Fintype.card J - 1 := by
      simp only [B, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ]
    dsimp only [assignments]
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      hBcard]
  calc
    ((Finset.univ : Finset (J → β)).filter fun p ↦
      (∀ j, p j ∈ T) ∧ P p).card
        ≤ (assignments.biUnion Q).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ assignments, (Q a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ assignments, b :=
      Finset.sum_le_sum fun a ha ↦ hQcard a ha
    _ = T.card ^ (Fintype.card J - 1) * b := by
      simp [hassignments]

/-- Exact count of ordered functions whose coordinates all lie in one finite
choice set. -/
lemma card_tupleFunctions (T : Finset (V × V)) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      ∀ j, p j ∈ T).card = T.card ^ Fintype.card I := by
  classical
  have heq :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        ∀ j, p j ∈ T) = Fintype.piFinset (fun _j : I ↦ T) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset]
  simp

lemma card_pairs_with_fixed_first_le (T : Finset (V × V)) (S : Finset V)
    (hT : T ⊆ S ×ˢ S) (x : V) :
    (T.filter fun yz ↦ x = yz.1).card ≤ S.card := by
  have hsub : (T.filter fun yz ↦ x = yz.1) ⊆ ({x} ×ˢ S) := by
    intro yz hyz
    have hyz' := Finset.mem_filter.mp hyz
    have hyzS := Finset.mem_product.mp (hT hyz'.1)
    exact Finset.mem_product.mpr ⟨by simpa [hyz'.2], hyzS.2⟩
  exact (Finset.card_le_card hsub).trans (by simp)

lemma card_pairs_with_fixed_second_le (T : Finset (V × V)) (S : Finset V)
    (hT : T ⊆ S ×ˢ S) (x : V) :
    (T.filter fun yz ↦ x = yz.2).card ≤ S.card := by
  have hsub : (T.filter fun yz ↦ x = yz.2) ⊆ (S ×ˢ {x}) := by
    intro yz hyz
    have hyz' := Finset.mem_filter.mp hyz
    have hyzS := Finset.mem_product.mp (hT hyz'.1)
    exact Finset.mem_product.mpr ⟨hyzS.1, by simpa [hyz'.2]⟩
  exact (Finset.card_le_card hsub).trans (by simp)

lemma card_diagonal_pairs_le (T : Finset (V × V)) (S : Finset V)
    (hT : T ⊆ S ×ˢ S) :
    (T.filter fun yz ↦ yz.1 = yz.2).card ≤ S.card := by
  have hsub : (T.filter fun yz ↦ yz.1 = yz.2) ⊆
      S.image fun x ↦ (x, x) := by
    intro yz hyz
    have hyz' := Finset.mem_filter.mp hyz
    have hyzS := Finset.mem_product.mp (hT hyz'.1)
    exact Finset.mem_image.mpr ⟨yz.1, hyzS.1, by ext <;> simp [hyz'.2]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- For two distinct endpoint slots, tuples in `T^s` on which the endpoints
coincide have the source-size bound `|T|^(s-1)|S|`. -/
lemma card_tuples_with_fixed_endpoint_collision_le
    (T : Finset (V × V)) (S : Finset V) (hT : T ⊆ S ×ˢ S)
    (a b : I ⊕ I) (hab : a ≠ b) (default : V × V) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧
        switchingEndpointMap p a = switchingEndpointMap p b).card ≤
      T.card ^ (Fintype.card I - 1) * S.card := by
  classical
  rcases a with i | i <;> rcases b with j | j
  · have hij : i ≠ j := by
      intro h
      subst j
      exact hab rfl
    apply card_functions_property_le_of_update_fiber_le T j default
      (fun p ↦ switchingEndpointMap p (Sum.inl i) =
        switchingEndpointMap p (Sum.inl j)) S.card
    intro r hr
    simpa [switchingEndpointMap, Function.update_of_ne hij] using
      card_pairs_with_fixed_first_le T S hT (r i).1
  · by_cases hij : i = j
    · subst j
      apply card_functions_property_le_of_update_fiber_le T i default
        (fun p ↦ switchingEndpointMap p (Sum.inl i) =
          switchingEndpointMap p (Sum.inr i)) S.card
      intro r hr
      simpa [switchingEndpointMap] using card_diagonal_pairs_le T S hT
    · apply card_functions_property_le_of_update_fiber_le T j default
        (fun p ↦ switchingEndpointMap p (Sum.inl i) =
          switchingEndpointMap p (Sum.inr j)) S.card
      intro r hr
      simpa [switchingEndpointMap, Function.update_of_ne hij] using
        card_pairs_with_fixed_second_le T S hT (r i).1
  · by_cases hij : i = j
    · subst j
      apply card_functions_property_le_of_update_fiber_le T i default
        (fun p ↦ switchingEndpointMap p (Sum.inr i) =
          switchingEndpointMap p (Sum.inl i)) S.card
      intro r hr
      simpa [switchingEndpointMap, eq_comm] using
        card_diagonal_pairs_le T S hT
    · apply card_functions_property_le_of_update_fiber_le T j default
        (fun p ↦ switchingEndpointMap p (Sum.inr i) =
          switchingEndpointMap p (Sum.inl j)) S.card
      intro r hr
      simpa [switchingEndpointMap, Function.update_of_ne hij] using
        card_pairs_with_fixed_first_le T S hT (r i).2
  · have hij : i ≠ j := by
      intro h
      subst j
      exact hab rfl
    apply card_functions_property_le_of_update_fiber_le T j default
      (fun p ↦ switchingEndpointMap p (Sum.inr i) =
        switchingEndpointMap p (Sum.inr j)) S.card
    intro r hr
    simpa [switchingEndpointMap, Function.update_of_ne hij] using
      card_pairs_with_fixed_second_le T S hT (r i).2

/-- The `O_s(|T|^(s-1)|S|)` repetition estimate from KSSS Lemma
13.10(a), with the explicit harmless constant `(2s)^2`. -/
lemma card_tuples_with_repeated_endpoint_le
    (T : Finset (V × V)) (S : Finset V) (hT : T ⊆ S ×ˢ S)
    (default : V × V) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧ ¬PairEndpointsDistinct p).card ≤
      (2 * Fintype.card I) ^ 2 *
        (T.card ^ (Fintype.card I - 1) * S.card) := by
  classical
  let J := I ⊕ I
  let R : J × J → Finset (I → V × V) := fun ab ↦
    if h : ab.1 ≠ ab.2 then
      (Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ T) ∧
          switchingEndpointMap p ab.1 = switchingEndpointMap p ab.2
    else ∅
  let M := T.card ^ (Fintype.card I - 1) * S.card
  have hR : ∀ ab : J × J, (R ab).card ≤ M := by
    intro ab
    by_cases hab : ab.1 ≠ ab.2
    · simpa only [R, M, dif_pos hab] using
        card_tuples_with_fixed_endpoint_collision_le
          T S hT ab.1 ab.2 hab default
    · have heq : ab.1 = ab.2 := not_ne_iff.mp hab
      simp [R, heq]
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ T) ∧ ¬PairEndpointsDistinct p) ⊆
        Finset.univ.biUnion R := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hnot : ¬Function.Injective (switchingEndpointMap p) := hp'.2
    simp only [Function.Injective] at hnot
    push_neg at hnot
    obtain ⟨a, b, heq, hab⟩ := hnot
    rw [Finset.mem_biUnion]
    refine ⟨(a, b), Finset.mem_univ _, ?_⟩
    simp only [R, dif_pos hab, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp'.1, heq⟩
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧ ¬PairEndpointsDistinct p).card
        ≤ (Finset.univ.biUnion R).card := Finset.card_le_card hsub
    _ ≤ ∑ ab : J × J, (R ab).card := Finset.card_biUnion_le
    _ ≤ ∑ _ab : J × J, M := Finset.sum_le_sum fun ab _hab ↦ hR ab
    _ = (2 * Fintype.card I) ^ 2 *
        (T.card ^ (Fintype.card I - 1) * S.card) := by
      simp only [Finset.sum_const, Finset.card_univ]
      change Fintype.card (J × J) * M = _
      dsimp only [J, M]
      simp only [Fintype.card_prod, Fintype.card_sum]
      ring

/-- The first counting estimate in KSSS Lemma 13.10(a), for one fixed
coordinate.  After fixing the other `s-1` pairs and the left endpoint, the
richness bound leaves at most `b` bad choices for the right endpoint. -/
lemma card_tuples_bad_private_at_le
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (q b : ℕ) (i : I) (default : V × V)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀) (hρ : 0 ≤ ρ)
    (hcommon : ∀ p : I → V × V, (∀ j, p j ∈ S ×ˢ S) →
      δ * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
          ρ * δ * S₀.card).card ≤
      (switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b := by
  classical
  let T := switchingPairs G S S₀ q
  let B : Finset I := Finset.univ.erase i
  let assignments : Finset (B → V × V) :=
    Fintype.piFinset fun _j : B ↦ T
  let full : (B → V × V) → V × V → I → V × V := fun a yz ↦
    extendFinsetAssignment B yz a
  let P : (B → V × V) → Finset (V × V) := fun a ↦
    (S ×ˢ S).filter fun yz ↦
      ((switchingPrivateNeighbors G (full a yz) i S₀).card : ℝ) <
        ρ * δ * S₀.card
  let Q : (B → V × V) → Finset (I → V × V) := fun a ↦
    (P a).image (full a)
  have hTsub : T ⊆ S ×ˢ S := by
    intro yz hyz
    have hyz' := (mem_switchingPairs_iff G S S₀ q yz.1 yz.2).mp hyz
    exact Finset.mem_product.mpr ⟨hyz'.1, hyz'.2.1⟩
  have hPcard : ∀ a ∈ assignments, (P a).card ≤ S.card * b := by
    intro a ha
    apply card_filter_product_le_mul_of_right_fiber_le S S
      (fun y z ↦
        ((switchingPrivateNeighbors G (full a (y, z)) i S₀).card : ℝ) <
          ρ * δ * S₀.card) b
    intro y hy
    let r : I → V × V := extendFinsetAssignment B default a
    have hfull : ∀ z,
        full a (y, z) = Function.update r i (y, z) := by
      intro z
      simpa only [full, r, B] using
        extendFinsetAssignment_erase_eq_update i default (y, z) a
    have hall : ∀ j,
        Function.update r i (y, y) j ∈ S ×ˢ S := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [hy]
      · rw [Function.update_of_ne hji]
        have hjB : j ∈ B := by simp [B, hji]
        have haj : a ⟨j, hjB⟩ ∈ T :=
          Fintype.mem_piFinset.mp ha ⟨j, hjB⟩
        simpa only [r, extendFinsetAssignment_apply_mem a hjB] using
          hTsub haj
    have hbad := card_bad_private_right_endpoints_le
      G S S₀ δ ρ α b i r y hrich hSS₀ hρ
      (hcommon (Function.update r i (y, y)) hall) hbudget
    simpa only [hfull] using hbad
  have hQcard : ∀ a ∈ assignments, (Q a).card ≤ S.card * b := by
    intro a ha
    exact (Finset.card_image_le.trans (hPcard a ha))
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
            ρ * δ * S₀.card) ⊆
        assignments.biUnion Q := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    let a : B → V × V := fun j ↦ p j.1
    have ha : a ∈ assignments := by
      apply Fintype.mem_piFinset.mpr
      intro j
      exact hp'.1 j.1
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    have hfullp : full a (p i) = p := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [full, B, extendFinsetAssignment]
      · have hjB : j ∈ B := by simp [B, hji]
        simpa only [full, a, extendFinsetAssignment_apply_mem a hjB]
    apply Finset.mem_image.mpr
    refine ⟨p i, ?_, hfullp⟩
    apply Finset.mem_filter.mpr
    have hpi := hTsub (hp'.1 i)
    refine ⟨hpi, ?_⟩
    simpa only [hfullp] using hp'.2
  have hassignments : assignments.card = T.card ^ (Fintype.card I - 1) := by
    have hIpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    have hBcard : B.card = Fintype.card I - 1 := by
      simp only [B, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ]
    dsimp only [assignments]
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      hBcard]
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
          ρ * δ * S₀.card).card
        ≤ (assignments.biUnion Q).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ assignments, (Q a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ assignments, S.card * b :=
      Finset.sum_le_sum fun a ha ↦ hQcard a ha
    _ = T.card ^ (Fintype.card I - 1) * S.card * b := by
      simp [hassignments, mul_assoc]
    _ = (switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b := by rfl

/-- Union bound over the coordinates in the first half of KSSS Lemma
13.10(a). -/
lemma card_tuples_with_some_bad_private_le
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (q b : ℕ) (default : V × V)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀) (hρ : 0 ≤ ρ)
    (hcommon : ∀ i (p : I → V × V), (∀ j, p j ∈ S ×ˢ S) →
      δ * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        ∃ i,
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
            ρ * δ * S₀.card).card ≤
      Fintype.card I *
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
          S.card * b) := by
  classical
  let P : I → Finset (I → V × V) := fun i ↦
    (Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
          ρ * δ * S₀.card
  have hP : ∀ i, (P i).card ≤
      (switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b := by
    intro i
    exact card_tuples_bad_private_at_le G S S₀ δ ρ α q b i default
      hrich hSS₀ hρ (hcommon i) hbudget
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          ∃ i,
            ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
              ρ * δ * S₀.card) ⊆
        Finset.univ.biUnion P := by
    intro p hp
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hp).2.2
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ p,
        (Finset.mem_filter.mp hp).2.1, hi⟩⟩
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        ∃ i,
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
            ρ * δ * S₀.card).card
        ≤ (Finset.univ.biUnion P).card := Finset.card_le_card hsub
    _ ≤ ∑ i : I, (P i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I,
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
          S.card * b) := Finset.sum_le_sum fun i _hi ↦ hP i
    _ = Fintype.card I *
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
          S.card * b) := by simp

/-- Before excluding repeated endpoints, at least three quarters of the
ordered tuples have all private neighborhoods of the required size. -/
lemma three_mul_tuple_count_le_four_mul_card_good_private
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (q b : ℕ) (default : V × V)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀) (hρ : 0 ≤ ρ)
    (hcommon : ∀ i (p : I → V × V), (∀ j, p j ∈ S ×ˢ S) →
      δ * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ α ≤ b)
    (hsmall : 4 * (Fintype.card I *
      ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b)) ≤
      (switchingPairs G S S₀ q).card ^ Fintype.card I) :
    3 * (switchingPairs G S S₀ q).card ^ Fintype.card I ≤
      4 * ((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          ∀ i, ρ * δ * S₀.card ≤
            ((switchingPrivateNeighbors G p i S₀).card : ℝ)).card := by
  classical
  let A : Finset (I → V × V) :=
    (Finset.univ : Finset (I → V × V)).filter fun p ↦
      ∀ j, p j ∈ switchingPairs G S S₀ q
  let Good : Finset (I → V × V) := A.filter fun p ↦
    ∀ i, ρ * δ * S₀.card ≤
      ((switchingPrivateNeighbors G p i S₀).card : ℝ)
  let Bad := A \ Good
  have hGoodSub : Good ⊆ A := Finset.filter_subset _ _
  have hBadEq : Bad =
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          ∃ i,
            ((switchingPrivateNeighbors G p i S₀).card : ℝ) <
              ρ * δ * S₀.card) := by
    ext p
    simp only [Bad, Good, A, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hT, hnot⟩
      refine ⟨hT, ?_⟩
      by_contra hnone
      push_neg at hnone
      exact hnot ⟨hT, hnone⟩
    · rintro ⟨hT, i, hi⟩
      refine ⟨hT, ?_⟩
      rintro ⟨_hT', hall⟩
      exact (not_le_of_gt hi) (hall i)
  have hBad := card_tuples_with_some_bad_private_le
    G S S₀ δ ρ α q b default hrich hSS₀ hρ hcommon hbudget
  have hBadSmall : 4 * Bad.card ≤ A.card := by
    rw [hBadEq]
    exact (Nat.mul_le_mul_left 4 hBad).trans (by
      simpa only [A, card_tupleFunctions] using hsmall)
  have hpartition : A.card = Good.card + Bad.card := by
    have hcard := Finset.card_le_card hGoodSub
    dsimp only [Bad]
    rw [Finset.card_sdiff_of_subset hGoodSub]
    omega
  have hmain : 3 * A.card ≤ 4 * Good.card := by omega
  have hGoodEq : Good =
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          ∀ i, ρ * δ * S₀.card ≤
            ((switchingPrivateNeighbors G p i S₀).card : ℝ)) := by
    ext p
    simp only [Good, A, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hGoodEq] at hmain
  simpa only [A, card_tupleFunctions] using hmain

/-- Finite combinatorial form of KSSS Lemma 13.10(a).  The two displayed
smallness assumptions are exactly the coordinate-union and endpoint-repeat
estimates; the source asymptotics make both automatic. -/
lemma switchingTuple_good_half
    (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
    (q b : ℕ) (default : V × V)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀) (hρ : 0 ≤ ρ)
    (hcommon : ∀ i (p : I → V × V), (∀ j, p j ∈ S ×ˢ S) →
      δ * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ α ≤ b)
    (hsmallPrivate : 4 * (Fintype.card I *
      ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b)) ≤
      (switchingPairs G S S₀ q).card ^ Fintype.card I)
    (hsmallRepeat : 4 * ((2 * Fintype.card I) ^ 2 *
      ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card)) ≤
      (switchingPairs G S S₀ q).card ^ Fintype.card I) :
    (switchingPairs G S S₀ q).card ^ Fintype.card I ≤
      2 * ((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          PairEndpointsDistinct p ∧
            ∀ i, ρ * δ * S₀.card ≤
              ((switchingPrivateNeighbors G p i S₀).card : ℝ)).card := by
  classical
  let T := switchingPairs G S S₀ q
  let GoodPrivate : Finset (I → V × V) :=
    (Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧
        ∀ i, ρ * δ * S₀.card ≤
          ((switchingPrivateNeighbors G p i S₀).card : ℝ)
  let Good : Finset (I → V × V) :=
    GoodPrivate.filter PairEndpointsDistinct
  let Repeated := GoodPrivate \ Good
  let AllRepeated : Finset (I → V × V) :=
    (Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧ ¬PairEndpointsDistinct p
  have hthree : 3 * T.card ^ Fintype.card I ≤ 4 * GoodPrivate.card := by
    simpa only [T, GoodPrivate] using
      three_mul_tuple_count_le_four_mul_card_good_private
        G S S₀ δ ρ α q b default hrich hSS₀ hρ hcommon hbudget
          hsmallPrivate
  have hGoodSub : Good ⊆ GoodPrivate := Finset.filter_subset _ _
  have hRepeatedSub : Repeated ⊆ AllRepeated := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hpPrivate := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, hpPrivate.2.1, ?_⟩
    intro hdistinct
    exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, hdistinct⟩)
  have hAllRepeated := card_tuples_with_repeated_endpoint_le (I := I)
    T S (by
      intro yz hyz
      have hyz' := (mem_switchingPairs_iff G S S₀ q yz.1 yz.2).mp hyz
      exact Finset.mem_product.mpr ⟨hyz'.1, hyz'.2.1⟩) default
  have hRepeatedSmall : 4 * Repeated.card ≤ T.card ^ Fintype.card I := by
    calc
      4 * Repeated.card ≤ 4 * AllRepeated.card :=
        Nat.mul_le_mul_left 4 (Finset.card_le_card hRepeatedSub)
      _ ≤ 4 * ((2 * Fintype.card I) ^ 2 *
          (T.card ^ (Fintype.card I - 1) * S.card)) :=
        Nat.mul_le_mul_left 4 hAllRepeated
      _ ≤ T.card ^ Fintype.card I := by
        simpa only [T] using hsmallRepeat
  have hpartition : GoodPrivate.card = Good.card + Repeated.card := by
    have hcard := Finset.card_le_card hGoodSub
    dsimp only [Repeated]
    rw [Finset.card_sdiff_of_subset hGoodSub]
    omega
  have hmain : T.card ^ Fintype.card I ≤ 2 * Good.card := by omega
  have hGoodEq : Good =
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          PairEndpointsDistinct p ∧
            ∀ i, ρ * δ * S₀.card ≤
              ((switchingPrivateNeighbors G p i S₀).card : ℝ)) := by
    ext p
    simp only [Good, GoodPrivate, T, Finset.mem_filter, Finset.mem_univ,
      true_and]
    aesop
  rw [hGoodEq] at hmain
  simpa only [T] using hmain

/-- KSSS Lemma 13.10(b) with the determining index set fixed.  There are at
most `|T|^|B|` assignments on the determining rows, and the previous lemma
bounds every corresponding extension fiber. -/
lemma card_tuples_with_fixed_basis_exceptional_certificate_le
    (G : SimpleGraph V) (S S₀ : Finset V) (T : Finset (V × V))
    (δ ρ α : ℝ) (m b : ℕ) (B : Finset I) (default : V × V)
    (hrich : RichOn G S₀ δ ρ α)
    (hSS₀ : S ⊆ S₀) (hT : T ⊆ S ×ˢ S)
    (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ T) ∧
        ∀ j, j ∉ B →
          ∃ t : B → Fin 3,
            m ≤ (switchingColumnFiber G p B S₀ t).card ∧
              (p j).1 ∈ lowExceptionalVertices G
                (switchingColumnFiber G p B S₀ t) ρ ∧
              (p j).2 ∈ highExceptionalVertices G
                (switchingColumnFiber G p B S₀ t) ρ).card ≤
      T.card ^ B.card *
        (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) := by
  classical
  let assignments : Finset (B → V × V) :=
    Fintype.piFinset fun _i : B ↦ T
  let P : (B → V × V) → Finset (I → V × V) := fun a ↦
    let r := extendFinsetAssignment B default a
    (Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ S ×ˢ S) ∧
        (∀ j ∈ B, p j = r j) ∧
          ∀ j, j ∉ B →
            ∃ t : B → Fin 3,
              m ≤ (switchingColumnFiber G r B S₀ t).card ∧
                (p j).1 ∈ lowExceptionalVertices G
                  (switchingColumnFiber G r B S₀ t) ρ ∧
                (p j).2 ∈ highExceptionalVertices G
                  (switchingColumnFiber G r B S₀ t) ρ
  have hPcard : ∀ a, (P a).card ≤
      (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) := by
    intro a
    simpa only [P] using card_fixed_basis_exceptional_tuples_le
      G S S₀ δ ρ α m b B (extendFinsetAssignment B default a)
      hrich hSS₀ hsize hbudget
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ T) ∧
          ∀ j, j ∉ B →
            ∃ t : B → Fin 3,
              m ≤ (switchingColumnFiber G p B S₀ t).card ∧
                (p j).1 ∈ lowExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ ∧
                (p j).2 ∈ highExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ) ⊆
        assignments.biUnion P := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    let a : B → V × V := fun i ↦ p i.1
    have ha : a ∈ assignments := by
      apply Fintype.mem_piFinset.mpr
      intro i
      exact hp'.1 i.1
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_, ?_, ?_⟩
    · intro j
      exact hT (hp'.1 j)
    · intro j hj
      simpa only [a, extendFinsetAssignment_apply_mem a hj]
    · intro j hj
      obtain ⟨t, ht, hy, hz⟩ := hp'.2 j hj
      have hEqOn : ∀ i ∈ B,
          p i = extendFinsetAssignment B default a i := by
        intro i hi
        simpa only [a, extendFinsetAssignment_apply_mem a hi]
      have hfiber := switchingColumnFiber_eq_of_eq_on
        (G := G) (A := S₀) (t := t) hEqOn
      exact ⟨t, by simpa only [hfiber] using ht,
        by simpa only [hfiber] using hy,
        by simpa only [hfiber] using hz⟩
  have hassignments : assignments.card = T.card ^ B.card := by
    simp only [assignments, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ T) ∧
          ∀ j, j ∉ B →
            ∃ t : B → Fin 3,
              m ≤ (switchingColumnFiber G p B S₀ t).card ∧
                (p j).1 ∈ lowExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ ∧
                (p j).2 ∈ highExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ).card
        ≤ (assignments.biUnion P).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ assignments, (P a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ assignments,
        (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) :=
      Finset.sum_le_sum fun a _ha ↦ hPcard a
    _ = T.card ^ B.card *
        (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) := by
      simp [hassignments]

/-- Finite counting core of KSSS Lemma 13.10(b).  The matrix argument supplies
one determining set `B` for every degenerate tuple; taking the union over all
subsets of the row index set costs only `2^s`.  Thus the sole remaining input
is the displayed numerical upper bound for a fixed `B`. -/
lemma card_kDegenerate_switchingTuples_le
    (G : SimpleGraph V) (S S₀ : Finset V)
    (δ ρ α : ℝ) (q budget k m b M : ℕ) (default : V × V)
    (hm : 0 < m) (hρ : 0 ≤ ρ)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q)
    (hscale : ((budget + 2 : ℕ) : ℝ) ≤ ρ * m)
    (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b)
    (hfixed : ∀ B : Finset I, B.card ≤ Fintype.card I - k →
      (switchingPairs G S S₀ q).card ^ B.card *
          (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) ≤ M) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        IsKDegenerate G p budget k).card ≤
      2 ^ Fintype.card I * M := by
  classical
  let T := switchingPairs G S S₀ q
  let d := Fintype.card I - k
  let P : Finset I → Finset (I → V × V) := fun B ↦
    if hB : B.card ≤ d then
      (Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ T) ∧
          ∀ j, j ∉ B →
            ∃ t : B → Fin 3,
              m ≤ (switchingColumnFiber G p B S₀ t).card ∧
                (p j).1 ∈ lowExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ ∧
                (p j).2 ∈ highExceptionalVertices G
                  (switchingColumnFiber G p B S₀ t) ρ
    else ∅
  have hTsub : T ⊆ S ×ˢ S := by
    intro yz hyz
    have h := (mem_switchingPairs_iff G S S₀ q yz.1 yz.2).mp hyz
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
  have hPcard : ∀ B, (P B).card ≤ M := by
    intro B
    by_cases hB : B.card ≤ d
    · have hcard := card_tuples_with_fixed_basis_exceptional_certificate_le
        G S S₀ T δ ρ α m b B default hrich hSS₀ hTsub hsize hbudget
      have hcard' : (P B).card ≤
          T.card ^ B.card *
            (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card) := by
        simpa only [P, dif_pos hB] using hcard
      exact hcard'.trans (by simpa only [T, d] using hfixed B hB)
    · simp [P, hB]
  have hsub :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          IsKDegenerate G p budget k) ⊆
        Finset.univ.powerset.biUnion P := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    obtain ⟨Q, B, hQ, hB, hcert⟩ :=
      hp'.2.exists_switching_fibers_with_exceptional_endpoints
        hm hρ hp'.1 hsupply hscale
    rw [Finset.mem_biUnion]
    refine ⟨B, Finset.mem_powerset.mpr (Finset.subset_univ B), ?_⟩
    have hBd : B.card ≤ d := by simpa only [d] using hB
    simp only [P, dif_pos hBd]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_, ?_⟩
    · simpa only [T] using hp'.1
    · intro j _hj
      exact hcert j
  calc
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          IsKDegenerate G p budget k).card
        ≤ (Finset.univ.powerset.biUnion P).card := Finset.card_le_card hsub
    _ ≤ ∑ B ∈ Finset.univ.powerset, (P B).card := Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ Finset.univ.powerset, M :=
      Finset.sum_le_sum fun B _hB ↦ hPcard B
    _ = 2 ^ Fintype.card I * M := by
      simp [Finset.card_powerset]

/-- Part (b) of KSSS Lemma 13.10 at `k = 0`: every tuple is
zero-degenerate, so the upper bound is exactly `|T|^s`. -/
lemma card_zeroDegenerate_switchingTuples
    (G : SimpleGraph V) (S S₀ : Finset V) (q budget : ℕ) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        IsKDegenerate G p budget 0).card =
      (switchingPairs G S S₀ q).card ^ Fintype.card I := by
  classical
  have heq :
      (Finset.univ : Finset (I → V × V)).filter (fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          IsKDegenerate G p budget 0) =
        (Finset.univ : Finset (I → V × V)).filter (fun p ↦
          ∀ j, p j ∈ switchingPairs G S S₀ q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hp
      exact ⟨hp, isKDegenerate_zero G p budget⟩
  rw [heq, card_tupleFunctions]

/-- Moving factors from the smaller base `c` to the larger base `a` can only
increase a product of fixed total degree. -/
lemma pow_mul_pow_le_pow_mul_pow_of_le
    {a c i s k : ℕ} (hk : k ≤ s) (hi : i ≤ s - k) (hca : c ≤ a) :
    a ^ i * c ^ (s - i) ≤ a ^ (s - k) * c ^ k := by
  let r := (s - k) - i
  have hsik : s - i = k + r := by
    dsimp [r]
    omega
  have hski : s - k = i + r := by
    dsimp [r]
    omega
  calc
    a ^ i * c ^ (s - i) = c ^ k * (a ^ i * c ^ r) := by
      rw [hsik, pow_add]
      ac_rfl
    _ ≤ c ^ k * (a ^ i * a ^ r) := by
      exact Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hca r))
    _ = a ^ (s - k) * c ^ k := by
      rw [hski, pow_add]
      ac_rfl

/-- Uniform finite form of KSSS Lemma 13.10(b).  The code/fiber choice count
`c = 3^(s-k)b²` is assumed no larger than the switching reservoir; this turns
the fixed-basis estimate into total degree `s`. -/
lemma card_kDegenerate_switchingTuples_le_uniform
    (G : SimpleGraph V) (S S₀ : Finset V)
    (δ ρ α : ℝ) (q budget k m b : ℕ) (default : V × V)
    (hk : k ≤ Fintype.card I)
    (hm : 0 < m) (hρ : 0 ≤ ρ)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q)
    (hscale : ((budget + 2 : ℕ) : ℝ) ≤ ρ * m)
    (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b)
    (hchoice : 3 ^ (Fintype.card I - k) * (b * b) ≤
      (switchingPairs G S S₀ q).card) :
    ((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        IsKDegenerate G p budget k).card ≤
      2 ^ Fintype.card I *
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - k) *
          (3 ^ (Fintype.card I - k) * (b * b)) ^ k) := by
  apply card_kDegenerate_switchingTuples_le G S S₀ δ ρ α q budget k m b
    ((switchingPairs G S S₀ q).card ^ (Fintype.card I - k) *
      (3 ^ (Fintype.card I - k) * (b * b)) ^ k)
    default hm hρ hrich hSS₀ hsupply hscale hsize hbudget
  intro B hB
  let c := 3 ^ (Fintype.card I - k) * (b * b)
  have hcode : 3 ^ B.card * (b * b) ≤ c := by
    exact Nat.mul_le_mul_right (b * b)
      (Nat.pow_le_pow_right (by omega) hB)
  calc
    (switchingPairs G S S₀ q).card ^ B.card *
        (3 ^ B.card * (b * b)) ^ (Fintype.card I - B.card)
        ≤ (switchingPairs G S S₀ q).card ^ B.card *
            c ^ (Fintype.card I - B.card) := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcode _)
    _ ≤ (switchingPairs G S S₀ q).card ^ (Fintype.card I - k) *
          c ^ k :=
      pow_mul_pow_le_pow_mul_pow_of_le hk hB hchoice

/-- Real-valued source normalization of Lemma 13.10(b).  The single
inequality `hratio` is exactly the eventual numerical comparison left after
the finite graph/matrix counting argument. -/
lemma card_kDegenerate_switchingTuples_le_div_sqrt
    (G : SimpleGraph V) (S S₀ : Finset V)
    (δ ρ α : ℝ) (q budget k m b n : ℕ) (default : V × V)
    (hk : k ≤ Fintype.card I) (hn : 0 < n)
    (hm : 0 < m) (hρ : 0 ≤ ρ)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀)
    (hsupply : 3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q)
    (hscale : ((budget + 2 : ℕ) : ℝ) ≤ ρ * m)
    (hsize : δ * S₀.card ≤ m)
    (hbudget : (S₀.card : ℝ) ^ α ≤ b)
    (hchoice : 3 ^ (Fintype.card I - k) * (b * b) ≤
      (switchingPairs G S S₀ q).card)
    (hratio :
      ((2 ^ Fintype.card I : ℕ) : ℝ) *
          ((3 ^ (Fintype.card I - k) * (b * b) : ℕ) : ℝ) ^ k *
          Real.sqrt n ^ k ≤
        ((switchingPairs G S S₀ q).card : ℝ) ^ k) :
    (((Finset.univ : Finset (I → V × V)).filter fun p ↦
      (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
        IsKDegenerate G p budget k).card : ℝ) ≤
      ((switchingPairs G S S₀ q).card : ℝ) ^ Fintype.card I /
        Real.sqrt n ^ k := by
  have hfinite := card_kDegenerate_switchingTuples_le_uniform
    G S S₀ δ ρ α q budget k m b default hk hm hρ hrich hSS₀
    hsupply hscale hsize hbudget hchoice
  have hfiniteReal :
      (((Finset.univ : Finset (I → V × V)).filter fun p ↦
        (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
          IsKDegenerate G p budget k).card : ℝ) ≤
        ((2 ^ Fintype.card I : ℕ) : ℝ) *
          ((switchingPairs G S S₀ q).card : ℝ) ^
            (Fintype.card I - k) *
          ((3 ^ (Fintype.card I - k) * (b * b) : ℕ) : ℝ) ^ k := by
    have hcast :
        (((Finset.univ : Finset (I → V × V)).filter fun p ↦
          (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
            IsKDegenerate G p budget k).card : ℝ) ≤
          ((2 ^ Fintype.card I *
            ((switchingPairs G S S₀ q).card ^ (Fintype.card I - k) *
              (3 ^ (Fintype.card I - k) * (b * b)) ^ k) : ℕ) : ℝ) := by
      exact_mod_cast hfinite
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hcast
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  apply hfiniteReal.trans
  rw [le_div_iff₀ (pow_pos hsqrt k)]
  calc
    (((2 ^ Fintype.card I : ℕ) : ℝ) *
          ((switchingPairs G S S₀ q).card : ℝ) ^
            (Fintype.card I - k) *
          ((3 ^ (Fintype.card I - k) * (b * b) : ℕ) : ℝ) ^ k) *
        Real.sqrt n ^ k
        = ((switchingPairs G S S₀ q).card : ℝ) ^
            (Fintype.card I - k) *
          (((2 ^ Fintype.card I : ℕ) : ℝ) *
            ((3 ^ (Fintype.card I - k) * (b * b) : ℕ) : ℝ) ^ k *
            Real.sqrt n ^ k) := by ring
    _ ≤ ((switchingPairs G S S₀ q).card : ℝ) ^
          (Fintype.card I - k) *
        ((switchingPairs G S S₀ q).card : ℝ) ^ k := by
      gcongr
    _ = ((switchingPairs G S S₀ q).card : ℝ) ^ Fintype.card I := by
      rw [← pow_add]
      congr 1
      omega

/-- A fixed constant times a smaller positive power is eventually bounded by
a larger power. -/
lemma eventually_const_mul_natCast_rpow_le_rpow
    (C a d : ℝ) (hd : 0 < d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ^ a ≤ (n : ℝ) ^ (a + d) := by
  have hgrow : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ d :=
    ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop C)
  filter_upwards [Filter.eventually_ge_atTop 1, hgrow] with n hn hC
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ d * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hn0 a)
    _ = (n : ℝ) ^ (a + d) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- The numerical comparison used in KSSS Lemma 13.10(b) is automatic for
large `n`, uniformly for `1 ≤ k ≤ s ≤ D`.  Here the richness budget is
rounded up from `n^(1/5)` and the switching reservoir has the source lower
bound `n^(24/25)/4`. -/
lemma eventually_switchingDegeneracy_ratio (D : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s k T : ℕ,
      s ≤ D → 0 < k → k ≤ s →
        (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤ T →
          let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
          let c := 3 ^ (s - k) * (b * b)
          c ≤ T ∧
            ((2 ^ s : ℕ) : ℝ) * (c : ℝ) ^ k *
                Real.sqrt n ^ k ≤ (T : ℝ) ^ k := by
  let C : ℝ := 16 * ((2 ^ D : ℕ) : ℝ) * ((3 ^ D : ℕ) : ℝ)
  have hgap : ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ^ (9 / 10 : ℝ) ≤
        (n : ℝ) ^ (24 / 25 : ℝ) := by
    have h := eventually_const_mul_natCast_rpow_le_rpow
      C (9 / 10 : ℝ) (3 / 50 : ℝ) (by norm_num)
    convert h using 1
    norm_num
  filter_upwards [Filter.eventually_ge_atTop 1, hgap] with n hn hgapn
  intro s k T hsD hkpos hks hT
  let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
  let c := 3 ^ (s - k) * (b * b)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hb : (b : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hceil := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg hnpos.le (1 / 5 : ℝ))).le
    change ((⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ _
    nlinarith
  have hpowsq : ((n : ℝ) ^ (1 / 5 : ℝ)) ^ 2 =
      (n : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hbSq : ((b * b : ℕ) : ℝ) ≤
      4 * (n : ℝ) ^ (2 / 5 : ℝ) := by
    have hsquare : (b : ℝ) ^ 2 ≤
        (2 * (n : ℝ) ^ (1 / 5 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    calc
      ((b * b : ℕ) : ℝ) = (b : ℝ) ^ 2 := by push_cast; ring
      _ ≤ (2 * (n : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := hsquare
      _ = 4 * (n : ℝ) ^ (2 / 5 : ℝ) := by
        rw [mul_pow, hpowsq]
        norm_num
  have hthree : ((3 ^ (s - k) : ℕ) : ℝ) ≤ (3 ^ D : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  have hc : (c : ℝ) ≤
      4 * ((3 ^ D : ℕ) : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) := by
    calc
      (c : ℝ) = ((3 ^ (s - k) : ℕ) : ℝ) * ((b * b : ℕ) : ℝ) := by
        simp [c]
      _ ≤
          ((3 ^ D : ℕ) : ℝ) *
            (4 * (n : ℝ) ^ (2 / 5 : ℝ)) := by
        exact mul_le_mul hthree hbSq (by positivity) (by positivity)
      _ = 4 * ((3 ^ D : ℕ) : ℝ) *
          (n : ℝ) ^ (2 / 5 : ℝ) := by ring
  have htwo : ((2 ^ s : ℕ) : ℝ) ≤ (2 ^ D : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) hsD
  have hpowsqrt : (n : ℝ) ^ (2 / 5 : ℝ) * Real.sqrt n =
      (n : ℝ) ^ (9 / 10 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    norm_num
  have hbaseGrowth :
      ((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n ≤
        (n : ℝ) ^ (24 / 25 : ℝ) / 4 := by
    have hpre :
        ((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n ≤
          4 * ((2 ^ D : ℕ) : ℝ) * ((3 ^ D : ℕ) : ℝ) *
            (n : ℝ) ^ (9 / 10 : ℝ) := by
      calc
        ((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n ≤
            ((2 ^ D : ℕ) : ℝ) *
              (4 * ((3 ^ D : ℕ) : ℝ) *
                (n : ℝ) ^ (2 / 5 : ℝ)) * Real.sqrt n := by
          gcongr
        _ = 4 * ((2 ^ D : ℕ) : ℝ) * ((3 ^ D : ℕ) : ℝ) *
            (n : ℝ) ^ (9 / 10 : ℝ) := by rw [← hpowsqrt]; ring
    have hgapn' :
        16 * ((2 ^ D : ℕ) : ℝ) * ((3 ^ D : ℕ) : ℝ) *
            (n : ℝ) ^ (9 / 10 : ℝ) ≤
          (n : ℝ) ^ (24 / 25 : ℝ) := by
      simpa only [C] using hgapn
    linarith
  have hbase :
      ((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n ≤ T :=
    hbaseGrowth.trans hT
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.one_le_rpow hnR (by norm_num)
  have htwo1 : (1 : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow s 2 (by omega))
  have hcTReal : (c : ℝ) ≤ T := by
    calc
      (c : ℝ) = 1 * (c : ℝ) * 1 := by ring
      _ ≤ ((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n := by
        gcongr
      _ ≤ T := hbase
  have hcT : c ≤ T := by exact_mod_cast hcTReal
  refine ⟨hcT, ?_⟩
  have htwoSelf : ((2 ^ s : ℕ) : ℝ) ≤
      ((2 ^ s : ℕ) : ℝ) ^ k :=
    le_self_pow₀ htwo1 (Nat.ne_of_gt hkpos)
  calc
    ((2 ^ s : ℕ) : ℝ) * (c : ℝ) ^ k * Real.sqrt n ^ k ≤
        ((2 ^ s : ℕ) : ℝ) ^ k * (c : ℝ) ^ k *
          Real.sqrt n ^ k := by gcongr
    _ = (((2 ^ s : ℕ) : ℝ) * (c : ℝ) * Real.sqrt n) ^ k := by
      simp only [mul_pow]
    _ ≤ (T : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hbase k

/-- Source-shaped eventual form of KSSS Lemma 13.10(b), for positive
degeneracy.  All graph and richness hypotheses remain quantified after the
single threshold depending only on the bounded tuple dimension `D`. -/
lemma eventually_card_kDegenerate_switchingTuples_le_div_sqrt
    (D : ℕ) (hI : Fintype.card I ≤ D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
        (q budget k m : ℕ) (default : V × V),
        0 < k → k ≤ Fintype.card I →
        0 < m → 0 ≤ ρ → RichOn G S₀ δ ρ α → S ⊆ S₀ →
        3 ^ (Fintype.card I - k) * m + budget + 2 ≤ q →
        ((budget + 2 : ℕ) : ℝ) ≤ ρ * m →
        δ * S₀.card ≤ m →
        (S₀.card : ℝ) ^ α ≤
          ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ →
        (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤
          (switchingPairs G S S₀ q).card →
        (((Finset.univ : Finset (I → V × V)).filter fun p ↦
          (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
            IsKDegenerate G p budget k).card : ℝ) ≤
          ((switchingPairs G S S₀ q).card : ℝ) ^ Fintype.card I /
            Real.sqrt n ^ k := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_switchingDegeneracy_ratio D] with n hn hratio
  intro G S S₀ δ ρ α q budget k m default hk hkI hm hρ hrich hSS₀
    hsupply hscale hsize hbudget hT
  have hnum := hratio (Fintype.card I) k
    (switchingPairs G S S₀ q).card hI hk hkI hT
  exact card_kDegenerate_switchingTuples_le_div_sqrt
    G S S₀ δ ρ α q budget k m
      ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ n default
    hkI (by omega) hm hρ hrich hSS₀ hsupply hscale hsize hbudget
    hnum.1 hnum.2

/-- The two numerical smallness conditions in Lemma 13.10(a) follow
uniformly, for bounded positive tuple dimension, from the source reservoir
bound `|T| ≥ |S| n^(12/25)/2`. -/
lemma eventually_switchingTuple_good_smallness (D : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s S T : ℕ,
      0 < s → s ≤ D →
        (S : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤ T →
          let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
          4 * (s * (T ^ (s - 1) * S * b)) ≤ T ^ s ∧
            4 * ((2 * s) ^ 2 * (T ^ (s - 1) * S)) ≤ T ^ s := by
  have hprivateGrowth : ∀ᶠ n : ℕ in Filter.atTop,
      (16 * (D : ℝ)) * (n : ℝ) ^ (1 / 5 : ℝ) ≤
        (n : ℝ) ^ (12 / 25 : ℝ) := by
    have h := eventually_const_mul_natCast_rpow_le_rpow
      (16 * (D : ℝ)) (1 / 5 : ℝ) (7 / 25 : ℝ) (by norm_num)
    convert h using 1
    norm_num
  have hrepeatGrowth : ∀ᶠ n : ℕ in Filter.atTop,
      (32 * (D : ℝ) ^ 2) ≤ (n : ℝ) ^ (12 / 25 : ℝ) := by
    have h := eventually_const_mul_natCast_rpow_le_rpow
      (32 * (D : ℝ) ^ 2) 0 (12 / 25 : ℝ) (by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop 1] with n hn hn1
    simpa only [Real.rpow_zero, mul_one, zero_add] using hn
  filter_upwards [Filter.eventually_ge_atTop 1, hprivateGrowth,
    hrepeatGrowth] with n hn hgrowthP hgrowthR
  intro s S T hs hsD hT
  let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hb : (b : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hceil := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg hnpos.le (1 / 5 : ℝ))).le
    change ((⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ _
    nlinarith
  have hsR : (s : ℝ) ≤ D := by exact_mod_cast hsD
  have hcoefP : 4 * (s : ℝ) * (b : ℝ) ≤
      8 * (D : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) := by
    calc
      4 * (s : ℝ) * (b : ℝ) ≤
          4 * (D : ℝ) * (2 * (n : ℝ) ^ (1 / 5 : ℝ)) := by
        gcongr
      _ = 8 * (D : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) := by ring
  have hbasePReal : ((4 * s * S * b : ℕ) : ℝ) ≤ T := by
    calc
      ((4 * s * S * b : ℕ) : ℝ) =
          (S : ℝ) * (4 * (s : ℝ) * (b : ℝ)) := by push_cast; ring
      _ ≤ (S : ℝ) *
          (8 * (D : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcoefP (by positivity)
      _ ≤ (S : ℝ) * ((n : ℝ) ^ (12 / 25 : ℝ) / 2) := by
        gcongr
        linarith
      _ = (S : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by ring
      _ ≤ T := hT
  have hbaseP : 4 * s * S * b ≤ T := by exact_mod_cast hbasePReal
  have hcoefR : 16 * (s : ℝ) ^ 2 ≤ 16 * (D : ℝ) ^ 2 := by
    gcongr
  have hbaseRReal : ((4 * (2 * s) ^ 2 * S : ℕ) : ℝ) ≤ T := by
    calc
      ((4 * (2 * s) ^ 2 * S : ℕ) : ℝ) =
          (S : ℝ) * (16 * (s : ℝ) ^ 2) := by push_cast; ring
      _ ≤ (S : ℝ) * (16 * (D : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcoefR (by positivity)
      _ ≤ (S : ℝ) * ((n : ℝ) ^ (12 / 25 : ℝ) / 2) := by
        gcongr
        linarith
      _ = (S : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by ring
      _ ≤ T := hT
  have hbaseR : 4 * (2 * s) ^ 2 * S ≤ T := by
    exact_mod_cast hbaseRReal
  constructor
  · calc
      4 * (s * (T ^ (s - 1) * S * b)) =
          T ^ (s - 1) * (4 * s * S * b) := by ring
      _ ≤ T ^ (s - 1) * T := Nat.mul_le_mul_left _ hbaseP
      _ = T ^ s := by rw [← pow_succ]; congr 1; omega
  · calc
      4 * ((2 * s) ^ 2 * (T ^ (s - 1) * S)) =
          T ^ (s - 1) * (4 * (2 * s) ^ 2 * S) := by ring
      _ ≤ T ^ (s - 1) * T := Nat.mul_le_mul_left _ hbaseR
      _ = T ^ s := by rw [← pow_succ]; congr 1; omega

/-- Source-shaped eventual form of KSSS Lemma 13.10(a).  The only
structural input left is precisely property (2) of Lemma 13.1. -/
lemma eventually_switchingTuple_good_half_of_commonNonneighbors (D : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph V) (S S₀ : Finset V) (δ ρ α : ℝ)
        (q : ℕ) (default : V × V),
        0 < Fintype.card I → 2 * Fintype.card I ≤ D →
        RichOn G S₀ δ ρ α → S ⊆ S₀ → 0 ≤ ρ →
        HasLargeCommonNonneighbors G S S₀ δ D →
        (S₀.card : ℝ) ^ α ≤
          ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ →
        (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
          (switchingPairs G S S₀ q).card →
        (switchingPairs G S S₀ q).card ^ Fintype.card I ≤
          2 * ((Finset.univ : Finset (I → V × V)).filter fun p ↦
            (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
              PairEndpointsDistinct p ∧
                ∀ i, ρ * δ * S₀.card ≤
                  ((switchingPrivateNeighbors G p i S₀).card : ℝ)).card := by
  filter_upwards [eventually_switchingTuple_good_smallness D] with n hsmall
  intro G S S₀ δ ρ α q default hIpos hID hrich hSS₀ hρ hcommon
    hbudget hT
  have hnum := hsmall (Fintype.card I) S.card
    (switchingPairs G S S₀ q).card hIpos (by omega) hT
  exact switchingTuple_good_half G S S₀ δ ρ α q
    ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ default hrich hSS₀ hρ
    (fun i p hp ↦ hcommon.on_switchingOtherEndpoints hID p hp i)
    hbudget hnum.1 hnum.2

end TupleMatrix

end Erdos88.Switching
