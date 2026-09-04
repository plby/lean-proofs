import Mathlib

/-!
# Petrov's odd-transversal parity lemma

This file develops the finite parity statement used in the proof of Erdős
Problem 842.  A transversal chooses one point from each of finitely many odd
parts.  The relation between distinct parts is symmetric and all of its
bipartite degrees are even.  Petrov's lemma says that an odd number of
transversals have even selected degree at every part.
-/

open scoped BigOperators

namespace Erdos842

namespace OddTransversal

universe u v

variable {I : Type u} (X : I → Type v)

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A relation between elements belonging to indexed (and possibly dependent) parts. -/
abbrev CrossRel := ∀ i j : I, X i → X j → Prop

/-- Symmetry of a relation between dependent parts. -/
def Symmetric (cross : CrossRel X) : Prop :=
  ∀ i j xi xj, cross i j xi xj ↔ cross j i xj xi

/-- The selected cross-degree of part `i` in the transversal `f`.

The explicit inequality excludes the diagonal part, so no assumption on
`cross i i` is needed by the parity theorem.
-/
noncomputable def selectedDegree [Fintype I] [DecidableEq I]
    (cross : CrossRel X) (f : ∀ i, X i) (i : I) : ℕ :=
  by
    classical
    exact ((Finset.univ.erase i).filter fun j ↦ cross i j (f i) (f j)).card

/-- A transversal is good when every selected cross-degree is even. -/
def Good [Fintype I] [DecidableEq I]
    (cross : CrossRel X) (f : ∀ i, X i) : Prop :=
  ∀ i, Even (selectedDegree X cross f i)

/-- The bipartite degree from a point of part `i` into part `j`. -/
noncomputable def crossDegree
    (cross : CrossRel X) (i j : I) [Fintype (X j)] (xi : X i) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset (X j)).filter fun xj ↦ cross i j xi xj).card

/-- The set of good transversals, as a finite subtype. -/
def goodTransversals [Fintype I] [DecidableEq I]
    [∀ i, Fintype (X i)] (cross : CrossRel X) : Type _ :=
  {f : ∀ i, X i // Good X cross f}

noncomputable instance [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) : Fintype (goodTransversals X cross) :=
  by
    classical
    letI : Fintype (∀ i, X i) := Pi.instFintype
    exact Subtype.fintype _

/-! ## Elementary parity interfaces -/

lemma odd_iff_cast_zmod_two_eq_one (m : ℕ) :
    Odd m ↔ (m : ZMod 2) = 1 := by
  constructor
  · rw [Nat.odd_iff]
    intro h
    rw [← ZMod.natCast_mod m 2, h]
    rfl
  · intro h
    rw [Nat.odd_iff]
    exact Nat.mod_eq_of_modEq ((ZMod.natCast_eq_natCast_iff m 1 2).mp h) (by omega)

lemma even_iff_cast_zmod_two_eq_zero (m : ℕ) :
    Even m ↔ (m : ZMod 2) = 0 := by
  constructor
  · rw [Nat.even_iff]
    intro h
    rw [← ZMod.natCast_mod m 2, h]
    rfl
  · intro h
    rw [Nat.even_iff]
    exact Nat.mod_eq_of_modEq ((ZMod.natCast_eq_natCast_iff m 0 2).mp h) (by omega)

lemma cast_card_filter_eq_sum_indicator
    {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    ((Finset.univ.filter p).card : ZMod 2) =
      ∑ a : A, if p a then 1 else 0 := by
  simp

lemma cast_card_subtype_eq_sum_indicator
    {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    (Fintype.card {a : A // p a} : ZMod 2) =
      ∑ a : A, if p a then 1 else 0 := by
  rw [Fintype.card_subtype]
  exact cast_card_filter_eq_sum_indicator p

lemma indicator_even_degree (m : ℕ) :
    (if Even m then (1 : ZMod 2) else 0) = 1 + (m : ZMod 2) := by
  by_cases h : Even m
  · simp [h, (even_iff_cast_zmod_two_eq_zero m).mp h]
  · have hm : (m : ZMod 2) = 1 :=
      (odd_iff_cast_zmod_two_eq_one m).mp (Nat.not_even_iff_odd.mp h)
    rw [if_neg h, hm]
    decide

lemma indicator_good_eq_prod (cross : CrossRel X)
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (f : ∀ i, X i) :
    (if Good X cross f then (1 : ZMod 2) else 0) =
      ∏ i : I, (1 + (selectedDegree X cross f i : ZMod 2)) := by
  classical
  by_cases h : Good X cross f
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro i _
    rw [← indicator_even_degree]
    simp [h i]
  · rw [if_neg h]
    have hn : ¬ ∀ i, Even (selectedDegree X cross f i) := by simpa [Good] using h
    simp only [not_forall] at hn
    obtain ⟨i, hi⟩ := hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [← indicator_even_degree]
    simp [hi]

lemma odd_goodTransversals_iff_sum_prod_eq_one
    (cross : CrossRel X) [Fintype I] [DecidableEq I]
    [∀ i, Fintype (X i)] :
    Odd (Fintype.card (goodTransversals X cross)) ↔
      (∑ f : ∀ i, X i,
        ∏ i : I, (1 + (selectedDegree X cross f i : ZMod 2))) = 1 := by
  classical
  let : Fintype (∀ i, X i) := Pi.instFintype
  change Odd (Fintype.card {f : ∀ i, X i // Good X cross f}) ↔ _
  rw [odd_iff_cast_zmod_two_eq_one,
    cast_card_subtype_eq_sum_indicator (Good X cross)]
  simp_rw [indicator_good_eq_prod]

lemma odd_card_pi [Fintype I] [∀ i, Fintype (X i)]
    (hodd : ∀ i, Odd (Fintype.card (X i))) :
    Odd (Fintype.card (∀ i, X i)) := by
  classical
  let : Fintype (∀ i, X i) := Pi.instFintype
  rw [Fintype.card_pi]
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hodd i).mul ih

/-! ## The functional-graph dichotomy behind Petrov's cancellation -/

/-- The simple graph obtained by forgetting the directions and loops of a function. -/
def functionGraph (g : I → I) : SimpleGraph I :=
  SimpleGraph.fromRel fun i j ↦ g i = j ∧ i ≠ j

@[simp] lemma functionGraph_adj (g : I → I) (i j : I) :
    (functionGraph g).Adj i j ↔
      i ≠ j ∧ (g i = j ∨ g j = i) := by
  simp [functionGraph, SimpleGraph.fromRel_adj, eq_comm, and_or_left]
  tauto

private lemma functionGraph_edgeFinset_subset_image
    [Fintype I] [DecidableEq I] (g : I → I) :
    (functionGraph g).edgeFinset ⊆
      ((Finset.univ.filter fun i ↦ g i ≠ i).image fun i ↦ s(i, g i)) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (functionGraph g).Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset] using he
      rw [functionGraph_adj] at hab
      obtain ⟨hne, hab | hba⟩ := hab
      · have hmove : g a ≠ a := by rw [hab]; exact hne.symm
        apply Finset.mem_image.mpr
        exact ⟨a, by simp [hmove], by simp [hab]⟩
      · have hmove : g b ≠ b := by rw [hba]; exact hne
        apply Finset.mem_image.mpr
        exact ⟨b, by simp [hmove], by simp [hba, Sym2.eq_swap]⟩

private lemma functionGraph_moved_subset_support
    [Fintype I] [DecidableEq I] (g : I → I) :
    ↑(Finset.univ.filter fun i ↦ g i ≠ i) ⊆ (functionGraph g).support := by
  intro i hi
  have hne : g i ≠ i := by simpa using hi
  exact ((functionGraph_adj g i (g i)).mpr ⟨hne.symm, Or.inl rfl⟩).mem_support_left

/-- If the undirected functional graph has no leaf, its moved points are exactly its support. -/
private lemma moved_eq_support_of_no_degree_one
    [Fintype I] [DecidableEq I] (g : I → I)
    (hleaf : ∀ i, (functionGraph g).degree i ≠ 1) :
    (Finset.univ.filter fun i ↦ g i ≠ i) = (functionGraph g).support.toFinset := by
  classical
  let G := functionGraph g
  let moved := Finset.univ.filter fun i ↦ g i ≠ i
  have hedge_moved : G.edgeFinset.card ≤ moved.card := by
    calc
      G.edgeFinset.card ≤ (moved.image fun i ↦ s(i, g i)).card :=
        Finset.card_le_card (functionGraph_edgeFinset_subset_image g)
      _ ≤ moved.card := Finset.card_image_le
  have hmoved_support : moved ⊆ G.support.toFinset := by
    intro i hi
    exact Set.mem_toFinset.mpr (functionGraph_moved_subset_support g hi)
  have hmoved_card : moved.card ≤ G.support.toFinset.card :=
    Finset.card_le_card hmoved_support
  have hdegree : ∀ i ∈ G.support.toFinset, 2 ≤ G.degree i := by
    intro i hi
    have hpos : 0 < G.degree i :=
      (G.degree_pos_iff_mem_support i).mpr (Set.mem_toFinset.mp hi)
    have hone : G.degree i ≠ 1 := by
      exact hleaf i
    omega
  have hsupport_edge : G.support.toFinset.card ≤ G.edgeFinset.card := by
    have hsum_lower : 2 * G.support.toFinset.card ≤
        ∑ i ∈ G.support.toFinset, G.degree i := by
      calc
        2 * G.support.toFinset.card = ∑ _i ∈ G.support.toFinset, 2 := by
          simp [mul_comm]
        _ ≤ ∑ i ∈ G.support.toFinset, G.degree i :=
          Finset.sum_le_sum fun i hi ↦ hdegree i hi
    rw [G.sum_degrees_support_eq_twice_card_edges] at hsum_lower
    omega
  have hcard : moved.card = G.support.toFinset.card := by omega
  exact Finset.eq_of_subset_of_card_le hmoved_support hcard.ge

private lemma bijective_of_no_degree_one
    [Fintype I] [DecidableEq I] (g : I → I)
    (hleaf : ∀ i, (functionGraph g).degree i ≠ 1) :
    Function.Bijective g := by
  classical
  have hmoved := moved_eq_support_of_no_degree_one g hleaf
  have hsurj : Function.Surjective g := by
    intro y
    by_cases hy : g y = y
    · exact ⟨y, hy⟩
    · by_contra hpre
      push_neg at hpre
      have hadj : ∀ z, (functionGraph g).Adj y z ↔ z = g y := by
        intro z
        rw [functionGraph_adj]
        constructor
        · rintro ⟨_, h | h⟩
          · exact h.symm
          · exact (hpre z h).elim
        · rintro rfl
          exact ⟨Ne.symm hy, Or.inl rfl⟩
      have hneighbors : (functionGraph g).neighborFinset y = {g y} := by
        ext z
        simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton] using hadj z
      have hdegree : (functionGraph g).degree y = 1 := by
        rw [← (functionGraph g).card_neighborFinset_eq_degree, hneighbors]
        simp
      exact hleaf y hdegree
  exact (Fintype.bijective_iff_surjective_and_card g).mpr ⟨hsurj, rfl⟩

private lemma inverse_ne_of_no_degree_one_of_ne_id
    [Fintype I] [DecidableEq I] (g : I → I)
    (hne : g ≠ id)
    (hleaf : ∀ i, (functionGraph g).degree i ≠ 1) :
    Equiv.ofBijective g (bijective_of_no_degree_one g hleaf) ≠
      (Equiv.ofBijective g (bijective_of_no_degree_one g hleaf)).symm := by
  classical
  let hb := bijective_of_no_degree_one g hleaf
  let e := Equiv.ofBijective g hb
  have hecoe : (e : I → I) = g := Equiv.coe_ofBijective g hb
  change e ≠ e.symm
  intro he
  have hex : ∃ i, g i ≠ i := by
    by_contra hall
    push_neg at hall
    apply hne
    funext i
    exact hall i
  obtain ⟨i, hi⟩ := hex
  have hsq_e : e (e i) = i := by
    have h := e.apply_symm_apply i
    rw [← he] at h
    exact h
  have hsq : g (g i) = i := by simpa only [← hecoe] using hsq_e
  have hinj : Function.Injective g := hb.injective
  have hadj : ∀ z, (functionGraph g).Adj i z ↔ z = g i := by
    intro z
    rw [functionGraph_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h.symm
      · exact hinj (h.trans hsq.symm)
    · rintro rfl
      exact ⟨hi.symm, Or.inl rfl⟩
  have hneighbors : (functionGraph g).neighborFinset i = {g i} := by
    ext z
    simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton] using hadj z
  have hdegree : (functionGraph g).degree i = 1 := by
    rw [← (functionGraph g).card_neighborFinset_eq_degree, hneighbors]
    simp
  exact hleaf i hdegree

/-- A nonidentity functional digraph either has a leaf, or is paired without a fixed point by
reversing all its directed cycles.  Fixed points of the function represent absent arcs. -/
theorem functionGraph_dichotomy [Fintype I] [DecidableEq I] (g : I → I) :
    g = id ∨
      (∃ i, (functionGraph g).degree i = 1) ∨
      ∃ e : I ≃ I, (e : I → I) = g ∧ e ≠ e.symm := by
  classical
  by_cases hid : g = id
  · exact Or.inl hid
  by_cases hleaf : ∃ i, (functionGraph g).degree i = 1
  · exact Or.inr (Or.inl hleaf)
  · right
    right
    push_neg at hleaf
    let hb := bijective_of_no_degree_one g hleaf
    let e := Equiv.ofBijective g hb
    exact ⟨e, Equiv.coe_ofBijective g hb, inverse_ne_of_no_degree_one_of_ne_id g hid hleaf⟩

/-! ## Special pairs and the expansion by functional digraphs -/

/-- A transversal realizes `g` if every non-fixed arrow of `g` is a crossing.  Fixed points
represent the choice of the `1` term at that part. -/
def Realizes (cross : CrossRel X) (g : I → I) (f : ∀ i, X i) : Prop :=
  ∀ i, i ≠ g i → cross i (g i) (f i) (f (g i))

/-- The `ZMod 2` indicator of the fiber of a functional-digraph pattern. -/
noncomputable def patternWeight [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) : ZMod 2 :=
  by
    classical
    letI : Fintype (∀ i, X i) := Pi.instFintype
    exact ∑ f : ∀ i, X i, if Realizes X cross g f then 1 else 0

private lemma indicator_realizes_eq_prod
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) (f : ∀ i, X i) :
    (if Realizes X cross g f then (1 : ZMod 2) else 0) =
      ∏ i : I, if i = g i ∨ cross i (g i) (f i) (f (g i)) then 1 else 0 := by
  classical
  by_cases h : Realizes X cross g f
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = g i
    · rw [if_pos (Or.inl hi)]
    · rw [if_pos (Or.inr (h i hi))]
  · rw [if_neg h]
    have hn : ¬ ∀ i, i ≠ g i → cross i (g i) (f i) (f (g i)) := by
      simpa only [Realizes] using h
    push Not at hn
    obtain ⟨i, hi, hcross⟩ := hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, hcross]

private lemma sum_one_or_cross
    [Fintype I] [DecidableEq I]
    (cross : CrossRel X) (f : ∀ i, X i) (i : I) :
    (∑ j : I, (if i = j ∨ cross i j (f i) (f j) then (1 : ZMod 2) else 0)) =
      1 + (selectedDegree X cross f i : ZMod 2) := by
  classical
  have herase :
      (∑ j ∈ (Finset.univ.erase i),
        (if i = j ∨ cross i j (f i) (f j) then (1 : ZMod 2) else 0)) =
        (selectedDegree X cross f i : ZMod 2) := by
    rw [selectedDegree, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    congr 1
    exact propext (or_iff_right (Ne.symm hji))
  calc
    (∑ j : I, (if i = j ∨ cross i j (f i) (f j) then (1 : ZMod 2) else 0)) =
        (∑ j ∈ (Finset.univ.erase i),
          (if i = j ∨ cross i j (f i) (f j) then (1 : ZMod 2) else 0)) + 1 := by
            symm
            convert Finset.sum_erase_add Finset.univ
              (fun j ↦ (if i = j ∨ cross i j (f i) (f j) then (1 : ZMod 2) else 0))
              (Finset.mem_univ i) using 1 <;> simp
    _ = 1 + (selectedDegree X cross f i : ZMod 2) := by rw [herase, add_comm]

/-- Expanding the even-degree indicators gives the sum over functional-digraph patterns. -/
lemma sum_patternWeight_eq_sum_good_indicator
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) :
    (∑ g : I → I, patternWeight X cross g) =
      ∑ f : ∀ i, X i,
        ∏ i : I, (1 + (selectedDegree X cross f i : ZMod 2)) := by
  classical
  let : Fintype (I → I) := Pi.instFintype
  let : Fintype (∀ i, X i) := Pi.instFintype
  simp only [patternWeight]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro f
  simp_rw [indicator_realizes_eq_prod]
  let coord : I → I → ZMod 2 := fun i j ↦
    if i = j ∨ cross i j (f i) (f j) then 1 else 0
  calc
    (∑ g : I → I, ∏ i : I,
        (if i = g i ∨ cross i (g i) (f i) (f (g i)) then 1 else 0)) =
        ∏ i : I, ∑ j : I, coord i j := (Fintype.prod_sum coord).symm
    _ = ∏ i : I, (1 + (selectedDegree X cross f i : ZMod 2)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_one_or_cross X cross f i

/-! ## Reversal of the leafless patterns -/

/-- Reverse every arrow when `g` is a permutation; leave nonpermutations unchanged. -/
noncomputable def reversePattern [Fintype I] (g : I → I) : I → I :=
  if h : Function.Bijective g then
    (Equiv.ofBijective g h).symm
  else g

lemma reversePattern_eq_of_bijective [Fintype I] (g : I → I)
    (h : Function.Bijective g) :
    reversePattern g = (Equiv.ofBijective g h).symm := by
  classical
  rw [reversePattern, dif_pos h]

lemma reversePattern_apply_apply [Fintype I] (g : I → I)
    (h : Function.Bijective g) (i : I) :
    reversePattern g (g i) = i := by
  rw [reversePattern_eq_of_bijective g h]
  exact (Equiv.ofBijective g h).symm_apply_apply i

lemma apply_reversePattern_apply [Fintype I] (g : I → I)
    (h : Function.Bijective g) (i : I) :
    g (reversePattern g i) = i := by
  rw [reversePattern_eq_of_bijective g h]
  exact (Equiv.ofBijective g h).apply_symm_apply i

lemma reversePattern_bijective [Fintype I] (g : I → I)
    (h : Function.Bijective g) :
    Function.Bijective (reversePattern g) := by
  rw [reversePattern_eq_of_bijective g h]
  exact (Equiv.ofBijective g h).symm.bijective

lemma reversePattern_involutive [Fintype I] :
    Function.Involutive (reversePattern : (I → I) → I → I) := by
  classical
  intro g
  by_cases h : Function.Bijective g
  · apply funext
    intro i
    have hr := reversePattern_bijective g h
    apply hr.injective
    rw [apply_reversePattern_apply (reversePattern g) hr]
    rw [reversePattern_apply_apply g h]
  · have hre : reversePattern g = g := by rw [reversePattern, dif_neg h]
    exact (congrArg reversePattern hre).trans hre

lemma functionGraph_reversePattern [Fintype I] [DecidableEq I]
    (g : I → I) (h : Function.Bijective g) :
    functionGraph (reversePattern g) = functionGraph g := by
  ext i j
  simp only [functionGraph_adj]
  constructor
  · rintro ⟨hij, hri | hrj⟩
    · exact ⟨hij, Or.inr (by
        rw [← hri]
        exact apply_reversePattern_apply g h i)⟩
    · exact ⟨hij, Or.inl (by
        rw [← hrj]
        exact apply_reversePattern_apply g h j)⟩
  · rintro ⟨hij, hgi | hgj⟩
    · exact ⟨hij, Or.inr (by
        rw [← hgi]
        exact reversePattern_apply_apply g h i)⟩
    · exact ⟨hij, Or.inl (by
        rw [← hgj]
        exact reversePattern_apply_apply g h j)⟩

lemma realizes_reversePattern_iff [Fintype I]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (g : I → I) (h : Function.Bijective g) (f : ∀ i, X i) :
    Realizes X cross (reversePattern g) f ↔ Realizes X cross g f := by
  constructor
  · intro hr i hi
    have hrev : reversePattern g (g i) = i := reversePattern_apply_apply g h i
    have hne : g i ≠ reversePattern g (g i) := by simpa only [hrev] using hi.symm
    have hc := hr (g i) hne
    rw [hrev] at hc
    exact (hsym i (g i) (f i) (f (g i))).mpr hc
  · intro hg i hi
    have happ : g (reversePattern g i) = i := apply_reversePattern_apply g h i
    have hne : reversePattern g i ≠ g (reversePattern g i) := by
      simpa only [happ] using hi.symm
    have hc := hg (reversePattern g i) hne
    rw [happ] at hc
    exact (hsym i (reversePattern g i) (f i) (f (reversePattern g i))).mpr hc

lemma patternWeight_reversePattern [Fintype I] [DecidableEq I]
    [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (g : I → I) (h : Function.Bijective g) :
    patternWeight X cross (reversePattern g) = patternWeight X cross g := by
  classical
  let : Fintype (∀ i, X i) := Pi.instFintype
  simp only [patternWeight]
  apply Finset.sum_congr rfl
  intro f _
  rw [if_congr (realizes_reversePattern_iff X cross hsym g h f) rfl rfl]

lemma reversePattern_ne_of_no_degree_one_of_ne_id
    [Fintype I] [DecidableEq I] (g : I → I)
    (hne : g ≠ id)
    (hleaf : ∀ i, (functionGraph g).degree i ≠ 1) :
    reversePattern g ≠ g := by
  classical
  let hb := bijective_of_no_degree_one g hleaf
  let e := Equiv.ofBijective g hb
  have hre : reversePattern g = e.symm := reversePattern_eq_of_bijective g hb
  have hcoe : (e : I → I) = g := Equiv.coe_ofBijective g hb
  intro h
  apply inverse_ne_of_no_degree_one_of_ne_id g hne hleaf
  ext i
  change e i = e.symm i
  rw [hcoe, ← h, hre]

lemma reversePattern_id [Fintype I] : reversePattern (id : I → I) = id := by
  funext i
  simpa using reversePattern_apply_apply (id : I → I) Function.bijective_id i

lemma patternWeight_id [Fintype I] [DecidableEq I]
    [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hodd : ∀ i, Odd (Fintype.card (X i))) :
    patternWeight X cross id = 1 := by
  classical
  let : Fintype (∀ i, X i) := Pi.instFintype
  have hreal : ∀ f : ∀ i, X i, Realizes X cross id f := by
    intro f i hi
    exact (hi rfl).elim
  simp only [patternWeight, hreal, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [Fintype.card_pi, Nat.cast_prod]
  apply Finset.prod_eq_one
  intro i _
  exact (odd_iff_cast_zmod_two_eq_one _).mp (hodd i)

/-- The patterns paired by reversal: nonidentity patterns whose functional graph has no leaf. -/
def IsReversalPattern [Fintype I] [DecidableEq I] (g : I → I) : Prop :=
  g ≠ id ∧ ∀ i, (functionGraph g).degree i ≠ 1

noncomputable def reversalPatterns [Fintype I] [DecidableEq I] : Finset (I → I) := by
  classical
  letI : Fintype (I → I) := Pi.instFintype
  exact Finset.univ.filter IsReversalPattern

@[simp] lemma mem_reversalPatterns [Fintype I] [DecidableEq I] (g : I → I) :
    g ∈ (reversalPatterns : Finset (I → I)) ↔ IsReversalPattern g := by
  classical
  simp [reversalPatterns]

lemma sum_patternWeight_reversalPatterns_eq_zero
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross) :
    ∑ g ∈ (reversalPatterns : Finset (I → I)), patternWeight X cross g = 0 := by
  classical
  let : Fintype (I → I) := Pi.instFintype
  apply Finset.sum_involution (fun g _ ↦ reversePattern g)
  · intro g hg
    have hs : IsReversalPattern g := (mem_reversalPatterns g).mp hg
    have hb := bijective_of_no_degree_one g hs.2
    rw [patternWeight_reversePattern X cross hsym g hb]
    change patternWeight X cross g + patternWeight X cross g = 0
    calc
      patternWeight X cross g + patternWeight X cross g =
          (2 : ZMod 2) * patternWeight X cross g := (two_mul _).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  · intro g hg _
    have hs : IsReversalPattern g := (mem_reversalPatterns g).mp hg
    exact reversePattern_ne_of_no_degree_one_of_ne_id g hs.1 hs.2
  · intro g _
    exact reversePattern_involutive g
  · intro g hg
    have hs : IsReversalPattern g := (mem_reversalPatterns g).mp hg
    have hb := bijective_of_no_degree_one g hs.2
    apply (mem_reversalPatterns (reversePattern g)).mpr
    constructor
    · intro hrid
      apply hs.1
      calc
        g = reversePattern (reversePattern g) := (reversePattern_involutive g).symm
        _ = reversePattern id := congrArg reversePattern hrid
        _ = id := reversePattern_id
    · intro i hi
      have hgraph := functionGraph_reversePattern g hb
      have := hs.2 i
      rw [hgraph] at hi
      exact this hi

/-! ## Even fibers at a leaf -/

/-- `p` is a leaf with unique distinct neighbour `q` among the nonloop arcs of `g`. -/
def IsLeaf (g : I → I) (p q : I) : Prop :=
  p ≠ q ∧
    (g p = q ∨ g q = p) ∧
    ∀ i, i ≠ g i → (i = p ∨ g i = p) →
      (i = p ∧ g i = q) ∨ (i = q ∧ g i = p)

lemma exists_isLeaf_of_degree_eq_one [Fintype I] [DecidableEq I]
    (g : I → I) {p : I} (hdegree : (functionGraph g).degree p = 1) :
    ∃ q, IsLeaf g p q := by
  classical
  obtain ⟨q, hpq, huniq⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
  have hpq' := (functionGraph_adj g p q).mp hpq
  refine ⟨q, hpq'.1, hpq'.2, ?_⟩
  intro i hi hinc
  rcases hinc with rfl | htarget
  · have hadj : (functionGraph g).Adj i (g i) :=
      (functionGraph_adj g i (g i)).mpr ⟨hi, Or.inl rfl⟩
    exact Or.inl ⟨rfl, huniq (g i) hadj⟩
  · have hip : i ≠ p := by simpa [htarget] using hi
    have hadj : (functionGraph g).Adj p i :=
      (functionGraph_adj g p i).mpr ⟨hip.symm, Or.inr htarget⟩
    exact Or.inr ⟨huniq i hadj, htarget⟩

/-- Dependent assignments away from one distinguished index. -/
abbrev Away (p : I) := ∀ i : {i : I // i ≠ p}, X i

/-- Extend an assignment away from `p` by a chosen value at `p`. -/
noncomputable def extendAway (p : I) (rest : Away X p) (xp : X p) : ∀ i, X i :=
  fun i ↦ if h : i = p then h.symm ▸ xp else rest ⟨i, h⟩

@[simp] lemma extendAway_same (p : I) (rest : Away X p) (xp : X p) :
    extendAway X p rest xp p = xp := by
  simp [extendAway]

@[simp] lemma extendAway_ne (p : I) (rest : Away X p) (xp : X p)
    {i : I} (hi : i ≠ p) :
    extendAway X p rest xp i = rest ⟨i, hi⟩ := by
  simp [extendAway, hi]

/-- The part of the realization condition supported completely away from `p`. -/
def RealizesAway (cross : CrossRel X) (g : I → I) (p : I) (rest : Away X p) : Prop :=
  ∀ i (hi : i ≠ g i) (hip : i ≠ p) (hgp : g i ≠ p),
    cross i (g i) (rest ⟨i, hip⟩) (rest ⟨g i, hgp⟩)

lemma realizes_extendAway_iff
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q)
    (rest : Away X p) (xp : X p) :
    Realizes X cross g (extendAway X p rest xp) ↔
      RealizesAway X cross g p rest ∧
        cross p q xp (rest ⟨q, hleaf.1.symm⟩) := by
  classical
  constructor
  · intro hreal
    constructor
    · intro i hi hip hgp
      simpa [extendAway, hip, hgp] using hreal i hi
    · rcases hleaf.2.1 with hpq | hqp
      · have hpn : p ≠ g p := by simpa [hpq] using hleaf.1
        have hr := hreal p hpn
        rw [hpq] at hr
        rw [extendAway_same, extendAway_ne X p rest xp hleaf.1.symm] at hr
        exact hr
      · have hqn : q ≠ g q := by simpa [hqp] using hleaf.1.symm
        have hc := hreal q hqn
        rw [hqp] at hc
        rw [extendAway_ne X p rest xp hleaf.1.symm, extendAway_same] at hc
        exact (hsym q p (rest ⟨q, hleaf.1.symm⟩) xp).mp hc
  · rintro ⟨haway, hpqCross⟩ i hi
    by_cases hip : i = p
    · subst i
      have hinc := hleaf.2.2 p hi (Or.inl rfl)
      rcases hinc with h | h
      · rw [h.2, extendAway_same, extendAway_ne X p rest xp hleaf.1.symm]
        exact hpqCross
      · exact (hleaf.1 h.1).elim
    · by_cases hgp : g i = p
      · have hinc := hleaf.2.2 i hi (Or.inr hgp)
        rcases hinc with h | h
        · exact (hip h.1).elim
        · have hiq : i = q := h.1
          subst i
          have hc := (hsym p q xp (rest ⟨q, hleaf.1.symm⟩)).mp hpqCross
          rw [hgp, extendAway_ne X p rest xp hleaf.1.symm, extendAway_same]
          exact hc
      · simpa [extendAway, hip, hgp] using haway i hi hip hgp

private lemma even_leaf_fiber
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q) (rest : Away X p) :
    Even (Fintype.card
      {xp : X p // Realizes X cross g (extendAway X p rest xp)}) := by
  classical
  by_cases haway : RealizesAway X cross g p rest
  · have hpred : ∀ xp : X p,
        Realizes X cross g (extendAway X p rest xp) ↔
          cross q p (rest ⟨q, hleaf.1.symm⟩) xp := by
      intro xp
      rw [realizes_extendAway_iff X cross hsym g hleaf rest xp]
      rw [and_iff_right haway]
      exact hsym p q xp (rest ⟨q, hleaf.1.symm⟩)
    rw [Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter fun xp : X p ↦
          Realizes X cross g (extendAway X p rest xp)) =
        Finset.univ.filter fun xp : X p ↦
          cross q p (rest ⟨q, hleaf.1.symm⟩) xp := by
      ext xp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred xp
    change Even ((Finset.univ.filter fun xp : X p ↦
      Realizes X cross g (extendAway X p rest xp)).card)
    rw [hfilter]
    exact heven q p (rest ⟨q, hleaf.1.symm⟩) hleaf.1.symm
  · have : IsEmpty {xp : X p // Realizes X cross g (extendAway X p rest xp)} :=
      ⟨fun xp ↦ haway
        ((realizes_extendAway_iff X cross hsym g hleaf rest xp.1).mp xp.2).1⟩
    simp

/-- Split a dependent transversal into its value at `p` and its restriction away from `p`. -/
noncomputable def piEquivSigmaAway (p : I) :
    (∀ i, X i) ≃ Σ rest : Away X p, X p where
  toFun f := ⟨fun i ↦ f i, f p⟩
  invFun z := extendAway X p z.1 z.2
  left_inv f := by
    funext i
    by_cases hi : i = p
    · subst i
      simp
    · simp [extendAway, hi]
  right_inv z := by
    rcases z with ⟨rest, xp⟩
    apply Sigma.ext
    · funext i
      exact extendAway_ne X p rest xp i.property
    · simp

noncomputable def realizerEquivSigmaFiber [Fintype I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) (p : I) :
    {f : ∀ i, X i // Realizes X cross g f} ≃
      Σ rest : Away X p,
        {xp : X p // Realizes X cross g (extendAway X p rest xp)} := by
  let e := piEquivSigmaAway X p
  let eSub : {f : ∀ i, X i // Realizes X cross g f} ≃
      {z : Σ rest : Away X p, X p //
        Realizes X cross g (extendAway X p z.1 z.2)} :=
    e.subtypeEquiv fun f ↦ by
      have heq : extendAway X p (e f).1 (e f).2 = f := e.symm_apply_apply f
      rw [heq]
  exact eSub.trans
    { toFun := fun z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      invFun := fun z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

lemma even_card_realizer_of_leaf
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q) :
    Even (Fintype.card {f : ∀ i, X i // Realizes X cross g f}) := by
  classical
  rw [Fintype.card_congr (realizerEquivSigmaFiber X cross g p), Fintype.card_sigma]
  induction (Finset.univ : Finset (Away X p)) using Finset.induction_on with
  | empty => simp
  | @insert rest s hrest ih =>
      rw [Finset.sum_insert hrest]
      exact (even_leaf_fiber X cross hsym heven g hleaf rest).add ih

lemma patternWeight_eq_zero_of_degree_eq_one
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p : I} (hdegree : (functionGraph g).degree p = 1) :
    patternWeight X cross g = 0 := by
  classical
  let : Fintype (∀ i, X i) := Pi.instFintype
  obtain ⟨q, hleaf⟩ := exists_isLeaf_of_degree_eq_one g hdegree
  have he := even_card_realizer_of_leaf X cross hsym heven g hleaf
  calc
    patternWeight X cross g =
        (Fintype.card {f : ∀ i, X i // Realizes X cross g f} : ZMod 2) := by
          symm
          exact cast_card_subtype_eq_sum_indicator (Realizes X cross g)
    _ = 0 := (even_iff_cast_zmod_two_eq_zero _).mp he

/-! ## Petrov's odd-transversal theorem -/

private lemma sum_patternWeight_eq_one
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (hodd : ∀ i, Odd (Fintype.card (X i)))
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi)) :
    (∑ g : I → I, patternWeight X cross g) = 1 := by
  classical
  let : Fintype (I → I) := Pi.instFintype
  let covered : Finset (I → I) := {id} ∪ reversalPatterns
  have hcovered : covered ⊆ Finset.univ := fun _ _ ↦ Finset.mem_univ _
  have hzero : ∀ g ∈ (Finset.univ : Finset (I → I)), g ∉ covered →
      patternWeight X cross g = 0 := by
    intro g _ hg
    have hid : g ≠ id := by
      intro h
      apply hg
      simp [covered, h]
    have hnrev : ¬ IsReversalPattern g := by
      intro hr
      apply hg
      simp [covered, hr]
    have hnotleafless : ¬ ∀ i, (functionGraph g).degree i ≠ 1 := by
      intro hall
      exact hnrev ⟨hid, hall⟩
    push Not at hnotleafless
    obtain ⟨p, hp⟩ := hnotleafless
    exact patternWeight_eq_zero_of_degree_eq_one X cross hsym heven g hp
  have hrestrict :
      ∑ g ∈ covered, patternWeight X cross g =
        ∑ g : I → I, patternWeight X cross g :=
    Finset.sum_subset hcovered hzero
  have hid_not_mem : (id : I → I) ∉ (reversalPatterns : Finset (I → I)) := by
    intro h
    have hr := (mem_reversalPatterns (id : I → I)).mp h
    exact hr.1 rfl
  have hdisj : Disjoint ({id} : Finset (I → I)) reversalPatterns := by
    rwa [Finset.disjoint_singleton_left]
  calc
    (∑ g : I → I, patternWeight X cross g) =
        ∑ g ∈ covered, patternWeight X cross g := hrestrict.symm
    _ = patternWeight X cross id +
        ∑ g ∈ (reversalPatterns : Finset (I → I)), patternWeight X cross g := by
          rw [show covered = {id} ∪ reversalPatterns from rfl,
            Finset.sum_union hdisj, Finset.sum_singleton]
    _ = 1 := by
      rw [patternWeight_id X cross hodd,
        sum_patternWeight_reversalPatterns_eq_zero X cross hsym, add_zero]

/-- **Petrov's odd-transversal lemma.**

Choose one point from every odd finite part.  If the crossing relation is symmetric and every
vertex has even degree into every other part, then an odd number of selections have even selected
degree at every part.
-/
theorem odd_goodTransversals
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsym : Symmetric X cross)
    (hodd : ∀ i, Odd (Fintype.card (X i)))
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi)) :
    Odd (Fintype.card (goodTransversals X cross)) := by
  rw [odd_goodTransversals_iff_sum_prod_eq_one]
  rw [← sum_patternWeight_eq_sum_good_indicator]
  exact sum_patternWeight_eq_one X cross hsym hodd heven

/-- Specialization used for triangle edges: there are three choices in every indexed part. -/
theorem odd_goodTransversals_fin_three (n : ℕ)
    (cross : CrossRel (fun _ : Fin n ↦ Fin 3))
    (hsym : Symmetric (fun _ : Fin n ↦ Fin 3) cross)
    (heven : ∀ i j (xi : Fin 3), i ≠ j →
      Even (crossDegree (fun _ : Fin n ↦ Fin 3) cross i j xi)) :
    Odd (Fintype.card
      (goodTransversals (fun _ : Fin n ↦ Fin 3) cross)) := by
  apply odd_goodTransversals (fun _ : Fin n ↦ Fin 3) cross hsym
  · intro i
    change Odd 3
    exact ⟨1, rfl⟩
  · exact heven

/-- Finset-cardinality form of the `Fin n`/`Fin 3` specialization. -/
theorem odd_card_good_filter_fin_three (n : ℕ)
    (cross : CrossRel (fun _ : Fin n ↦ Fin 3))
    (hsym : Symmetric (fun _ : Fin n ↦ Fin 3) cross)
    (heven : ∀ i j (xi : Fin 3), i ≠ j →
      Even (crossDegree (fun _ : Fin n ↦ Fin 3) cross i j xi)) :
    Odd ((Finset.univ.filter fun f : Fin n → Fin 3 ↦
      Good (fun _ : Fin n ↦ Fin 3) cross f).card) := by
  rw [← Fintype.card_subtype]
  exact odd_goodTransversals_fin_three n cross hsym heven


end OddTransversal

end Erdos842
