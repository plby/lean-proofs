/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos551.Erdos551Core
import ErdosProblems.Erdos752.Erdos752Assembly
import ErdosProblems.Erdos551.Erdos551ScaffoldGaps

/-!
# Erdős Problem 551: the sufficiently-large theorem

This main module combines the reusable Ramsey, stability, and absorption
development in `Erdos551Core` with the bounded BFS path-closing theorem from
the Erdős 752 development.  The final theorem states the unconditional
eventual resolution of Problem 551.
-/

open scoped BigOperators Classical SimpleGraph NNReal
open Filter Asymptotics Topology

namespace Erdos551

open Fintype _root_.SimpleGraph

/-! ## Full alternating-hub handles -/

/-- `a` is an anchor in the selected side `A` for the hub vertex `x`.
Vertices already in `A` anchor to themselves; vertices on the alternating
side anchor across one scaffold edge. -/
def IsHubAnchor {V : Type*} (G : SimpleGraph V)
    (A : Finset V) (x a : V) : Prop :=
  a ∈ A ∧ (a = x ∨ G.Adj a x)

/-- Every vertex on the alternating side has two distinct neighbours on the
selected side.  This is the two-choice fact needed to avoid a prescribed
anchor when converting full-hub cross-edges into selected-side handles. -/
theorem exists_two_distinct_selected_neighbors_of_mem_alternatingSide
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} {A B : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hq : 2 ≤ q) {x : V} (hx : x ∈ B) :
    ∃ a₀ ∈ A, ∃ a₁ ∈ A,
      a₀ ≠ a₁ ∧ G.Adj a₀ x ∧ G.Adj a₁ x := by
  classical
  rcases hscaffold with
    ⟨hqpos, a, b, hA, hB, ha, _hb, _hAB, hab, hba⟩
  rw [hB] at hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  refine ⟨a i, ?_, a (finCyclicSucc hqpos i), ?_, ?_, hab i,
    (hba i).symm⟩
  · rw [hA]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · rw [hA]
    exact Finset.mem_image.mpr
      ⟨finCyclicSucc hqpos i, Finset.mem_univ _, rfl⟩
  · intro heq
    have hisucc : i = finCyclicSucc hqpos i := ha heq
    have hval := congrArg Fin.val hisucc
    simp only [finCyclicSucc] at hval
    have hiq : i.val + 1 < q := by
      by_contra hnot
      have hiTop : i.val + 1 = q := by omega
      rw [hiTop, Nat.mod_self] at hval
      omega
    rw [Nat.mod_eq_of_lt hiq] at hval
    omega

/-- Every vertex of the full alternating core has a selected-side anchor. -/
theorem exists_hubAnchor
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} {A B : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hq : 2 ≤ q) {x : V} (hx : x ∈ A ∪ B) :
    ∃ a : V, IsHubAnchor G A x a := by
  classical
  by_cases hxA : x ∈ A
  · exact ⟨x, hxA, Or.inl rfl⟩
  · have hxB : x ∈ B := (Finset.mem_union.mp hx).resolve_left hxA
    obtain ⟨a, haA, _b, _hbA, _hab, hax, _hbx⟩ :=
      exists_two_distinct_selected_neighbors_of_mem_alternatingSide
        G hscaffold hq hxB
    exact ⟨a, haA, Or.inr hax⟩

/-- A scaffold admits a canonical anchoring map which is injective on each
of the two sides separately.  It fixes `A`, and sends `b i` to `a i` on
`B`.  Separating the later matching into its four side-types therefore
makes all selected anchors globally distinct. -/
theorem exists_alternatingAnchor_map
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} {A B : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B) :
    ∃ anchor : V → V,
      (∀ x ∈ A ∪ B, IsHubAnchor G A x (anchor x)) ∧
      (∀ x ∈ A, anchor x = x) ∧
      Set.InjOn anchor (A : Set V) ∧ Set.InjOn anchor (B : Set V) ∧
      ∀ x ∈ B, IsCanonicalScaffoldMate G hscaffold x (anchor x) := by
  classical
  rcases hcanonical : cyclicAlternatingScaffoldData G hscaffold with
    ⟨hq, a, b, hA, hB, ha, hb, hAB, hab, _hba⟩
  let eb : Fin q ≃ B :=
    Equiv.ofBijective (fun i : Fin q => (⟨b i, by
      rw [hB]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : B))
      ⟨fun _ _ h => hb (Subtype.ext_iff.mp h), by
        intro x
        have hxImage : x.1 ∈ Finset.univ.image b := by
          simpa [hB] using x.2
        rcases Finset.mem_image.mp hxImage with ⟨i, _hi, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩
  let anchor : V → V := fun x =>
    if hx : x ∈ B then a (eb.symm ⟨x, hx⟩) else x
  refine ⟨anchor, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxB : x ∈ B
    · have hindex : b (eb.symm ⟨x, hxB⟩) = x := by
        have he := eb.apply_symm_apply ⟨x, hxB⟩
        exact congrArg Subtype.val he
      constructor
      · rw [hA]
        exact Finset.mem_image.mpr
          ⟨eb.symm ⟨x, hxB⟩, Finset.mem_univ _, by
            simp [anchor, hxB]⟩
      · right
        simpa [anchor, hxB, hindex] using hab (eb.symm ⟨x, hxB⟩)
    · have hxA : x ∈ A := (Finset.mem_union.mp hx).resolve_right hxB
      exact ⟨by simpa [anchor, hxB] using hxA,
        Or.inl (by simp [anchor, hxB])⟩
  · intro x hx
    have hxB : x ∉ B := fun h => (Finset.disjoint_left.mp hAB) hx h
    simp [anchor, hxB]
  · intro x hx y hy hxy
    have hxB : x ∉ B := fun h => (Finset.disjoint_left.mp hAB) hx h
    have hyB : y ∉ B := fun h => (Finset.disjoint_left.mp hAB) hy h
    simpa [anchor, hxB, hyB] using hxy
  · intro x hx y hy hxy
    have hxF : x ∈ B := by simpa using hx
    have hyF : y ∈ B := by simpa using hy
    have hxy' : a (eb.symm ⟨x, hxF⟩) = a (eb.symm ⟨y, hyF⟩) := by
      change (if hx' : x ∈ B then a (eb.symm ⟨x, hx'⟩) else x) =
        (if hy' : y ∈ B then a (eb.symm ⟨y, hy'⟩) else y) at hxy
      rw [dif_pos hxF, dif_pos hyF] at hxy
      exact hxy
    have hsubx : (⟨x, hxF⟩ : B) = ⟨y, hyF⟩ := by
      apply eb.symm.injective
      apply ha
      exact hxy'
    exact congrArg Subtype.val hsubx
  · intro x hx
    let i : Fin q := eb.symm ⟨x, hx⟩
    have hbi : b i = x := by
      have he := eb.apply_symm_apply ⟨x, hx⟩
      exact congrArg Subtype.val he
    unfold IsCanonicalScaffoldMate
    rw [hcanonical]
    refine ⟨i, hbi, ?_⟩
    simp [anchor, hx, i]

/-- Any two distinct vertices of the full alternating core `A ∪ B` have
distinct anchors in `A`.  The only nontrivial case is an endpoint in `B`;
its two consecutive scaffold neighbours let us avoid the other anchor. -/
theorem exists_distinct_hubAnchors
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} {A B : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hq : 2 ≤ q) {x y : V} (hx : x ∈ A ∪ B) (hy : y ∈ A ∪ B)
    (hxy : x ≠ y) :
    ∃ a b : V, a ≠ b ∧ IsHubAnchor G A x a ∧ IsHubAnchor G A y b := by
  classical
  by_cases hxA : x ∈ A
  · by_cases hyA : y ∈ A
    · exact ⟨x, y, hxy, ⟨hxA, Or.inl rfl⟩, ⟨hyA, Or.inl rfl⟩⟩
    · have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left hyA
      obtain ⟨b₀, hb₀A, b₁, hb₁A, hbne, hb₀y, hb₁y⟩ :=
        exists_two_distinct_selected_neighbors_of_mem_alternatingSide
          G hscaffold hq hyB
      by_cases hxb₀ : x = b₀
      · exact ⟨x, b₁, fun h => hbne (hxb₀.symm.trans h),
          ⟨hxA, Or.inl rfl⟩, ⟨hb₁A, Or.inr hb₁y⟩⟩
      · exact ⟨x, b₀, hxb₀, ⟨hxA, Or.inl rfl⟩,
          ⟨hb₀A, Or.inr hb₀y⟩⟩
  · have hxB : x ∈ B := (Finset.mem_union.mp hx).resolve_left hxA
    obtain ⟨a₀, ha₀A, a₁, ha₁A, hane, ha₀x, ha₁x⟩ :=
      exists_two_distinct_selected_neighbors_of_mem_alternatingSide
        G hscaffold hq hxB
    by_cases hyA : y ∈ A
    · by_cases ha₀y : a₀ = y
      · exact ⟨a₁, y, fun h => hane (ha₀y.trans h.symm),
          ⟨ha₁A, Or.inr ha₁x⟩, ⟨hyA, Or.inl rfl⟩⟩
      · exact ⟨a₀, y, ha₀y, ⟨ha₀A, Or.inr ha₀x⟩,
          ⟨hyA, Or.inl rfl⟩⟩
    · have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left hyA
      obtain ⟨b₀, hb₀A, b₁, hb₁A, hbne, hb₀y, hb₁y⟩ :=
        exists_two_distinct_selected_neighbors_of_mem_alternatingSide
          G hscaffold hq hyB
      by_cases hab₀ : a₀ = b₀
      · exact ⟨a₀, b₁, fun h => hbne (hab₀.symm.trans h),
          ⟨ha₀A, Or.inr ha₀x⟩, ⟨hb₁A, Or.inr hb₁y⟩⟩
      · exact ⟨a₀, b₀, hab₀, ⟨ha₀A, Or.inr ha₀x⟩,
          ⟨hb₀A, Or.inr hb₀y⟩⟩

/-- A cross-edge between the two full alternating cores becomes a short
path between their selected sides.  Its length is one, two, or three,
according to how many endpoints already lie in the selected sides. -/
theorem exists_selected_handle_of_fullCore_crossEdge
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q₁ q₂ : ℕ}
    {A₁ B₁ A₂ B₂ : Finset V}
    (hscaffold₁ : IsCyclicAlternatingScaffold G q₁ A₁ B₁)
    (hscaffold₂ : IsCyclicAlternatingScaffold G q₂ A₂ B₂)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (hregions : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    {x y : V} (hx : x ∈ A₁ ∪ B₁) (hy : y ∈ A₂ ∪ B₂)
    (hxy : G.Adj x y) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, ∃ p : G.Walk a b,
      p.IsPath ∧ 1 ≤ p.length ∧ p.length ≤ 3 ∧
        ∀ z ∈ p.support, z ∈ (A₁ ∪ B₁) ∪ (A₂ ∪ B₂) := by
  classical
  have hxyne : x ≠ y := hxy.ne
  obtain ⟨a, ha⟩ := exists_hubAnchor G hscaffold₁ hq₁ hx
  have ha₁ : a ∈ A₁ := ha.1
  have _haAnchor : a = x ∨ G.Adj a x := ha.2
  -- Choose the second anchor independently; disjoint regions make it
  -- automatically distinct from the first one.
  obtain ⟨b, hb⟩ := exists_hubAnchor G hscaffold₂ hq₂ hy
  have hb₂ : b ∈ A₂ := hb.1
  have hbAnchor : b = y ∨ G.Adj b y := hb.2
  have hcross_ne : ∀ u ∈ A₁ ∪ B₁, ∀ v ∈ A₂ ∪ B₂, u ≠ v := by
    intro u hu v hv huv
    exact (Finset.disjoint_left.mp hregions) hu (huv ▸ hv)
  have hay : a ≠ y := hcross_ne a (Finset.mem_union_left _ ha₁) y hy
  have hxb : x ≠ b := hcross_ne x hx b (Finset.mem_union_left _ hb₂)
  have hab' : a ≠ b := hcross_ne a (Finset.mem_union_left _ ha₁)
    b (Finset.mem_union_left _ hb₂)
  rcases _haAnchor with haxEq | hax
  · subst a
    rcases hbAnchor with hbyEq | hby
    · subst b
      let p : G.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
      refine ⟨x, ha₁, y, hb₂, p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxyne]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ hy
    · let p : G.Walk x b :=
        SimpleGraph.Walk.cons hxy
          (SimpleGraph.Walk.cons hby.symm SimpleGraph.Walk.nil)
      refine ⟨x, ha₁, b, hb₂, p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxyne, hxb,
          hby.ne.symm]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ hy
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hb₂)
  · rcases hbAnchor with hbyEq | hby
    · subst b
      let p : G.Walk a y := SimpleGraph.Walk.cons hax
        (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil)
      refine ⟨a, ha₁, y, hb₂, p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hax.ne, hay, hxyne]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha₁)
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ hy
    · let p : G.Walk a b :=
        SimpleGraph.Walk.cons hax (SimpleGraph.Walk.cons hxy
          (SimpleGraph.Walk.cons hby.symm SimpleGraph.Walk.nil))
      refine ⟨a, ha₁, b, hb₂, p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hax.ne, hay, hab', hxyne, hxb,
          hby.ne.symm]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha₁)
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ hy
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hb₂)

/-- Supplied selected-side anchors turn a cross-edge into a path of length
at most three.  Besides the region localization used above, this version
records the four possible support vertices.  That sharper conclusion is
what makes a homogeneous matching of cross-edges into a vertex-disjoint
family of handles. -/
theorem exists_selected_handle_of_hubAnchors
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {A₁ B₁ A₂ B₂ : Finset V}
    (hregions : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    {x y a b : V} (hx : x ∈ A₁ ∪ B₁) (hy : y ∈ A₂ ∪ B₂)
    (hxy : G.Adj x y) (ha : IsHubAnchor G A₁ x a)
    (hb : IsHubAnchor G A₂ y b) :
    ∃ p : G.Walk a b,
      p.IsPath ∧ 1 ≤ p.length ∧ p.length ≤ 3 ∧
        ∀ z ∈ p.support, z = a ∨ z = x ∨ z = y ∨ z = b := by
  classical
  have hcross_ne : ∀ u ∈ A₁ ∪ B₁, ∀ v ∈ A₂ ∪ B₂, u ≠ v := by
    intro u hu v hv huv
    exact (Finset.disjoint_left.mp hregions) hu (huv ▸ hv)
  have haU : a ∈ A₁ ∪ B₁ := Finset.mem_union_left _ ha.1
  have hbU : b ∈ A₂ ∪ B₂ := Finset.mem_union_left _ hb.1
  have hxyne : x ≠ y := hxy.ne
  have hay : a ≠ y := hcross_ne a haU y hy
  have hxb : x ≠ b := hcross_ne x hx b hbU
  have hab : a ≠ b := hcross_ne a haU b hbU
  rcases ha.2 with haxEq | hax
  · subst a
    rcases hb.2 with hbyEq | hby
    · subst b
      let p : G.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
      refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxyne]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl <;> simp
    · let p : G.Walk x b := SimpleGraph.Walk.cons hxy
        (SimpleGraph.Walk.cons hby.symm SimpleGraph.Walk.nil)
      refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxyne, hxb,
          hby.ne.symm]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl <;> simp
  · rcases hb.2 with hbyEq | hby
    · subst b
      let p : G.Walk a y := SimpleGraph.Walk.cons hax
        (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil)
      refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hax.ne, hay, hxyne]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl <;> simp
    · let p : G.Walk a b :=
        SimpleGraph.Walk.cons hax (SimpleGraph.Walk.cons hxy
          (SimpleGraph.Walk.cons hby.symm SimpleGraph.Walk.nil))
      refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hax.ne, hay, hab, hxyne, hxb,
          hby.ne.symm]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> simp

/-- A cross matching between two disjoint full cores has a quarter-sized
submatching with a fixed endpoint side in each core.  The matching is
oriented from the first core to the second one.  Homogeneity is the exact
condition under which the canonical scaffold anchor maps are injective on
all selected endpoints. -/
theorem exists_homogeneous_oriented_crossMatching
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {A₁ B₁ A₂ B₂ : Finset V} {m : ℕ}
    (hregions : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (hcross : HasCrossMatchingAtLeast G (A₁ ∪ B₁) (A₂ ∪ B₂) m) :
    ∃ M : Finset (V × V), ∃ left right : M → V,
      m / 4 ≤ M.card ∧
      (∀ e : M, left e ∈ A₁ ∪ B₁ ∧ right e ∈ A₂ ∪ B₂ ∧
        G.Adj (left e) (right e)) ∧
      (∀ e f : M, e ≠ f →
        left e ≠ left f ∧ left e ≠ right f ∧
          right e ≠ left f ∧ right e ≠ right f) ∧
      ((∀ e : M, left e ∈ A₁) ∨ (∀ e : M, left e ∈ B₁)) ∧
      ((∀ e : M, right e ∈ A₂) ∨ (∀ e : M, right e ∈ B₂)) := by
  classical
  obtain ⟨M₀, hM₀, hm, hM₀cross⟩ := hcross
  let left₀ : V × V → V := fun e =>
    if e.1 ∈ A₁ ∪ B₁ then e.1 else e.2
  let right₀ : V × V → V := fun e =>
    if e.1 ∈ A₁ ∪ B₁ then e.2 else e.1
  have hleft₀ : ∀ e ∈ M₀, left₀ e ∈ A₁ ∪ B₁ := by
    intro e he
    rcases hM₀cross e he with he12 | he21
    · have hleftEq : left₀ e = e.1 := by
        simp only [left₀, if_pos he12.1]
      rw [hleftEq]
      exact he12.1
    · have he1not : e.1 ∉ A₁ ∪ B₁ := by
        intro he1
        exact (Finset.disjoint_left.mp hregions) he1 he21.1
      have hleftEq : left₀ e = e.2 := by
        simp only [left₀, if_neg he1not]
      rw [hleftEq]
      exact he21.2
  have hright₀ : ∀ e ∈ M₀, right₀ e ∈ A₂ ∪ B₂ := by
    intro e he
    rcases hM₀cross e he with he12 | he21
    · have hrightEq : right₀ e = e.2 := by
        simp only [right₀, if_pos he12.1]
      rw [hrightEq]
      exact he12.2
    · have he1not : e.1 ∉ A₁ ∪ B₁ := by
        intro he1
        exact (Finset.disjoint_left.mp hregions) he1 he21.1
      have hrightEq : right₀ e = e.1 := by
        simp only [right₀, if_neg he1not]
      rw [hrightEq]
      exact he21.1
  have hadj₀ : ∀ e ∈ M₀, G.Adj (left₀ e) (right₀ e) := by
    intro e he
    have hedge := hM₀.1 e he
    by_cases he1 : e.1 ∈ A₁ ∪ B₁
    · have hleftEq : left₀ e = e.1 := by
        simp only [left₀, if_pos he1]
      have hrightEq : right₀ e = e.2 := by
        simp only [right₀, if_pos he1]
      rw [hleftEq, hrightEq]
      exact hedge
    · have hleftEq : left₀ e = e.2 := by
        simp only [left₀, if_neg he1]
      have hrightEq : right₀ e = e.1 := by
        simp only [right₀, if_neg he1]
      rw [hleftEq, hrightEq]
      exact hedge.symm
  let color₁ : V × V → Bool := fun e => decide (left₀ e ∈ A₁)
  have hhalf₀ : (Finset.univ : Finset Bool).card * (M₀.card / 2) ≤ M₀.card := by
    simp
    exact Nat.mul_div_le M₀.card 2
  obtain ⟨c₁, _hc₁, hc₁card⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := M₀) (t := Finset.univ) (f := color₁)
      (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hhalf₀
  let M₁ : Finset (V × V) := M₀.filter fun e => color₁ e = c₁
  have hM₁card : M₀.card / 2 ≤ M₁.card := by
    simpa [M₁] using hc₁card
  let color₂ : V × V → Bool := fun e => decide (right₀ e ∈ A₂)
  have hhalf₁ : (Finset.univ : Finset Bool).card * (M₁.card / 2) ≤ M₁.card := by
    simp
    exact Nat.mul_div_le M₁.card 2
  obtain ⟨c₂, _hc₂, hc₂card⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := M₁) (t := Finset.univ) (f := color₂)
      (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hhalf₁
  let M : Finset (V × V) := M₁.filter fun e => color₂ e = c₂
  have hMcard₂ : M₁.card / 2 ≤ M.card := by
    simpa [M] using hc₂card
  have hmM : m / 4 ≤ M.card := by
    have hdiv₁ : m / 2 ≤ M₀.card / 2 := Nat.div_le_div_right hm
    have hdiv₂ : (m / 2) / 2 ≤ M₁.card / 2 :=
      Nat.div_le_div_right (hdiv₁.trans hM₁card)
    simpa [Nat.div_div_eq_div_mul] using hdiv₂.trans hMcard₂
  let left : M → V := fun e => left₀ e.1
  let right : M → V := fun e => right₀ e.1
  have hMsub₁ : M ⊆ M₁ := Finset.filter_subset _ _
  have hM₁sub₀ : M₁ ⊆ M₀ := Finset.filter_subset _ _
  have hMsub₀ : M ⊆ M₀ := hMsub₁.trans hM₁sub₀
  have hends : ∀ e : M, left e ∈ A₁ ∪ B₁ ∧ right e ∈ A₂ ∪ B₂ ∧
      G.Adj (left e) (right e) := by
    intro e
    exact ⟨hleft₀ e.1 (hMsub₀ e.2), hright₀ e.1 (hMsub₀ e.2),
      hadj₀ e.1 (hMsub₀ e.2)⟩
  have hpairs : ∀ e f : M, e ≠ f →
      left e ≠ left f ∧ left e ≠ right f ∧
        right e ≠ left f ∧ right e ≠ right f := by
    intro e f hef
    have hev : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
    have hd := hM₀.2 e.1 (hMsub₀ e.2) f.1 (hMsub₀ f.2) hev
    by_cases he1 : e.1.1 ∈ A₁ ∪ B₁ <;>
      by_cases hf1 : f.1.1 ∈ A₁ ∪ B₁ <;>
        simp [left, right, left₀, right₀, he1, hf1] at ⊢ <;> aesop
  have hside₁ : (∀ e : M, left e ∈ A₁) ∨ (∀ e : M, left e ∈ B₁) := by
    cases c₁ with
    | false =>
        right
        intro e
        have heM₁ : e.1 ∈ M₁ := hMsub₁ e.2
        have hcolor : color₁ e.1 = false := (Finset.mem_filter.mp heM₁).2
        have hnotA : left e ∉ A₁ := by
          simpa [left, color₁] using hcolor
        exact (Finset.mem_union.mp (hends e).1).resolve_left hnotA
    | true =>
        left
        intro e
        have heM₁ : e.1 ∈ M₁ := hMsub₁ e.2
        have hcolor : color₁ e.1 = true := (Finset.mem_filter.mp heM₁).2
        simpa [left, color₁] using hcolor
  have hside₂ : (∀ e : M, right e ∈ A₂) ∨ (∀ e : M, right e ∈ B₂) := by
    cases c₂ with
    | false =>
        right
        intro e
        have hcolor : color₂ e.1 = false := (Finset.mem_filter.mp e.2).2
        have hnotA : right e ∉ A₂ := by
          simpa [right, color₂] using hcolor
        exact (Finset.mem_union.mp (hends e).2.1).resolve_left hnotA
    | true =>
        left
        intro e
        have hcolor : color₂ e.1 = true := (Finset.mem_filter.mp e.2).2
        simpa [right, color₂] using hcolor
  exact ⟨M, left, right, hmM, hends, hpairs, hside₁, hside₂⟩

/-- A full-core cross matching yields a quarter-sized family of pairwise
vertex-disjoint paths of length at most three between the selected sides.
The loss of four is solely the split into the four endpoint-side types. -/
theorem exists_disjoint_selected_handle_family_of_fullCore_crossMatching
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q₁ q₂ m : ℕ}
    {A₁ B₁ A₂ B₂ : Finset V}
    (hscaffold₁ : IsCyclicAlternatingScaffold G q₁ A₁ B₁)
    (hscaffold₂ : IsCyclicAlternatingScaffold G q₂ A₂ B₂)
    (hregions : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (hcross : HasCrossMatchingAtLeast G (A₁ ∪ B₁) (A₂ ∪ B₂) m) :
    ∃ M : Finset (V × V), ∃ a b : M → V,
      ∃ p : ∀ e : M, G.Walk (a e) (b e),
        m / 4 ≤ M.card ∧
        (∀ e : M, a e ∈ A₁ ∧ b e ∈ A₂ ∧
          (p e).IsPath ∧ 1 ≤ (p e).length ∧ (p e).length ≤ 3) ∧
        (∀ e f : M, e ≠ f → (p e).support.Disjoint (p f).support) ∧
        ∀ e : M, ∀ z ∈ (p e).support,
          z = a e ∨ IsCanonicalScaffoldMate G hscaffold₁ z (a e) ∨
          z = b e ∨ IsCanonicalScaffoldMate G hscaffold₂ z (b e) := by
  classical
  obtain ⟨M, left, right, hmM, hends, hpairs, hside₁, hside₂⟩ :=
    exists_homogeneous_oriented_crossMatching G hregions hcross
  obtain ⟨anchor₁, hanchor₁, hfix₁, hinjA₁, hinjB₁, hmate₁⟩ :=
    exists_alternatingAnchor_map G hscaffold₁
  obtain ⟨anchor₂, hanchor₂, hfix₂, hinjA₂, hinjB₂, hmate₂⟩ :=
    exists_alternatingAnchor_map G hscaffold₂
  have hAB₁ : Disjoint A₁ B₁ := by
    rcases hscaffold₁ with ⟨_, _, _, _, _, _, _, h, _, _⟩
    exact h
  have hAB₂ : Disjoint A₂ B₂ := by
    rcases hscaffold₂ with ⟨_, _, _, _, _, _, _, h, _, _⟩
    exact h
  let a : M → V := fun e => anchor₁ (left e)
  let b : M → V := fun e => anchor₂ (right e)
  have haAnchor : ∀ e : M, IsHubAnchor G A₁ (left e) (a e) := by
    intro e
    exact hanchor₁ (left e) (hends e).1
  have hbAnchor : ∀ e : M, IsHubAnchor G A₂ (right e) (b e) := by
    intro e
    exact hanchor₂ (right e) (hends e).2.1
  have hhandle : ∀ e : M, ∃ w : G.Walk (a e) (b e),
      w.IsPath ∧ 1 ≤ w.length ∧ w.length ≤ 3 ∧
        ∀ z ∈ w.support,
          z = a e ∨ z = left e ∨ z = right e ∨ z = b e := by
    intro e
    exact exists_selected_handle_of_hubAnchors G hregions
      (hends e).1 (hends e).2.1 (hends e).2.2 (haAnchor e) (hbAnchor e)
  let p : ∀ e : M, G.Walk (a e) (b e) := fun e =>
    Classical.choose (hhandle e)
  have hpSpec : ∀ e : M,
      (p e).IsPath ∧ 1 ≤ (p e).length ∧ (p e).length ≤ 3 ∧
        ∀ z ∈ (p e).support,
          z = a e ∨ z = left e ∨ z = right e ∨ z = b e := by
    intro e
    exact Classical.choose_spec (hhandle e)
  have hcrossNe : ∀ u ∈ A₁ ∪ B₁, ∀ v ∈ A₂ ∪ B₂, u ≠ v := by
    intro u hu v hv huv
    exact (Finset.disjoint_left.mp hregions) hu (huv ▸ hv)
  have haa : ∀ e f : M, e ≠ f → a e ≠ a f := by
    intro e f hef haf
    apply (hpairs e f hef).1
    rcases hside₁ with hA | hB
    · exact hinjA₁ (by simpa using hA e) (by simpa using hA f) haf
    · exact hinjB₁ (by simpa using hB e) (by simpa using hB f) haf
  have hal : ∀ e f : M, e ≠ f → a e ≠ left f := by
    intro e f hef
    rcases hside₁ with hA | hB
    · change anchor₁ (left e) ≠ left f
      rw [hfix₁ (left e) (hA e)]
      exact (hpairs e f hef).1
    · intro h
      exact (Finset.disjoint_left.mp hAB₁) (haAnchor e).1 (h ▸ hB f)
  have hla : ∀ e f : M, e ≠ f → left e ≠ a f := by
    intro e f hef h
    exact hal f e hef.symm h.symm
  have hbb : ∀ e f : M, e ≠ f → b e ≠ b f := by
    intro e f hef hbf
    apply (hpairs e f hef).2.2.2
    rcases hside₂ with hA | hB
    · exact hinjA₂ (by simpa using hA e) (by simpa using hA f) hbf
    · exact hinjB₂ (by simpa using hB e) (by simpa using hB f) hbf
  have hbr : ∀ e f : M, e ≠ f → b e ≠ right f := by
    intro e f hef
    rcases hside₂ with hA | hB
    · change anchor₂ (right e) ≠ right f
      rw [hfix₂ (right e) (hA e)]
      exact (hpairs e f hef).2.2.2
    · intro h
      exact (Finset.disjoint_left.mp hAB₂) (hbAnchor e).1 (h ▸ hB f)
  have hrb : ∀ e f : M, e ≠ f → right e ≠ b f := by
    intro e f hef h
    exact hbr f e hef.symm h.symm
  have hfirst : ∀ e f : M, e ≠ f → ∀ u,
      (u = a e ∨ u = left e) → ∀ v,
        (v = a f ∨ v = left f) → u ≠ v := by
    intro e f hef u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact haa e f hef
    · exact hal e f hef
    · exact hla e f hef
    · exact (hpairs e f hef).1
  have hsecond : ∀ e f : M, e ≠ f → ∀ u,
      (u = right e ∨ u = b e) → ∀ v,
        (v = right f ∨ v = b f) → u ≠ v := by
    intro e f hef u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (hpairs e f hef).2.2.2
    · exact hrb e f hef
    · exact hbr e f hef
    · exact hbb e f hef
  refine ⟨M, a, b, p, hmM, ?_, ?_, ?_⟩
  · intro e
    exact ⟨(haAnchor e).1, (hbAnchor e).1, (hpSpec e).1,
      (hpSpec e).2.1, (hpSpec e).2.2.1⟩
  · intro e f hef
    rw [List.disjoint_left]
    intro z hze hzf
    have hze' := (hpSpec e).2.2.2 z hze
    have hzf' := (hpSpec f).2.2.2 z hzf
    have hzeSide : (z = a e ∨ z = left e) ∨
        (z = right e ∨ z = b e) := by
      rcases hze' with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hzfSide : (z = a f ∨ z = left f) ∨
        (z = right f ∨ z = b f) := by
      rcases hzf' with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases hzeSide with hzeFirst | hzeSecond
    · rcases hzfSide with hzfFirst | hzfSecond
      · exact hfirst e f hef z hzeFirst z hzfFirst rfl
      · have hz₁ : z ∈ A₁ ∪ B₁ := by
          rcases hzeFirst with h | h
          · exact h ▸ Finset.mem_union_left _ (haAnchor e).1
          · exact h ▸ (hends e).1
        have hz₂ : z ∈ A₂ ∪ B₂ := by
          rcases hzfSecond with h | h
          · exact h ▸ (hends f).2.1
          · exact h ▸ Finset.mem_union_left _ (hbAnchor f).1
        exact hcrossNe z hz₁ z hz₂ rfl
    · rcases hzfSide with hzfFirst | hzfSecond
      · have hz₂ : z ∈ A₂ ∪ B₂ := by
          rcases hzeSecond with h | h
          · exact h ▸ (hends e).2.1
          · exact h ▸ Finset.mem_union_left _ (hbAnchor e).1
        have hz₁ : z ∈ A₁ ∪ B₁ := by
          rcases hzfFirst with h | h
          · exact h ▸ Finset.mem_union_left _ (haAnchor f).1
          · exact h ▸ (hends f).1
        exact hcrossNe z hz₁ z hz₂ rfl
      · exact hsecond e f hef z hzeSecond z hzfSecond rfl
  · intro e z hz
    rcases (hpSpec e).2.2.2 z hz with h | h | h | h
    · exact Or.inl h
    · by_cases hleftA : left e ∈ A₁
      · left
        rw [h]
        exact (hfix₁ (left e) hleftA).symm
      · right
        left
        have hleftB : left e ∈ B₁ :=
          (Finset.mem_union.mp (hends e).1).resolve_left hleftA
        simpa [a, h] using hmate₁ (left e) hleftB
    · by_cases hrightA : right e ∈ A₂
      · right
        right
        left
        rw [h]
        exact (hfix₂ (right e) hrightA).symm
      · right
        right
        right
        have hrightB : right e ∈ B₂ :=
          (Finset.mem_union.mp (hends e).2.1).resolve_left hrightA
        simpa [b, h] using hmate₂ (right e) hrightB
    · exact Or.inr (Or.inr (Or.inl h))

/-! ## Global selection of full-core handles -/

/-- A pairwise-disjoint finite family with more members than a forbidden
vertex set contains a member disjoint from that set.  One forbidden vertex
can meet at most one member of the family. -/
theorem exists_member_disjoint_of_pairwiseDisjoint_of_card_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : Finset α) (S : α → Finset β) (F : Finset β)
    (hpair : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (S e) (S f))
    (hcard : F.card < M.card) :
    ∃ e ∈ M, Disjoint (S e) F := by
  classical
  by_contra hno
  push_neg at hno
  have hmeet : ∀ e : {x // x ∈ M}, ∃ z, z ∈ S e.1 ∧ z ∈ F := by
    intro e
    exact Finset.not_disjoint_iff.mp (hno e.1 e.2)
  let pick : {x // x ∈ M} → β := fun e => Classical.choose (hmeet e)
  have hpickS : ∀ e, pick e ∈ S e.1 := fun e =>
    (Classical.choose_spec (hmeet e)).1
  have hpickF : ∀ e, pick e ∈ F := fun e =>
    (Classical.choose_spec (hmeet e)).2
  have hinj : Function.Injective pick := by
    intro e f hef
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hpair e.1 e.2 f.1 f.2 (fun h => hne (Subtype.ext h))))
        (hpickS e) (hef ▸ hpickS f)
  have himage : (Finset.univ.image pick) ⊆ F := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨e, _he, rfl⟩
    exact hpickF e
  have hle : M.card ≤ F.card := by
    calc
      M.card = Fintype.card {x // x ∈ M} := by simp
      _ = (Finset.univ.image pick).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
      _ ≤ F.card := Finset.card_le_card himage
  omega

/-- A support of a path of length at most three contains at most four
vertices. -/
theorem Walk.support_toFinset_card_le_four_of_length_le_three
    {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length ≤ 3) : p.support.toFinset.card ≤ 4 := by
  calc
    p.support.toFinset.card ≤ p.support.length := List.toFinset_card_le _
    _ = p.length + 1 := p.length_support
    _ ≤ 4 := by omega

/-- Along a finite chain of distinct-hub interactions, quarter-sized local
handle families can be chosen globally vertex-disjoint.  The budget charges
at most four vertices for each earlier length-at-most-three handle. -/
theorem exists_globally_disjoint_selected_handle_chain
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : ι → Finset V)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j)) :
    ∀ {m R : ℕ} (Z : Finset V) (hub : Fin (m + 1) → ι),
      (∀ i : Fin m, hub i.castSucc ≠ hub i.succ) →
      Z.card + 4 * m < R / 4 →
      (∀ i : Fin m,
        HasCrossMatchingAtLeast G
          (A (hub i.castSucc) ∪ B (hub i.castSucc))
          (A (hub i.succ) ∪ B (hub i.succ)) R) →
      ∃ a b : Fin m → V, ∃ p : ∀ i : Fin m, G.Walk (a i) (b i),
        (∀ i, a i ∈ A (hub i.castSucc) ∧
          b i ∈ A (hub i.succ) ∧
          (p i).IsPath ∧ 1 ≤ (p i).length ∧ (p i).length ≤ 3) ∧
        (∀ i j, i ≠ j →
          Disjoint (p i).support.toFinset (p j).support.toFinset) ∧
        (∀ i, Disjoint (p i).support.toFinset Z) ∧
        ∀ i, ∀ z ∈ (p i).support,
          z = a i ∨
            IsCanonicalScaffoldMate G (hscaffold (hub i.castSucc)) z (a i) ∨
          z = b i ∨
            IsCanonicalScaffoldMate G (hscaffold (hub i.succ)) z (b i) := by
  classical
  intro m
  induction m with
  | zero =>
      intro R Z hub _hne _hbudget _hstep
      exact ⟨fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, by simp⟩
  | succ m ih =>
      intro R Z hub hne hbudget hstep
      let hub₀ : Fin (m + 1) → ι := fun i => hub i.castSucc
      have hne₀ : ∀ i : Fin m, hub₀ i.castSucc ≠ hub₀ i.succ := by
        intro i
        simpa [hub₀] using hne i.castSucc
      have hbudget₀ : Z.card + 4 * m < R / 4 := by omega
      have hstep₀ : ∀ i : Fin m,
          HasCrossMatchingAtLeast G
            (A (hub₀ i.castSucc) ∪ B (hub₀ i.castSucc))
            (A (hub₀ i.succ) ∪ B (hub₀ i.succ)) R := by
        intro i
        simpa [hub₀] using hstep i.castSucc
      obtain ⟨a, b, p, hp, hpdisj, hpZ, hpMate⟩ :=
        ih Z hub₀ hne₀ hbudget₀ hstep₀
      let last : Fin (m + 1) := Fin.last m
      obtain ⟨M, aM, bM, pM, hMcard, hM, hMdisj, hMmate⟩ :=
        exists_disjoint_selected_handle_family_of_fullCore_crossMatching
          G (hscaffold (hub last.castSucc)) (hscaffold (hub last.succ))
            (hregions _ _ (hne last)) (hstep last)
      let F : Finset V :=
        Z ∪ (Finset.univ : Finset (Fin m)).biUnion
          (fun i => (p i).support.toFinset)
      have hFcard : F.card ≤ Z.card + 4 * m := by
        dsimp [F]
        have hu := Finset.card_union_le Z
          ((Finset.univ : Finset (Fin m)).biUnion
            (fun i => (p i).support.toFinset))
        have hb : ((Finset.univ : Finset (Fin m)).biUnion
            (fun i => (p i).support.toFinset)).card ≤ 4 * m := by
          calc
            ((Finset.univ : Finset (Fin m)).biUnion
                (fun i => (p i).support.toFinset)).card ≤
                (Finset.univ : Finset (Fin m)).card * 4 := by
                  apply Finset.card_biUnion_le_card_mul
                  intro i _hi
                  exact Walk.support_toFinset_card_le_four_of_length_le_three
                    (p i) (hp i).2.2.2.2
            _ = 4 * m := by simp [Nat.mul_comm]
        omega
      have hFM : F.card < M.card :=
        (hFcard.trans_lt hbudget₀).trans_le hMcard
      obtain ⟨e, _heM, heF⟩ :=
        exists_member_disjoint_of_pairwiseDisjoint_of_card_lt
          (Finset.univ : Finset M) (fun e => (pM e).support.toFinset) F
          (by
            intro e he f hf hef
            simpa [Finset.disjoint_left, List.disjoint_left] using
              hMdisj e f hef)
          (by simpa using hFM)
      let eM : M := e
      let a' : Fin (m + 1) → V := Fin.lastCases (aM eM) a
      let b' : Fin (m + 1) → V := Fin.lastCases (bM eM) b
      let p' : ∀ i : Fin (m + 1), G.Walk (a' i) (b' i) :=
        Fin.lastCases
          ((pM eM).copy (by simp [a']) (by simp [b']))
          (fun i => (p i).copy (by simp [a']) (by simp [b']))
      refine ⟨a', b', p', ?_, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simpa [a', b', p', eM, last] using hM eM
        | cast i =>
            simpa [a', b', p', hub₀] using hp i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                have hjF : (p j).support.toFinset ⊆ F := by
                  intro z hz
                  apply Finset.mem_union_right
                  exact Finset.mem_biUnion.mpr
                    ⟨j, Finset.mem_univ _, by simpa using hz⟩
                have hd := heF.mono_right hjF
                simpa [p', eM] using hd
        | cast i =>
            induction j using Fin.lastCases with
            | last =>
                have hiF : (p i).support.toFinset ⊆ F := by
                  intro z hz
                  apply Finset.mem_union_right
                  exact Finset.mem_biUnion.mpr
                    ⟨i, Finset.mem_univ _, by simpa using hz⟩
                have hd := heF.symm.mono_left hiF
                simpa [p', eM] using hd
            | cast j =>
                have hij' : i ≠ j := by
                  intro h
                  exact hij (congrArg Fin.castSucc h)
                simpa [p'] using hpdisj i j hij'
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simpa [p', eM] using
              (heF.mono_right (Finset.subset_union_left : Z ⊆ F))
        | cast i => simpa [p'] using hpZ i
      · intro i z hz
        induction i using Fin.lastCases with
        | last =>
            simpa [a', b', p', eM, last] using
              hMmate eM z (by simpa [p', eM] using hz)
        | cast i =>
            simpa [a', b', p', hub₀] using
              hpMate i z (by simpa [p'] using hz)

/-- Walk-indexed form of the global full-core handle selector, with an
initial finite set avoided by every selected handle. -/
theorem exists_globally_disjoint_selected_handles_along_walk_avoiding
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph ι)
    (A B : ι → Finset V) {q R : ℕ}
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j))
    (Z : Finset V)
    {u v : ι} (w : H.Walk u v)
    (hbudget : Z.card + 4 * w.length < R / 4)
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R) :
    ∃ a b : Fin w.length → V,
      ∃ p : ∀ i : Fin w.length, G.Walk (a i) (b i),
        (∀ i, a i ∈ A (w.getVert i.val) ∧
          b i ∈ A (w.getVert (i.val + 1)) ∧
          (p i).IsPath ∧ 1 ≤ (p i).length ∧ (p i).length ≤ 3) ∧
        (∀ i j, i ≠ j →
          Disjoint (p i).support.toFinset (p j).support.toFinset) ∧
        (∀ i, Disjoint (p i).support.toFinset Z) ∧
        ∀ i, ∀ z ∈ (p i).support,
          z = a i ∨
            IsCanonicalScaffoldMate G
              (hscaffold (w.getVert i.val)) z (a i) ∨
          z = b i ∨
            IsCanonicalScaffoldMate G
              (hscaffold (w.getVert (i.val + 1))) z (b i) := by
  let hub : Fin (w.length + 1) → ι := fun i => w.getVert i.val
  have hne : ∀ i : Fin w.length, hub i.castSucc ≠ hub i.succ := by
    intro i
    exact (w.adj_getVert_succ i.isLt).ne
  have hstep : ∀ i : Fin w.length,
      HasCrossMatchingAtLeast G
        (A (hub i.castSucc) ∪ B (hub i.castSucc))
        (A (hub i.succ) ∪ B (hub i.succ)) R := by
    intro i
    apply hlarge
    exact w.adj_getVert_succ i.isLt
  obtain ⟨a, b, p, hp, hdisj, havoid, hmate⟩ :=
    exists_globally_disjoint_selected_handle_chain
      G A B hscaffold hregions Z hub hne hbudget hstep
  refine ⟨a, b, p, ?_, hdisj, havoid, ?_⟩
  · intro i
    simpa [hub] using hp i
  · intro i z hz
    simpa [hub] using hmate i z hz

/-- Walk-indexed form without an initial forbidden set. -/
theorem exists_globally_disjoint_selected_handles_along_walk
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph ι)
    (A B : ι → Finset V) {q R : ℕ}
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j))
    {u v : ι} (w : H.Walk u v)
    (hbudget : 4 * w.length < R / 4)
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R) :
    ∃ a b : Fin w.length → V,
      ∃ p : ∀ i : Fin w.length, G.Walk (a i) (b i),
        (∀ i, a i ∈ A (w.getVert i.val) ∧
          b i ∈ A (w.getVert (i.val + 1)) ∧
          (p i).IsPath ∧ 1 ≤ (p i).length ∧ (p i).length ≤ 3) ∧
        ∀ i j, i ≠ j →
          Disjoint (p i).support.toFinset (p j).support.toFinset := by
  obtain ⟨a, b, p, hp, hdisj, _havoid, _hmate⟩ :=
    exists_globally_disjoint_selected_handles_along_walk_avoiding
      G H A B hscaffold hregions ∅ w (by simpa using hbudget) hlarge
  exact ⟨a, b, p, hp, hdisj⟩

/-- Cyclic assembly with path-valued handles.  Removing the first edge of
each external handle turns that edge into the ordinary cross-edge expected
by the finite cyclic assembler; the remaining tail is prepended to the
internal route at the next visit. -/
theorem cycleGraph_isContained_of_cyclic_path_handles
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m k : ℕ} (hk : 3 ≤ k)
    (x y : Fin (m + 1) → V)
    (h : ∀ i : Fin (m + 1), G.Walk (x i) (y i))
    (hhPath : ∀ i, (h i).IsPath)
    (hhNonempty : ∀ i, 1 ≤ (h i).length)
    (pred : Fin (m + 1) → Fin (m + 1))
    (hpredSucc : ∀ i : Fin m, pred i.succ = i.castSucc)
    (hpredZero : pred 0 = Fin.last m)
    (r : ∀ i : Fin (m + 1), G.Walk (y (pred i)) (x i))
    (hrPath : ∀ i, (r i).IsPath)
    (htailDisj : ∀ i,
      (h (pred i)).tail.support.Disjoint (r i).support.tail)
    (hrouteDisj : ∀ i j, i ≠ j →
      ((h (pred i)).tail.append (r i)).support.Disjoint
        ((h (pred j)).tail.append (r j)).support)
    (hlong : 1 <
      (∑ i : Fin (m + 1),
        ((h (pred i)).tail.append (r i)).length) + m)
    (hlen :
      (∑ i : Fin (m + 1),
        ((h (pred i)).tail.append (r i)).length) + m + 1 = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  let a : Fin (m + 1) → V := fun i => (h (pred i)).snd
  let b : Fin (m + 1) → V := x
  let route : ∀ i : Fin (m + 1), G.Walk (a i) (b i) := fun i =>
    (h (pred i)).tail.append (r i)
  have hroute : ∀ i, (route i).IsPath := by
    intro i
    apply isPath_append_of_support_disjoint_tail G
    · exact (hhPath (pred i)).tail
    · exact hrPath i
    · exact htailDisj i
  have hcross : ∀ i : Fin m,
      G.Adj (b i.castSucc) (a i.succ) := by
    intro i
    have hn : ¬ (h i.castSucc).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty i.castSucc
    change G.Adj (x i.castSucc) ((h (pred i.succ)).snd)
    rw [hpredSucc i]
    exact (h i.castSucc).adj_snd hn
  have hclose : G.Adj (b (Fin.last m)) (a 0) := by
    have hn : ¬ (h (Fin.last m)).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty (Fin.last m)
    change G.Adj (x (Fin.last m)) ((h (pred 0)).snd)
    rw [hpredZero]
    exact (h (Fin.last m)).adj_snd hn
  apply cycleGraph_isContained_of_cyclic_cross_edges_and_disjoint_paths_fin
    G hk a b route hroute
  · intro i j hij
    exact hrouteDisj i j hij
  · exact hcross
  · exact hclose
  · simpa [route] using hlong
  · simpa [route] using hlen

/-- Cyclic predecessor on a nonempty finite ordinal. -/
def finCyclicPred {q : ℕ} (hq : 0 < q) (i : Fin q) : Fin q :=
  if hi : i.val = 0 then ⟨q - 1, by omega⟩
  else ⟨i.val - 1, by omega⟩

theorem finCyclicPred_zero {q : ℕ} (hq : 0 < q) :
    finCyclicPred hq ⟨0, hq⟩ = ⟨q - 1, by omega⟩ := by
  apply Fin.ext
  simp [finCyclicPred]

@[simp]
theorem finCyclicPred_succ {m : ℕ} (i : Fin m) :
    finCyclicPred (by omega : 0 < m + 1) i.succ = i.castSucc := by
  apply Fin.ext
  simp [finCyclicPred]

theorem finCyclicPred_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (finCyclicPred hq) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact hi.trans hj.symm
    · simp [finCyclicPred, hi, hj] at hval
      omega
  · by_cases hj : j.val = 0
    · simp [finCyclicPred, hi, hj] at hval
      omega
    · simp [finCyclicPred, hi, hj] at hval
      omega

theorem finCyclicPred_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finCyclicPred (by omega : 0 < q) i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  by_cases hi : i.val = 0
  · simp [finCyclicPred, hi] at hval
    omega
  · simp [finCyclicPred, hi] at hval
    omega

@[simp]
theorem finCyclicPred_finCyclicSucc {q : ℕ} (hq : 0 < q) (i : Fin q) :
    finCyclicPred hq (finCyclicSucc hq i) = i := by
  apply Fin.ext
  by_cases hi : i.val + 1 < q
  · have hmod : (i.val + 1) % q = i.val + 1 := Nat.mod_eq_of_lt hi
    have hne : (i.val + 1) % q ≠ 0 := by omega
    simp [finCyclicPred, finCyclicSucc, hmod, hne]
  · have hiTop : i.val + 1 = q := by omega
    simp [finCyclicPred, finCyclicSucc, hiTop]
    omega

/-- Cardinal-indexed cyclic assembly with path-valued handles. -/
theorem cycleGraph_isContained_of_cyclic_path_handles_val
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q k : ℕ} (hq : 0 < q) (hk : 3 ≤ k)
    (x y : Fin q → V)
    (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hhPath : ∀ i, (h i).IsPath)
    (hhNonempty : ∀ i, 1 ≤ (h i).length)
    (pred : Fin q → Fin q)
    (hpredNext : ∀ i j : Fin q, j.val = i.val + 1 → pred j = i)
    (hpredClose : ∀ i j : Fin q, i.val + 1 = q → j.val = 0 → pred j = i)
    (r : ∀ i : Fin q, G.Walk (y (pred i)) (x i))
    (hrPath : ∀ i, (r i).IsPath)
    (htailDisj : ∀ i,
      (h (pred i)).tail.support.Disjoint (r i).support.tail)
    (hrouteDisj : ∀ i j, i ≠ j →
      ((h (pred i)).tail.append (r i)).support.Disjoint
        ((h (pred j)).tail.append (r j)).support)
    (hlong : 1 <
      (∑ i : Fin q, ((h (pred i)).tail.append (r i)).length) + (q - 1))
    (hlen :
      (∑ i : Fin q, ((h (pred i)).tail.append (r i)).length) + q = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  let a : Fin q → V := fun i => (h (pred i)).snd
  let b : Fin q → V := x
  let route : ∀ i : Fin q, G.Walk (a i) (b i) := fun i =>
    (h (pred i)).tail.append (r i)
  have hroute : ∀ i, (route i).IsPath := by
    intro i
    apply isPath_append_of_support_disjoint_tail G
    · exact (hhPath (pred i)).tail
    · exact hrPath i
    · exact htailDisj i
  have hcross : ∀ i j : Fin q, j.val = i.val + 1 →
      G.Adj (b i) (a j) := by
    intro i j hij
    have hn : ¬ (h i).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty i
    change G.Adj (x i) ((h (pred j)).snd)
    rw [hpredNext i j hij]
    exact (h i).adj_snd hn
  have hclose : ∀ i j : Fin q, i.val + 1 = q → j.val = 0 →
      G.Adj (b i) (a j) := by
    intro i j hi hj
    have hn : ¬ (h i).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty i
    change G.Adj (x i) ((h (pred j)).snd)
    rw [hpredClose i j hi hj]
    exact (h i).adj_snd hn
  apply cycleGraph_isContained_of_cyclic_cross_edges_and_disjoint_paths_val
    G hq hk a b route hroute hrouteDisj hcross hclose
  · simpa [route] using hlong
  · simpa [route] using hlen

/-- If each internal route meets the whole external handle system only at
its own incoming or outgoing endpoint, the path-valued handles and the
internal routes splice to a simple cycle. -/
theorem cycleGraph_isContained_of_disjoint_path_handles_and_internal_routes
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m k : ℕ} (hm : 1 ≤ m) (hk : 3 ≤ k)
    (x y : Fin (m + 1) → V)
    (h : ∀ i : Fin (m + 1), G.Walk (x i) (y i))
    (hhPath : ∀ i, (h i).IsPath)
    (hhNonempty : ∀ i, 1 ≤ (h i).length)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (r : ∀ i : Fin (m + 1),
      G.Walk (y (finCyclicPred (by omega : 0 < m + 1) i)) (x i))
    (hrPath : ∀ i, (r i).IsPath)
    (hrDisj : ∀ i j, i ≠ j →
      (r i).support.Disjoint (r j).support)
    (hrExternal : ∀ i e z, z ∈ (r i).support →
      z ∈ (h e).support →
      (e = finCyclicPred (by omega : 0 < m + 1) i ∧ z = y e) ∨
        (e = i ∧ z = x e))
    (hlong : 1 <
      (∑ i : Fin (m + 1),
        ((h (finCyclicPred (by omega : 0 < m + 1) i)).tail.append
          (r i)).length) + m)
    (hlen :
      (∑ i : Fin (m + 1),
        ((h (finCyclicPred (by omega : 0 < m + 1) i)).tail.append
          (r i)).length) + m + 1 = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  let pred : Fin (m + 1) → Fin (m + 1) :=
    finCyclicPred (by omega : 0 < m + 1)
  have hpredInj : Function.Injective pred :=
    finCyclicPred_injective (by omega)
  have hpredNe : ∀ i, pred i ≠ i := by
    intro i
    exact finCyclicPred_ne_self (by omega) i
  have hxy : ∀ i, x i ≠ y i := by
    intro i hxyEq
    have hnil : (h i).Nil := (hhPath i).nil_iff_eq.mpr hxyEq
    have hzero := hnil.length_eq_zero
    have hpos := hhNonempty i
    omega
  have htailFull : ∀ e z, z ∈ (h e).tail.support →
      z ∈ (h e).support := by
    intro e z hz
    rw [(h e).support_tail_of_not_nil (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty e)] at hz
    exact List.mem_of_mem_tail hz
  have hstartNotTail : ∀ e, x e ∉ (h e).tail.support := by
    intro e
    rw [(h e).support_tail_of_not_nil (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty e)]
    have hn := (hhPath e).support_nodup
    rw [← (h e).cons_tail_support] at hn
    exact hn.notMem
  have htailDisj : ∀ i,
      (h (pred i)).tail.support.Disjoint (r i).support.tail := by
    intro i z hzH hzR
    have hzHfull := htailFull (pred i) z hzH
    rcases hrExternal i (pred i) z (List.mem_of_mem_tail hzR) hzHfull with
      hzIn | hzOut
    · have hn := (hrPath i).support_nodup
      rw [← (r i).cons_tail_support] at hn
      exact hn.notMem (hzIn.2 ▸ hzR)
    · exact hpredNe i hzOut.1
  have hrouteDisj : ∀ i j, i ≠ j →
      ((h (pred i)).tail.append (r i)).support.Disjoint
        ((h (pred j)).tail.append (r j)).support := by
    intro i j hij z hzi hzj
    rw [SimpleGraph.Walk.support_append] at hzi hzj
    simp only [List.mem_append] at hzi hzj
    rcases hzi with hzHi | hzRi <;> rcases hzj with hzHj | hzRj
    · have hzHi' := htailFull (pred i) z hzHi
      have hzHj' := htailFull (pred j) z hzHj
      exact hhDisj (pred i) (pred j)
        (fun hpred => hij (hpredInj hpred)) hzHi' hzHj'
    · have hzHi' := htailFull (pred i) z hzHi
      rcases hrExternal j (pred i) z (List.mem_of_mem_tail hzRj) hzHi' with
        hzIn | hzOut
      · exact hij (hpredInj hzIn.1)
      · exact hstartNotTail j (hzOut.1 ▸ hzOut.2 ▸ hzHi)
    · have hzHj' := htailFull (pred j) z hzHj
      rcases hrExternal i (pred j) z (List.mem_of_mem_tail hzRi) hzHj' with
        hzIn | hzOut
      · exact hij (hpredInj hzIn.1.symm)
      · exact hstartNotTail i (hzOut.1 ▸ hzOut.2 ▸ hzHj)
    · exact hrDisj i j hij (List.mem_of_mem_tail hzRi)
        (List.mem_of_mem_tail hzRj)
  apply cycleGraph_isContained_of_cyclic_path_handles
    (r := r) G hk x y h hhPath hhNonempty pred
  · intro i
    exact finCyclicPred_succ i
  · apply Fin.ext
    simpa [pred] using congrArg Fin.val
      (finCyclicPred_zero (q := m + 1) (by omega))
  · exact hrPath
  · exact htailDisj
  · exact hrouteDisj
  · simpa [pred] using hlong
  · simpa [pred] using hlen

/-- Cardinal-indexed form of the path-handle/internal-route splice. -/
theorem cycleGraph_isContained_of_disjoint_path_handles_and_internal_routes_val
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q k : ℕ} (hq : 2 ≤ q) (hk : 3 ≤ k)
    (x y : Fin q → V)
    (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hhPath : ∀ i, (h i).IsPath)
    (hhNonempty : ∀ i, 1 ≤ (h i).length)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (r : ∀ i : Fin q,
      G.Walk (y (finCyclicPred (by omega : 0 < q) i)) (x i))
    (hrPath : ∀ i, (r i).IsPath)
    (hrDisj : ∀ i j, i ≠ j →
      (r i).support.Disjoint (r j).support)
    (hrExternal : ∀ i e z, z ∈ (r i).support →
      z ∈ (h e).support →
      (e = finCyclicPred (by omega : 0 < q) i ∧ z = y e) ∨
        (e = i ∧ z = x e))
    (hlong : 1 <
      (∑ i : Fin q,
        ((h (finCyclicPred (by omega : 0 < q) i)).tail.append
          (r i)).length) + (q - 1))
    (hlen :
      (∑ i : Fin q,
        ((h (finCyclicPred (by omega : 0 < q) i)).tail.append
          (r i)).length) + q = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  let pred : Fin q → Fin q := finCyclicPred (by omega : 0 < q)
  have hpredInj : Function.Injective pred :=
    finCyclicPred_injective (by omega)
  have hpredNe : ∀ i, pred i ≠ i := by
    intro i
    exact finCyclicPred_ne_self hq i
  have hxy : ∀ i, x i ≠ y i := by
    intro i hxyEq
    have hnil : (h i).Nil := (hhPath i).nil_iff_eq.mpr hxyEq
    have hzero := hnil.length_eq_zero
    have hpos := hhNonempty i
    omega
  have htailFull : ∀ e z, z ∈ (h e).tail.support →
      z ∈ (h e).support := by
    intro e z hz
    rw [(h e).support_tail_of_not_nil (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty e)] at hz
    exact List.mem_of_mem_tail hz
  have hstartNotTail : ∀ e, x e ∉ (h e).tail.support := by
    intro e
    rw [(h e).support_tail_of_not_nil (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hhNonempty e)]
    have hn := (hhPath e).support_nodup
    rw [← (h e).cons_tail_support] at hn
    exact hn.notMem
  have htailDisj : ∀ i,
      (h (pred i)).tail.support.Disjoint (r i).support.tail := by
    intro i z hzH hzR
    have hzHfull := htailFull (pred i) z hzH
    rcases hrExternal i (pred i) z (List.mem_of_mem_tail hzR) hzHfull with
      hzIn | hzOut
    · have hn := (hrPath i).support_nodup
      rw [← (r i).cons_tail_support] at hn
      exact hn.notMem (hzIn.2 ▸ hzR)
    · exact hpredNe i hzOut.1
  have hrouteDisj : ∀ i j, i ≠ j →
      ((h (pred i)).tail.append (r i)).support.Disjoint
        ((h (pred j)).tail.append (r j)).support := by
    intro i j hij z hzi hzj
    rw [SimpleGraph.Walk.support_append] at hzi hzj
    simp only [List.mem_append] at hzi hzj
    rcases hzi with hzHi | hzRi <;> rcases hzj with hzHj | hzRj
    · have hzHi' := htailFull (pred i) z hzHi
      have hzHj' := htailFull (pred j) z hzHj
      exact hhDisj (pred i) (pred j)
        (fun hpred => hij (hpredInj hpred)) hzHi' hzHj'
    · have hzHi' := htailFull (pred i) z hzHi
      rcases hrExternal j (pred i) z (List.mem_of_mem_tail hzRj) hzHi' with
        hzIn | hzOut
      · exact hij (hpredInj hzIn.1)
      · exact hstartNotTail j (hzOut.1 ▸ hzOut.2 ▸ hzHi)
    · have hzHj' := htailFull (pred j) z hzHj
      rcases hrExternal i (pred j) z (List.mem_of_mem_tail hzRi) hzHj' with
        hzIn | hzOut
      · exact hij (hpredInj hzIn.1.symm)
      · exact hstartNotTail i (hzOut.1 ▸ hzOut.2 ▸ hzHj)
    · exact hrDisj i j hij (List.mem_of_mem_tail hzRi)
        (List.mem_of_mem_tail hzRj)
  apply cycleGraph_isContained_of_cyclic_path_handles_val
    G (by omega) hk x y h hhPath hhNonempty pred
  · intro i j hij
    have hj0 : j.val ≠ 0 := by omega
    apply Fin.ext
    simp [pred, finCyclicPred, hj0]
    omega
  · intro i j hi hj
    apply Fin.ext
    simp [pred, finCyclicPred, hj]
    omega
  · exact hrPath
  · exact htailDisj
  · exact hrouteDisj
  · simpa [pred] using hlong
  · simpa [pred] using hlen

/-- Endpoints obtained by rotating a globally disjoint cyclic handle family
are all distinct in exactly the form required by greedy robust routing. -/
theorem cyclic_path_handle_endpoints_pairwise
    {V : Type*} {G : SimpleGraph V} {q : ℕ} (hq : 2 ≤ q)
    (x y : Fin q → V) (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hhPath : ∀ i, (h i).IsPath)
    (hhNonempty : ∀ i, 1 ≤ (h i).length)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support) :
    let pred := finCyclicPred (by omega : 0 < q)
    let a : Fin q → V := fun i => y (pred i)
    let b : Fin q → V := x
    (∀ i, a i ≠ b i) ∧
      ∀ i j, i ≠ j →
        a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j := by
  let pred := finCyclicPred (by omega : 0 < q)
  let a : Fin q → V := fun i => y (pred i)
  let b : Fin q → V := x
  have hpredInj : Function.Injective pred := finCyclicPred_injective (by omega)
  have hpredNe : ∀ i, pred i ≠ i := fun i => finCyclicPred_ne_self hq i
  have hxy : ∀ i, x i ≠ y i := by
    intro i hEq
    have hnil : (h i).Nil := (hhPath i).nil_iff_eq.mpr hEq
    have hzero := hnil.length_eq_zero
    have hpos := hhNonempty i
    omega
  refine ⟨?_, ?_⟩
  · intro i hai
    dsimp [a, b] at hai
    exact hhDisj (pred i) i (hpredNe i)
      (h (pred i)).end_mem_support
      (by rw [hai]; exact (h i).start_mem_support)
  · intro i j hij
    have hpredij : pred i ≠ pred j := fun hEq => hij (hpredInj hEq)
    have haa : a i ≠ a j := by
      intro hEq
      dsimp [a] at hEq
      exact hhDisj (pred i) (pred j) hpredij
        (h (pred i)).end_mem_support
        (by rw [hEq]; exact (h (pred j)).end_mem_support)
    have hab : a i ≠ b j := by
      by_cases hp : pred i = j
      · intro hEq
        subst j
        exact hxy (pred i) (by simpa [a, b] using hEq.symm)
      · intro hEq
        dsimp [a, b] at hEq
        exact hhDisj (pred i) j hp
          (h (pred i)).end_mem_support
          (by rw [hEq]; exact (h j).start_mem_support)
    have hba : b i ≠ a j := by
      by_cases hp : i = pred j
      · intro hEq
        subst i
        exact hxy (pred j) (by simpa [a, b] using hEq)
      · intro hEq
        dsimp [a, b] at hEq
        exact hhDisj i (pred j) hp
          (h i).start_mem_support
          (by rw [hEq]; exact (h (pred j)).end_mem_support)
    have hbb : b i ≠ b j := by
      intro hEq
      dsimp [b] at hEq
      exact hhDisj i j hij (h i).start_mem_support
        (by rw [hEq]; exact (h j).start_mem_support)
    exact ⟨haa, hab, hba, hbb⟩

/-- Grouped robust routing in the complement of a cyclic external handle
system.  Every internal route can meet an external handle only at its own
incoming or outgoing endpoint. -/
theorem exists_grouped_internal_routes_avoiding_cyclic_path_handles
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q θ C : ℕ} (hq : 2 ≤ q)
    (hub : Fin q → ι) (A D : ι → Finset V)
    (hrob : ∀ i, RobustPairSet G (A i) (D i) θ)
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ D i) (A j ∪ D j))
    (x y : Fin q → V) (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (hEcard :
      ((Finset.univ : Finset (Fin q)).biUnion
        (fun e => (h e).support.toFinset)).card ≤ C)
    (weight : Fin q → ℕ)
    (ha : ∀ i, y (finCyclicPred (by omega : 0 < q) i) ∈ A (hub i))
    (hb : ∀ i, x i ∈ A (hub i))
    (hab : ∀ i,
      y (finCyclicPred (by omega : 0 < q) i) ≠ x i)
    (hpairs : ∀ i j, i ≠ j →
      y (finCyclicPred (by omega : 0 < q) i) ≠
          y (finCyclicPred (by omega : 0 < q) j) ∧
      y (finCyclicPred (by omega : 0 < q) i) ≠ x j ∧
      x i ≠ y (finCyclicPred (by omega : 0 < q) j) ∧
      x i ≠ x j)
    (hU : ∀ i : ι, ∀ t : {j : Fin q // hub j = i},
      C + (∑ s : {j : Fin q // hub j = i},
        (2 * (weight s.1 + 1) + 1)) + (weight t.1 + 2) ≤ (A i).card)
    (hθ : ∀ i : ι,
      C + (∑ s : {j : Fin q // hub j = i},
        (2 * (weight s.1 + 1) + 1)) ≤ θ) :
    ∃ r : ∀ i : Fin q,
        G.Walk (y (finCyclicPred (by omega : 0 < q) i)) (x i),
      (∀ i, (r i).IsPath) ∧
      (∀ i, (r i).length = 2 * (weight i + 1)) ∧
      (∀ i j, i ≠ j → (r i).support.Disjoint (r j).support) ∧
      ∀ i e z, z ∈ (r i).support → z ∈ (h e).support →
        (e = finCyclicPred (by omega : 0 < q) i ∧ z = y e) ∨
          (e = i ∧ z = x e) := by
  classical
  let pred : Fin q → Fin q := finCyclicPred (by omega : 0 < q)
  let a : Fin q → V := fun i => y (pred i)
  let b : Fin q → V := x
  let E : Finset V := (Finset.univ : Finset (Fin q)).biUnion
    (fun e => (h e).support.toFinset)
  let visits : ι → Finset (Fin q) := fun c =>
    Finset.univ.filter (fun i => hub i = c)
  let P : ι → Finset V := fun c =>
    (visits c).image a ∪ (visits c).image b
  let F : ι → Finset V := fun c => E \ P c
  have haP : ∀ i, a i ∈ P (hub i) := by
    intro i
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  have hbP : ∀ i, b i ∈ P (hub i) := by
    intro i
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  have haF : ∀ i, a i ∉ F (hub i) := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2 (haP i)
  have hbF : ∀ i, b i ∉ F (hub i) := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2 (hbP i)
  have hFcard : ∀ c, (F c).card ≤ C := by
    intro c
    exact (Finset.card_le_card Finset.sdiff_subset).trans
      (by simpa [E] using hEcard)
  obtain ⟨r, hrPath, hrLen, hrAvoid, _hrLoc, hrDisj⟩ :=
    exists_pairwise_disjoint_even_paths_lengths_grouped_robust
      G weight hub A D hrob hregions a b F
      (by simpa [a, pred] using ha) (by simpa [b] using hb)
      haF hbF (by simpa [a, b, pred] using hab)
      (by simpa [a, b, pred] using hpairs)
      (by
        intro c t
        have hc := hU c t
        have hFc := hFcard c
        omega)
      (by
        intro c
        have hc := hθ c
        have hFc := hFcard c
        omega)
  refine ⟨r, hrPath, hrLen, hrDisj, ?_⟩
  intro i e z hzR hzH
  have hzE : z ∈ E := Finset.mem_biUnion.mpr
    ⟨e, Finset.mem_univ _, by simpa using hzH⟩
  have hzP : z ∈ P (hub i) := by
    by_contra hzP
    exact hrAvoid i z hzR (Finset.mem_sdiff.mpr ⟨hzE, hzP⟩)
  have hzEndpoint : z = a i ∨ z = b i := by
    rcases Finset.mem_union.mp hzP with hzA | hzB
    · rcases Finset.mem_image.mp hzA with ⟨t, ht, hta⟩
      have hthub : hub t = hub i := (Finset.mem_filter.mp ht).2
      by_cases hti : t = i
      · subst t
        exact Or.inl hta.symm
      · exact (hrDisj i t (Ne.symm hti)) hzR
          (hta ▸ (r t).start_mem_support) |>.elim
    · rcases Finset.mem_image.mp hzB with ⟨t, ht, htb⟩
      have hthub : hub t = hub i := (Finset.mem_filter.mp ht).2
      by_cases hti : t = i
      · subst t
        exact Or.inr htb.symm
      · exact (hrDisj i t (Ne.symm hti)) hzR
          (htb ▸ (r t).end_mem_support) |>.elim
  rcases hzEndpoint with hza | hzb
  · left
    have he : e = pred i := by
      by_contra hne
      exact hhDisj e (pred i) hne hzH
        (by rw [hza]; exact (h (pred i)).end_mem_support)
    exact ⟨by simpa [pred] using he, by simpa [a, pred, he] using hza⟩
  · right
    have he : e = i := by
      by_contra hne
      exact hhDisj e i hne hzH
        (by rw [hzb]; exact (h i).start_mem_support)
    exact ⟨he, by simpa [b, he] using hzb⟩

/-- A nontrivial closed auxiliary walk with large full-core matchings admits
a globally disjoint cyclic selected-handle system avoiding an initial set,
with incoming endpoints obtained by cyclic predecessor rotation. -/
theorem exists_cyclic_selected_path_handles_along_closed_walk_avoiding
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph ι)
    (A B : ι → Finset V) {q R : ℕ}
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j))
    (Z : Finset V)
    {u : ι} (w : H.Walk u u) (hwlen : 2 ≤ w.length)
    (hbudget : Z.card + 4 * w.length < R / 4)
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R) :
    ∃ x y : Fin w.length → V,
      ∃ h : ∀ i : Fin w.length, G.Walk (x i) (y i),
        (∀ i, x i ∈ A (w.getVert i.val) ∧
          y i ∈ A (w.getVert (i.val + 1)) ∧
          (h i).IsPath ∧ 1 ≤ (h i).length ∧ (h i).length ≤ 3) ∧
        (∀ i,
          y (finCyclicPred (by omega : 0 < w.length) i) ∈
            A (w.getVert i.val)) ∧
        (∀ i j, i ≠ j → (h i).support.Disjoint (h j).support) ∧
        (∀ i, Disjoint (h i).support.toFinset Z) ∧
        ∀ i, ∀ z ∈ (h i).support,
          z = x i ∨
            IsCanonicalScaffoldMate G
              (hscaffold (w.getVert i.val)) z (x i) ∨
          z = y i ∨
            IsCanonicalScaffoldMate G
              (hscaffold (w.getVert (i.val + 1))) z (y i) := by
  obtain ⟨x, y, h, hh, hhDisj, hhZ, hhMate⟩ :=
    exists_globally_disjoint_selected_handles_along_walk_avoiding
      G H A B hscaffold hregions Z w hbudget hlarge
  have hhDisjList : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support := by
    intro i j hij
    simpa [Finset.disjoint_left, List.disjoint_left] using hhDisj i j hij
  refine ⟨x, y, h, hh, ?_, hhDisjList, hhZ, hhMate⟩
  intro i
  let pred := finCyclicPred (by omega : 0 < w.length)
  by_cases hi : i.val = 0
  · have hpred : pred i = ⟨w.length - 1, by omega⟩ := by
      apply Fin.ext
      simp [pred, finCyclicPred, hi]
    have hy := (hh (pred i)).2.1
    have hend : w.getVert ((pred i).val + 1) = w.getVert i.val := by
      calc
        w.getVert ((pred i).val + 1) = w.getVert w.length := by
          apply congrArg w.getVert
          have hpv := congrArg Fin.val hpred
          dsimp at hpv
          omega
        _ = u := w.getVert_length
        _ = w.getVert i.val := by rw [hi]; simp
    change y (pred i) ∈ A (w.getVert i.val)
    rw [← hend]
    exact hy
  · have hpredVal : (pred i).val + 1 = i.val := by
      simp [pred, finCyclicPred, hi]
      omega
    have hy := (hh (pred i)).2.1
    change y (pred i) ∈ A (w.getVert i.val)
    simpa [hpredVal] using hy

/-- Closed-walk selected handles without an initial forbidden set. -/
theorem exists_cyclic_selected_path_handles_along_closed_walk
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph ι)
    (A B : ι → Finset V) {q R : ℕ}
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j : ι, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j))
    {u : ι} (w : H.Walk u u) (hwlen : 2 ≤ w.length)
    (hbudget : 4 * w.length < R / 4)
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R) :
    ∃ x y : Fin w.length → V,
      ∃ h : ∀ i : Fin w.length, G.Walk (x i) (y i),
        (∀ i, x i ∈ A (w.getVert i.val) ∧
          y i ∈ A (w.getVert (i.val + 1)) ∧
          (h i).IsPath ∧ 1 ≤ (h i).length ∧ (h i).length ≤ 3) ∧
        (∀ i,
          y (finCyclicPred (by omega : 0 < w.length) i) ∈
            A (w.getVert i.val)) ∧
        ∀ i j, i ≠ j → (h i).support.Disjoint (h j).support := by
  obtain ⟨x, y, h, hh, hin, hdisj, _havoid, _hmate⟩ :=
    exists_cyclic_selected_path_handles_along_closed_walk_avoiding
      G H A B hscaffold hregions ∅ w hwlen (by simpa using hbudget) hlarge
  exact ⟨x, y, h, hh, hin, hdisj⟩

/-- Full-core doubled-path lift.  Cross matchings may use either side of an
alternating scaffold.  The selected handles are anchored back in the major
side, while the canonical-mate avoidance invariant keeps all doubled
scaffold routes internally disjoint from every handle. -/
theorem cycleGraph_isContained_of_largeFullCoreMatching_path_alternatingScaffolds
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) {u v : ι} (w : H.Walk u v)
    {d q theta R k : ℕ}
    (hwlen : w.length = d + 1) (hwpath : w.IsPath)
    (A B D : ι → Finset V)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hq : 8 ≤ q) (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hhandleBudget : 8 * (d + 1) < R / 4)
    (hk : 3 ≤ k) (hbase : 18 * (d + 1) ≤ k)
    (hevenCapacity : (k - 14 * (d + 1)) / 2 ≤
      (q - 8) * (d + 2))
    (hoddCapacity : (k - (14 * (d + 1) - 1)) / 2 ≤
      (q - 8) * (d + 1)) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  let closed : H.Walk u u := w.append w.reverse
  have hclosedLen : closed.length = (d + 2) + d := by
    simp [closed, hwlen]
    omega
  have hclosedLong : 2 ≤ closed.length := by
    rw [hclosedLen]
    omega
  have hclosedBudget : 4 * closed.length < R / 4 := by
    rw [hclosedLen]
    omega
  obtain ⟨xc, yc, hc, hhc, hinc, hhcDisj, _hhEmpty, hhcMate⟩ :=
    exists_cyclic_selected_path_handles_along_closed_walk_avoiding
      G H A B hscaffold
        (fun i j hij => (hregions i j hij).mono
          Finset.subset_union_left Finset.subset_union_left)
        ∅ closed hclosedLong (by simpa using hclosedBudget) hlarge
  let toClosed : Fin ((d + 2) + d) → Fin closed.length :=
    fun i => Fin.cast hclosedLen.symm i
  have hclosedGet : ∀ i : Fin ((d + 2) + d),
      closed.getVert (toClosed i).val =
        w.getVert (doubledPathPosition d i).val := by
    intro i
    simpa [closed, toClosed] using
      getVert_append_reverse_eq_doubledPathPosition w hwlen i
  let x : Fin ((d + 2) + d) → V := fun i => xc (toClosed i)
  let y : Fin ((d + 2) + d) → V := fun i => yc (toClosed i)
  let h : ∀ i : Fin ((d + 2) + d), G.Walk (x i) (y i) :=
    fun i => hc (toClosed i)
  have hh : ∀ i, x i ∈ A (w.getVert (doubledPathPosition d i).val) ∧
      y i ∈ A (closed.getVert ((toClosed i).val + 1)) ∧
      (h i).IsPath ∧ 1 ≤ (h i).length ∧ (h i).length ≤ 3 := by
    intro i
    have hi := hhc (toClosed i)
    exact ⟨by simpa [x, hclosedGet i] using hi.1, hi.2.1,
      hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
  have hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support := by
    intro i j hij
    apply hhcDisj (toClosed i) (toClosed j)
    intro hEq
    apply hij
    apply Fin.ext
    simpa [toClosed] using congrArg Fin.val hEq
  let pred : Fin ((d + 2) + d) → Fin ((d + 2) + d) :=
    finCyclicPred (by omega)
  let next : Fin ((d + 2) + d) → Fin ((d + 2) + d) :=
    finCyclicSucc (by omega)
  have htoPred : ∀ i, toClosed (pred i) =
      finCyclicPred (by omega : 0 < closed.length) (toClosed i) := by
    intro i
    apply Fin.ext
    by_cases hi : i.val = 0
    · simp [toClosed, pred, finCyclicPred, hclosedLen, hi]
    · simp [toClosed, pred, finCyclicPred, hclosedLen, hi]
  have hpredNext : ∀ i, pred (next i) = i := by
    intro i
    exact finCyclicPred_finCyclicSucc (by omega) i
  have hnextGet : ∀ i,
      closed.getVert (next i).val = closed.getVert (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < (d + 2) + d
    · have hmod : (i.val + 1) % ((d + 2) + d) = i.val + 1 :=
        Nat.mod_eq_of_lt hi
      simp [next, finCyclicSucc, hmod]
    · have hiTop : i.val + 1 = (d + 2) + d := by omega
      have hnextZero : (next i).val = 0 := by
        simp [next, finCyclicSucc, hiTop]
      rw [hnextZero, hiTop, ← hclosedLen]
      rw [closed.getVert_zero, closed.getVert_length]
  have haRoute : ∀ i,
      y (pred i) ∈ A (w.getVert (doubledPathPosition d i).val) := by
    intro i
    have hi := hinc (toClosed i)
    rw [← htoPred i] at hi
    simpa [y, hclosedGet i] using hi
  have hbRoute : ∀ i,
      x i ∈ A (w.getVert (doubledPathPosition d i).val) :=
    fun i => (hh i).1
  have hnextHub : ∀ i,
      closed.getVert ((toClosed i).val + 1) =
        w.getVert (doubledPathPosition d (next i)).val := by
    intro i
    have hval : (toClosed i).val = i.val := rfl
    rw [hval, ← hnextGet i]
    exact hclosedGet (next i)
  let ar : Fin ((d + 2) + d) → V := fun i => y (pred i)
  let br : Fin ((d + 2) + d) → V := x
  have hmateHandle : ∀ i, ∀ z ∈ (h i).support,
      z = x i ∨
        IsCanonicalScaffoldMate G
          (hscaffold (w.getVert (doubledPathPosition d i).val)) z (br i) ∨
      z = y i ∨
        IsCanonicalScaffoldMate G
          (hscaffold (w.getVert (doubledPathPosition d (next i)).val)) z
            (ar (next i)) := by
    intro i z hz
    rcases hhcMate (toClosed i) z (by simpa [h] using hz) with
      hz | hz | hz | hz
    · exact Or.inl (by simpa [x] using hz)
    · exact Or.inr (Or.inl (by
        rw [hclosedGet i] at hz
        simpa [br, x] using hz))
    · exact Or.inr (Or.inr (Or.inl (by simpa [y] using hz)))
    · right; right; right
      rw [hnextHub i] at hz
      simpa [ar, y, pred, next, hpredNext i] using hz
  obtain ⟨hab, hpairs⟩ :=
    cyclic_path_handle_endpoints_pairwise
      (by omega : 2 ≤ (d + 2) + d) x y h
      (fun i => (hh i).2.2.1) (fun i => (hh i).2.2.2.1) hhDisj
  let S : ℕ := ∑ i : Fin ((d + 2) + d), (h (pred i)).length
  have hSlower : (d + 2) + d ≤ S := by
    calc
      (d + 2) + d = ∑ _i : Fin ((d + 2) + d), 1 := by simp
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (hh (pred i)).2.2.2.1
  have hSupper : S ≤ 3 * ((d + 2) + d) := by
    calc
      S ≤ ∑ _i : Fin ((d + 2) + d), 3 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (hh (pred i)).2.2.2.2
      _ = 3 * ((d + 2) + d) := by simp [Nat.mul_comm]
  have hbaseLe : 12 * (d + 1) + S ≤ k := by
    omega
  have hexistsRoute : ∃ route : ∀ i : Fin ((d + 2) + d),
      G.Walk (ar i) (br i),
      (∀ i, (route i).IsPath) ∧
      (∀ i j, i ≠ j → (route i).support.Disjoint (route j).support) ∧
      (∀ i, ∀ z ∈ (route i).support,
        z ∈ (A (w.getVert (doubledPathPosition d i).val) ∪
          B (w.getVert (doubledPathPosition d i).val)) ∨
        z ∈ D (w.getVert (doubledPathPosition d i).val)) ∧
      (∀ i j z, (IsCanonicalScaffoldMate G
            (hscaffold (w.getVert (doubledPathPosition d j).val)) z (ar j) ∨
          IsCanonicalScaffoldMate G
            (hscaffold (w.getVert (doubledPathPosition d j).val)) z (br j)) →
        z ∉ (route i).support) ∧
      (∑ i, (route i).length) = k - S := by
    let base : ℕ := 12 * (d + 1) + S
    by_cases hpar : (k - base) % 2 = 0
    · let z : ℕ := (k - base) / 2
      have hdiff : k - base = 2 * z := by
        have hdivmod := Nat.div_add_mod (k - base) 2
        dsimp [z]
        omega
      have hzle : z ≤ (k - 14 * (d + 1)) / 2 := by
        dsimp [z]
        apply Nat.div_le_div_right
        dsimp [base]
        omega
      obtain ⟨weight, hweightSum, hweight⟩ :=
        exists_fin_weights_sum_eq_le_fun
          (fun _ : Fin (d + 2) => q - 8) (z := z) (by
            have hz' : z ≤ (q - 8) * (d + 2) :=
              hzle.trans hevenCapacity
            simpa [Nat.mul_comm] using hz')
      obtain ⟨route, hroute, hrouteDisj, hrouteSum, _hfirst,
          hrouteLoc, hrouteMate⟩ :=
        exists_doubled_path_alternatingScaffold_routes
          G H w hwlen hwpath A B D hscaffold hrob hmajorD hq htheta hregions
            weight hweight ar br
            (by simpa [ar] using haRoute) (by simpa [br] using hbRoute)
            (by simpa [ar, br, pred] using hab)
            (by simpa [ar, br, pred] using hpairs)
      refine ⟨route, hroute, hrouteDisj, hrouteLoc, hrouteMate, ?_⟩
      rw [hrouteSum, hweightSum]
      dsimp [base] at hdiff
      omega
    · have hmod : (k - base) % 2 = 1 := by
        have hlt := Nat.mod_lt (k - base) (by omega : 0 < 2)
        omega
      have hbasePos : 0 < base := by dsimp [base]; omega
      let z : ℕ := (k - (base - 1)) / 2
      have hpar' : (k - (base - 1)) % 2 = 0 := by
        have heq : k - (base - 1) = (k - base) + 1 := by
          dsimp [base] at hbaseLe ⊢
          omega
        rw [heq, Nat.add_mod]
        simp [hmod]
      have hdiff : k - (base - 1) = 2 * z := by
        have hdivmod := Nat.div_add_mod (k - (base - 1)) 2
        dsimp [z]
        omega
      have hzle : z ≤ (k - (14 * (d + 1) - 1)) / 2 := by
        dsimp [z]
        apply Nat.div_le_div_right
        dsimp [base]
        omega
      obtain ⟨weightTail, hweightTailSum, hweightTail⟩ :=
        exists_fin_weights_sum_eq_le_fun
          (fun _ : Fin (d + 1) => q - 8) (z := z) (by
            simpa [Nat.mul_comm] using hzle.trans hoddCapacity)
      let weight : Fin (d + 2) → ℕ := Fin.cases 0 weightTail
      have hweightZero : weight 0 = 0 := by simp [weight]
      have hweight : ∀ i, weight i ≤ q - 8 := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [weight]
        · simpa [weight] using hweightTail j
      have hweightSum : (∑ i, weight i) = z := by
        rw [Fin.sum_univ_succ]
        simpa [weight] using hweightTailSum
      obtain ⟨route, hroute, hrouteDisj, hrouteSum, hrouteLoc,
          hrouteMate⟩ :=
        exists_doubled_path_alternatingScaffold_routes_odd_first
          G H w hwlen hwpath A B D hscaffold hrob hmajorD hq htheta hregions
            (hmatch (w.getVert 0)) weight hweight hweightZero ar br
            (by simpa [ar] using haRoute) (by simpa [br] using hbRoute)
            (by simpa [ar, br, pred] using hab)
            (by simpa [ar, br, pred] using hpairs)
      refine ⟨route, hroute, hrouteDisj, hrouteLoc, hrouteMate, ?_⟩
      rw [hrouteSum, hweightSum]
      dsimp [base] at hdiff
      omega
  obtain ⟨route, hroute, hrouteDisj, hrouteLoc, hrouteMate, hrouteSum⟩ :=
    hexistsRoute
  have hrExternal : ∀ i e z, z ∈ (route i).support →
      z ∈ (h e).support →
      (e = pred i ∧ z = y e) ∨ (e = i ∧ z = x e) := by
    intro i e z hzR hzH
    rcases hmateHandle e z hzH with hz | hz | hz | hz
    · by_cases hei : e = i
      · exact Or.inr ⟨hei, hz⟩
      · exfalso
        exact hrouteDisj i e (Ne.symm hei) hzR
          (hz ▸ (route e).end_mem_support)
    · exact (hrouteMate i e z (Or.inr hz) hzR).elim
    · let j : Fin ((d + 2) + d) := next e
      have hpj : pred j = e := hpredNext e
      by_cases hij : i = j
      · subst i
        exact Or.inl ⟨hpj.symm, hz⟩
      · exfalso
        apply hrouteDisj i j hij hzR
        have harj : ar j = y e := by simp [ar, j, hpj]
        rw [hz, ← harj]
        exact (route j).start_mem_support
    · let j : Fin ((d + 2) + d) := next e
      have hpj : pred j = e := hpredNext e
      have hz' : IsCanonicalScaffoldMate G
          (hscaffold (w.getVert (doubledPathPosition d j).val)) z (ar j) := by
        simpa [j, ar, hpj] using hz
      exact (hrouteMate i j z (Or.inl hz') hzR).elim
  have htailSum :
      (∑ i : Fin ((d + 2) + d), (h (pred i)).tail.length) +
          ((d + 2) + d) = S := by
    calc
      (∑ i : Fin ((d + 2) + d), (h (pred i)).tail.length) +
          ((d + 2) + d) =
          ∑ i : Fin ((d + 2) + d), ((h (pred i)).tail.length + 1) := by
            simp [Finset.sum_add_distrib]
      _ = S := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (h (pred i)).length_tail_add_one (by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          exact (hh (pred i)).2.2.2.1)
  have htotal :
      (∑ i : Fin ((d + 2) + d),
        ((h (pred i)).tail.append (route i)).length) + ((d + 2) + d) = k := by
    simp_rw [SimpleGraph.Walk.length_append]
    rw [Finset.sum_add_distrib]
    omega
  apply cycleGraph_isContained_of_disjoint_path_handles_and_internal_routes_val
    G (by omega) hk x y h (fun i => (hh i).2.2.1)
      (fun i => (hh i).2.2.2.1) hhDisj route hroute hrouteDisj
      (by simpa [pred] using hrExternal)
  · have heq :
        (∑ i : Fin ((d + 2) + d),
          ((h (pred i)).tail.append (route i)).length) +
            ((d + 2) + d - 1) = k - 1 := by omega
    rw [heq]
    omega
  · simpa [pred] using htotal

/-- Contrapositive path-free interface for the full-core lift.  It applies
to an arbitrary auxiliary graph; no degree or connectedness hypothesis is
needed once a sufficiently long simple auxiliary path has already been
found. -/
theorem not_exists_largeFullCoreMatching_path_of_cycleFree
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) (A B D : ι → Finset V)
    {d q theta R k : ℕ}
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hq : 8 ≤ q) (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hhandleBudget : 8 * (d + 1) < R / 4)
    (hk : 3 ≤ k) (hbase : 18 * (d + 1) ≤ k)
    (hevenCapacity : (k - 14 * (d + 1)) / 2 ≤
      (q - 8) * (d + 2))
    (hoddCapacity : (k - (14 * (d + 1) - 1)) / 2 ≤
      (q - 8) * (d + 1))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    ¬ ∃ u v : ι, ∃ w : H.Walk u v,
      w.IsPath ∧ w.length = d + 1 := by
  rintro ⟨u, v, w, hwpath, hwlen⟩
  apply hcycle
  exact cycleGraph_isContained_of_largeFullCoreMatching_path_alternatingScaffolds
    G H w hwlen hwpath A B D hscaffold hrob hmajorD hq htheta hregions
      hlarge hmatch hhandleBudget hk hbase hevenCapacity hoddCapacity

/-- At the canonical square-root scale, the internal alternating routes of a
path with `floor (sqrt k / 16)` labels have capacity at least half of `k`.
This is the raw (unsubtracted) capacity required by the full-core lift. -/
theorem sqrt_sixteenth_fullCore_capacity {k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k) :
    k / 2 ≤ (9 * Nat.sqrt k - 8) * (Nat.sqrt k / 16) := by
  let s : ℕ := Nat.sqrt k
  let L : ℕ := s / 16
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have hL16 : 16 ≤ L := by
    dsimp [L]
    omega
  have hLlower : 16 * L ≤ s := by
    dsimp [L]
    have h := Nat.div_mul_le_self s 16
    simpa [Nat.mul_comm] using h
  have hkupper : k < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' k
  let r : ℕ := s - 16 * L
  have hrDecomp : 16 * L + r = s := by
    dsimp [r]
    omega
  have hr : r ≤ 15 := by
    dsimp [r, L]
    omega
  let a : ℕ := 9 * s - 8
  have haDecomp : a + 8 = 9 * s := by
    dsimp [a]
    omega
  have hrL : r * L ≤ 15 * L := Nat.mul_le_mul_right L hr
  have hrr : r * r ≤ 15 * 15 := Nat.mul_le_mul hr hr
  have hLL : 16 * L ≤ L * L := Nat.mul_le_mul_right L hL16
  have hraw : k ≤ 2 * (a * L) := by
    have hsquareUpper : k ≤ (s + 1) ^ 2 := Nat.le_of_lt hkupper
    have hpoly : (s + 1) ^ 2 ≤ 2 * (a * L) := by
      nlinarith
    exact hsquareUpper.trans hpoly
  have hdiv : k / 2 ≤ a * L := Nat.div_le_of_le_mul (by
    simpa [Nat.mul_comm] using hraw)
  simpa [a, L, s] using hdiv

/-- Tight full-core path scale.  The denominator is exactly twice the
per-hub weight capacity `9 * sqrt k - 8`; one extra quotient unit handles
natural-number rounding.  At large square-root scale it is still below the
coarser `sqrt k / 16` budget. -/
theorem tight_fullCore_scale_estimates {k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k) :
    let s := Nat.sqrt k
    let L := k / (18 * s - 16) + 1
    0 < L ∧ L ≤ s / 16 ∧ k / 2 ≤ (9 * s - 8) * L := by
  let s : ℕ := Nat.sqrt k
  let a : ℕ := 9 * s - 8
  let den : ℕ := 2 * a
  let L : ℕ := k / den + 1
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have ha : a + 8 = 9 * s := by dsimp [a]; omega
  have hden : den = 18 * s - 16 := by dsimp [den, a]; omega
  have hdenpos : 0 < den := by dsimp [den, a]; omega
  have hLpos : 0 < L := by
    simpa [L, Nat.add_comm] using Nat.succ_pos (k / den)
  have hkltDenL : k < den * L := by
    dsimp [L]
    exact Nat.lt_mul_div_succ k hdenpos
  have hcapacity : k / 2 ≤ a * L := by
    apply Nat.div_le_of_le_mul
    have hk : k ≤ 2 * (a * L) := by
      have : k ≤ den * L := hkltDenL.le
      simpa [den, Nat.mul_assoc] using this
    simpa [Nat.mul_comm] using hk
  let D : ℕ := s / 16
  have hD16 : 16 * D ≤ s := by
    dsimp [D]
    exact Nat.mul_div_le s 16
  have hsD : s ≤ 17 * D := by
    have hmod : s % 16 < 16 := Nat.mod_lt s (by omega)
    have hdivmod : 16 * (s / 16) + s % 16 = s := Nat.div_add_mod s 16
    dsimp [D]
    have hD : 15 ≤ s / 16 := by omega
    omega
  have hkupper : k < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' k
  have hdenDecomp : (18 * s - 16) + 16 = 18 * s := by omega
  have hpoly : 17 * (s + 1) ^ 2 ≤ (18 * s - 16) * s := by
    nlinarith
  have hprod : (18 * s - 16) * s ≤
      (18 * s - 16) * (17 * D) :=
    Nat.mul_le_mul_left _ hsD
  have hsqD : (s + 1) ^ 2 ≤ (18 * s - 16) * D := by
    have hscaled : 17 * (s + 1) ^ 2 ≤
        17 * ((18 * s - 16) * D) := by
      calc
        17 * (s + 1) ^ 2 ≤ (18 * s - 16) * s := hpoly
        _ ≤ (18 * s - 16) * (17 * D) := hprod
        _ = 17 * ((18 * s - 16) * D) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hkDenD : k < den * D := by
    calc
      k < (s + 1) ^ 2 := hkupper
      _ ≤ (18 * s - 16) * D := hsqD
      _ = den * D := by rw [hden]
  have hLle : L ≤ D := by
    dsimp [L]
    have hdivlt : k / den < D :=
      (Nat.div_lt_iff_lt_mul hdenpos).2 (by
        simpa [Nat.mul_comm] using hkDenD)
    omega
  have hall : 0 < L ∧ L ≤ D ∧ k / 2 ≤ a * L :=
    ⟨hLpos, hLle, hcapacity⟩
  simpa only [s, L, D, a, den, hden] using hall

/-- Path exclusion at the tight full-core scale.  Compared with the
`sqrt k / 16` specialization below, this uses the actual alternating-route
capacity and therefore places the number of scaffold labels at asymptotic
scale `sqrt k / 18`. -/
theorem not_exists_tight_fullCoreMatching_path_of_cycleFree
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let L := k / (18 * Nat.sqrt k - 16) + 1
    ¬ ∃ u v : ι, ∃ w : H.Walk u v,
      w.IsPath ∧ w.length = L := by
  let s : ℕ := Nat.sqrt k
  let L : ℕ := k / (18 * s - 16) + 1
  let d : ℕ := L - 1
  obtain ⟨hLpos, hLcoarse, hcapacity⟩ :=
    tight_fullCore_scale_estimates hsqrt
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have hsk : s ≤ k := by simpa [s] using Nat.sqrt_le_self k
  have hd : d + 1 = L := by
    dsimp [d]
    exact Nat.sub_add_cancel (by simpa [L, s] using hLpos)
  change ¬ ∃ u v : ι, ∃ w : H.Walk u v, w.IsPath ∧ w.length = L
  rw [← hd]
  apply not_exists_largeFullCoreMatching_path_of_cycleFree
    G H A B D (d := d) (q := 9 * Nat.sqrt k) (theta := theta)
      (R := R) (k := k) hscaffold hrob hmajorD
  · omega
  · exact htheta
  · exact hregions
  · exact hlarge
  · exact hmatch
  · have hLs : L ≤ s := by
      exact hLcoarse.trans (Nat.div_le_self s 16)
    have h32 : 32 * L ≤ 2 * s := by
      have h16 : 16 * L ≤ s := by
        have hmul := Nat.mul_le_mul_left 16 hLcoarse
        exact hmul.trans (Nat.mul_div_le s 16)
      omega
    omega
  · omega
  · rw [hd]
    have hLs : L ≤ s := hLcoarse.trans (Nat.div_le_self s 16)
    have hsquare : s ^ 2 ≤ k := by
      simpa [s] using Nat.sqrt_le' k
    have h18 : 18 ≤ s := by omega
    exact (Nat.mul_le_mul h18 hLs).trans (by simpa [pow_two] using hsquare)
  · rw [hd]
    have hsub : (k - 14 * L) / 2 ≤ k / 2 :=
      Nat.div_le_div_right (Nat.sub_le k _)
    have hmono : (9 * s - 8) * L ≤ (9 * s - 8) * (L + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ L)
    have hcap : k / 2 ≤ (9 * s - 8) * L := by
      simpa [L, s] using hcapacity
    have hd2 : d + 2 = L + 1 := by omega
    simpa [s, hd2] using hsub.trans (hcap.trans hmono)
  · rw [hd]
    have hsub : (k - (14 * L - 1)) / 2 ≤ k / 2 :=
      Nat.div_le_div_right (Nat.sub_le k _)
    have hcap : k / 2 ≤ (9 * s - 8) * L := by
      simpa [L, s] using hcapacity
    simpa [s] using hsub.trans hcap
  · exact hcycle

/-- A connected maximum-degree-two full-core interaction graph has at most
the tight number of labels.  Otherwise its elementary path structure gives
the path excluded by `not_exists_tight_fullCoreMatching_path_of_cycleFree`. -/
theorem card_le_tight_fullCore_scale_of_cycleFree_connected_degree_le_two
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) (hconn : H.Connected)
    (hdeg : ∀ i : ι, H.degree i ≤ 2)
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i : ι, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    Fintype.card ι ≤ k / (18 * Nat.sqrt k - 16) + 1 := by
  let L : ℕ := k / (18 * Nat.sqrt k - 16) + 1
  let d : ℕ := L - 1
  have hLpos : 0 < L := by dsimp [L]; exact Nat.zero_lt_succ _
  have hd : d + 1 = L := by dsimp [d]; omega
  by_contra hnot
  have hroom : d + 1 < Fintype.card ι := by
    rw [hd]
    simpa [L] using hnot
  obtain ⟨u, v, w, hwpath, hwlen⟩ :=
    exists_isPath_length_eq_of_connected_degree_le_two H hconn hdeg hroom
  apply not_exists_tight_fullCoreMatching_path_of_cycleFree
    G H A B D hsqrt hscaffold hrob hmajorD htheta hregions hlarge
      hmatch hmatchBudget hcycle
  exact ⟨u, v, w, hwpath, by simpa [L, hd] using hwlen⟩

/-- Concrete path exclusion at the square-root scale.  In a `C_k`-free
ambient graph, the full-core large-matching interaction graph contains no
simple path with `floor (sqrt k / 16)` edges. -/
theorem not_exists_sqrt_div_sixteen_path_in_fullCoreMatchingGraph_of_cycleFree
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 4 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    ¬ ∃ u v : ι, ∃ w : H.Walk u v,
      w.IsPath ∧ w.length = Nat.sqrt k / 16 := by
  let s : ℕ := Nat.sqrt k
  let L : ℕ := s / 16
  let d : ℕ := L - 1
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have hLpos : 0 < L := by dsimp [L]; omega
  have hd : d + 1 = L := by dsimp [d]; omega
  change ¬ ∃ u v : ι, ∃ w : H.Walk u v, w.IsPath ∧ w.length = L
  rw [← hd]
  apply not_exists_largeFullCoreMatching_path_of_cycleFree
    G H A B D (d := d) (q := 9 * Nat.sqrt k) (theta := theta)
      (R := R) (k := k) hscaffold hrob hmajorD
  · omega
  · exact htheta
  · exact hregions
  · exact hlarge
  · exact hmatch
  · have hLlower : 16 * L ≤ s := by
      dsimp [L]
      have h := Nat.div_mul_le_self s 16
      simpa [Nat.mul_comm] using h
    have hfour : 4 * (16 * L) ≤ R := by
      have : 4 * s ≤ R := (by simpa [s] using hmatchBudget.le)
      exact (Nat.mul_le_mul_left 4 hLlower).trans this
    have hLdiv : 16 * L ≤ R / 4 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfour
    rw [hd]
    omega
  · have hsquare : s ^ 2 ≤ k := by
      simpa [s] using Nat.sqrt_le' k
    nlinarith
  · rw [hd]
    have hLle : L ≤ s := Nat.div_le_self s 16
    have hsquare : s ^ 2 ≤ k := by
      simpa [s] using Nat.sqrt_le' k
    have h18 : 18 ≤ s := by omega
    exact (Nat.mul_le_mul h18 hLle).trans (by simpa [pow_two] using hsquare)
  · rw [hd]
    have hraw := sqrt_sixteenth_fullCore_capacity hsqrt
    have hsub : (k - 14 * L) / 2 ≤ k / 2 :=
      Nat.div_le_div_right (Nat.sub_le k _)
    have hmono : (9 * s - 8) * L ≤ (9 * s - 8) * (L + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ L)
    have hraw' : k / 2 ≤ (9 * s - 8) * L := by
      simpa [L, s] using hraw
    have : (k - 14 * L) / 2 ≤ (9 * s - 8) * (L + 1) := by
      exact hsub.trans (hraw'.trans hmono)
    have hd2 : d + 2 = L + 1 := by omega
    simpa [hd2]
  · rw [hd]
    exact (Nat.div_le_div_right (Nat.sub_le k _)).trans
      (by simpa [L, s] using sqrt_sixteenth_fullCore_capacity hsqrt)
  · exact hcycle

/-- Concrete component bound repaired for pruned auxiliary edges.  An edge
of the auxiliary graph only has to enlarge to a matching between the full
alternating cores `A i ∪ B i`; the canonical anchor/mate lift above then
constructs the forbidden target cycle. -/
theorem card_le_sqrt_div_sixteen_of_cycleFree_connected_degree_le_two_alternatingScaffold_fullCore
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) (hconn : H.Connected)
    (hdeg : ∀ i : ι, H.degree i ≤ 2)
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hlarge : ∀ i j : ι, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hmatch : ∀ i : ι, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 4 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    Fintype.card ι ≤ Nat.sqrt k / 16 := by
  let s : ℕ := Nat.sqrt k
  let L : ℕ := s / 16
  let d : ℕ := L - 1
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have hLpos : 0 < L := by
    dsimp [L]
    omega
  have hd : d + 1 = L := by
    dsimp [d]
    omega
  by_contra hnot
  have hroom : d + 1 < Fintype.card ι := by
    rw [hd]
    simpa [L, s] using hnot
  obtain ⟨u, v, w, hwpath, hwlen⟩ :=
    exists_isPath_length_eq_of_connected_degree_le_two H hconn hdeg hroom
  apply hcycle
  apply cycleGraph_isContained_of_largeFullCoreMatching_path_alternatingScaffolds
    G H w hwlen hwpath A B D hscaffold hrob hmajorD
  · omega
  · exact htheta
  · exact hregions
  · exact hlarge
  · exact hmatch
  · have hLlower : 16 * L ≤ s := by
      dsimp [L]
      have h := Nat.div_mul_le_self s 16
      simpa [Nat.mul_comm] using h
    have hfour : 4 * (16 * L) ≤ R := by
      have : 4 * s ≤ R := (by simpa [s] using hmatchBudget.le)
      exact (Nat.mul_le_mul_left 4 hLlower).trans this
    have hLdiv : 16 * L ≤ R / 4 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfour
    rw [hd]
    omega
  · have hsquare : s ^ 2 ≤ k := by
      simpa [s] using Nat.sqrt_le' k
    nlinarith
  · rw [hd]
    have hLle : L ≤ s := by
      exact Nat.div_le_self s 16
    have hsquare : s ^ 2 ≤ k := by
      simpa [s] using Nat.sqrt_le' k
    have h18 : 18 ≤ s := by omega
    exact (Nat.mul_le_mul h18 hLle).trans (by simpa [pow_two] using hsquare)
  · rw [hd]
    have hraw := sqrt_sixteenth_fullCore_capacity hsqrt
    have hsub : (k - 14 * L) / 2 ≤ k / 2 :=
      Nat.div_le_div_right (Nat.sub_le k _)
    have hmono : (9 * s - 8) * L ≤ (9 * s - 8) * (L + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ L)
    have hraw' : k / 2 ≤ (9 * s - 8) * L := by
      simpa [L, s] using hraw
    have : (k - 14 * L) / 2 ≤ (9 * s - 8) * (L + 1) := by
      exact hsub.trans (hraw'.trans hmono)
    have hd2 : d + 2 = L + 1 := by omega
    simpa [hd2]
  · rw [hd]
    exact (Nat.div_le_div_right (Nat.sub_le k _)).trans
      (by simpa [L, s] using sqrt_sixteenth_fullCore_capacity hsqrt)

/-- Canonical connected-component form of the repaired full-core bound.
Repeated-attachment pruning makes the selected-side auxiliary graph have
maximum degree two.  Its matchings enlarge monotonically to the full
alternating cores, where the anchor/mate lift applies. -/
theorem ncard_component_le_sqrt_div_sixteen_after_RepeatedAttachmentFinset_fullCoreHandles
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 4 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (c : (LargeCrossMatchingGraph G
      (fun i => A i \ RepeatedAttachmentFinset G A) R).ConnectedComponent) :
    c.supp.ncard ≤ Nat.sqrt k / 16 := by
  let W : ι → Finset V :=
    fun i => A i \ RepeatedAttachmentFinset G A
  let H : SimpleGraph ι := LargeCrossMatchingGraph G W R
  let K : SimpleGraph c := c.toSimpleGraph
  let Ac : c → Finset V := fun i => A i.1
  let Bc : c → Finset V := fun i => B i.1
  let Dc : c → Finset V := fun i => D i.1
  have hAdisj : ∀ i j : ι, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    exact (hregions i j hij).mono
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (Finset.subset_union_left.trans Finset.subset_union_left)
  have hHdeg : ∀ i : ι, H.degree i ≤ 2 := by
    intro i
    apply degree_largeCrossMatchingGraph_after_RepeatedAttachmentFinset_le_two
      G A hAdisj
    · intro j
      rw [hAcard j]
    · exact hmatchBudget
  have hKdeg : ∀ i : c, K.degree i ≤ 2 := by
    intro i
    let f : SimpleGraph.Copy K H :=
      ⟨c.toSimpleGraph_hom, fun _ _ h => Subtype.ext h⟩
    exact (f.degree_le i).trans (hHdeg i.1)
  have hKlarge : ∀ i j : c, K.Adj i j →
      HasCrossMatchingAtLeast G (Ac i ∪ Bc i) (Ac j ∪ Bc j) R := by
    intro i j hij
    apply HasCrossMatchingAtLeast.mono_sets
      (hasCrossMatchingAtLeast_of_largeCrossMatchingGraph_adj
        (G := G) (U := W) (m := R) ?_)
      (Finset.sdiff_subset.trans Finset.subset_union_left)
      (Finset.sdiff_subset.trans Finset.subset_union_left)
    apply (c.toSimpleGraph_adj i.property j.property).mp
    simpa [K, H] using hij
  have hKregions : ∀ i j : c, i ≠ j →
      Disjoint ((Ac i ∪ Bc i) ∪ Dc i) ((Ac j ∪ Bc j) ∪ Dc j) := by
    intro i j hij
    apply hregions i.1 j.1
    intro h
    exact hij (Subtype.ext h)
  have hbound : Fintype.card c ≤ Nat.sqrt k / 16 := by
    apply card_le_sqrt_div_sixteen_of_cycleFree_connected_degree_le_two_alternatingScaffold_fullCore
      G K c.connected_toSimpleGraph hKdeg Ac Bc Dc hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · exact htheta
    · exact hKregions
    · exact hKlarge
    · intro i
      exact hmatch i.1
    · exact hmatchBudget
    · exact hcycle
  have hcCard : Fintype.card c = c.supp.ncard := by
    calc
      Fintype.card c = Fintype.card c.supp := by
        apply Fintype.card_congr
        exact
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      _ = c.supp.ncard := Set.fintypeCard_eq_ncard c.supp
  simpa [hcCard] using hbound

/-- General degree-two pruning estimate.  Outside the canonical repeated-
attachment set, matchings to distinct auxiliary neighbours consume disjoint
endpoint sets in the displayed core.  Thus three neighbours are impossible
as soon as three matching budgets exceed the core cardinality. -/
theorem degree_largeCrossMatchingGraph_after_RepeatedAttachmentFinset_le_two_of_three_mul
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : ι → Finset V) {R C : ℕ}
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (U i) (U j))
    (hcard : ∀ i : ι, (U i).card ≤ C)
    (hR : C < 3 * R) (i : ι) :
    (LargeCrossMatchingGraph G
      (fun j => U j \ RepeatedAttachmentFinset G U) R).degree i ≤ 2 := by
  let X : Finset V := RepeatedAttachmentFinset G U
  let W : ι → Finset V := fun j => U j \ X
  have hbudget :
      R * (LargeCrossMatchingGraph G W R).degree i ≤ (U i).card := by
    apply mul_degree_largeCrossMatchingGraph_le_card_of_no_repeated_attachment
      G U W R
    · intro j
      exact Finset.sdiff_subset
    · exact hdisj
    · intro a b c hab hac hbc x hx y hy z hz hxy hxz
      apply no_repeated_attachment_outside_RepeatedAttachmentFinset
        G U a b c hab hac hbc x
      · exact (Finset.mem_sdiff.mp hx).1
      · simpa [X] using (Finset.mem_sdiff.mp hx).2
      · exact hy
      · exact hz
      · exact hxy
      · exact hxz
  change (LargeCrossMatchingGraph G W R).degree i ≤ 2
  by_contra hdegNot
  have hdeg : 3 ≤ (LargeCrossMatchingGraph G W R).degree i := by omega
  have h3R : 3 * R ≤ R * (LargeCrossMatchingGraph G W R).degree i := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left R hdeg
  exact (not_lt_of_ge (hbudget.trans (hcard i))) (hR.trans_le h3R)

/-- Full-alternating-core component form.  Repeated-attachment pruning is
performed on `A i ∪ B i` itself, so different auxiliary components already
separate the two large scaffold sides that will become the stability seed
blocks. -/
theorem ncard_fullAlternatingCore_component_le_sqrt_div_sixteen_after_RepeatedAttachmentFinset
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (hBcard : ∀ i, (B i).card = 9 * Nat.sqrt k)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (c : (LargeCrossMatchingGraph G
      (fun i => (A i ∪ B i) \
        RepeatedAttachmentFinset G (fun j => A j ∪ B j)) R).ConnectedComponent) :
    c.supp.ncard ≤ Nat.sqrt k / 16 := by
  let U : ι → Finset V := fun i => A i ∪ B i
  let X : Finset V := RepeatedAttachmentFinset G U
  let W : ι → Finset V := fun i => U i \ X
  let H : SimpleGraph ι := LargeCrossMatchingGraph G W R
  let K : SimpleGraph c := c.toSimpleGraph
  let Ac : c → Finset V := fun i => A i.1
  let Bc : c → Finset V := fun i => B i.1
  let Dc : c → Finset V := fun i => D i.1
  have hUdisj : ∀ i j : ι, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    exact (hregions i j hij).mono Finset.subset_union_left
      Finset.subset_union_left
  have hUcard : ∀ i : ι, (U i).card ≤ 18 * Nat.sqrt k := by
    intro i
    rw [Finset.card_union_of_disjoint (hAB i), hAcard i, hBcard i]
    omega
  have hHdeg : ∀ i : ι, H.degree i ≤ 2 := by
    intro i
    apply degree_largeCrossMatchingGraph_after_RepeatedAttachmentFinset_le_two_of_three_mul
      G U hUdisj hUcard
    · omega
  have hKdeg : ∀ i : c, K.degree i ≤ 2 := by
    intro i
    let f : SimpleGraph.Copy K H :=
      ⟨c.toSimpleGraph_hom, fun _ _ h => Subtype.ext h⟩
    exact (f.degree_le i).trans (hHdeg i.1)
  have hKlarge : ∀ i j : c, K.Adj i j →
      HasCrossMatchingAtLeast G (Ac i ∪ Bc i) (Ac j ∪ Bc j) R := by
    intro i j hij
    apply HasCrossMatchingAtLeast.mono_sets
      (hasCrossMatchingAtLeast_of_largeCrossMatchingGraph_adj
        (G := G) (U := W) (m := R) ?_)
      Finset.sdiff_subset Finset.sdiff_subset
    apply (c.toSimpleGraph_adj i.property j.property).mp
    simpa [K, H] using hij
  have hKregions : ∀ i j : c, i ≠ j →
      Disjoint ((Ac i ∪ Bc i) ∪ Dc i) ((Ac j ∪ Bc j) ∪ Dc j) := by
    intro i j hij
    apply hregions i.1 j.1
    intro h
    exact hij (Subtype.ext h)
  have hbound : Fintype.card c ≤ Nat.sqrt k / 16 := by
    apply card_le_sqrt_div_sixteen_of_cycleFree_connected_degree_le_two_alternatingScaffold_fullCore
      G K c.connected_toSimpleGraph hKdeg Ac Bc Dc hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · exact htheta
    · exact hKregions
    · exact hKlarge
    · intro i
      exact hmatch i.1
    · omega
    · exact hcycle
  have hcCard : Fintype.card c = c.supp.ncard := by
    calc
      Fintype.card c = Fintype.card c.supp := by
        apply Fintype.card_congr
        exact
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      _ = c.supp.ncard := Set.fintypeCard_eq_ncard c.supp
  simpa [hcCard] using hbound

/-- Tight version of the full alternating-core component estimate.  Its
proof uses the same canonical repeated-attachment pruning and degree-two
argument as the coarse square-root bound, but invokes the capacity-optimal
path length above. -/
theorem ncard_fullAlternatingCore_component_le_tight_scale_after_RepeatedAttachmentFinset
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (hBcard : ∀ i, (B i).card = 9 * Nat.sqrt k)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (c : (LargeCrossMatchingGraph G
      (fun i => (A i ∪ B i) \
        RepeatedAttachmentFinset G (fun j => A j ∪ B j)) R).ConnectedComponent) :
    c.supp.ncard ≤ k / (18 * Nat.sqrt k - 16) + 1 := by
  let U : ι → Finset V := fun i => A i ∪ B i
  let X : Finset V := RepeatedAttachmentFinset G U
  let W : ι → Finset V := fun i => U i \ X
  let H : SimpleGraph ι := LargeCrossMatchingGraph G W R
  let K : SimpleGraph c := c.toSimpleGraph
  let Ac : c → Finset V := fun i => A i.1
  let Bc : c → Finset V := fun i => B i.1
  let Dc : c → Finset V := fun i => D i.1
  have hUdisj : ∀ i j : ι, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    exact (hregions i j hij).mono Finset.subset_union_left
      Finset.subset_union_left
  have hUcard : ∀ i : ι, (U i).card ≤ 18 * Nat.sqrt k := by
    intro i
    rw [Finset.card_union_of_disjoint (hAB i), hAcard i, hBcard i]
    omega
  have hHdeg : ∀ i : ι, H.degree i ≤ 2 := by
    intro i
    apply degree_largeCrossMatchingGraph_after_RepeatedAttachmentFinset_le_two_of_three_mul
      G U hUdisj hUcard
    omega
  have hKdeg : ∀ i : c, K.degree i ≤ 2 := by
    intro i
    let f : SimpleGraph.Copy K H :=
      ⟨c.toSimpleGraph_hom, fun _ _ h => Subtype.ext h⟩
    exact (f.degree_le i).trans (hHdeg i.1)
  have hKlarge : ∀ i j : c, K.Adj i j →
      HasCrossMatchingAtLeast G (Ac i ∪ Bc i) (Ac j ∪ Bc j) R := by
    intro i j hij
    apply HasCrossMatchingAtLeast.mono_sets
      (hasCrossMatchingAtLeast_of_largeCrossMatchingGraph_adj
        (G := G) (U := W) (m := R) ?_)
      Finset.sdiff_subset Finset.sdiff_subset
    apply (c.toSimpleGraph_adj i.property j.property).mp
    simpa [K, H] using hij
  have hKregions : ∀ i j : c, i ≠ j →
      Disjoint ((Ac i ∪ Bc i) ∪ Dc i) ((Ac j ∪ Bc j) ∪ Dc j) := by
    intro i j hij
    apply hregions i.1 j.1
    intro h
    exact hij (Subtype.ext h)
  have hbound : Fintype.card c ≤
      k / (18 * Nat.sqrt k - 16) + 1 := by
    apply card_le_tight_fullCore_scale_of_cycleFree_connected_degree_le_two
      G K c.connected_toSimpleGraph hKdeg Ac Bc Dc hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · exact htheta
    · exact hKregions
    · exact hKlarge
    · intro i
      exact hmatch i.1
    · exact hmatchBudget
    · exact hcycle
  have hcCard : Fintype.card c = c.supp.ncard := by
    calc
      Fintype.card c = Fintype.card c.supp := by
        apply Fintype.card_congr
        exact
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      _ = c.supp.ncard := Set.fintypeCard_eq_ncard c.supp
  simpa [hcCard] using hbound

/-- Approximate stability blocks on both large scaffold sides.  Distinct
components are anticomplete after the standard small-matching cover, and
each component union has the explicit `18 sqrt(k) * floor(sqrt(k)/16)`
cardinality bound. -/
theorem exists_exceptional_set_separating_fullAlternatingCore_components
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (hBcard : ∀ i, (B i).card = 9 * Nat.sqrt k)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
    let U : J → Finset V := fun i => A i.1 ∪ B i.1
    let W : J → Finset V :=
      fun i => U i \ RepeatedAttachmentFinset G U
    let H : SimpleGraph J := LargeCrossMatchingGraph G W R
    ∃ X : Finset V,
      X.card ≤ 2 * R * Fintype.card J * Fintype.card J ∧
      (∀ c d : H.ConnectedComponent, c ≠ d →
        ∀ i ∈ c.supp, ∀ j ∈ d.supp,
          ∀ a ∈ W i \ X, ∀ b ∈ W j \ X, ¬ G.Adj a b) ∧
      ∀ c : H.ConnectedComponent,
        (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
          (Nat.sqrt k / 16) * (18 * Nat.sqrt k) := by
  classical
  let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
  let AJ : J → Finset V := fun i => A i.1
  let BJ : J → Finset V := fun i => B i.1
  let DJ : J → Finset V := fun i => D i.1
  let U : J → Finset V := fun i => AJ i ∪ BJ i
  let W : J → Finset V :=
    fun i => U i \ RepeatedAttachmentFinset G U
  let H : SimpleGraph J := LargeCrossMatchingGraph G W R
  obtain ⟨X, hX, hsep⟩ :=
    exists_exceptional_set_separating_largeCrossMatching_components G W R
  refine ⟨X, hX, hsep, ?_⟩
  intro c
  have hcomponent : c.supp.ncard ≤ Nat.sqrt k / 16 := by
    apply ncard_fullAlternatingCore_component_le_sqrt_div_sixteen_after_RepeatedAttachmentFinset
      G AJ BJ DJ hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · intro i
      exact hAcard i.1
    · intro i
      exact hBcard i.1
    · intro i
      exact hAB i.1
    · exact htheta
    · intro i j hij
      apply hregions i.1 j.1
      intro h
      exact hij (Subtype.ext h)
    · intro i
      exact i.2
    · exact hmatchBudget
    · exact hcycle
  have hpiece : ∀ i ∈ c.supp.toFinset, (W i \ X).card ≤
      18 * Nat.sqrt k := by
    intro i _hi
    calc
      (W i \ X).card ≤ (U i).card := by
        apply Finset.card_le_card
        exact Finset.sdiff_subset.trans Finset.sdiff_subset
      _ = (AJ i).card + (BJ i).card := Finset.card_union_of_disjoint (hAB i.1)
      _ = 18 * Nat.sqrt k := by rw [hAcard i.1, hBcard i.1]; omega
  have hblock : (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
      c.supp.toFinset.card * (18 * Nat.sqrt k) :=
    Finset.card_biUnion_le_card_mul _ _ _ hpiece
  have hsuppCard : c.supp.toFinset.card = c.supp.ncard := by
    simpa using (Set.ncard_eq_toFinset_card c.supp).symm
  calc
    (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
        c.supp.toFinset.card * (18 * Nat.sqrt k) := hblock
    _ ≤ (Nat.sqrt k / 16) * (18 * Nat.sqrt k) := by
      rw [hsuppCard]
      exact Nat.mul_le_mul_right _ hcomponent

/-- Tight approximate-stability separator.  The component blocks are
pairwise anticomplete after the same global small-matching cover, while the
number of exact alternating cores in each block is bounded by the
capacity-optimal full-core scale. -/
theorem exists_exceptional_set_separating_fullAlternatingCore_components_tight
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (hBcard : ∀ i, (B i).card = 9 * Nat.sqrt k)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatchBudget : 6 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
    let U : J → Finset V := fun i => A i.1 ∪ B i.1
    let W : J → Finset V :=
      fun i => U i \ RepeatedAttachmentFinset G U
    let H : SimpleGraph J := LargeCrossMatchingGraph G W R
    ∃ X : Finset V,
      X.card ≤ 2 * R * Fintype.card J * Fintype.card J ∧
      (∀ c d : H.ConnectedComponent, c ≠ d →
        ∀ i ∈ c.supp, ∀ j ∈ d.supp,
          ∀ a ∈ W i \ X, ∀ b ∈ W j \ X, ¬ G.Adj a b) ∧
      ∀ c : H.ConnectedComponent,
        (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
          (k / (18 * Nat.sqrt k - 16) + 1) *
            (18 * Nat.sqrt k) := by
  classical
  let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
  let AJ : J → Finset V := fun i => A i.1
  let BJ : J → Finset V := fun i => B i.1
  let DJ : J → Finset V := fun i => D i.1
  let U : J → Finset V := fun i => AJ i ∪ BJ i
  let W : J → Finset V :=
    fun i => U i \ RepeatedAttachmentFinset G U
  let H : SimpleGraph J := LargeCrossMatchingGraph G W R
  obtain ⟨X, hX, hsep⟩ :=
    exists_exceptional_set_separating_largeCrossMatching_components G W R
  refine ⟨X, hX, hsep, ?_⟩
  intro c
  have hcomponent : c.supp.ncard ≤
      k / (18 * Nat.sqrt k - 16) + 1 := by
    apply ncard_fullAlternatingCore_component_le_tight_scale_after_RepeatedAttachmentFinset
      G AJ BJ DJ hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · intro i
      exact hAcard i.1
    · intro i
      exact hBcard i.1
    · intro i
      exact hAB i.1
    · exact htheta
    · intro i j hij
      apply hregions i.1 j.1
      intro h
      exact hij (Subtype.ext h)
    · intro i
      exact i.2
    · exact hmatchBudget
    · exact hcycle
  have hpiece : ∀ i ∈ c.supp.toFinset, (W i \ X).card ≤
      18 * Nat.sqrt k := by
    intro i _hi
    calc
      (W i \ X).card ≤ (U i).card := by
        apply Finset.card_le_card
        exact Finset.sdiff_subset.trans Finset.sdiff_subset
      _ = (AJ i).card + (BJ i).card :=
        Finset.card_union_of_disjoint (hAB i.1)
      _ = 18 * Nat.sqrt k := by rw [hAcard i.1, hBcard i.1]; omega
  have hblock : (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
      c.supp.toFinset.card * (18 * Nat.sqrt k) :=
    Finset.card_biUnion_le_card_mul _ _ _ hpiece
  have hsuppCard : c.supp.toFinset.card = c.supp.ncard := by
    simpa using (Set.ncard_eq_toFinset_card c.supp).symm
  calc
    (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
        c.supp.toFinset.card * (18 * Nat.sqrt k) := hblock
    _ ≤ (k / (18 * Nat.sqrt k - 16) + 1) *
          (18 * Nat.sqrt k) := by
      rw [hsuppCard]
      exact Nat.mul_le_mul_right _ hcomponent

/-- Stable-block output for the parity-broken hub subfamily, now using the
full-core handle lift.  This is the component separator needed by the final
stability assembly. -/
theorem exists_exceptional_set_separating_small_alternatingScaffold_components_fullCoreHandles
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {theta R k : ℕ}
    (hsqrt : 256 ≤ Nat.sqrt k)
    (hscaffold : ∀ i,
      IsCyclicAlternatingScaffold G (9 * Nat.sqrt k) (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = 9 * Nat.sqrt k)
    (htheta : 7 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatchBudget : 4 * Nat.sqrt k < R)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
    let AJ : J → Finset V := fun i => A i.1
    let W : J → Finset V :=
      fun i => AJ i \ RepeatedAttachmentFinset G AJ
    let H : SimpleGraph J := LargeCrossMatchingGraph G W R
    ∃ X : Finset V,
      X.card ≤ 2 * R * Fintype.card J * Fintype.card J ∧
      (∀ c d : H.ConnectedComponent, c ≠ d →
        ∀ i ∈ c.supp, ∀ j ∈ d.supp,
          ∀ a ∈ W i \ X, ∀ b ∈ W j \ X, ¬ G.Adj a b) ∧
      ∀ c : H.ConnectedComponent,
        (c.supp.toFinset.biUnion fun i => W i \ X).card ≤ k - 1 := by
  classical
  let J := {i : ι // HasThreeDisjointAdjPairFamily G (A i)}
  let AJ : J → Finset V := fun i => A i.1
  let BJ : J → Finset V := fun i => B i.1
  let DJ : J → Finset V := fun i => D i.1
  let W : J → Finset V :=
    fun i => AJ i \ RepeatedAttachmentFinset G AJ
  let H : SimpleGraph J := LargeCrossMatchingGraph G W R
  obtain ⟨X, hX, hsep⟩ :=
    exists_exceptional_set_separating_largeCrossMatching_components G W R
  refine ⟨X, hX, hsep, ?_⟩
  intro c
  have hcomponent : c.supp.ncard ≤ Nat.sqrt k / 16 := by
    apply ncard_component_le_sqrt_div_sixteen_after_RepeatedAttachmentFinset_fullCoreHandles
      G AJ BJ DJ hsqrt
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · intro i
      exact hAcard i.1
    · exact htheta
    · intro i j hij
      apply hregions i.1 j.1
      intro h
      exact hij (Subtype.ext h)
    · intro i
      exact i.2
    · exact hmatchBudget
    · exact hcycle
  have hpiece : ∀ i ∈ c.supp.toFinset, (W i \ X).card ≤ 9 * Nat.sqrt k := by
    intro i _hi
    calc
      (W i \ X).card ≤ (AJ i).card := by
        apply Finset.card_le_card
        exact Finset.sdiff_subset.trans Finset.sdiff_subset
      _ = 9 * Nat.sqrt k := hAcard i.1
  have hblock : (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
      c.supp.toFinset.card * (9 * Nat.sqrt k) :=
    Finset.card_biUnion_le_card_mul _ _ _ hpiece
  have hsuppCard : c.supp.toFinset.card = c.supp.ncard := by
    simpa using (Set.ncard_eq_toFinset_card c.supp).symm
  have hblock' : (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
      (Nat.sqrt k / 16) * (9 * Nat.sqrt k) := by
    calc
      (c.supp.toFinset.biUnion fun i => W i \ X).card ≤
          c.supp.toFinset.card * (9 * Nat.sqrt k) := hblock
      _ ≤ (Nat.sqrt k / 16) * (9 * Nat.sqrt k) := by
        rw [hsuppCard]
        exact Nat.mul_le_mul_right _ hcomponent
  let s : ℕ := Nat.sqrt k
  let L : ℕ := s / 16
  have hs : 256 ≤ s := by simpa [s] using hsqrt
  have hLlower : 16 * L ≤ s := by
    dsimp [L]
    have h := Nat.div_mul_le_self s 16
    simpa [Nat.mul_comm] using h
  have h9L : 9 * L < s := by omega
  have hspos : 0 < s := by omega
  have hprod : L * (9 * s) < s ^ 2 := by
    have hmul := Nat.mul_lt_mul_of_pos_right h9L hspos
    nlinarith
  have hsquare : s ^ 2 ≤ k := by
    simpa [s] using Nat.sqrt_le' k
  have htarget : (Nat.sqrt k / 16) * (9 * Nat.sqrt k) ≤ k - 1 := by
    change L * (9 * s) ≤ k - 1
    omega
  exact hblock'.trans htarget

/-- A sufficiently edge-dense consecutive BFS-layer pair contains an
ambient cycle in a controlled medium-length interval.  The lower endpoint
comes from the Erdős--Gallai path bound, while the upper endpoint is the
explicit detour bound in the Erdős--Faudree--Rousseau--Schelp BFS assembly.

This is the finite density-to-cycle bridge used in the KLS first-slow-layer
argument.  Its formulation deliberately keeps the precise BFS radius in the
upper endpoint, so the later stopping-time estimate can replace it by a
binary logarithm of the ambient order. -/

theorem exists_cycle_length_between_of_dense_bfsPair
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (root : V) (i D : ℕ)
    (hE : (Erdos752.bfsPair G root i).edgeFinset.Nonempty)
    (hdense : (8 * (D + 1)) *
        (Erdos752.bfsPair G root i).support.ncard ≤
          (Erdos752.bfsPair G root i).edgeFinset.card) :
    ∃ l : ℕ, D ≤ l ∧ l ≤ 8 * (D + 1) + 2 * i ∧
      ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = l := by
  classical
  let K : SimpleGraph V := Erdos752.bfsPair G root i
  let J : SimpleGraph K.support := K.induce K.support
  let q : ℕ := 8 * (D + 1)
  have hKsupport : K.support.Nonempty := by
    exact Erdos182.support_nonempty_of_edgeFinset_nonempty hE
  letI : Nonempty K.support := hKsupport.to_subtype
  have hpath : ∃ a b : K.support, ∃ p : J.Walk a b,
      p.IsPath ∧ q ≤ p.length := by
    by_contra hno
    have hlt := card_edgeFinset_lt_mul_card_of_no_long_path J q hno
    have hedge : J.edgeFinset.card = K.edgeFinset.card := by
      simpa [J] using K.card_edgeFinset_induce_support
    have hcard : Fintype.card K.support = K.support.ncard := by
      exact Set.fintypeCard_eq_ncard K.support
    have hq : q = 8 * (D + 1) := rfl
    rw [hedge, hcard, hq] at hlt
    exact (Nat.not_lt_of_ge (by simpa [K] using hdense)) hlt
  obtain ⟨a, b, p, hp, hplen⟩ := hpath
  let p₀ : J.Walk a (p.getVert q) := p.take q
  have hp₀ : p₀.IsPath := hp.take q
  have hp₀len : p₀.length = q := by
    simp [p₀, SimpleGraph.Walk.take_length, Nat.min_eq_left hplen]
  have hp₀four : 4 ≤ p₀.length := by
    rw [hp₀len]
    dsimp [q]
    omega
  obtain ⟨L, hLcard, hLcycles⟩ :=
    Erdos752.exists_cycle_lengths_of_induce_support_path_bounded
      G hconn root i (K := K) (by simp [K]) p₀ hp₀ hp₀four
  have hLlarge : D + 1 ≤ L.card := by
    rw [hp₀len] at hLcard
    dsimp [q] at hLcard
    omega
  have hexists : ∃ l ∈ L, D ≤ l := by
    by_contra hno
    push_neg at hno
    have hsub : L ⊆ Finset.range D := by
      intro l hl
      exact Finset.mem_range.mpr (hno l hl)
    have hsmall := Finset.card_le_card hsub
    simp only [Finset.card_range] at hsmall
    omega
  obtain ⟨l, hlL, hDl⟩ := hexists
  obtain ⟨hlupper, v, c, hc, hclen⟩ := hLcycles l hlL
  refine ⟨l, hDl, ?_, v, c, hc, hclen⟩
  rw [hp₀len] at hlupper
  simpa [q] using hlupper

/-- A connected bipartite graph with logarithmically large minimum degree
contains a cycle in the medium-length interval used in the KLS auxiliary
graph argument.  The first slow BFS ball supplies the dense consecutive
slice, and the preceding density-to-cycle theorem closes it. -/
theorem exists_medium_cycle_of_connected_bipartite_minDegree
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hbip : G.IsBipartite)
    (root : V) (b D δ : ℕ) (hb : 2 ≤ b)
    (hmin : ∀ v : V, δ ≤ G.degree v)
    (hmargin : 2 * ((8 * (D + 1)) * b *
      (Nat.log b (Fintype.card V) + 1)) < δ) :
    ∃ l : ℕ, D ≤ l ∧
      l ≤ 8 * (D + 1) + 2 * Nat.log b (Fintype.card V) ∧
      _root_.SimpleGraph.cycleGraph l ⊑ G := by
  obtain ⟨i, hi, hE, hdense⟩ :=
    exists_dense_bfsPair_index_le_log_of_minDegree
      G hconn hbip root b (8 * (D + 1)) δ hb hmin hmargin
  obtain ⟨l, hDl, hli, v, c, hc, hclen⟩ :=
    exists_cycle_length_between_of_dense_bfsPair
      G hconn root i D hE hdense
  refine ⟨l, hDl, ?_, ?_⟩
  · omega
  · apply (_root_.SimpleGraph.cycleGraph_isContained_iff ?_).2
    · exact ⟨v, c, hc, hclen⟩
    · exact hc.three_le_length.trans_eq hclen

/-- Edge-density form of the medium-cycle lemma.  A minimum-degree core,
a maximum cut, and one connected component lose only the explicit constant
factor in the density hypothesis; the component cycle then embeds back into
the original graph. -/
theorem exists_medium_cycle_of_edge_density
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b D δ : ℕ) (hb : 2 ≤ b)
    (hE : G.edgeFinset.Nonempty)
    (hdense : (8 * δ) * G.support.ncard ≤
      2 * G.edgeFinset.card)
    (hmargin : 2 * ((8 * (D + 1)) * b *
      (Nat.log b (Fintype.card V) + 1)) < δ) :
    ∃ l : ℕ, D ≤ l ∧
      l ≤ 8 * (D + 1) + 2 * Nat.log b (Fintype.card V) ∧
      _root_.SimpleGraph.cycleGraph l ⊑ G := by
  classical
  obtain ⟨H, instH, hHs, hHG, _hHedges, hHmin⟩ :=
    Erdos182.exists_induced_minDegree_core G (8 * δ) hE hdense
  letI : DecidableRel H.Adj := instH
  let J : SimpleGraph H.support := H.induce H.support
  letI : Nonempty H.support := hHs.to_subtype
  have hJmin : 4 * δ ≤ J.minDegree := by
    dsimp [J]
    omega
  obtain ⟨B, instB, hBJ, hBbip, hBdeg⟩ :=
    exists_bipartite_subgraph_twice_degree J hJmin
  letI : DecidableRel B.Adj := instB
  have hδpos : 0 < δ := by omega
  obtain ⟨c, instC, hCconn, hCbip, hCdeg, _hcB, _hcJ⟩ :=
    Erdos752.exists_connected_bipartite_component_of_le B
      (by positivity : 0 < 4 * δ) hBJ hBbip hBdeg
  letI : DecidableRel c.toSimpleGraph.Adj := instC
  letI : Nonempty c := c.nonempty_supp.to_subtype
  let root : c := Classical.choice inferInstance
  have hcV : Fintype.card c ≤ Fintype.card V := by
    apply Fintype.card_le_of_injective (fun x : c => x.1.1)
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hlog : Nat.log b (Fintype.card c) ≤
      Nat.log b (Fintype.card V) := Nat.log_mono_right hcV
  have hmarginC : 2 * ((8 * (D + 1)) * b *
      (Nat.log b (Fintype.card c) + 1)) < δ := by
    have hmul := Nat.mul_le_mul_left (2 * ((8 * (D + 1)) * b))
      (Nat.add_le_add_right hlog 1)
    have hmul' : 2 * ((8 * (D + 1)) * b *
        (Nat.log b (Fintype.card c) + 1)) ≤
        2 * ((8 * (D + 1)) * b *
          (Nat.log b (Fintype.card V) + 1)) := by
      simpa only [Nat.mul_assoc] using hmul
    exact hmul'.trans_lt hmargin
  have hCmin : ∀ v : c, δ ≤ c.toSimpleGraph.degree v := by
    intro v
    have hv := hCdeg v
    omega
  obtain ⟨l, hDl, hlC, hcycleC⟩ :=
    exists_medium_cycle_of_connected_bipartite_minDegree
      c.toSimpleGraph hCconn hCbip root b D δ hb hCmin hmarginC
  refine ⟨l, hDl, ?_, ?_⟩
  · exact hlC.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 hlog) (8 * (D + 1)))
  · exact (((hcycleC.trans
        (Erdos752.componentEmbedding B c).isContained).trans
          (SimpleGraph.IsContained.of_le hBJ)).trans
        (SimpleGraph.Embedding.induce H.support).isContained).trans
      (SimpleGraph.IsContained.of_le hHG)

/-! ## Sidewise selected full-core cycles -/

@[simp] theorem finCyclicSucc_castSucc {m : ℕ} (i : Fin m) :
    finCyclicSucc (by omega : 0 < m + 1) i.castSucc = i.succ := by
  apply Fin.ext
  simp [finCyclicSucc, Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]

@[simp] theorem finCyclicSucc_last {m : ℕ} :
    finCyclicSucc (by omega : 0 < m + 1) (Fin.last m) = 0 := by
  apply Fin.ext
  simp [finCyclicSucc]

theorem finCyclicSucc_finCyclicPred {q : ℕ} (hq : 0 < q) (i : Fin q) :
    finCyclicSucc hq (finCyclicPred hq i) = i := by
  apply finCyclicPred_injective hq
  simpa using finCyclicPred_finCyclicSucc hq (finCyclicPred hq i)

/-- If a collection chooses only one side of an alternating scaffold, the
canonical two-vertex supports of two distinct chosen vertices are disjoint.
This packages precisely the extra freshness needed when selected auxiliary
edges are allowed to end on either side of the full core. -/
theorem disjoint_canonicalAnchor_pairs_of_common_side
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} {A B I : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (anchor : V → V)
    (hanchor : ∀ x ∈ A ∪ B, IsHubAnchor G A x (anchor x))
    (hfix : ∀ x ∈ A, anchor x = x)
    (hinjA : Set.InjOn anchor (A : Set V))
    (hinjB : Set.InjOn anchor (B : Set V))
    (hside : I ⊆ A ∨ I ⊆ B)
    {x y : V} (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    Disjoint ({anchor x, x} : Finset V) {anchor y, y} := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzX hzY
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzX hzY
  rcases hside with hIA | hIB
  · have hxA := hIA hx
    have hyA := hIA hy
    have hax := hfix x hxA
    have hay := hfix y hyA
    rcases hzX with hzx | hzx <;> rcases hzY with hzy | hzy <;>
      subst z <;> simp_all
  · have hxB := hIB hx
    have hyB := hIB hy
    have haxA : anchor x ∈ A := (hanchor x (Finset.mem_union_right _ hxB)).1
    have hayA : anchor y ∈ A := (hanchor y (Finset.mem_union_right _ hyB)).1
    have hAB : Disjoint A B := by
      rcases hscaffold with ⟨_, _, _, _, _, _, _, h, _, _⟩
      exact h
    rcases hzX with hzx | hzx <;> rcases hzY with hzy | hzy
    · exact hxy (hinjB hxB hyB (hzx.symm.trans hzy))
    · exact (Finset.disjoint_left.mp hAB) haxA (hzx.symm ▸ hzy ▸ hyB)
    · exact (Finset.disjoint_left.mp hAB) hayA (hzy.symm ▸ hzx ▸ hxB)
    · exact hxy (hzx.symm.trans hzy)

/-- A selected auxiliary cycle whose class in each hub lies wholly in one
of the two scaffold sides lifts to a cyclic family of pairwise-disjoint
short handles anchored in the selected side.  The support of every handle
is an anchor or its canonical opposite-side mate, exactly as required by
the repeated-visit near-spanning router. -/
theorem exists_sidewise_selected_path_handles_of_cycle
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m q : ℕ} (hm : 2 ≤ m)
    (A B D I : ι → Finset V)
    (M : Finset (SelectedCrossEdge V ι))
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hside : ∀ i, I i ⊆ A i ∨ I i ⊆ B i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hcopy : _root_.SimpleGraph.cycleGraph (m + 1) ⊑
      SelectedCrossEdgeGraph M) :
    ∃ f : Fin (m + 1) → ι, Function.Injective f ∧
      ∃ x y : Fin (m + 1) → V,
        ∃ h : ∀ e : Fin (m + 1), G.Walk (x e) (y e),
          (∀ e, (h e).IsPath ∧ 1 ≤ (h e).length ∧ (h e).length ≤ 3) ∧
          (∀ e d, e ≠ d → (h e).support.Disjoint (h d).support) ∧
          (∀ e z, z ∈ (h e).support →
            z = x e ∨
              IsCanonicalScaffoldMate G (hscaffold (f e)) z (x e) ∨
            z = y e ∨
              IsCanonicalScaffoldMate G
                (hscaffold (f (finCyclicSucc (by omega : 0 < m + 1) e)))
                  z (y e)) ∧
          (∀ i, y (finCyclicPred (by omega : 0 < m + 1) i) ∈ A (f i)) ∧
          (∀ i, x i ∈ A (f i)) ∧
          (∀ i, y (finCyclicPred (by omega : 0 < m + 1) i) ≠ x i) ∧
          ∀ i j, i ≠ j →
            y (finCyclicPred (by omega : 0 < m + 1) i) ≠
                y (finCyclicPred (by omega : 0 < m + 1) j) ∧
            y (finCyclicPred (by omega : 0 < m + 1) i) ≠ x j ∧
            x i ≠ y (finCyclicPred (by omega : 0 < m + 1) j) ∧
            x i ≠ x j := by
  classical
  obtain ⟨f, hfinj, a, b, haI, hbI, hab, hcross, hclose⟩ :=
    exists_distinct_cyclic_cross_edges_of_cycleGraph_isContained_selectedCrossEdgeGraph
      hm G I M hM hcopy
  let next : Fin (m + 1) → Fin (m + 1) := finCyclicSucc (by omega)
  let pred : Fin (m + 1) → Fin (m + 1) := finCyclicPred (by omega)
  let anchor : ι → V → V := fun c =>
    Classical.choose (exists_alternatingAnchor_map G (hscaffold c))
  have hanchor : ∀ c x, x ∈ A c ∪ B c →
      IsHubAnchor G (A c) x (anchor c x) := by
    intro c
    exact (Classical.choose_spec
      (exists_alternatingAnchor_map G (hscaffold c))).1
  have hfix : ∀ c x, x ∈ A c → anchor c x = x := by
    intro c
    exact (Classical.choose_spec
      (exists_alternatingAnchor_map G (hscaffold c))).2.1
  have hinjA : ∀ c, Set.InjOn (anchor c) (A c : Set V) := by
    intro c
    exact (Classical.choose_spec
      (exists_alternatingAnchor_map G (hscaffold c))).2.2.1
  have hinjB : ∀ c, Set.InjOn (anchor c) (B c : Set V) := by
    intro c
    exact (Classical.choose_spec
      (exists_alternatingAnchor_map G (hscaffold c))).2.2.2.1
  have hmate : ∀ c z, z ∈ B c →
      IsCanonicalScaffoldMate G (hscaffold c) z (anchor c z) := by
    intro c
    exact (Classical.choose_spec
      (exists_alternatingAnchor_map G (hscaffold c))).2.2.2.2
  let ain : Fin (m + 1) → V := fun i => anchor (f i) (a i)
  let bout : Fin (m + 1) → V := fun i => anchor (f i) (b i)
  let inPair : Fin (m + 1) → Finset V := fun i => {ain i, a i}
  let outPair : Fin (m + 1) → Finset V := fun i => {bout i, b i}
  have hlocal : ∀ i, Disjoint (outPair i) (inPair i) := by
    intro i
    apply disjoint_canonicalAnchor_pairs_of_common_side
      G (hscaffold (f i)) (anchor (f i))
        (hanchor (f i)) (hfix (f i)) (hinjA (f i)) (hinjB (f i))
        (hside (f i)) (hbI i) (haI i) (hab i).symm
  have hnextPred : ∀ i, next (pred i) = i := by
    intro i
    exact finCyclicSucc_finCyclicPred (by omega) i
  have hpredNext : ∀ i, pred (next i) = i := by
    intro i
    exact finCyclicPred_finCyclicSucc (by omega) i
  have hnextInj : Function.Injective next := by
    intro i j hij
    have := congrArg pred hij
    simpa [hpredNext] using this
  have hnextNe : ∀ i, next i ≠ i := by
    intro i h
    have hp := congrArg pred h
    have hself : i = pred i := by simpa [hpredNext] using hp
    exact finCyclicPred_ne_self (by omega : 2 ≤ m + 1) i hself.symm
  have hcrossCyclic : ∀ i, G.Adj (b i) (a (next i)) := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa [next] using hclose
    | cast i => simpa [next] using hcross i
  have hhandle : ∀ e, ∃ p : G.Walk (bout e) (ain (next e)),
      p.IsPath ∧ 1 ≤ p.length ∧ p.length ≤ 3 ∧
      ∀ z ∈ p.support,
        z = bout e ∨ z = b e ∨ z = a (next e) ∨ z = ain (next e) := by
    intro e
    apply exists_selected_handle_of_hubAnchors G
      ((hregions (f e) (f (next e)) (hfinj.ne (hnextNe e).symm)).mono
        Finset.subset_union_left Finset.subset_union_left)
      ((hside (f e)).elim (fun h => Finset.mem_union_left _ (h (hbI e)))
        (fun h => Finset.mem_union_right _ (h (hbI e))))
      ((hside (f (next e))).elim
        (fun h => Finset.mem_union_left _ (h (haI (next e))))
        (fun h => Finset.mem_union_right _ (h (haI (next e)))))
      (hcrossCyclic e) (hanchor (f e) (b e) (by
        rcases hside (f e) with h | h
        · exact Finset.mem_union_left _ (h (hbI e))
        · exact Finset.mem_union_right _ (h (hbI e))))
      (hanchor (f (next e)) (a (next e)) (by
        rcases hside (f (next e)) with h | h
        · exact Finset.mem_union_left _ (h (haI (next e)))
        · exact Finset.mem_union_right _ (h (haI (next e)))))
  let x : Fin (m + 1) → V := bout
  let y : Fin (m + 1) → V := fun e => ain (next e)
  let h : ∀ e : Fin (m + 1), G.Walk (x e) (y e) := fun e =>
    Classical.choose (hhandle e)
  have hh : ∀ e, (h e).IsPath ∧ 1 ≤ (h e).length ∧ (h e).length ≤ 3 ∧
      ∀ z ∈ (h e).support,
        z = bout e ∨ z = b e ∨ z = a (next e) ∨ z = ain (next e) := by
    intro e
    exact Classical.choose_spec (hhandle e)
  have houtRegion : ∀ i z, z ∈ outPair i → z ∈ A (f i) ∪ B (f i) := by
    intro i z hz
    simp only [outPair, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_union_left _ (hanchor (f i) (b i) (by
        rcases hside (f i) with hs | hs
        · exact Finset.mem_union_left _ (hs (hbI i))
        · exact Finset.mem_union_right _ (hs (hbI i)))).1
    · rcases hside (f i) with hs | hs
      · exact Finset.mem_union_left _ (hs (hbI i))
      · exact Finset.mem_union_right _ (hs (hbI i))
  have hinRegion : ∀ i z, z ∈ inPair i → z ∈ A (f i) ∪ B (f i) := by
    intro i z hz
    simp only [inPair, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_union_left _ (hanchor (f i) (a i) (by
        rcases hside (f i) with hs | hs
        · exact Finset.mem_union_left _ (hs (haI i))
        · exact Finset.mem_union_right _ (hs (haI i)))).1
    · rcases hside (f i) with hs | hs
      · exact Finset.mem_union_left _ (hs (haI i))
      · exact Finset.mem_union_right _ (hs (haI i))
  have hsameIndex : ∀ i j z,
      z ∈ A (f i) ∪ B (f i) → z ∈ A (f j) ∪ B (f j) → i = j := by
    intro i j z hzi hzj
    by_contra hij
    exact Finset.disjoint_left.mp
      ((hregions (f i) (f j) (hfinj.ne hij)).mono
        Finset.subset_union_left Finset.subset_union_left) hzi hzj
  have hhPairs : ∀ e z, z ∈ (h e).support →
      z ∈ outPair e ∨ z ∈ inPair (next e) := by
    intro e z hz
    rcases (hh e).2.2.2 z hz with hz | hz | hz | hz
    · exact Or.inl (by simp [outPair, hz])
    · exact Or.inl (by simp [outPair, hz])
    · exact Or.inr (by simp [inPair, hz])
    · exact Or.inr (by simp [inPair, hz])
  have hhDisj : ∀ e d, e ≠ d → (h e).support.Disjoint (h d).support := by
    intro e d hed z hze hzd
    rcases hhPairs e z hze with hzeOut | hzeIn <;>
      rcases hhPairs d z hzd with hzdOut | hzdIn
    · exact hed (hsameIndex e d z (houtRegion e z hzeOut)
        (houtRegion d z hzdOut))
    · have heq := hsameIndex e (next d) z (houtRegion e z hzeOut)
        (hinRegion (next d) z hzdIn)
      exact Finset.disjoint_left.mp (hlocal e) hzeOut (by simpa [heq] using hzdIn)
    · have heq := hsameIndex (next e) d z (hinRegion (next e) z hzeIn)
        (houtRegion d z hzdOut)
      exact Finset.disjoint_left.mp (hlocal d) hzdOut (by simpa [heq] using hzeIn)
    · exact hed (hnextInj (hsameIndex (next e) (next d) z
        (hinRegion (next e) z hzeIn) (hinRegion (next d) z hzdIn)))
  have hhMate : ∀ e z, z ∈ (h e).support →
      z = x e ∨ IsCanonicalScaffoldMate G (hscaffold (f e)) z (x e) ∨
      z = y e ∨
        IsCanonicalScaffoldMate G (hscaffold (f (next e))) z (y e) := by
    intro e z hz
    rcases (hh e).2.2.2 z hz with hz | hz | hz | hz
    · left
      simpa [x, bout] using hz
    · rcases hside (f e) with hs | hs
      · left
        simpa [x, bout, hfix (f e) (b e) (hs (hbI e))] using hz
      · subst z
        right; left
        simpa [x, bout] using (hmate (f e) (b e) (hs (hbI e)))
    · rcases hside (f (next e)) with hs | hs
      · right; right; left
        simpa [y, ain, hfix (f (next e)) (a (next e))
          (hs (haI (next e)))] using hz
      · subst z
        right; right; right
        simpa [y, ain] using
          (hmate (f (next e)) (a (next e)) (hs (haI (next e))))
    · right; right; left
      simpa [y, ain] using hz
  have hinA : ∀ i, ain i ∈ A (f i) := by
    intro i
    exact (hanchor (f i) (a i) (by
      rcases hside (f i) with hs | hs
      · exact Finset.mem_union_left _ (hs (haI i))
      · exact Finset.mem_union_right _ (hs (haI i)))).1
  have houtA : ∀ i, bout i ∈ A (f i) := by
    intro i
    exact (hanchor (f i) (b i) (by
      rcases hside (f i) with hs | hs
      · exact Finset.mem_union_left _ (hs (hbI i))
      · exact Finset.mem_union_right _ (hs (hbI i)))).1
  have hlocalNe : ∀ i, ain i ≠ bout i := by
    intro i hEq
    have houtmem : bout i ∈ outPair i := by simp [outPair]
    have hinmem : bout i ∈ inPair i := by rw [← hEq]; simp [inPair]
    exact Finset.disjoint_left.mp (hlocal i) houtmem hinmem
  have ha : ∀ i, y (pred i) ∈ A (f i) := by
    intro i
    simpa [y, hnextPred] using hinA i
  have hb : ∀ i, x i ∈ A (f i) := by
    intro i
    simpa [x] using houtA i
  have hab' : ∀ i, y (pred i) ≠ x i := by
    intro i
    simpa [x, y, hnextPred] using hlocalNe i
  have hpairs : ∀ i j, i ≠ j →
      y (pred i) ≠ y (pred j) ∧ y (pred i) ≠ x j ∧
        x i ≠ y (pred j) ∧ x i ≠ x j := by
    intro i j hij
    have hdisj := (hregions (f i) (f j) (hfinj.ne hij)).mono
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (Finset.subset_union_left.trans Finset.subset_union_left)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hEq
    · exact Finset.disjoint_left.mp hdisj (ha i) (hEq ▸ ha j)
    · exact Finset.disjoint_left.mp hdisj (ha i) (hEq ▸ hb j)
    · exact Finset.disjoint_left.mp hdisj (hb i) (hEq ▸ ha j)
    · exact Finset.disjoint_left.mp hdisj (hb i) (hEq ▸ hb j)
  exact ⟨f, hfinj, x, y, h,
    fun e => ⟨(hh e).1, (hh e).2.1, (hh e).2.2.1⟩,
    fun e d hed => hhDisj e d hed, hhMate, ha, hb, hab', hpairs⟩

/-- The selected auxiliary graph of matching-backed robust hubs has bounded
average degree whenever every medium auxiliary cycle fits inside the target
ambient cycle.  The numerical fitting condition is kept explicit so that
the eventual KLS parameter package can instantiate it without hiding any
rounding. -/
theorem card_selectedCrossEdgeSystem_lt_of_cycleFree_matched
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U T I : ι → Finset V) (θ : ι → ℕ)
    (M : Finset (SelectedCrossEdge V ι))
    (hrob : ∀ i, RobustPairSet G (U i) (T i) (θ i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hIU : ∀ i, I i ⊆ U i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (U i))
    {b D δ k : ℕ} (hb : 2 ≤ b) (hD : 3 ≤ D) (hk : 3 ≤ k)
    (hmargin : 2 * ((8 * (D + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D ≤ l →
      l ≤ 8 * (D + 1) + 2 * Nat.log b (Fintype.card ι) →
      let ℓ := k - (3 * l - 2)
      5 ≤ ℓ ∧ (∀ i, ℓ ≤ (U i).card) ∧
        ∀ i, ℓ + 1 ≤ θ i)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    M.card < 4 * δ * Fintype.card ι := by
  classical
  by_contra hnot
  have hδ : 0 < δ := by omega
  have hlarge : 4 * δ * Fintype.card ι ≤ M.card := by omega
  have hsupp : (SelectedCrossEdgeGraph M).support.ncard ≤
      Fintype.card ι := by
    simpa using Set.ncard_le_ncard
      (Set.subset_univ (SelectedCrossEdgeGraph M).support)
  have hdense : (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
      2 * (SelectedCrossEdgeGraph M).edgeFinset.card := by
    rw [card_edgeFinset_selectedCrossEdgeGraph hM]
    calc
      (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
          (8 * δ) * Fintype.card ι := Nat.mul_le_mul_left _ hsupp
      _ = 2 * (4 * δ * Fintype.card ι) := by ring
      _ ≤ 2 * M.card := Nat.mul_le_mul_left 2 hlarge
  have hMne : M.Nonempty := by
    apply Finset.card_pos.mp
    have hcardι : 0 < Fintype.card ι := Fintype.card_pos
    exact (Nat.mul_pos (Nat.mul_pos (by omega) hδ) hcardι).trans_le hlarge
  have hE : (SelectedCrossEdgeGraph M).edgeFinset.Nonempty := by
    rw [← Finset.card_pos, card_edgeFinset_selectedCrossEdgeGraph hM]
    exact Finset.card_pos.mpr hMne
  obtain ⟨l, hDl, hlupper, hcopy⟩ :=
    exists_medium_cycle_of_edge_density
      (SelectedCrossEdgeGraph M) b D δ hb hE hdense hmargin
  obtain ⟨hℓ, hℓU, hℓθ⟩ := hfit l hDl hlupper
  let m : ℕ := l - 1
  let ℓ : ℕ := k - (3 * l - 2)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hml : m + 1 = l := by dsimp [m]; omega
  apply hcycle
  apply cycleGraph_isContained_of_selectedCrossEdgeGraph_cycle_matched
    hm hk G U T I θ M hrob hregions hIU hM hmatch hℓ hℓU hℓθ
      (fun _ : Fin m => 0)
  · intro i j
    have := hℓU i
    omega
  · intro i j
    have := hℓθ i
    omega
  · rw [hml]
    exact hcopy
  · simp only [Fin.sum_const]
    dsimp [ℓ, m]
    omega

/-- Thin-alternating-scaffold form of the selected H1 average-degree bound.
The logarithmic auxiliary cycle is lifted by the all-parity capacity theorem,
so the compact hubs need only the fixed robust parameter used by the KLS
decomposition rather than robustness proportional to the target length. -/
theorem card_selectedCrossEdgeSystem_lt_of_cycleFree_alternatingScaffold_matched
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T I : ι → Finset V) (q theta : ℕ)
    (M : Finset (SelectedCrossEdge V ι))
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (T i) theta)
    (hmajorT : ∀ i, Disjoint (A i ∪ B i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ T i) ((A j ∪ B j) ∪ T j))
    (hIA : ∀ i, I i ⊆ A i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hq : 5 ≤ q) (htheta : 6 ≤ theta)
    {b D₀ δ k : ℕ} (hb : 2 ≤ b) (hD₀ : 3 ≤ D₀) (hk : 3 ≤ k)
    (hmargin : 2 * ((8 * (D₀ + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D₀ ≤ l →
      l ≤ 8 * (D₀ + 1) + 2 * Nat.log b (Fintype.card ι) →
      7 * l ≤ k ∧
        (k - (7 * l - 1)) / 2 ≤ (q - 4) * (l - 1))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    M.card < 4 * δ * Fintype.card ι := by
  classical
  by_contra hnot
  have hδ : 0 < δ := by omega
  have hlarge : 4 * δ * Fintype.card ι ≤ M.card := by omega
  have hsupp : (SelectedCrossEdgeGraph M).support.ncard ≤
      Fintype.card ι := by
    simpa using Set.ncard_le_ncard
      (Set.subset_univ (SelectedCrossEdgeGraph M).support)
  have hdense : (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
      2 * (SelectedCrossEdgeGraph M).edgeFinset.card := by
    rw [card_edgeFinset_selectedCrossEdgeGraph hM]
    calc
      (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
          (8 * δ) * Fintype.card ι := Nat.mul_le_mul_left _ hsupp
      _ = 2 * (4 * δ * Fintype.card ι) := by ring
      _ ≤ 2 * M.card := Nat.mul_le_mul_left 2 hlarge
  have hMne : M.Nonempty := by
    apply Finset.card_pos.mp
    have hcardι : 0 < Fintype.card ι := Fintype.card_pos
    exact (Nat.mul_pos (Nat.mul_pos (by omega) hδ) hcardι).trans_le hlarge
  have hE : (SelectedCrossEdgeGraph M).edgeFinset.Nonempty := by
    rw [← Finset.card_pos, card_edgeFinset_selectedCrossEdgeGraph hM]
    exact Finset.card_pos.mpr hMne
  obtain ⟨l, hD₀l, hlupper, hcopy⟩ :=
    exists_medium_cycle_of_edge_density
      (SelectedCrossEdgeGraph M) b D₀ δ hb hE hdense hmargin
  obtain ⟨hbase, hcap⟩ := hfit l hD₀l hlupper
  let m : ℕ := l - 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hml : m + 1 = l := by dsimp [m]; omega
  apply hcycle
  apply cycleGraph_isContained_of_selectedCrossEdgeGraph_alternatingScaffold_cycle_matched_capacity
    hm hk G A B T I M hscaffold hrob hmajorT hq htheta hregions
      hIA hM hmatch
  · rw [hml]
    exact hcopy
  · simpa [hml] using hbase
  · simpa [hml, m] using hcap

/-! ## Source-scale separated robust routing

The generic grouped router in the core deliberately charges the whole
support of every earlier route to the core side of a robust pair.  For the
KLS decomposition the core and connector side are disjoint, so this loses a
factor two.  The following version records the two exact support charges:
an even route of length `2 * (r + 1)` uses at most `r + 2` core vertices
and at most `r + 1` connector vertices. -/

/-- An avoiding even robust route with separate core and connector charges.
The disjointness of `U` and `T` means that prescribed core vertices never
consume common-neighbour capacity in `T`. -/
theorem exists_even_path_between_of_robustPairSet_avoiding_separated
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {U T F : Finset V} {theta r : ℕ}
    (hrob : RobustPairSet G U T theta) (hUT : Disjoint U T)
    {a b : V} (haU : a ∈ U) (hbU : b ∈ U)
    (haF : a ∉ F) (hbF : b ∉ F) (hab : a ≠ b)
    (hUcard : r + 2 ≤ (U \ F).card)
    (hTbudget : (F ∩ T).card + (r + 1) ≤ theta) :
    ∃ p : G.Walk a b,
      p.IsPath ∧ p.length = 2 * (r + 1) ∧
      (∀ v ∈ p.support, v ∉ F) ∧
      (∀ v ∈ p.support, v ∈ U ∨ v ∈ T) ∧
      (p.support.toFinset ∩ U).card ≤ r + 2 ∧
      (p.support.toFinset ∩ T).card ≤ r + 1 := by
  classical
  let U' : Finset V := U \ F
  have haU' : a ∈ U' := Finset.mem_sdiff.mpr ⟨haU, haF⟩
  have hbU' : b ∈ U' := Finset.mem_sdiff.mpr ⟨hbU, hbF⟩
  let W : Finset V := (U'.erase a).erase b
  have hbErase : b ∈ U'.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbU'⟩
  have hWcard : r ≤ W.card := by
    simp only [W, Finset.card_erase_of_mem hbErase,
      Finset.card_erase_of_mem haU']
    change r ≤ (U \ F).card - 1 - 1
    omega
  obtain ⟨A, hAW, hAcard⟩ := Finset.exists_subset_card_eq hWcard
  let e : Fin r ≃ A := (Finset.equivFinOfCardEq hAcard).symm
  let g : Fin (r + 1) → V := Fin.cons a (fun i : Fin r => e i)
  let f : Fin (r + 2) → V := Fin.snoc g b
  have heinj : Function.Injective (fun i : Fin r => (e i : V)) := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  have ha_not_range : a ∉ Set.range (fun i : Fin r => (e i : V)) := by
    rintro ⟨i, hi⟩
    have heiW : (e i : V) ∈ W := hAW (e i).property
    have hne : (e i : V) ≠ a :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp heiW).2).1
    exact hne hi
  have hginj : Function.Injective g :=
    Fin.cons_injective_iff.mpr ⟨ha_not_range, heinj⟩
  have hb_not_range : b ∉ Set.range g := by
    rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => exact hab (by simpa [g] using hi)
    | succ i =>
        have heiW : (e i : V) ∈ W := hAW (e i).property
        have hne : (e i : V) ≠ b := (Finset.mem_erase.mp heiW).1
        exact hne (by simpa [g] using hi)
  have hfinj : Function.Injective f :=
    Fin.snoc_injective_iff.mpr ⟨hginj, hb_not_range⟩
  have hfU' : ∀ i : Fin (r + 2), f i ∈ U' := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa [f] using hbU'
    | cast i =>
        dsimp [f]
        rw [Fin.snoc_castSucc]
        induction i using Fin.cases with
        | zero => exact haU'
        | succ j =>
            have hejW : (e j : V) ∈ W := hAW (e j).property
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hejW).2).2
  have hfU : ∀ i : Fin (r + 2), f i ∈ U :=
    fun i => (Finset.mem_sdiff.mp (hfU' i)).1
  have hfF : ∀ i : Fin (r + 2), f i ∉ F :=
    fun i => (Finset.mem_sdiff.mp (hfU' i)).2
  let left : Fin (r + 1) → V := fun i => f i.castSucc
  let right : Fin (r + 1) → V := fun i => f i.succ
  have hpair : ∀ i : Fin (r + 1), theta ≤
      (Erdos163.FiniteDefect.commonNeighbors G ![left i, right i] T).card := by
    intro i
    exact hrob _ (hfU i.castSucc) _ (hfU i.succ)
  obtain ⟨z, hzinj, hz⟩ :=
    exists_fresh_middle_vertices_fin G left right hpair hTbudget
  have hfz : ∀ i : Fin (r + 2), ∀ j : Fin (r + 1), f i ≠ z j := by
    intro i j hij
    exact (Finset.disjoint_left.mp hUT) (hfU i) (hij ▸ (hz j).1)
  have hzF : ∀ j : Fin (r + 1), z j ∉ F := by
    intro j hzjF
    exact (hz j).2.1 (Finset.mem_inter.mpr ⟨hzjF, (hz j).1⟩)
  have hadj : ∀ i : Fin (r + 1),
      G.Adj (f i.castSucc) (z i) ∧ G.Adj (z i) (f i.succ) := by
    intro i
    simpa [left, right] using (hz i).2.2
  obtain ⟨p, hp, hplen, hpsupp⟩ :=
    exists_alternating_path_fin G f z hfinj hzinj hfz hadj
  have hstart : f 0 = a := by simp [f, g]
  have hend : f (Fin.last (r + 1)) = b := by simp [f]
  let p' : G.Walk a b := p.copy hstart hend
  have hp'supp : ∀ v ∈ p'.support,
      (∃ i : Fin (r + 2), v = f i) ∨
        ∃ j : Fin (r + 1), v = z j := by
    intro v hv
    have hvp : v ∈ p.support := by simpa [p'] using hv
    rcases hpsupp v hvp with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨j, hj.symm⟩
  refine ⟨p', by simpa [p'] using hp,
    by simpa [p', SimpleGraph.Walk.length_copy] using hplen, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases hp'supp v hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact hfF i
    · exact hzF j
  · intro v hv
    rcases hp'supp v hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (hfU i)
    · exact Or.inr (hz j).1
  · calc
      (p'.support.toFinset ∩ U).card ≤
          ((Finset.univ : Finset (Fin (r + 2))).image f).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_inter.mp hv with ⟨hvp, hvU⟩
        rcases hp'supp v (by simpa using hvp) with
          ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact (Finset.disjoint_left.mp hUT) hvU (hz j).1 |>.elim
      _ = r + 2 := by
        rw [Finset.card_image_of_injective _ hfinj]
        simp
  · calc
      (p'.support.toFinset ∩ T).card ≤
          ((Finset.univ : Finset (Fin (r + 1))).image z).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_inter.mp hv with ⟨hvp, hvT⟩
        rcases hp'supp v (by simpa using hvp) with
          ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact (Finset.disjoint_left.mp hUT) (hfU i) hvT |>.elim
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      _ = r + 1 := by
        rw [Finset.card_image_of_injective _ hzinj]
        simp

/-- Greedy exact-length routing inside one robust pair, with the two
reservoirs accounted for separately.  The old support-size estimate charges
every connector against `U` and every core vertex against `T`; this form
records the actual alternating-path usage. -/
theorem exists_pairwise_disjoint_even_paths_lengths_separated
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ {q theta : ℕ} (r : Fin q → ℕ) {U T F : Finset V},
      RobustPairSet G U T theta → Disjoint U T →
      ∀ (a b : Fin q → V),
      (∀ i, a i ∈ U) → (∀ i, b i ∈ U) →
      (∀ i, a i ∉ F) → (∀ i, b i ∉ F) →
      (∀ i, a i ≠ b i) →
      (∀ i j, i ≠ j →
        a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j) →
      (F ∩ U).card + (∑ i : Fin q, (r i + 2)) ≤ U.card →
      (F ∩ T).card + (∑ i : Fin q, (r i + 1)) ≤ theta →
      ∃ p : ∀ i : Fin q, G.Walk (a i) (b i),
        (∀ i, (p i).IsPath) ∧
        (∀ i, (p i).length = 2 * (r i + 1)) ∧
        (∀ i, ∀ v ∈ (p i).support, v ∉ F) ∧
        (∀ i, ∀ v ∈ (p i).support, v ∈ U ∨ v ∈ T) ∧
        (∀ i j, i ≠ j → (p i).support.Disjoint (p j).support) ∧
        ((F ∪ (Finset.univ : Finset (Fin q)).biUnion
          (fun i => (p i).support.toFinset)) ∩ U).card ≤
            (F ∩ U).card + ∑ i : Fin q, (r i + 2) ∧
        ((F ∪ (Finset.univ : Finset (Fin q)).biUnion
          (fun i => (p i).support.toFinset)) ∩ T).card ≤
            (F ∩ T).card + ∑ i : Fin q, (r i + 1) := by
  classical
  intro q
  induction q with
  | zero =>
      intro theta r U T F hrob hUT a b ha hb haF hbF hab hpairs hU hT
      refine ⟨fun i => i.elim0, ?_⟩
      simp
  | succ q ih =>
      intro theta r U T F hrob hUT a b ha hb haF hbF hab hpairs hU hT
      let last : Fin (q + 1) := Fin.last q
      let r₀ : Fin q → ℕ := fun i => r i.castSucc
      let a₀ : Fin q → V := fun i => a i.castSucc
      let b₀ : Fin q → V := fun i => b i.castSucc
      let F' : Finset V := insert (a last) (insert (b last) F)
      have hsumU : (∑ i : Fin (q + 1), (r i + 2)) =
          (∑ i : Fin q, (r₀ i + 2)) + (r last + 2) := by
        rw [Fin.sum_univ_castSucc]
      have hsumT : (∑ i : Fin (q + 1), (r i + 1)) =
          (∑ i : Fin q, (r₀ i + 1)) + (r last + 1) := by
        rw [Fin.sum_univ_castSucc]
      have hF'U : (F' ∩ U).card = (F ∩ U).card + 2 := by
        have hset : F' ∩ U =
            insert (a last) (insert (b last) (F ∩ U)) := by
          ext v
          simp [F', ha last, hb last]
        have hbnot : b last ∉ F ∩ U := by
          simp [hbF last]
        have hanot : a last ∉ insert (b last) (F ∩ U) := by
          simp [hab last, haF last]
        rw [hset, Finset.card_insert_of_notMem hanot,
          Finset.card_insert_of_notMem hbnot]
      have haT : ∀ i, a i ∉ T := by
        intro i hai
        exact (Finset.disjoint_left.mp hUT) (ha i) hai
      have hbT : ∀ i, b i ∉ T := by
        intro i hbi
        exact (Finset.disjoint_left.mp hUT) (hb i) hbi
      have hF'T : F' ∩ T = F ∩ T := by
        ext v
        simp only [F', Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hav | hbv | hvF, hvT⟩
          · exact (haT last (hav ▸ hvT)).elim
          · exact (hbT last (hbv ▸ hvT)).elim
          · exact ⟨hvF, hvT⟩
        · rintro ⟨hvF, hvT⟩
          exact ⟨Or.inr (Or.inr hvF), hvT⟩
      have ha₀F : ∀ i, a₀ i ∉ F' := by
        intro i
        have hpair := hpairs i.castSucc last (Fin.castSucc_ne_last i)
        simp [a₀, F', hpair.1, hpair.2.1, haF i.castSucc]
      have hb₀F : ∀ i, b₀ i ∉ F' := by
        intro i
        have hpair := hpairs i.castSucc last (Fin.castSucc_ne_last i)
        simp [b₀, F', hpair.2.2.1, hpair.2.2.2, hbF i.castSucc]
      have hU₀ : (F' ∩ U).card + (∑ i : Fin q, (r₀ i + 2)) ≤ U.card := by
        rw [hsumU] at hU
        omega
      have hT₀ : (F' ∩ T).card + (∑ i : Fin q, (r₀ i + 1)) ≤ theta := by
        rw [hsumT] at hT
        rw [hF'T]
        omega
      obtain ⟨p, hp, hplen, hpavoid, hploc, hpdisj, hpU, hpT⟩ :=
        ih r₀ hrob hUT a₀ b₀
          (fun i => ha i.castSucc) (fun i => hb i.castSucc)
          ha₀F hb₀F (fun i => hab i.castSucc)
          (fun i j hij => hpairs i.castSucc j.castSucc (by
            intro h
            exact hij (Fin.castSucc_injective _ h))) hU₀ hT₀
      let used : Finset V :=
        F ∪ (Finset.univ : Finset (Fin q)).biUnion
          (fun i => (p i).support.toFinset)
      have haLastUsed : a last ∉ used := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hmem | hmem
        · exact haF last hmem
        · rcases Finset.mem_biUnion.mp hmem with ⟨i, _hi, hmem⟩
          exact hpavoid i (a last) (by simpa using hmem) (by simp [F'])
      have hbLastUsed : b last ∉ used := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hmem | hmem
        · exact hbF last hmem
        · rcases Finset.mem_biUnion.mp hmem with ⟨i, _hi, hmem⟩
          exact hpavoid i (b last) (by simpa using hmem) (by simp [F'])
      have husedSub : used ⊆
          F' ∪ (Finset.univ : Finset (Fin q)).biUnion
            (fun i => (p i).support.toFinset) := by
        intro v hv
        rcases Finset.mem_union.mp hv with hvF | hvp
        · exact Finset.mem_union_left _ (by simp [F', hvF])
        · exact Finset.mem_union_right _ hvp
      have husedU : (used ∩ U).card ≤
          (F ∩ U).card + ∑ i : Fin q, (r₀ i + 2) := by
        have hset :
            F' ∪ (Finset.univ : Finset (Fin q)).biUnion
                (fun i => (p i).support.toFinset) =
              insert (a last) (insert (b last) used) := by
          ext v
          simp [F', used, or_assoc, or_left_comm, or_comm]
        have hinter :
            (insert (a last) (insert (b last) used) ∩ U) =
              insert (a last) (insert (b last) (used ∩ U)) := by
          ext v
          simp [ha last, hb last]
        have hbnot : b last ∉ used ∩ U := by
          simp [hbLastUsed]
        have hanot : a last ∉ insert (b last) (used ∩ U) := by
          simp [hab last, haLastUsed]
        rw [hset, hinter, Finset.card_insert_of_notMem hanot,
          Finset.card_insert_of_notMem hbnot] at hpU
        omega
      have husedT : (used ∩ T).card ≤
          (F ∩ T).card + ∑ i : Fin q, (r₀ i + 1) := by
        have hle : (used ∩ T).card ≤
            ((F' ∪ (Finset.univ : Finset (Fin q)).biUnion
              (fun i => (p i).support.toFinset)) ∩ T).card := by
          apply Finset.card_le_card
          intro v hv
          exact Finset.mem_inter.mpr
            ⟨husedSub (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
        change (used ∩ T).card ≤
          (F ∩ T).card + ∑ i : Fin q, (r₀ i + 1)
        rw [hF'T] at hpT
        exact hle.trans hpT
      have hLastCard : r last + 2 ≤ (U \ used).card := by
        rw [Finset.card_sdiff]
        rw [hsumU] at hU
        omega
      have hLastBudget : (used ∩ T).card + (r last + 1) ≤ theta := by
        rw [hsumT] at hT
        omega
      obtain ⟨plast, hplast, hplastlen, hplastavoid, hplastloc,
          hplastU, hplastT⟩ :=
        exists_even_path_between_of_robustPairSet_avoiding_separated
          G hrob hUT (ha last) (hb last) haLastUsed hbLastUsed
            (hab last) hLastCard hLastBudget
      let p' : ∀ i : Fin (q + 1), G.Walk (a i) (b i) :=
        Fin.lastCases plast p
      refine ⟨p', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa [p'] using hplast
        | cast i => simpa [p', a₀, b₀] using hp i
      · intro i
        induction i using Fin.lastCases with
        | last => simpa [p', last] using hplastlen
        | cast i => simpa [p', r₀] using hplen i
      · intro i v hv
        induction i using Fin.lastCases with
        | last =>
            exact fun hvF => hplastavoid v (by simpa [p'] using hv)
              (Finset.mem_union_left _ hvF)
        | cast i =>
            exact fun hvF => hpavoid i v (by simpa [p'] using hv)
              (by simp [F', hvF])
      · intro i v hv
        induction i using Fin.lastCases with
        | last => exact hplastloc v (by simpa [p'] using hv)
        | cast i => exact hploc i v (by simpa [p'] using hv)
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                intro v hvlast hvj
                exact hplastavoid v (by simpa [p'] using hvlast)
                  (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                    ⟨j, Finset.mem_univ _, by simpa [p'] using hvj⟩))
        | cast i =>
            induction j using Fin.lastCases with
            | last =>
                intro v hvi hvlast
                exact hplastavoid v (by simpa [p'] using hvlast)
                  (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                    ⟨i, Finset.mem_univ _, by simpa [p'] using hvi⟩))
            | cast j =>
                have hij' : i ≠ j := by
                  intro h
                  exact hij (congrArg Fin.castSucc h)
                simpa [p'] using hpdisj i j hij'
      · have hrewrite :
            F ∪ (Finset.univ : Finset (Fin (q + 1))).biUnion
                (fun i => (p' i).support.toFinset) =
              used ∪ plast.support.toFinset := by
            ext v
            simp only [used, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_univ, true_and]
            constructor
            · rintro (hvF | ⟨i, hi⟩)
              · exact Or.inl (Or.inl hvF)
              · induction i using Fin.lastCases with
                | last => exact Or.inr (by simpa [p'] using hi)
                | cast i => exact Or.inl (Or.inr ⟨i, by simpa [p'] using hi⟩)
            · intro hv
              rcases hv with hused | hvlast
              · rcases hused with hvF | ⟨i, hi⟩
                · exact Or.inl hvF
                · exact Or.inr ⟨i.castSucc, by simpa [p'] using hi⟩
              · exact Or.inr ⟨last, by simpa [p', last] using hvlast⟩
        rw [hrewrite, hsumU]
        calc
          ((used ∪ plast.support.toFinset) ∩ U).card ≤
              (used ∩ U).card +
                (plast.support.toFinset ∩ U).card := by
            rw [show (used ∪ plast.support.toFinset) ∩ U =
              (used ∩ U) ∪ (plast.support.toFinset ∩ U) by
                ext v
                simp only [Finset.mem_inter, Finset.mem_union]
                constructor
                · rintro ⟨hu | hp, hvU⟩
                  · exact Or.inl ⟨hu, hvU⟩
                  · exact Or.inr ⟨hp, hvU⟩
                · rintro (⟨hu, hvU⟩ | ⟨hp, hvU⟩)
                  · exact ⟨Or.inl hu, hvU⟩
                  · exact ⟨Or.inr hp, hvU⟩]
            exact Finset.card_union_le _ _
          _ ≤ ((F ∩ U).card + ∑ i : Fin q, (r₀ i + 2)) +
                (r last + 2) := Nat.add_le_add husedU hplastU
        omega
      · have hrewrite :
            F ∪ (Finset.univ : Finset (Fin (q + 1))).biUnion
                (fun i => (p' i).support.toFinset) =
              used ∪ plast.support.toFinset := by
            ext v
            simp only [used, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_univ, true_and]
            constructor
            · rintro (hvF | ⟨i, hi⟩)
              · exact Or.inl (Or.inl hvF)
              · induction i using Fin.lastCases with
                | last => exact Or.inr (by simpa [p'] using hi)
                | cast i => exact Or.inl (Or.inr ⟨i, by simpa [p'] using hi⟩)
            · intro hv
              rcases hv with hused | hvlast
              · rcases hused with hvF | ⟨i, hi⟩
                · exact Or.inl hvF
                · exact Or.inr ⟨i.castSucc, by simpa [p'] using hi⟩
              · exact Or.inr ⟨last, by simpa [p', last] using hvlast⟩
        rw [hrewrite, hsumT]
        calc
          ((used ∪ plast.support.toFinset) ∩ T).card ≤
              (used ∩ T).card +
                (plast.support.toFinset ∩ T).card := by
            rw [show (used ∪ plast.support.toFinset) ∩ T =
              (used ∩ T) ∪ (plast.support.toFinset ∩ T) by
                ext v
                simp only [Finset.mem_inter, Finset.mem_union]
                constructor
                · rintro ⟨hu | hp, hvT⟩
                  · exact Or.inl ⟨hu, hvT⟩
                  · exact Or.inr ⟨hp, hvT⟩
                · rintro (⟨hu, hvT⟩ | ⟨hp, hvT⟩)
                  · exact ⟨Or.inl hu, hvT⟩
                  · exact ⟨Or.inr hp, hvT⟩]
            exact Finset.card_union_le _ _
          _ ≤ ((F ∩ T).card + ∑ i : Fin q, (r₀ i + 1)) +
                (r last + 1) := Nat.add_le_add husedT hplastT
        omega

/-- Fintype-indexed interface to the separated exact-length router. -/
theorem exists_pairwise_disjoint_even_paths_lengths_fintype_separated
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {theta : ℕ} (r : J → ℕ) {U T F : Finset V}
    (hrob : RobustPairSet G U T theta) (hUT : Disjoint U T)
    (a b : J → V)
    (ha : ∀ i, a i ∈ U) (hb : ∀ i, b i ∈ U)
    (haF : ∀ i, a i ∉ F) (hbF : ∀ i, b i ∉ F)
    (hab : ∀ i, a i ≠ b i)
    (hpairs : ∀ i j, i ≠ j →
      a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j)
    (hU : (F ∩ U).card + (∑ i : J, (r i + 2)) ≤ U.card)
    (hT : (F ∩ T).card + (∑ i : J, (r i + 1)) ≤ theta) :
    ∃ p : ∀ i : J, G.Walk (a i) (b i),
      (∀ i, (p i).IsPath) ∧
      (∀ i, (p i).length = 2 * (r i + 1)) ∧
      (∀ i, ∀ v ∈ (p i).support, v ∉ F) ∧
      (∀ i, ∀ v ∈ (p i).support, v ∈ U ∨ v ∈ T) ∧
      ∀ i j, i ≠ j → (p i).support.Disjoint (p j).support := by
  classical
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let r' : Fin (Fintype.card J) → ℕ := fun i => r (e i)
  let a' : Fin (Fintype.card J) → V := fun i => a (e i)
  let b' : Fin (Fintype.card J) → V := fun i => b (e i)
  have hsumU : (∑ i : Fin (Fintype.card J), (r' i + 2)) =
      ∑ j : J, (r j + 2) := by
    exact e.sum_comp (fun j : J => r j + 2)
  have hsumT : (∑ i : Fin (Fintype.card J), (r' i + 1)) =
      ∑ j : J, (r j + 1) := by
    exact e.sum_comp (fun j : J => r j + 1)
  obtain ⟨q, hq, hqlen, hqavoid, hqloc, hqdisj, _hqU, _hqT⟩ :=
    exists_pairwise_disjoint_even_paths_lengths_separated
      G r' hrob hUT a' b'
        (fun i => ha (e i)) (fun i => hb (e i))
        (fun i => haF (e i)) (fun i => hbF (e i))
        (fun i => hab (e i))
        (fun i j hij => hpairs (e i) (e j) (fun h => hij (e.injective h)))
        (by rw [hsumU]; exact hU) (by rw [hsumT]; exact hT)
  let p : ∀ i : J, G.Walk (a i) (b i) := fun i =>
    (q (e.symm i)).copy (by simp [a', e]) (by simp [b', e])
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [p] using hq (e.symm i)
  · intro i
    simpa [p, r'] using hqlen (e.symm i)
  · intro i v hv
    apply hqavoid (e.symm i) v
    simpa [p] using hv
  · intro i v hv
    exact hqloc (e.symm i) v (by simpa [p] using hv)
  · intro i j hij
    have hij' : e.symm i ≠ e.symm j := by
      intro h
      apply hij
      exact e.symm.injective h
    simpa [p] using hqdisj (e.symm i) (e.symm j) hij'

/-- Per-hub separated routing.  Requests in one fiber share only that hub's
two budgets; disjoint robust regions separate distinct fibers. -/
theorem exists_pairwise_disjoint_even_paths_lengths_grouped_separated
    {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {theta : ℕ} (r : J → ℕ) (hub : J → I)
    (U T : I → Finset V)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (a b : J → V) (F : I → Finset V)
    (ha : ∀ x, a x ∈ U (hub x)) (hb : ∀ x, b x ∈ U (hub x))
    (haF : ∀ x, a x ∉ F (hub x)) (hbF : ∀ x, b x ∉ F (hub x))
    (hab : ∀ x, a x ≠ b x)
    (hpairs : ∀ x y, x ≠ y →
      a x ≠ a y ∧ a x ≠ b y ∧ b x ≠ a y ∧ b x ≠ b y)
    (hU : ∀ i,
      ((F i) ∩ U i).card +
        (∑ x : {j : J // hub j = i}, (r x.1 + 2)) ≤ (U i).card)
    (hT : ∀ i,
      ((F i) ∩ T i).card +
        (∑ x : {j : J // hub j = i}, (r x.1 + 1)) ≤ theta) :
    ∃ p : ∀ x : J, G.Walk (a x) (b x),
      (∀ x, (p x).IsPath) ∧
      (∀ x, (p x).length = 2 * (r x + 1)) ∧
      (∀ x, ∀ v ∈ (p x).support, v ∉ F (hub x)) ∧
      (∀ x, ∀ v ∈ (p x).support,
        v ∈ U (hub x) ∨ v ∈ T (hub x)) ∧
      ∀ x y, x ≠ y → (p x).support.Disjoint (p y).support := by
  classical
  have hex : ∀ i : I,
      ∃ p : ∀ x : {j : J // hub j = i}, G.Walk (a x.1) (b x.1),
        (∀ x, (p x).IsPath) ∧
        (∀ x, (p x).length = 2 * (r x.1 + 1)) ∧
        (∀ x, ∀ v ∈ (p x).support, v ∉ F i) ∧
        (∀ x, ∀ v ∈ (p x).support, v ∈ U i ∨ v ∈ T i) ∧
        ∀ x y, x ≠ y → (p x).support.Disjoint (p y).support := by
    intro i
    apply exists_pairwise_disjoint_even_paths_lengths_fintype_separated
      G (fun x : {j : J // hub j = i} => r x.1)
        (hrob i) (hUT i) (fun x => a x.1) (fun x => b x.1)
    · intro x
      simpa [x.property] using ha x.1
    · intro x
      simpa [x.property] using hb x.1
    · intro x
      simpa [x.property] using haF x.1
    · intro x
      simpa [x.property] using hbF x.1
    · exact fun x => hab x.1
    · intro x y hxy
      apply hpairs x.1 y.1
      intro h
      exact hxy (Subtype.ext h)
    · exact hU i
    · exact hT i
  let route := fun i : I => Classical.choose (hex i)
  have hlocal := fun i : I => Classical.choose_spec (hex i)
  let p : ∀ x : J, G.Walk (a x) (b x) := fun x =>
    route (hub x) ⟨x, rfl⟩
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hlocal (hub x)).1 ⟨x, rfl⟩
  · intro x
    exact (hlocal (hub x)).2.1 ⟨x, rfl⟩
  · intro x v hv
    exact (hlocal (hub x)).2.2.1 ⟨x, rfl⟩ v (by simpa [p] using hv)
  · intro x v hv
    exact (hlocal (hub x)).2.2.2.1 ⟨x, rfl⟩ v (by simpa [p] using hv)
  · intro x y hxy
    by_cases hh : hub x = hub y
    · have hsub : (⟨x, rfl⟩ : {z : J // hub z = hub x}) ≠
          ⟨y, hh.symm⟩ := by
        intro h
        exact hxy (congrArg Subtype.val h)
      have hd := (hlocal (hub x)).2.2.2.2
        ⟨x, rfl⟩ ⟨y, hh.symm⟩ hsub
      have harg :
          HEq (⟨y, hh.symm⟩ : {z : J // hub z = hub x})
            (⟨y, rfl⟩ : {z : J // hub z = hub y}) := by
        exact Mathlib.Tactic.DepRewrite.hdcongrArg hh
          (fun c hc =>
            (⟨y, hh.symm.trans hc⟩ : {z : J // hub z = c}))
      let supp : ∀ c : I, {z : J // hub z = c} → List V :=
        fun c z => (route c z).support
      have hfun : supp (hub x) ≍ supp (hub y) := congr_arg_heq supp hh
      have hsupp : supp (hub x) ⟨y, hh.symm⟩ =
          supp (hub y) ⟨y, rfl⟩ := congr_heq hfun harg
      dsimp [p]
      change (supp (hub x) ⟨x, rfl⟩).Disjoint
        (supp (hub y) ⟨y, rfl⟩)
      rw [← hsupp]
      exact hd
    · intro v hvx hvy
      have hlx := (hlocal (hub x)).2.2.2.1 ⟨x, rfl⟩ v
        (by simpa [p] using hvx)
      have hly := (hlocal (hub y)).2.2.2.1 ⟨y, rfl⟩ v
        (by simpa [p] using hvy)
      apply (Finset.disjoint_left.mp (hregions (hub x) (hub y) hh))
      · exact Finset.mem_union.mpr hlx
      · exact Finset.mem_union.mpr hly

/-- Fresh-root cyclic splice with separate core and connector accounting on
every noninitial visit.  The distinguished root route supplies the required
parity; freshness keeps it in a region disjoint from all tail routes. -/
theorem cycleGraph_isContained_of_cyclic_fresh_root_routes_lengths_separated
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m ell theta k : ℕ} (r : Fin m → ℕ) (hk : 3 ≤ k)
    (hub : Fin (m + 1) → I) (U T : I → Finset V)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hfresh : ∀ j : Fin m, hub j.succ ≠ hub 0)
    (a b : Fin (m + 1) → V)
    (ha : ∀ i, a i ∈ U (hub i)) (hb : ∀ i, b i ∈ U (hub i))
    (hab : ∀ i, a i ≠ b i)
    (hpairs : ∀ i j, i ≠ j →
      a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j)
    (hcross : ∀ i : Fin m, G.Adj (b i.castSucc) (a i.succ))
    (hclose : G.Adj (b (Fin.last m)) (a 0))
    (hell : 5 ≤ ell)
    (hparity : HasCrossMatchingAtLeast G (U (hub 0)) (U (hub 0)) 3)
    (hFirstU : ell ≤ (U (hub 0)).card)
    (hFirstT : ell + 1 ≤ theta)
    (hRestU : ∀ i : I,
      (∑ x : {j : Fin m // hub j.succ = i}, (r x.1 + 2)) ≤
        (U i).card)
    (hRestT : ∀ i : I,
      (∑ x : {j : Fin m // hub j.succ = i}, (r x.1 + 1)) ≤
        theta)
    (hlen : ell + (∑ j : Fin m, 2 * (r j + 1)) + (m + 1) = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  let Fedge : Finset V := {a 0, b 0}
  have hFedgecard : Fedge.card < 3 := by
    have hcard : Fedge.card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨x, hxU, y, hyU, hxFedge, hyFedge, hxy⟩ :=
    exists_oriented_cross_edge_avoiding_of_hasCrossMatchingAtLeast
      G hparity hFedgecard
  have hxdata : x ≠ a 0 ∧ x ≠ b 0 := by
    simpa [Fedge] using hxFedge
  have hydata : y ≠ a 0 ∧ y ≠ b 0 := by
    simpa [Fedge] using hyFedge
  obtain ⟨p₀, hp₀, hp₀len, _hp₀avoid, hp₀loc⟩ :=
    exists_path_between_of_robustPairSet_and_parity_edge_avoiding (F := ∅) G
      (hrob (hub 0)) (ha 0) hxU hyU (hb 0)
      (by simp) (by simp) (by simp) (by simp) hxy
      hxdata.1.symm hydata.1.symm (hab 0)
      hxdata.2 hydata.2 hell (by simpa using hFirstU)
      (by simpa using hFirstT)
  let aR : Fin m → V := fun j => a j.succ
  let bR : Fin m → V := fun j => b j.succ
  let hubR : Fin m → I := fun j => hub j.succ
  obtain ⟨pR, hpR, hpRlen, _hpRavoid, hpRloc, hpRdisj⟩ :=
    exists_pairwise_disjoint_even_paths_lengths_grouped_separated
      G r hubR U T hrob hUT hregions aR bR (fun _ => ∅)
      (fun j => ha j.succ) (fun j => hb j.succ)
      (by simp) (by simp) (fun j => hab j.succ)
      (fun i j hij => hpairs i.succ j.succ (by
        intro h
        exact hij (Fin.succ_injective _ h)))
      (by
        intro i
        simpa [hubR] using hRestU i)
      (by
        intro i
        simpa [hubR] using hRestT i)
  have hp₀R : ∀ j, p₀.support.Disjoint (pR j).support := by
    intro j v hv₀ hvR
    have hv₀loc := hp₀loc v hv₀
    have hvRloc := hpRloc j v hvR
    exact (Finset.disjoint_left.mp
      (hregions (hub 0) (hubR j) (Ne.symm (hfresh j))))
        (Finset.mem_union.mpr hv₀loc) (Finset.mem_union.mpr hvRloc)
  let p : ∀ i : Fin (m + 1), G.Walk (a i) (b i) := Fin.cases p₀ pR
  have hp : ∀ i, (p i).IsPath := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [p] using hp₀
    | succ i => simpa [p, aR, bR] using hpR i
  have hpdisj : ∀ i j, i ≠ j →
      (p i).support.Disjoint (p j).support := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa [p] using hp₀R j
    | succ i =>
        induction j using Fin.cases with
        | zero => simpa [p] using (hp₀R i).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              exact hij (congrArg Fin.succ h)
            simpa [p] using hpRdisj i j hij'
  have hsum : (∑ i : Fin (m + 1), (p i).length) =
      ell + ∑ j : Fin m, 2 * (r j + 1) := by
    rw [Fin.sum_univ_succ]
    have hrest : (∑ i : Fin m, (p i.succ).length) =
        ∑ i : Fin m, 2 * (r i + 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa [p] using hpRlen i
    rw [hrest]
    simp [p, hp₀len]
  apply cycleGraph_isContained_of_cyclic_cross_edges_and_disjoint_paths_fin
    G hk a b p hp hpdisj hcross hclose
  · rw [hsum]
    omega
  · rw [hsum]
    exact hlen

/-- Value-indexed wrapper for the preceding fresh-root splice. -/
theorem cycleGraph_isContained_of_cyclic_fresh_root_routes_lengths_separated_val
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q ell theta k : ℕ} (hq : 0 < q) (hk : 3 ≤ k)
    (r : Fin (q - 1) → ℕ) (hub : Fin q → I)
    (tail : Fin (q - 1) → Fin q) (htail : ∀ j, (tail j).val = j.val + 1)
    (U T : I → Finset V)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hfresh : ∀ j, hub (tail j) ≠ hub ⟨0, hq⟩)
    (a b : Fin q → V)
    (ha : ∀ i, a i ∈ U (hub i)) (hb : ∀ i, b i ∈ U (hub i))
    (hab : ∀ i, a i ≠ b i)
    (hpairs : ∀ i j, i ≠ j →
      a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j)
    (hcross : ∀ i j : Fin q, j.val = i.val + 1 → G.Adj (b i) (a j))
    (hclose : ∀ i j : Fin q, i.val + 1 = q → j.val = 0 →
      G.Adj (b i) (a j))
    (hell : 5 ≤ ell)
    (hparity : HasCrossMatchingAtLeast G
      (U (hub ⟨0, hq⟩)) (U (hub ⟨0, hq⟩)) 3)
    (hFirstU : ell ≤ (U (hub ⟨0, hq⟩)).card)
    (hFirstT : ell + 1 ≤ theta)
    (hRestU : ∀ i : I,
      (∑ x : {j : Fin (q - 1) // hub (tail j) = i}, (r x.1 + 2)) ≤
        (U i).card)
    (hRestT : ∀ i : I,
      (∑ x : {j : Fin (q - 1) // hub (tail j) = i}, (r x.1 + 1)) ≤
        theta)
    (hlen : ell + (∑ j : Fin (q - 1), 2 * (r j + 1)) + q = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  cases q with
  | zero => omega
  | succ m =>
      have hm : m + 1 - 1 = m := Nat.add_sub_cancel m 1
      let indexEquiv : Fin (m + 1 - 1) ≃ Fin m :=
        (Fin.castOrderIso hm).toEquiv
      let rM : Fin m → ℕ := fun j => r (indexEquiv.symm j)
      let fiberEquiv (i : I) :
          {j : Fin (m + 1 - 1) // hub (tail j) = i} ≃
            {j : Fin m // hub j.succ = i} :=
        { toFun := fun j => ⟨indexEquiv j.1, by
            have hj : tail j.1 = (indexEquiv j.1).succ := by
              apply Fin.ext
              simpa [indexEquiv] using htail j.1
            simpa [hj] using j.2⟩
          invFun := fun j => ⟨indexEquiv.symm j.1, by
            have hj : tail (indexEquiv.symm j.1) = j.1.succ := by
              apply Fin.ext
              simpa [indexEquiv] using htail (indexEquiv.symm j.1)
            simpa [hj] using j.2⟩
          left_inv := fun j => Subtype.ext (indexEquiv.symm_apply_apply j.1)
          right_inv := fun j => Subtype.ext (indexEquiv.apply_symm_apply j.1) }
      have hsumU (i : I) :
          (∑ x : {j : Fin (m + 1 - 1) // hub (tail j) = i},
            (r x.1 + 2)) =
          ∑ x : {j : Fin m // hub j.succ = i}, (rM x.1 + 2) := by
        simpa [fiberEquiv, rM] using
          (fiberEquiv i).sum_comp
            (fun x : {j : Fin m // hub j.succ = i} => rM x.1 + 2)
      have hsumT (i : I) :
          (∑ x : {j : Fin (m + 1 - 1) // hub (tail j) = i},
            (r x.1 + 1)) =
          ∑ x : {j : Fin m // hub j.succ = i}, (rM x.1 + 1) := by
        simpa [fiberEquiv, rM] using
          (fiberEquiv i).sum_comp
            (fun x : {j : Fin m // hub j.succ = i} => rM x.1 + 1)
      have hsumLen :
          (∑ j : Fin (m + 1 - 1), 2 * (r j + 1)) =
            ∑ j : Fin m, 2 * (rM j + 1) := by
        simpa [rM] using
          indexEquiv.sum_comp (fun j : Fin m => 2 * (rM j + 1))
      have hzero : (0 : Fin (m + 1)) = ⟨0, hq⟩ := Fin.ext rfl
      apply cycleGraph_isContained_of_cyclic_fresh_root_routes_lengths_separated
        G rM hk hub U T hrob hUT hregions
          (fun j => by
            have hj : tail (indexEquiv.symm j) = j.succ := by
              apply Fin.ext
              simpa [indexEquiv] using htail (indexEquiv.symm j)
            have hf := hfresh (indexEquiv.symm j)
            rw [hj] at hf
            have hh : hub 0 = hub ⟨0, hq⟩ := congrArg hub hzero
            exact fun heq => hf (heq.trans hh)) a b
      · exact ha
      · exact hb
      · exact hab
      · exact hpairs
      · intro i
        apply hcross i.castSucc i.succ
        simp
      · apply hclose (Fin.last m) 0 <;> simp
      · exact hell
      · have hh : hub 0 = hub ⟨0, hq⟩ := congrArg hub hzero
        rw [hh]
        exact hparity
      · have hh : hub 0 = hub ⟨0, hq⟩ := congrArg hub hzero
        rw [hh]
        exact hFirstU
      · exact hFirstT
      · intro i
        rw [← hsumU i]
        exact hRestU i
      · intro i
        rw [← hsumT i]
        exact hRestT i
      · rw [← hsumLen]
        simpa using hlen

/-- Exact all-parity lift of a fresh-root closed auxiliary walk with
separated core/connector budgets on its nonroot visits. -/
theorem cycleGraph_isContained_of_closed_largeCrossMatching_walk_fresh_root_separated
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph I) (U T : I → Finset V)
    {ell theta R k : ℕ} {u : I} (w : H.Walk u u)
    (r : Fin (w.length - 1) → ℕ)
    (hwlen : 2 ≤ w.length)
    (hwfresh : ∀ j : Fin (w.length - 1),
      w.getVert (j.val + 1) ≠ u)
    (hmatchBudget : 2 * w.length < R)
    (hlarge : ∀ i j, H.Adj i j → HasCrossMatchingAtLeast G (U i) (U j) R)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hell : 5 ≤ ell)
    (hparity : HasCrossMatchingAtLeast G (U u) (U u) 3)
    (hFirstU : ell ≤ (U u).card)
    (hFirstT : ell + 1 ≤ theta)
    (hRestU : ∀ i : I,
      (∑ x : {j : Fin (w.length - 1) //
        w.getVert (j.val + 1) = i}, (r x.1 + 2)) ≤ (U i).card)
    (hRestT : ∀ i : I,
      (∑ x : {j : Fin (w.length - 1) //
        w.getVert (j.val + 1) = i}, (r x.1 + 1)) ≤ theta)
    (hlen : ell + (∑ j : Fin (w.length - 1), 2 * (r j + 1)) +
      w.length = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  obtain ⟨a, b, ha, hb, hab, hpairs, hcross, hclose⟩ :=
    exists_globally_disjoint_cyclic_cross_edges_along_closed_walk
      G H U w hwlen hmatchBudget hlarge
  let tail : Fin (w.length - 1) → Fin w.length := fun j =>
    ⟨j.val + 1, by omega⟩
  apply cycleGraph_isContained_of_cyclic_fresh_root_routes_lengths_separated_val
    G (by omega) (by omega) r (fun i => w.getVert i.val) tail
      (fun _ => rfl) U T hrob hUT hregions
      (by
        intro j
        simpa [tail] using hwfresh j) a b
  · exact ha
  · exact hb
  · exact hab
  · exact hpairs
  · exact hcross
  · exact hclose
  · exact hell
  · simpa using hparity
  · simpa using hFirstU
  · exact hFirstT
  · intro i
    simpa [tail] using hRestU i
  · intro i
    simpa [tail] using hRestT i
  · exact hlen

/-- Exact quotient/remainder allocation over the nonroot support of a
fresh-root closed walk. -/
theorem exists_exact_balanced_visit_weights_of_closed_walk_fresh_root
    {I : Type*} [Fintype I] (H : SimpleGraph I) {u : I}
    (w : H.Walk u u) {t z : ℕ} (ht : 2 ≤ t)
    (hsupp : w.support.toFinset.card = t)
    (hwfresh : ∀ j : Fin (w.length - 1),
      w.getVert (j.val + 1) ≠ u) :
    ∃ r : Fin (w.length - 1) → ℕ,
      (∑ j, r j) = z ∧
      (∀ j, r j ≤ z / (t - 1) + 1) ∧
      ∀ i, (∑ j : {j : Fin (w.length - 1) //
        w.getVert (j.val + 1) = i}, r j.1) ≤ z / (t - 1) + 1 := by
  classical
  let S : Finset I := w.support.toFinset.erase u
  have hu : u ∈ w.support.toFinset := by
    simpa using w.start_mem_support
  have hScard : S.card = t - 1 := by
    simp [S, Finset.card_erase_of_mem hu, hsupp]
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have : S.card = 0 := by simp [hzero]
    omega
  have hcover : ∀ i ∈ S, ∃ j : Fin (w.length - 1),
      w.getVert (j.val + 1) = i := by
    intro i hi
    have hiSupp : i ∈ w.support := by
      exact List.mem_toFinset.mp (Finset.mem_of_mem_erase hi)
    have hiu : i ≠ u := Finset.ne_of_mem_erase hi
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hiSupp
    have hnpos : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := by omega
      subst n
      exact hiu (by simpa using hn.symm)
    have hnlt : n < w.length := by
      by_contra hnnot
      have hneq : n = w.length := by omega
      subst n
      exact hiu (by simpa using hn.symm)
    let j : Fin (w.length - 1) := ⟨n - 1, by omega⟩
    refine ⟨j, ?_⟩
    simpa [j, show n - 1 + 1 = n by omega] using hn
  obtain ⟨r, hrsum, hrle, hrfiber⟩ :=
    exists_exact_balanced_visit_weights_of_covers_finset
      (w.length - 1) z (fun j : Fin (w.length - 1) =>
        w.getVert (j.val + 1)) S hSne hcover
  refine ⟨r, hrsum, ?_, ?_⟩
  · intro j
    simpa [hScard] using hrle j
  · intro i
    simpa [hScard] using hrfiber i

/-- A target length splits into a parity-correct root route of length five
or six and an even residual distributed over a doubled-tree tour. -/
theorem exists_short_root_route_decomposition {t k : ℕ}
    (ht : 2 ≤ t) (hfit : 6 * (t - 1) + 4 ≤ k) :
    ∃ ell z : ℕ, 5 ≤ ell ∧ ell ≤ 6 ∧
      ell + 2 * (z + (2 * (t - 1) - 1)) + 2 * (t - 1) = k := by
  by_cases hk : Even k
  · rcases hk with ⟨d, hd⟩
    refine ⟨6, d - (3 * (t - 1) + 2), by omega, by omega, ?_⟩
    omega
  · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
    rcases hkodd with ⟨d, hd⟩
    refine ⟨5, d - (3 * (t - 1) + 1), by omega, by omega, ?_⟩
    omega

/-- Source-scale component lift.  A connected auxiliary component on `t`
hubs already forces `C_k` with local budgets of order `t + k/t`, because
core and connector vertices are now counted separately. -/
theorem cycleGraph_isContained_of_connected_largeCrossMatching_separated_of_card_ge
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph I) (U T : I → Finset V)
    {t theta R k : ℕ} (hconn : H.Connected)
    (ht : 2 ≤ t) (htcard : t ≤ Fintype.card I)
    (hfit : 6 * (t - 1) + 4 ≤ k)
    (hmatchBudget : 2 * (2 * (t - 1)) < R)
    (hlarge : ∀ i j, H.Adj i j → HasCrossMatchingAtLeast G (U i) (U j) R)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hparity : ∀ i, HasCrossMatchingAtLeast G (U i) (U i) 3)
    (hU : ∀ i,
      k / (2 * (t - 1)) + 1 + 2 * (2 * (t - 1) - 1) ≤
        (U i).card)
    (hT : k / (2 * (t - 1)) + 1 + (2 * (t - 1) - 1) ≤
      theta) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  obtain ⟨u, w, hwlen, hwsupp, hwfresh⟩ :=
    Erdos551.SimpleGraph.Connected.exists_closed_walk_length_twice_sub_one_fresh_root_of_le_card
      H hconn (by omega) htcard
  obtain ⟨ell, z, hell, hellsix, hdecomp⟩ :=
    exists_short_root_route_decomposition ht hfit
  obtain ⟨r, hrsum, _hrle, hrfiber⟩ :=
    exists_exact_balanced_visit_weights_of_closed_walk_fresh_root
      H w ht hwsupp hwfresh (z := z)
  have hzhalf : z ≤ k / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  have hzquot : z / (t - 1) ≤ k / (2 * (t - 1)) := by
    calc
      z / (t - 1) ≤ (k / 2) / (t - 1) :=
        Nat.div_le_div_right hzhalf
      _ = k / (2 * (t - 1)) := by
        rw [Nat.div_div_eq_div_mul]
  have hwpos : 0 < w.length := by rw [hwlen]; omega
  have hden : 0 < 2 * (t - 1) := by omega
  have hquot3 : 3 ≤ k / (2 * (t - 1)) := by
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  apply cycleGraph_isContained_of_closed_largeCrossMatching_walk_fresh_root_separated
    G H U T w r
  · rw [hwlen]
    omega
  · exact hwfresh
  · rw [hwlen]
    exact hmatchBudget
  · exact hlarge
  · exact hrob
  · exact hUT
  · exact hregions
  · exact hell
  · exact hparity u
  · have hu := hU u
    omega
  · by_cases ht2 : t = 2
    · have hquot5 : 5 ≤ k / 2 := by
        apply (Nat.le_div_iff_mul_le (by omega)).2
        omega
      have hT2 := hT
      rw [ht2] at hT2
      have htheta7 : 7 ≤ theta := by
        apply le_trans (show 7 ≤ k / 2 + 1 + (2 * (2 - 1) - 1) by omega)
        simpa using hT2
      omega
    · have ht3 : 3 ≤ t := by omega
      have hconn3 : 3 ≤ 2 * (t - 1) - 1 := by omega
      have htheta7 : 7 ≤ theta := by
        apply le_trans
          (show 7 ≤ k / (2 * (t - 1)) + 1 +
            (2 * (t - 1) - 1) by omega)
        exact hT
      omega
  · intro i
    let J := {j : Fin (w.length - 1) // w.getVert (j.val + 1) = i}
    have hcardJ : Fintype.card J ≤ 2 * (t - 1) - 1 := by
      calc
        Fintype.card J ≤ Fintype.card (Fin (w.length - 1)) :=
          Fintype.card_subtype_le _
        _ = w.length - 1 := Fintype.card_fin _
        _ = 2 * (t - 1) - 1 := by rw [hwlen]
    have hsumr := hrfiber i
    change (∑ x : J, r x.1) ≤ z / (t - 1) + 1 at hsumr
    have hsum : (∑ x : J, (r x.1 + 2)) =
        (∑ x : J, r x.1) + 2 * Fintype.card J := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    rw [hsum]
    have hui := hU i
    omega
  · intro i
    let J := {j : Fin (w.length - 1) // w.getVert (j.val + 1) = i}
    have hcardJ : Fintype.card J ≤ 2 * (t - 1) - 1 := by
      calc
        Fintype.card J ≤ Fintype.card (Fin (w.length - 1)) :=
          Fintype.card_subtype_le _
        _ = w.length - 1 := Fintype.card_fin _
        _ = 2 * (t - 1) - 1 := by rw [hwlen]
    have hsumr := hrfiber i
    change (∑ x : J, r x.1) ≤ z / (t - 1) + 1 at hsumr
    have hsum : (∑ x : J, (r x.1 + 1)) =
        (∑ x : J, r x.1) + Fintype.card J := by
      simp [Finset.sum_add_distrib]
    rw [hsum]
    omega
  · have hroutes : (∑ j : Fin (w.length - 1), 2 * (r j + 1)) =
        2 * ((∑ j : Fin (w.length - 1), r j) + (w.length - 1)) := by
      calc
        (∑ j : Fin (w.length - 1), 2 * (r j + 1)) =
            ∑ j : Fin (w.length - 1), (2 * r j + 2) := by
          apply Finset.sum_congr rfl
          intro j _hj
          omega
        _ = (∑ j : Fin (w.length - 1), 2 * r j) +
            ∑ _j : Fin (w.length - 1), 2 := Finset.sum_add_distrib
        _ = 2 * ((∑ j : Fin (w.length - 1), r j) +
            (w.length - 1)) := by
          simp [Finset.mul_sum, Nat.mul_comm, Nat.mul_add]
    rw [hroutes, hrsum, hwlen]
    exact hdecomp

/-- Contrapositive form of the source-scale component lift. -/
theorem card_lt_of_cycleFree_connected_largeCrossMatching_separated
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph I) (U T : I → Finset V)
    {t theta R k : ℕ} (hconn : H.Connected)
    (ht : 2 ≤ t) (hfit : 6 * (t - 1) + 4 ≤ k)
    (hmatchBudget : 2 * (2 * (t - 1)) < R)
    (hlarge : ∀ i j, H.Adj i j → HasCrossMatchingAtLeast G (U i) (U j) R)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hparity : ∀ i, HasCrossMatchingAtLeast G (U i) (U i) 3)
    (hU : ∀ i,
      k / (2 * (t - 1)) + 1 + 2 * (2 * (t - 1) - 1) ≤
        (U i).card)
    (hT : k / (2 * (t - 1)) + 1 + (2 * (t - 1) - 1) ≤ theta)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    Fintype.card I < t := by
  by_contra hnot
  apply hcycle
  exact cycleGraph_isContained_of_connected_largeCrossMatching_separated_of_card_ge
    G H U T hconn ht (by omega) hfit hmatchBudget hlarge hrob hUT
      hregions hparity hU hT

/-- Component form allowing the cross-matchings to be selected from pruned
subsets of the robust routing cores. -/
theorem ncard_component_lt_of_cycleFree_largeCrossMatching_separated_pruned
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : I → Finset V) {t theta R k : ℕ}
    (hWU : ∀ i, W i ⊆ U i)
    (ht : 2 ≤ t) (hfit : 6 * (t - 1) + 4 ≤ k)
    (hmatchBudget : 2 * (2 * (t - 1)) < R)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) theta)
    (hUT : ∀ i, Disjoint (U i) (T i))
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (hparity : ∀ i, HasCrossMatchingAtLeast G (U i) (U i) 3)
    (hU : ∀ i,
      k / (2 * (t - 1)) + 1 + 2 * (2 * (t - 1) - 1) ≤
        (U i).card)
    (hT : k / (2 * (t - 1)) + 1 + (2 * (t - 1) - 1) ≤ theta)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (c : (LargeCrossMatchingGraph G W R).ConnectedComponent) :
    c.supp.ncard < t := by
  let K : SimpleGraph c := c.toSimpleGraph
  let Uc : c → Finset V := fun i => U i.1
  let Tc : c → Finset V := fun i => T i.1
  have hKlarge : ∀ i j : c, K.Adj i j →
      HasCrossMatchingAtLeast G (Uc i) (Uc j) R := by
    intro i j hij
    apply HasCrossMatchingAtLeast.mono_sets
      (hasCrossMatchingAtLeast_of_largeCrossMatchingGraph_adj
        (G := G) (U := W) (m := R) ?_)
      (hWU i.1) (hWU j.1)
    apply (c.toSimpleGraph_adj i.property j.property).mp
    simpa [K] using hij
  have hKregions : ∀ i j : c, i ≠ j →
      Disjoint (Uc i ∪ Tc i) (Uc j ∪ Tc j) := by
    intro i j hij
    apply hregions i.1 j.1
    intro h
    exact hij (Subtype.ext h)
  have hKcard : Fintype.card c < t := by
    apply card_lt_of_cycleFree_connected_largeCrossMatching_separated
      G K Uc Tc c.connected_toSimpleGraph ht hfit hmatchBudget hKlarge
        (fun i => hrob i.1) (fun i => hUT i.1) hKregions
        (fun i => hparity i.1) (fun i => hU i.1) hT hcycle
  have hcCard : Fintype.card c = c.supp.ncard := by
    calc
      Fintype.card c = Fintype.card c.supp := by
        apply Fintype.card_congr
        exact
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      _ = c.supp.ncard := Set.fintypeCard_eq_ncard c.supp
  simpa [hcCard] using hKcard

/-- Cardinal bound for a component union after one vertex is removed from
each exact core.  At `t=C+1` the component theorem gives at most `C`
labels, and `C * floor(k/C) ≤ k` supplies the strict `k-1` bound. -/
theorem card_component_biUnion_le_pred_of_exact_cores
    {V I : Type*} [Fintype V] [Fintype I]
    (H : SimpleGraph I) (W : I → Finset V) {C tau k : ℕ}
    (hC : 0 < C) (hcard : ∀ i, (W i).card ≤ tau - 1)
    (htau : tau = k / C)
    (hcomp : ∀ c : H.ConnectedComponent, c.supp.ncard < C + 1) :
    ∀ c : H.ConnectedComponent,
      (c.supp.toFinset.biUnion W).card ≤ k - 1 := by
  intro c
  have hpiece : ∀ i ∈ c.supp.toFinset, (W i).card ≤ tau - 1 := by
    intro i _hi
    exact hcard i
  have hunion : (c.supp.toFinset.biUnion W).card ≤
      c.supp.toFinset.card * (tau - 1) :=
    Finset.card_biUnion_le_card_mul _ _ _ hpiece
  have hsupp : c.supp.toFinset.card = c.supp.ncard := by
    simpa using (Set.ncard_eq_toFinset_card c.supp).symm
  have hlabels : c.supp.toFinset.card ≤ C := by
    rw [hsupp]
    have := hcomp c
    omega
  have hprod : C * tau ≤ k := by
    rw [htau]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k C
  calc
    (c.supp.toFinset.biUnion W).card ≤
        c.supp.toFinset.card * (tau - 1) := hunion
    _ ≤ C * (tau - 1) := Nat.mul_le_mul_right _ hlabels
    _ ≤ k - 1 := by
      by_cases hz : tau = 0
      · simp [hz]
      have htaupos : 0 < tau := Nat.pos_of_ne_zero hz
      have heq : C * tau = C * (tau - 1) + C := by
        conv_lhs => rw [show tau = (tau - 1) + 1 by omega]
        rw [Nat.mul_add]
        simp
      rw [heq] at hprod
      omega

/-- Halving both the numerator scale and denominator scale gives the exact
floor inequality needed by the source-scale route budget. -/
theorem two_mul_div_two_mul_le_div (k C : ℕ) (hC : 0 < C) :
    2 * (k / (2 * C)) ≤ k / C := by
  apply (Nat.le_div_iff_mul_le hC).2
  have hdiv := Nat.div_mul_le_self k (2 * C)
  calc
    2 * (k / (2 * C)) * C = (k / (2 * C)) * (2 * C) := by ring
    _ ≤ k := hdiv

/-- The two denominator scales in the eighth-root extraction differ by a
factor four, including their integer-floor losses. -/
theorem four_mul_div_eight_mul_le_div_two_mul_main
    (k c : ℕ) (hc : 0 < c) :
    4 * (k / (8 * c)) ≤ k / (2 * c) := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * c)).2
  have hdiv := Nat.div_mul_le_self k (8 * c)
  calc
    4 * (k / (8 * c)) * (2 * c) =
        (k / (8 * c)) * (8 * c) := by ring
    _ ≤ k := hdiv

/-- Pure arithmetic package for choosing `t=C+1` at an exact core scale
`tau=floor(k/C)`. -/
theorem exact_core_source_scale_component_numerics
    {C tau Theta k : ℕ} (hC : 2 ≤ C) (htau : tau = k / C)
    (hlarge : 8 * C ≤ tau) (hTheta : 4 * tau ≤ Theta) :
    2 ≤ C + 1 ∧
    6 * ((C + 1) - 1) + 4 ≤ k ∧
    2 * (2 * ((C + 1) - 1)) < 4 * C + 1 ∧
    k / (2 * ((C + 1) - 1)) + 1 +
        2 * (2 * ((C + 1) - 1) - 1) ≤ tau ∧
    k / (2 * ((C + 1) - 1)) + 1 +
        (2 * ((C + 1) - 1) - 1) ≤ Theta - 2 * tau := by
  have hCpos : 0 < C := by omega
  have hprod : C * tau ≤ k := by
    rw [htau]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k C
  have hhalf : 2 * (k / (2 * C)) ≤ tau := by
    rw [htau]
    exact two_mul_div_two_mul_le_div k C hCpos
  have hCC : 8 * C * C ≤ k := by
    calc
      8 * C * C = C * (8 * C) := by ring
      _ ≤ C * tau := Nat.mul_le_mul_left C hlarge
      _ ≤ k := hprod
  have hfit : 6 * C + 4 ≤ k := by
    have hpoly : 6 * C + 4 ≤ 8 * C * C := by nlinarith
    exact hpoly.trans hCC
  have hUcost : k / (2 * C) + 1 + 2 * (2 * C - 1) ≤ tau := by
    omega
  have hTcost : k / (2 * C) + 1 + (2 * C - 1) ≤
      Theta - 2 * tau := by
    omega
  simpa only [Nat.add_sub_cancel] using
    (show 2 ≤ C + 1 ∧ 6 * C + 4 ≤ k ∧
      2 * (2 * C) < 4 * C + 1 ∧
      k / (2 * C) + 1 + 2 * (2 * C - 1) ≤ tau ∧
      k / (2 * C) + 1 + (2 * C - 1) ≤ Theta - 2 * tau from
        ⟨by omega, hfit, by omega, hUcost, hTcost⟩)

/-- For each fixed divisor, the eighth-root core eventually dominates the
linear `C` overhead of the separated component lift. -/
theorem eventually_divisor_eighthRoot_component_numerics
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let a := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let R := 4 * B
      let C := 8 * a * R ^ 5
      let Theta := k / (2 * a * R ^ 5)
      let tau := k / C
      2 ≤ C ∧ 8 * C ≤ tau ∧ 4 * tau ≤ Theta := by
  let R : ℕ := 4 * B
  let Q : ℕ := 2048 * R ^ 10
  have hRpos : 0 < R := by dsimp [R]; omega
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  filter_upwards [htriple.eventually (eventually_ge_atTop Q)] with k hkQ
  let s : ℕ := Nat.sqrt k
  let q : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt q
  let a : ℕ := r + 1
  let C : ℕ := 8 * a * R ^ 5
  have hrQ : Q ≤ r := by simpa [r, q, s] using hkQ
  have hrpos : 0 < r := hQpos.trans_le hrQ
  have hr2q : r ^ 2 ≤ q := by
    dsimp [r]
    exact Nat.sqrt_le' q
  have hq2s : q ^ 2 ≤ s := by
    dsimp [q]
    exact Nat.sqrt_le' s
  have hs2k : s ^ 2 ≤ k := by
    dsimp [s]
    exact Nat.sqrt_le' k
  have hr4s : r ^ 4 ≤ s := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hr2q 2
      _ ≤ s := hq2s
  have hr8k : r ^ 8 ≤ k := by
    calc
      r ^ 8 = (r ^ 4) ^ 2 := by ring
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hr4s 2
      _ ≤ k := hs2k
  have ha2r : a ≤ 2 * r := by dsimp [a]; omega
  have hCle : C ≤ 16 * r * R ^ 5 := by
    calc
      C = 8 * a * R ^ 5 := rfl
      _ ≤ 8 * (2 * r) * R ^ 5 := by gcongr
      _ = 16 * r * R ^ 5 := by ring
  have hrle6 : r ≤ r ^ 6 :=
    Nat.le_self_pow (by norm_num : (6 : ℕ) ≠ 0) r
  have hcoef : 2048 * R ^ 10 ≤ r ^ 6 := by
    exact hrQ.trans hrle6
  have hCbig : 8 * C ^ 2 ≤ k := by
    calc
      8 * C ^ 2 ≤ 8 * (16 * r * R ^ 5) ^ 2 := by gcongr
      _ = r ^ 2 * (2048 * R ^ 10) := by ring
      _ ≤ r ^ 2 * r ^ 6 := Nat.mul_le_mul_left (r ^ 2) hcoef
      _ = r ^ 8 := by ring
      _ ≤ k := hr8k
  have hCpos : 0 < C := by dsimp [C, a]; positivity
  have h8C : 8 * C ≤ k / C := by
    exact (Nat.le_div_iff_mul_le hCpos).2 (by
      simpa [pow_two, Nat.mul_assoc] using hCbig)
  have hfour : 4 * (k / C) ≤ k / (2 * a * R ^ 5) := by
    have hc : 0 < a * R ^ 5 := by positivity
    simpa [C, Nat.mul_assoc] using
      four_mul_div_eight_mul_le_div_two_mul_main k (a * R ^ 5) hc
  have hCtwo : 2 ≤ C := by
    have hfactorPos : 0 < a * R ^ 5 := by positivity
    have hfactor : 1 ≤ a * R ^ 5 := by omega
    dsimp [C]
    nlinarith
  exact ⟨hCtwo, h8C, by simpa [C, a, r, q, s, R] using hfour⟩

/-! ## Thin eighth-root alternating regions -/

/-- The eighth-root DRC core can be retained while its routing target is
sampled down to order `k / (a * R^5)^2`.  Thus the displayed region has
order `2 * tau + o(tau)`, rather than the order-`k` region supplied by the
unsampled decomposition.  This is the sharp form needed for the final
component count: the leading contribution is exactly the two alternating
core sides. -/
theorem exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree_rho
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B k n : ℕ} (rho : ℕ) (hB : 16 ≤ B) (hk : 4 * B ≤ k) (hn : 2 ≤ n)
    (hfree : G.IndepSetFree n)
    (hroom : 3 * Nat.log 2 (Fintype.card V) + 1 ≤ k)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (hscale : (4 * B) ^ 36 ≤
      4 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1))
    (hpositive : 8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) *
      (4 * B) ^ 5 ≤ k)
    (hreserve : 2 *
      (k / (8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5)) ≤
      k / (2 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5))
    (hsample :
      let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let R : ℕ := 4 * B
      let c : ℕ := a * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) / (1 / 2 : ℝ≥0) ^ rho) +
        ((k : ℝ≥0) * sigma) / K) < 1) :
    let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
    let R : ℕ := 4 * B
    let c : ℕ := a * R ^ 5
    let Θ : ℕ := k / (2 * c)
    let τ : ℕ := k / (8 * c)
    let K : ℕ := k / (4 * c ^ 2) + 1
    ∃ F : Finset (Finset V),
      (∀ H ∈ F, IsCompactAlternatingHub G (rho + 1) τ (2 * τ + K) H) ∧
      DisjointFinsetFamily F ∧
      F.biUnion id ⊆ Finset.univ ∧
      ((Finset.univ : Finset V) \ F.biUnion id).card <
        16 * ((n - 1) * (((k - 1) / B - 1) + 1)) := by
  let d : ℕ := (k - 1) / B - 1
  let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
  let R : ℕ := 4 * B
  let c : ℕ := a * R ^ 5
  let Θ : ℕ := k / (2 * c)
  let τ : ℕ := k / (8 * c)
  let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
  let K : ℕ := k / (4 * c ^ 2) + 1
  have hBpos : 0 < B := by omega
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hkpos : 0 < k := by omega
  have hapos : 0 < a := by dsimp [a]; positivity
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by
    dsimp [d]
    have hq3 : 3 ≤ (k - 1) / B := by
      apply (Nat.le_div_iff_mul_le hBpos).2
      omega
    omega
  have hτpos : 0 < τ := by
    dsimp [τ, c]
    exact Nat.div_pos
      (by simpa [a, R, Nat.mul_assoc] using hpositive) (by positivity)
  have hKpos : 0 < K := by
    simpa [K] using Nat.zero_lt_succ (k / (4 * c ^ 2))
  have hsigma : sigma ≤ 1 := by
    have hden : 0 < 16 * c ^ 2 := by positivity
    dsimp [sigma]
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 16 * c ^ 2 by omega)
    · exact_mod_cast hden
  apply exists_disjoint_compactAlternatingHub_family
    G hτpos
      (by simpa [τ, Θ, c, a, R, Nat.mul_assoc] using hreserve)
      hKpos sigma hsigma
    (m := 16 * ((n - 1) * (d + 1)))
    (Dmax := k) (Θ := Θ) (r := rho)
  · intro S hSsize
    apply exists_localRobustHub_in_finset_of_large_indepSetFree_cycleFree
      G hn hd hfree hSsize (by omega) hroom hcycle (by omega : 0 < 20)
        hτpos (by positivity : (0 : ℝ) < 1 / a)
    · intro δ m hδ hδm _hmk
      have hkδ : k ≤ R * δ := by
        simpa [R, d] using
          (k_le_four_mul_divisor_mul_of_pred_div_sub_one_le_two_mul
            hBpos hk hδ)
      simpa [Θ, c, Nat.mul_assoc] using
        (div_two_mul_a_mul_pow5_le_inv_a_mul_density_four_mul_card_of_ratio
          hRpos hapos hkpos hkδ hδm)
    · intro δ m hδ hδm _hmk
      have hkδ : k ≤ R * δ := by
        simpa [R, d] using
          (k_le_four_mul_divisor_mul_of_pred_div_sub_one_le_two_mul
            hBpos hk hδ)
      simpa [τ, c, Nat.mul_assoc] using
        (div_eight_mul_a_mul_pow5_sq_le_density_twenty_mul_card_sq_div_two_of_ratio
          hRpos hapos hkpos hkδ hδm (by simpa [R, a] using hscale))
    · intro m hm1 hmk
      simpa [a] using
        (two_mul_inv_succ_sqrt_sqrt_sqrt_pow_twenty_lt_inv_sq
          (by omega) hm1 hmk)
  · simpa [τ, K, Θ, sigma, c, a, R, Nat.mul_assoc] using hsample

/-- Fixed-six specialization of the arbitrary-robustness thin eighth-root
decomposition. -/
theorem exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B k n : ℕ} (hB : 16 ≤ B) (hk : 4 * B ≤ k) (hn : 2 ≤ n)
    (hfree : G.IndepSetFree n)
    (hroom : 3 * Nat.log 2 (Fintype.card V) + 1 ≤ k)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (hscale : (4 * B) ^ 36 ≤
      4 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1))
    (hpositive : 8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) *
      (4 * B) ^ 5 ≤ k)
    (hreserve : 2 *
      (k / (8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5)) ≤
      k / (2 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5))
    (hsample :
      let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let R : ℕ := 4 * B
      let c : ℕ := a * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) / (1 / 2 : ℝ≥0) ^ 6) +
        ((k : ℝ≥0) * sigma) / K) < 1) :
    let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
    let R : ℕ := 4 * B
    let c : ℕ := a * R ^ 5
    let τ : ℕ := k / (8 * c)
    let K : ℕ := k / (4 * c ^ 2) + 1
    ∃ F : Finset (Finset V),
      (∀ H ∈ F, IsCompactAlternatingHub G 7 τ (2 * τ + K) H) ∧
      DisjointFinsetFamily F ∧
      F.biUnion id ⊆ Finset.univ ∧
      ((Finset.univ : Finset V) \ F.biUnion id).card <
        16 * ((n - 1) * (((k - 1) / B - 1) + 1)) := by
  simpa using
    (exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree_rho
      G 6 hB hk hn hfree hroom hcycle hscale hpositive hreserve hsample)

/-- A degree-sixteen polynomial is eventually dominated by the exponential
decay needed for eighth-root compact-target sampling. -/
theorem eventually_sixteenth_mul_exp_neg_lt_half_of_denominator
    (D : ℕ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop,
      (17179869184 * Real.exp (1 / 32) : ℝ) *
          (x ^ 16 * Real.exp (-(1 / (D : ℝ)) * x)) < 1 / 2 := by
  have ht0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (16 : ℝ) (1 / (D : ℝ)) (by positivity)
  have ht : Tendsto
      (fun x : ℝ ↦ x ^ 16 * Real.exp (-(1 / (D : ℝ)) * x))
      atTop (𝓝 0) := by
    apply ht0.congr'
    filter_upwards with x
    have hx : x ^ (16 : ℝ) = x ^ (16 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hx]
  have ht' : Tendsto
      (fun x : ℝ ↦ (17179869184 * Real.exp (1 / 32) : ℝ) *
        (x ^ 16 * Real.exp (-(1 / (D : ℝ)) * x)))
      atTop (𝓝 0) := by
    convert ht.const_mul (17179869184 * Real.exp (1 / 32) : ℝ) using 1 <;>
      simp
  exact ht'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

/-- Pointwise first-moment estimate for the sampled eighth-root core.  The
tail term is bounded by a degree-sixteen polynomial times exponential decay
in `floor(k^(1/8))`; the size term is strictly below one half by the defining
quotient in `K`. -/
theorem divisor_eighthRoot_sampling_inequality_of_sixteenth_decay
    {R k rho : ℕ} (hR : 0 < R)
    (hr : 1 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt k)))
    (hreserve :
      let a := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let c := a * R ^ 5
      2 * (k / (8 * c)) ≤ k / (2 * c))
    (hrhoBudget :
      let r := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let c := (r + 1) * R ^ 5
      let Θ := k / (2 * c)
      let τ := k / (8 * c)
      32 * c ^ 2 * (2048 * R ^ 15 * rho + r) ≤
        (2048 * R ^ 15) * (Θ - 2 * τ))
    (hdecay :
      (268435456 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (2048 * R ^ 15 : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) < 1 / 2) :
    let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
    let c : ℕ := a * R ^ 5
    let Θ : ℕ := k / (2 * c)
    let τ : ℕ := k / (8 * c)
    let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
    let K : ℕ := k / (4 * c ^ 2) + 1
    (((τ * τ : ℕ) : ℝ≥0) *
        ((1 - sigma / 2) ^ (Θ - 2 * τ) / (1 / 2 : ℝ≥0) ^ rho) +
      ((k : ℝ≥0) * sigma) / K) < 1 := by
  let s : ℕ := Nat.sqrt k
  let q : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt q
  let a : ℕ := r + 1
  let c : ℕ := a * R ^ 5
  let Θ : ℕ := k / (2 * c)
  let τ : ℕ := k / (8 * c)
  let theta : ℕ := Θ - 2 * τ
  let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
  let K : ℕ := k / (4 * c ^ 2) + 1
  have hrpos : 0 < r := by
    simpa [r, q, s] using (Nat.zero_lt_of_lt hr)
  have hapos : 0 < a := by dsimp [a]; omega
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hRone : 1 ≤ R := hR
  have hcone : 1 ≤ c := hcpos
  have hreserve' : 2 * τ ≤ Θ := by
    simpa [τ, Θ, c, a, r, q, s] using hreserve
  have hsplit : theta + 2 * τ = Θ := by
    dsimp [theta]
    exact Nat.sub_add_cancel hreserve'
  have hquot : k < 2 * c * (Θ + 1) := by
    simpa [Nat.mul_assoc] using
      (Nat.lt_mul_div_succ k (by positivity : 0 < 2 * c))
  have htaufloor : 8 * c * τ ≤ k := by
    have h := Nat.div_mul_le_self k (8 * c)
    simpa [τ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hdecomp : 4 * c * (Θ + 1) =
      4 * c * (theta + 1) + 8 * c * τ := by
    rw [← hsplit]
    ring
  have htwok : 2 * k < 4 * c * (Θ + 1) := by
    have hmul := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hquot
    calc
      2 * k < 2 * (2 * c * (Θ + 1)) := hmul
      _ = 4 * c * (Θ + 1) := by ring
  rw [hdecomp] at htwok
  have hkTheta : k < 4 * c * (theta + 1) := by omega
  have hrSq : r ^ 2 ≤ q := by
    dsimp [r]
    exact Nat.sqrt_le' q
  have hqLt : q < (r + 1) ^ 2 := by
    dsimp [r]
    exact Nat.lt_succ_sqrt' q
  have hqLe : q ≤ 4 * r ^ 2 := by
    have hrSum : r + 1 ≤ 2 * r := by omega
    calc
      q ≤ (r + 1) ^ 2 := hqLt.le
      _ ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left hrSum 2
      _ = 4 * r ^ 2 := by ring
  have hsLt : s < (q + 1) ^ 2 := by
    dsimp [q]
    exact Nat.lt_succ_sqrt' s
  have hsLe : s ≤ 64 * r ^ 4 := by
    have hqSum : q + 1 ≤ 2 * q := by
      have hqpos : 0 < q := hrpos.trans_le (Nat.sqrt_le_self q)
      omega
    calc
      s ≤ (q + 1) ^ 2 := hsLt.le
      _ ≤ (2 * q) ^ 2 := Nat.pow_le_pow_left hqSum 2
      _ = 4 * q ^ 2 := by ring
      _ ≤ 4 * (4 * r ^ 2) ^ 2 := by gcongr
      _ = 64 * r ^ 4 := by ring
  have hkLt : k < (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.lt_succ_sqrt' k
  have hkLe : k ≤ 16384 * r ^ 8 := by
    have hsSum : s + 1 ≤ 2 * s := by
      have hspos : 0 < s := by
        exact hrpos.trans_le (Nat.sqrt_le_self q) |>.trans_le
          (Nat.sqrt_le_self s)
      omega
    calc
      k ≤ (s + 1) ^ 2 := hkLt.le
      _ ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left hsSum 2
      _ = 4 * s ^ 2 := by ring
      _ ≤ 4 * (64 * r ^ 4) ^ 2 := by gcongr
      _ = 16384 * r ^ 8 := by ring
  have hr4k : r ^ 4 ≤ k := by
    have hr4s : r ^ 4 ≤ s := by
      calc
        r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hrSq 2
        _ ≤ s := Nat.sqrt_le' s
    calc
      r ^ 4 ≤ s := hr4s
      _ ≤ k := Nat.sqrt_le_self k
  have hcLe : c ≤ 2 * r * R ^ 5 := by
    have haLe : a ≤ 2 * r := by dsimp [a]; omega
    dsimp [c]
    gcongr
  have hcCube : c ^ 3 ≤ 8 * r ^ 3 * R ^ 15 := by
    calc
      c ^ 3 ≤ (2 * r * R ^ 5) ^ 3 := Nat.pow_le_pow_left hcLe 3
      _ = 8 * r ^ 3 * R ^ 15 := by ring
  have hrateNat : 128 * r * c ^ 3 ≤ 1024 * k * R ^ 15 := by
    calc
      128 * r * c ^ 3 ≤ 128 * r * (8 * r ^ 3 * R ^ 15) := by gcongr
      _ = 1024 * r ^ 4 * R ^ 15 := by ring
      _ ≤ 1024 * k * R ^ 15 := by gcongr
  have hsigmaLe : sigma ≤ 1 := by
    have hden : 0 < 16 * c ^ 2 := by positivity
    dsimp [sigma]
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 16 * c ^ 2 by omega)
    · exact_mod_cast hden
  have hsigma2 : sigma / 2 ≤ 1 :=
    (div_le_self (show 0 ≤ sigma from zero_le)
      (by norm_num : (1 : ℝ≥0) ≤ 2)).trans hsigmaLe
  have hbaseCoe :
      ((1 - sigma / 2 : ℝ≥0) : ℝ) =
        1 - 1 / (32 * (c : ℝ) ^ 2) := by
    rw [NNReal.coe_sub hsigma2]
    simp [sigma]
    field_simp
    ring
  have hbaseExp :
      ((1 - sigma / 2 : ℝ≥0) : ℝ) ≤
        Real.exp (-(1 / (32 * (c : ℝ) ^ 2))) := by
    rw [hbaseCoe]
    exact Real.one_sub_le_exp_neg _
  have hpowExp :
      (((1 - sigma / 2) ^ theta : ℝ≥0) : ℝ) ≤
        Real.exp (-((theta : ℝ) / (32 * (c : ℝ) ^ 2))) := by
    rw [NNReal.coe_pow]
    calc
      ((1 - sigma / 2 : ℝ≥0) : ℝ) ^ theta ≤
          Real.exp (-(1 / (32 * (c : ℝ) ^ 2))) ^ theta :=
        pow_le_pow_left₀ (by positivity) hbaseExp theta
      _ = Real.exp (-((theta : ℝ) / (32 * (c : ℝ) ^ 2))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
  have hrate :
      (r : ℝ) / (1024 * (R : ℝ) ^ 15) ≤
        (k : ℝ) / (128 * (c : ℝ) ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrateNat)
  have hkThetaR : (k : ℝ) < 4 * c * (theta + 1) := by
    exact_mod_cast hkTheta
  have hexponent0 :
      -((theta : ℝ) / (32 * (c : ℝ) ^ 2)) ≤
        1 / (32 * (c : ℝ) ^ 2) -
          (k : ℝ) / (128 * (c : ℝ) ^ 3) := by
    have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
    field_simp
    nlinarith [hkThetaR]
  have hsmallCorrection :
      1 / (32 * (c : ℝ) ^ 2) ≤ 1 / 32 := by
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hcone
    apply (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
      (by positivity : (0 : ℝ) < 32 * c ^ 2)
      (by norm_num : (0 : ℝ) < 32)).2
    nlinarith [sq_nonneg ((c : ℝ) - 1)]
  have hexponent :
      -((theta : ℝ) / (32 * (c : ℝ) ^ 2)) ≤
        1 / 32 - (1 / (1024 * (R : ℝ) ^ 15)) * r := by
    have hrw : (1 / (1024 * (R : ℝ) ^ 15)) * r =
        (r : ℝ) / (1024 * (R : ℝ) ^ 15) := by ring
    rw [hrw]
    linarith
  have htailExp :
      (((1 - sigma / 2) ^ theta : ℝ≥0) : ℝ) ≤
        Real.exp (1 / 32) *
          Real.exp (-(1 / (1024 * (R : ℝ) ^ 15)) * r) := by
    calc
      _ ≤ Real.exp (-((theta : ℝ) / (32 * (c : ℝ) ^ 2))) := hpowExp
      _ ≤ Real.exp (1 / 32 - (1 / (1024 * (R : ℝ) ^ 15)) * r) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (1 / 32) *
          Real.exp (-(1 / (1024 * (R : ℝ) ^ 15)) * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hrhoExponent :
      (rho : ℝ) - (theta : ℝ) / (32 * (c : ℝ) ^ 2) ≤
        -(1 / (2048 * (R : ℝ) ^ 15)) * r := by
    have hbudgetNat : 32 * c ^ 2 * (2048 * R ^ 15 * rho + r) ≤
        (2048 * R ^ 15) * theta := by
      simpa [r, q, s, c, a, theta, Θ, τ] using hrhoBudget
    have hbudgetReal :
        (32 : ℝ) * c ^ 2 * ((2048 : ℝ) * R ^ 15 * rho + r) ≤
          ((2048 : ℝ) * R ^ 15) * theta := by
      exact_mod_cast hbudgetNat
    have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
    have hRR : (0 : ℝ) < R := by exact_mod_cast hR
    field_simp
    nlinarith
  have htwoPow : (2 : ℝ) ^ rho ≤ Real.exp (rho : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    calc
      (2 : ℝ) ^ rho ≤ (Real.exp 1) ^ rho :=
        pow_le_pow_left₀ (by norm_num) htwo rho
      _ = Real.exp (rho : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
  have htailExpRho :
      (((1 - sigma / 2) ^ theta : ℝ≥0) : ℝ) * (2 : ℝ) ^ rho ≤
        Real.exp (1 / 32) *
          Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) := by
    calc
      (((1 - sigma / 2) ^ theta : ℝ≥0) : ℝ) * (2 : ℝ) ^ rho ≤
          Real.exp (-((theta : ℝ) / (32 * (c : ℝ) ^ 2))) *
            Real.exp (rho : ℝ) :=
        mul_le_mul hpowExp htwoPow (by positivity) (by positivity)
      _ = Real.exp ((rho : ℝ) -
          (theta : ℝ) / (32 * (c : ℝ) ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) :=
        Real.exp_le_exp.mpr hrhoExponent
      _ ≤ Real.exp (1 / 32) *
          Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) := by
        have hone : (1 : ℝ) ≤ Real.exp (1 / 32) :=
          Real.one_le_exp (by norm_num)
        calc
          Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) =
              1 * Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) := by ring
          _ ≤ Real.exp (1 / 32) *
              Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) :=
            mul_le_mul_of_nonneg_right hone
              (Real.exp_pos (-(1 / (2048 * (R : ℝ) ^ 15)) * r)).le
  have hτsq : (τ : ℝ) ^ 2 ≤ 268435456 * (r : ℝ) ^ 16 := by
    have hτk : τ ≤ k := Nat.div_le_self _ _
    have hτbound : τ ≤ 16384 * r ^ 8 := hτk.trans hkLe
    exact_mod_cast (show τ ^ 2 ≤ 268435456 * r ^ 16 by
      calc
        τ ^ 2 ≤ (16384 * r ^ 8) ^ 2 := Nat.pow_le_pow_left hτbound 2
        _ = 268435456 * r ^ 16 := by ring)
  have htail :
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ theta / (1 / 2 : ℝ≥0) ^ rho) : ℝ≥0) <
        1 / 2 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num only [one_div, inv_inv]
    ring_nf
    have htailExp' :
        (((1 - sigma * (1 / 2) : ℝ≥0) : ℝ) ^ theta) *
            (2 : ℝ) ^ rho ≤
          Real.exp (1 / 32) *
            Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r) := by
      simpa [div_eq_mul_inv] using htailExpRho
    calc
      (τ : ℝ) ^ 2 *
          (((1 - sigma * (1 / 2) : ℝ≥0) : ℝ) ^ theta) * (2 : ℝ) ^ rho ≤
        (268435456 * (r : ℝ) ^ 16) *
          (Real.exp (1 / 32) *
            Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r)) := by
          calc
            (τ : ℝ) ^ 2 *
                (((1 - sigma * (1 / 2) : ℝ≥0) : ℝ) ^ theta) *
                (2 : ℝ) ^ rho =
              (τ : ℝ) ^ 2 *
                ((((1 - sigma * (1 / 2) : ℝ≥0) : ℝ) ^ theta) *
                  (2 : ℝ) ^ rho) := by ring
            _ ≤ (268435456 * (r : ℝ) ^ 16) *
                (Real.exp (1 / 32) *
                  Real.exp (-(1 / (2048 * (R : ℝ) ^ 15)) * r)) :=
              mul_le_mul hτsq htailExp' (by positivity) (by positivity)
      _ = (268435456 * Real.exp (1 / 32) : ℝ) *
          ((r : ℝ) ^ 16 *
            Real.exp (-(1 / (2048 * R ^ 15 : ℝ)) * r)) := by
          push_cast
          ring
      _ < 1 / 2 := by simpa [r, q, s] using hdecay
  have hsize : (((k : ℝ≥0) * sigma / K : ℝ≥0)) < 1 / 2 := by
    rw [← NNReal.coe_lt_coe]
    dsimp [sigma, K]
    push_cast
    have hdivNat : k < 4 * c ^ 2 * (k / (4 * c ^ 2) + 1) :=
      Nat.lt_mul_div_succ k (by positivity)
    have hdivR : (k : ℝ) <
        4 * (c : ℝ) ^ 2 * (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1) := by
      exact_mod_cast hdivNat
    have hdenpos : (0 : ℝ) <
        16 * (c : ℝ) ^ 2 * (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1) := by
      positivity
    calc
      (k : ℝ) * (1 / (16 * (c : ℝ) ^ 2)) /
          (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1) =
          (k : ℝ) / (16 * (c : ℝ) ^ 2 *
            (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1)) := by field_simp
      _ < 1 / 4 := by
        rw [div_lt_iff₀ hdenpos]
        calc
          (k : ℝ) < 4 * (c : ℝ) ^ 2 *
              (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1) := hdivR
          _ = (1 / 4) * (16 * (c : ℝ) ^ 2 *
              (((k / (4 * c ^ 2) : ℕ) : ℝ) + 1)) := by ring
      _ < 1 / 2 := by norm_num
  change
    (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ theta / (1 / 2 : ℝ≥0) ^ rho) +
        ((k : ℝ≥0) * sigma) / K < 1)
  exact lt_of_lt_of_le (add_lt_add htail hsize) (by norm_num)

/-- The eighth-root compact-target first-moment inequality holds eventually
for every fixed divisor. -/
theorem eventually_divisor_eighthRoot_sampling_inequality
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let R : ℕ := 4 * B
      let c : ℕ := a * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) / (1 / 2 : ℝ≥0) ^ 6) +
        ((k : ℝ≥0) * sigma) / K) < 1 := by
  let R : ℕ := 4 * B
  let D : ℕ := 2048 * R ^ 15
  have hR : 0 < R := by dsimp [R]; omega
  have hD : 0 < D := by dsimp [D]; positivity
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  have htripleReal : Tendsto
      (fun k : ℕ => (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htriple
  have hdecayBig : ∀ᶠ k : ℕ in atTop,
      (17179869184 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) < 1 / 2 :=
    htripleReal.eventually
      (eventually_sixteenth_mul_exp_neg_lt_half_of_denominator D hD)
  have hdecay : ∀ᶠ k : ℕ in atTop,
      (268435456 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) < 1 / 2 := by
    filter_upwards [hdecayBig] with k hk
    calc
      (268435456 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) ≤
        (17179869184 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) := by
            gcongr
            norm_num
      _ < 1 / 2 := hk
  filter_upwards [htriple.eventually (eventually_ge_atTop (6 * D + 1)),
    eventually_divisor_eighthRoot_alternatingHub_numerics B hB,
    hdecay] with k hr hnum hkdecay
  apply divisor_eighthRoot_sampling_inequality_of_sixteenth_decay hR (by omega)
  · simpa [R, Nat.mul_assoc] using hnum.2.2.2
  · let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
    let c : ℕ := (r + 1) * R ^ 5
    let Θ : ℕ := k / (2 * c)
    let τ : ℕ := k / (8 * c)
    let theta : ℕ := Θ - 2 * τ
    have hrbig : 6 * D + 1 ≤ r := by simpa [r] using hr
    have hrpos : 0 < r := by omega
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hreserve : 2 * τ ≤ Θ := by
      simpa [τ, Θ, c, r, R, Nat.mul_assoc] using hnum.2.2.2
    have hsplit : theta + 2 * τ = Θ := by
      dsimp [theta]
      exact Nat.sub_add_cancel hreserve
    have hquot : k < 2 * c * (Θ + 1) := by
      simpa [Nat.mul_assoc] using
        (Nat.lt_mul_div_succ k (by positivity : 0 < 2 * c))
    have htaufloor : 8 * c * τ ≤ k := by
      have h := Nat.div_mul_le_self k (8 * c)
      simpa [τ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hdecomp : 4 * c * (Θ + 1) =
        4 * c * (theta + 1) + 8 * c * τ := by
      rw [← hsplit]
      ring
    have hkTheta : k < 4 * c * (theta + 1) := by
      have htwok : 2 * k < 4 * c * (Θ + 1) := by
        have hm := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hquot
        calc
          2 * k < 2 * (2 * c * (Θ + 1)) := hm
          _ = 4 * c * (Θ + 1) := by ring
      rw [hdecomp] at htwok
      omega
    have h8c : 8 * c ≤ k := by
      simpa [c, r, R, Nat.mul_assoc] using hnum.2.2.1
    have hthetaPos : 0 < theta := by
      by_contra hz
      have hzero : theta = 0 := by omega
      rw [hzero] at hkTheta
      omega
    have hkThetaWeak : k ≤ 8 * c * theta := by
      calc
        k ≤ 4 * c * (theta + 1) := hkTheta.le
        _ ≤ 8 * c * theta := by
          have htheta : theta + 1 ≤ 2 * theta := by omega
          calc
            4 * c * (theta + 1) ≤ 4 * c * (2 * theta) := by gcongr
            _ = 8 * c * theta := by ring
    let s : ℕ := Nat.sqrt k
    let q : ℕ := Nat.sqrt s
    have hr2q : r ^ 2 ≤ q := by
      dsimp [r, q]
      exact Nat.sqrt_le' q
    have hq2s : q ^ 2 ≤ s := by
      dsimp [q]
      exact Nat.sqrt_le' s
    have hs2k : s ^ 2 ≤ k := by
      dsimp [s]
      exact Nat.sqrt_le' k
    have hr8k : r ^ 8 ≤ k := by
      calc
        r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left
          (Nat.pow_le_pow_left hr2q 2) 2
        _ ≤ s ^ 2 := Nat.pow_le_pow_left hq2s 2
        _ ≤ k := hs2k
    have hcLe : c ≤ 2 * r * R ^ 5 := by
      dsimp [c]
      gcongr
      omega
    have htailScale : 6 * D + r ≤ r ^ 5 := by
      have h6D : 6 * D ≤ r - 1 := by omega
      have htwoR : 2 * r ≤ r ^ 2 := by nlinarith
      have hr2r5 : r ^ 2 ≤ r ^ 5 := by
        calc
          r ^ 2 ≤ r ^ 2 * r ^ 3 :=
            Nat.le_mul_of_pos_right _ (by positivity : 0 < r ^ 3)
          _ = r ^ 5 := by ring
      omega
    have hscaled : 8 * c *
        (32 * c ^ 2 * (D * 6 + r)) ≤ D * k := by
      calc
        8 * c * (32 * c ^ 2 * (D * 6 + r)) =
            256 * c ^ 3 * (D * 6 + r) := by ring
        _ ≤ 256 * (2 * r * R ^ 5) ^ 3 * (D * 6 + r) := by gcongr
        _ = D * (r ^ 3 * (D * 6 + r)) := by
          dsimp [D]
          ring
        _ ≤ D * r ^ 8 := by
          gcongr
          calc
            r ^ 3 * (D * 6 + r) ≤ r ^ 3 * r ^ 5 :=
              Nat.mul_le_mul_left _ (by
                simpa [Nat.mul_comm] using htailScale)
            _ = r ^ 8 := by ring
        _ ≤ D * k := Nat.mul_le_mul_left D hr8k
    have htargetScaled : 8 * c *
        (32 * c ^ 2 * (D * 6 + r)) ≤
          8 * c * (D * theta) := by
      calc
        _ ≤ D * k := hscaled
        _ ≤ D * (8 * c * theta) := Nat.mul_le_mul_left D hkThetaWeak
        _ = 8 * c * (D * theta) := by ring
    have htarget : 32 * c ^ 2 * (D * 6 + r) ≤ D * theta := by
      exact Nat.le_of_mul_le_mul_left htargetScaled (by positivity)
    simpa [D, R, r, c, Θ, τ, theta] using htarget
  · dsimp [D, R] at hkdecay ⊢
    convert hkdecay using 1 <;> norm_num <;> ring

/-- Generic arithmetic budget for a growing compact-target exponent.  At
the eighth-root scale it is enough that the exponent contribution is at
most the fifth power of the scale parameter. -/
theorem eventually_divisor_eighthRoot_robustness_budget_of_tail_scale
    (B : ℕ) (hB : 16 ≤ B) (rho : ℕ → ℕ)
    (htail : ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let D : ℕ := 2048 * R ^ 15
      D * rho k + r ≤ r ^ 5) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let c : ℕ := (r + 1) * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      32 * c ^ 2 * (2048 * R ^ 15 * rho k + r) ≤
        (2048 * R ^ 15) * (Θ - 2 * τ) := by
  let R : ℕ := 4 * B
  let D : ℕ := 2048 * R ^ 15
  have hR : 0 < R := by dsimp [R]; omega
  have hD : 0 < D := by dsimp [D]; positivity
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  filter_upwards [htriple.eventually (eventually_ge_atTop (D + 2)),
    eventually_divisor_eighthRoot_alternatingHub_numerics B hB, htail]
      with k hr hnum htailScale
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  let c : ℕ := (r + 1) * R ^ 5
  let Θ : ℕ := k / (2 * c)
  let τ : ℕ := k / (8 * c)
  let theta : ℕ := Θ - 2 * τ
  have hrbig : D + 2 ≤ r := by simpa [r] using hr
  have hrpos : 0 < r := by omega
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hreserve : 2 * τ ≤ Θ := by
    simpa [τ, Θ, c, r, R, Nat.mul_assoc] using hnum.2.2.2
  have hsplit : theta + 2 * τ = Θ := by
    dsimp [theta]
    exact Nat.sub_add_cancel hreserve
  have hquot : k < 2 * c * (Θ + 1) := by
    simpa [Nat.mul_assoc] using
      (Nat.lt_mul_div_succ k (by positivity : 0 < 2 * c))
  have htaufloor : 8 * c * τ ≤ k := by
    have h := Nat.div_mul_le_self k (8 * c)
    simpa [τ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hdecomp : 4 * c * (Θ + 1) =
      4 * c * (theta + 1) + 8 * c * τ := by
    rw [← hsplit]
    ring
  have hkTheta : k < 4 * c * (theta + 1) := by
    have htwok : 2 * k < 4 * c * (Θ + 1) := by
      have hm := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hquot
      calc
        2 * k < 2 * (2 * c * (Θ + 1)) := hm
        _ = 4 * c * (Θ + 1) := by ring
    rw [hdecomp] at htwok
    omega
  have h8c : 8 * c ≤ k := by
    simpa [c, r, R, Nat.mul_assoc] using hnum.2.2.1
  have hthetaPos : 0 < theta := by
    by_contra hz
    have hzero : theta = 0 := by omega
    rw [hzero] at hkTheta
    omega
  have hkThetaWeak : k ≤ 8 * c * theta := by
    calc
      k ≤ 4 * c * (theta + 1) := hkTheta.le
      _ ≤ 8 * c * theta := by
        have htheta : theta + 1 ≤ 2 * theta := by omega
        calc
          4 * c * (theta + 1) ≤ 4 * c * (2 * theta) := by gcongr
          _ = 8 * c * theta := by ring
  let s : ℕ := Nat.sqrt k
  let q : ℕ := Nat.sqrt s
  have hr2q : r ^ 2 ≤ q := by
    dsimp [r, q]
    exact Nat.sqrt_le' q
  have hq2s : q ^ 2 ≤ s := by
    dsimp [q]
    exact Nat.sqrt_le' s
  have hs2k : s ^ 2 ≤ k := by
    dsimp [s]
    exact Nat.sqrt_le' k
  have hr8k : r ^ 8 ≤ k := by
    calc
      r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
      _ ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_left hr2q 2) 2
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hq2s 2
      _ ≤ k := hs2k
  have hcLe : c ≤ 2 * r * R ^ 5 := by
    dsimp [c]
    gcongr
    omega
  have hscaled : 8 * c *
      (32 * c ^ 2 * (D * rho k + r)) ≤ D * k := by
    calc
      8 * c * (32 * c ^ 2 * (D * rho k + r)) =
          256 * c ^ 3 * (D * rho k + r) := by ring
      _ ≤ 256 * (2 * r * R ^ 5) ^ 3 * (D * rho k + r) := by gcongr
      _ = D * (r ^ 3 * (D * rho k + r)) := by
        dsimp [D]
        ring
      _ ≤ D * r ^ 8 := by
        gcongr
        calc
          r ^ 3 * (D * rho k + r) ≤ r ^ 3 * r ^ 5 :=
            Nat.mul_le_mul_left _ htailScale
          _ = r ^ 8 := by ring
      _ ≤ D * k := Nat.mul_le_mul_left D hr8k
  have htargetScaled : 8 * c *
      (32 * c ^ 2 * (D * rho k + r)) ≤
        8 * c * (D * theta) := by
    calc
      _ ≤ D * k := hscaled
      _ ≤ D * (8 * c * theta) := Nat.mul_le_mul_left D hkThetaWeak
      _ = 8 * c * (D * theta) := by ring
  have htarget : 32 * c ^ 2 * (D * rho k + r) ≤ D * theta := by
    exact Nat.le_of_mul_le_mul_left htargetScaled (by positivity)
  simpa [D, R, r, c, Θ, τ, theta] using htarget

/-- At the eighth-root scale the first-moment exponent may itself be the
eighth-root parameter.  The polynomial budget still has three spare powers
of that parameter. -/
theorem eventually_divisor_eighthRoot_growing_robustness_budget
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let c : ℕ := (r + 1) * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      32 * c ^ 2 * (2048 * R ^ 15 * r + r) ≤
        (2048 * R ^ 15) * (Θ - 2 * τ) := by
  let R : ℕ := 4 * B
  let D : ℕ := 2048 * R ^ 15
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  apply eventually_divisor_eighthRoot_robustness_budget_of_tail_scale
    B hB (fun k => Nat.sqrt (Nat.sqrt (Nat.sqrt k)))
  filter_upwards [htriple.eventually (eventually_ge_atTop (D + 2))]
      with k hr
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  have hrbig : D + 2 ≤ r := by simpa [r] using hr
  have hrpos : 0 < r := by omega
  have hcoef : D + 1 ≤ r := by omega
  have hsq : r ^ 2 ≤ r ^ 5 := by
    calc
      r ^ 2 ≤ r ^ 2 * r ^ 3 :=
        Nat.le_mul_of_pos_right _ (by positivity : 0 < r ^ 3)
      _ = r ^ 5 := by ring
  dsimp only
  change D * r + r ≤ r ^ 5
  calc
    D * r + r = (D + 1) * r := by ring
    _ ≤ r * r := Nat.mul_le_mul_right r hcoef
    _ = r ^ 2 := by ring
    _ ≤ r ^ 5 := hsq

/-- The exponent may be eight times the full exact component scale
`P = 8 * (floor(k^(1/8)) + 1) * R^5`.  This covers the worst repeated-visit
robustness charge of a doubled-tree tour and remains linear in the
eighth-root parameter. -/
theorem eventually_divisor_eighthRoot_exact_scale_robustness_budget
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let P : ℕ := 8 * (r + 1) * R ^ 5
      let c : ℕ := (r + 1) * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      32 * c ^ 2 * (2048 * R ^ 15 * (8 * P) + r) ≤
        (2048 * R ^ 15) * (Θ - 2 * τ) := by
  let R : ℕ := 4 * B
  let D : ℕ := 2048 * R ^ 15
  let E : ℕ := 128 * D * R ^ 5 + 1
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  apply eventually_divisor_eighthRoot_robustness_budget_of_tail_scale
    B hB (fun k =>
      8 * (8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5))
  filter_upwards [htriple.eventually (eventually_ge_atTop E)] with k hr
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  have hrbig : E ≤ r := by simpa [r] using hr
  have hrpos : 0 < r := by
    have hEpos : 0 < E := by dsimp [E]; positivity
    exact hEpos.trans_le hrbig
  have hP : 64 * (r + 1) * R ^ 5 ≤ 128 * r * R ^ 5 := by
    calc
      64 * (r + 1) * R ^ 5 ≤ 64 * (2 * r) * R ^ 5 := by gcongr; omega
      _ = 128 * r * R ^ 5 := by ring
  have hlinear : D * (64 * (r + 1) * R ^ 5) + r ≤ E * r := by
    calc
      D * (64 * (r + 1) * R ^ 5) + r ≤
          D * (128 * r * R ^ 5) + r := Nat.add_le_add_right
            (Nat.mul_le_mul_left D hP) r
      _ = (128 * D * R ^ 5 + 1) * r := by ring
      _ = E * r := by rfl
  have hsq : r ^ 2 ≤ r ^ 5 := by
    calc
      r ^ 2 ≤ r ^ 2 * r ^ 3 :=
        Nat.le_mul_of_pos_right _ (by positivity : 0 < r ^ 3)
      _ = r ^ 5 := by ring
  have hfinal : D * (64 * (r + 1) * R ^ 5) + r ≤ r ^ 5 :=
    hlinear.trans <| (Nat.mul_le_mul_right r hrbig).trans <| by
      simpa [pow_two] using hsq
  dsimp [D, R, r] at hfinal
  convert hfinal using 1 <;> ring

/-- Generic eventual first-moment wrapper.  Once an exponent function obeys
the displayed arithmetic budget, exponential decay discharges the analytic
part uniformly. -/
theorem eventually_divisor_eighthRoot_sampling_inequality_of_budget
    (B : ℕ) (hB : 16 ≤ B) (rho : ℕ → ℕ)
    (hbudget : ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let c : ℕ := (r + 1) * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      32 * c ^ 2 * (2048 * R ^ 15 * rho k + r) ≤
        (2048 * R ^ 15) * (Θ - 2 * τ)) :
    ∀ᶠ k : ℕ in atTop,
      let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
      let R : ℕ := 4 * B
      let c : ℕ := a * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) /
            (1 / 2 : ℝ≥0) ^ rho k) +
        ((k : ℝ≥0) * sigma) / K) < 1 := by
  let R : ℕ := 4 * B
  let D : ℕ := 2048 * R ^ 15
  have hR : 0 < R := by dsimp [R]; omega
  have hD : 0 < D := by dsimp [D]; positivity
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  have htripleReal : Tendsto
      (fun k : ℕ => (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htriple
  have hdecayBig : ∀ᶠ k : ℕ in atTop,
      (17179869184 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) < 1 / 2 :=
    htripleReal.eventually
      (eventually_sixteenth_mul_exp_neg_lt_half_of_denominator D hD)
  have hdecay : ∀ᶠ k : ℕ in atTop,
      (268435456 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) < 1 / 2 := by
    filter_upwards [hdecayBig] with k hk
    calc
      (268435456 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) ≤
        (17179869184 * Real.exp (1 / 32) : ℝ) *
          ((Nat.sqrt (Nat.sqrt (Nat.sqrt k)) : ℝ) ^ 16 *
            Real.exp (-(1 / (D : ℝ)) *
              Nat.sqrt (Nat.sqrt (Nat.sqrt k)))) := by
            gcongr
            norm_num
      _ < 1 / 2 := hk
  filter_upwards [htriple.eventually (eventually_ge_atTop 1),
    eventually_divisor_eighthRoot_alternatingHub_numerics B hB,
    hbudget, hdecay] with k hr hnum hkbudget hkdecay
  apply divisor_eighthRoot_sampling_inequality_of_sixteenth_decay
    (rho := rho k) hR (by omega)
  · simpa [R, Nat.mul_assoc] using hnum.2.2.2
  · simpa [R, Nat.mul_assoc] using hkbudget
  · dsimp [D, R] at hkdecay ⊢
    convert hkdecay using 1 <;> norm_num <;> ring

/-- The sampled connector target can have robustness
`floor(k^(1/8)) + 1`, rather than merely a fixed constant. -/
theorem eventually_divisor_eighthRoot_sampling_inequality_growing
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let a : ℕ := r + 1
      let R : ℕ := 4 * B
      let c : ℕ := a * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) /
            (1 / 2 : ℝ≥0) ^ r) +
        ((k : ℝ≥0) * sigma) / K) < 1 := by
  simpa using
    (eventually_divisor_eighthRoot_sampling_inequality_of_budget
      B hB (fun k => Nat.sqrt (Nat.sqrt (Nat.sqrt k)))
      (eventually_divisor_eighthRoot_growing_robustness_budget B hB))

/-- Exact-component-scale sampling.  The retained connector reservoir has
enough common neighbours for a number of simultaneous visits proportional
to the eventual component-size parameter `P`. -/
theorem eventually_divisor_eighthRoot_sampling_inequality_exact_scale
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let P : ℕ := 8 * (r + 1) * R ^ 5
      let c : ℕ := (r + 1) * R ^ 5
      let Θ : ℕ := k / (2 * c)
      let τ : ℕ := k / (8 * c)
      let sigma : ℝ≥0 := 1 / ((16 * c ^ 2 : ℕ) : ℝ≥0)
      let K : ℕ := k / (4 * c ^ 2) + 1
      (((τ * τ : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ (Θ - 2 * τ) /
            (1 / 2 : ℝ≥0) ^ (8 * P)) +
        ((k : ℝ≥0) * sigma) / K) < 1 := by
  exact eventually_divisor_eighthRoot_sampling_inequality_of_budget
    B hB
    (fun k => 8 *
      (8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5))
    (eventually_divisor_eighthRoot_exact_scale_robustness_budget B hB)

/-- Unconditional eventual thin eighth-root decomposition.  All numerical
and probabilistic hypotheses are discharged uniformly once the divisor is
fixed. -/
theorem eventually_exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      ∀ {V : Type*} [Fintype V]
        (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ},
        2 ≤ n → G.IndepSetFree n →
        3 * Nat.log 2 (Fintype.card V) + 1 ≤ k →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        let a : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1
        let R : ℕ := 4 * B
        let c : ℕ := a * R ^ 5
        let τ : ℕ := k / (8 * c)
        let K : ℕ := k / (4 * c ^ 2) + 1
        ∃ F : Finset (Finset V),
          (∀ H ∈ F, IsCompactAlternatingHub G 7 τ (2 * τ + K) H) ∧
          DisjointFinsetFamily F ∧
          F.biUnion id ⊆ Finset.univ ∧
          ((Finset.univ : Finset V) \ F.biUnion id).card <
            16 * ((n - 1) * (((k - 1) / B - 1) + 1)) := by
  filter_upwards [eventually_divisor_eighthRoot_alternatingHub_numerics B hB,
    eventually_divisor_eighthRoot_sampling_inequality B hB]
      with k hnum hsample
  intro V instV G instG n hn hfree hroom hcycle
  exact
    exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree
      G hB hnum.1 hn hfree hroom hcycle hnum.2.1 hnum.2.2.1
        hnum.2.2.2 hsample

/-- Unconditional eventual thin decomposition retaining growing connector
robustness.  This is the source-faithful form needed when a component router
visits a nonconstant number of hubs. -/
theorem eventually_exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_growing
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      ∀ {V : Type*} [Fintype V]
        (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ},
        2 ≤ n → G.IndepSetFree n →
        3 * Nat.log 2 (Fintype.card V) + 1 ≤ k →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
        let a : ℕ := r + 1
        let R : ℕ := 4 * B
        let c : ℕ := a * R ^ 5
        let τ : ℕ := k / (8 * c)
        let K : ℕ := k / (4 * c ^ 2) + 1
        ∃ F : Finset (Finset V),
          (∀ H ∈ F,
            IsCompactAlternatingHub G (r + 1) τ (2 * τ + K) H) ∧
          DisjointFinsetFamily F ∧
          F.biUnion id ⊆ Finset.univ ∧
          ((Finset.univ : Finset V) \ F.biUnion id).card <
            16 * ((n - 1) * (((k - 1) / B - 1) + 1)) := by
  filter_upwards [eventually_divisor_eighthRoot_alternatingHub_numerics B hB,
    eventually_divisor_eighthRoot_sampling_inequality_growing B hB]
      with k hnum hsample
  intro V instV G instG n hn hfree hroom hcycle
  exact
    exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree_rho
      G (Nat.sqrt (Nat.sqrt (Nat.sqrt k))) hB hnum.1 hn hfree hroom
        hcycle hnum.2.1 hnum.2.2.1 hnum.2.2.2 hsample

/-- Exact-component-scale form of the thin decomposition. -/
theorem eventually_exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_exact_scale
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      ∀ {V : Type*} [Fintype V]
        (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ},
        2 ≤ n → G.IndepSetFree n →
        3 * Nat.log 2 (Fintype.card V) + 1 ≤ k →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
        let R : ℕ := 4 * B
        let P : ℕ := 8 * (r + 1) * R ^ 5
        let c : ℕ := (r + 1) * R ^ 5
        let τ : ℕ := k / (8 * c)
        let K : ℕ := k / (4 * c ^ 2) + 1
        ∃ F : Finset (Finset V),
          (∀ H ∈ F,
            IsCompactAlternatingHub G (8 * P + 1) τ (2 * τ + K) H) ∧
          DisjointFinsetFamily F ∧
          F.biUnion id ⊆ Finset.univ ∧
          ((Finset.univ : Finset V) \ F.biUnion id).card <
            16 * ((n - 1) * (((k - 1) / B - 1) + 1)) := by
  filter_upwards [eventually_divisor_eighthRoot_alternatingHub_numerics B hB,
    eventually_divisor_eighthRoot_sampling_inequality_exact_scale B hB]
      with k hnum hsample
  intro V instV G instG n hn hfree hroom hcycle
  exact
    exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_of_two_pass_cycleFree_rho
      G (8 * (8 * (Nat.sqrt (Nat.sqrt (Nat.sqrt k)) + 1) * (4 * B) ^ 5))
        hB hnum.1 hn hfree hroom hcycle hnum.2.1 hnum.2.2.1
        hnum.2.2.2 hsample

/-! ## Scale-free parity accounting -/

/-- Scale-free form of the hybrid selected-path accounting theorem.  The
earlier diagonal specialization fixed every alternating side at
`9 * sqrt k`; the proof only uses an exact common scaffold size `q` and the
corresponding capacity `(q-4)(d-1)`. -/
theorem unbroken_alternatingScaffold_selected_count_of_hybrid_lift_at_scale
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {q theta k n σ pathThreshold : ℕ}
    (hk : 3 ≤ k) (hn : 0 < n) (hpath : 2 ≤ pathThreshold)
    (hfree : G.IndepSetFree n)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hσA : ∀ i, σ ≤ (A i).card)
    (hq : 4 ≤ q) (htheta : 3 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hbase : ∀ d s : ℕ,
      pathThreshold ≤ d → d ≤ pathThreshold + 1 →
      s ≤ 2 * Nat.log 2
        (Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}) →
      (d + s) + 6 * (d - 1) + 2 * (s + 1) ≤ k)
    (hcap : ∀ d s : ℕ,
      pathThreshold ≤ d → d ≤ pathThreshold + 1 →
      s ≤ 2 * Nat.log 2
        (Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}) →
      (k - ((d + s) + 6 * (d - 1))) / 2 ≤
        (q - 4) * (d - 1))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    (((σ - 4) - 4 * (pathThreshold + 1)) *
        Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)} <
      32 * (pathThreshold + 1) * n) := by
  classical
  let J := {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}
  let AJ : J → Finset V := fun i => A i.1
  let BJ : J → Finset V := fun i => B i.1
  let DJ : J → Finset V := fun i => D i.1
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    let I : J → Finset V := fun i =>
      Classical.choose
        (exists_large_indep_sdiff_of_not_hasThreeDisjointAdjPairFamily
          G (AJ i) i.2)
    have hI : ∀ i : J,
        I i ⊆ AJ i ∧ G.IsIndepSet (I i : Set V) ∧
          (AJ i).card - 4 ≤ (I i).card := by
      intro i
      exact Classical.choose_spec
        (exists_large_indep_sdiff_of_not_hasThreeDisjointAdjPairFamily
          G (AJ i) i.2)
    have hIcard : ∀ i : J, σ - 4 ≤ (I i).card := by
      intro i
      exact (Nat.sub_le_sub_right (by simpa [AJ] using hσA i.1) 4).trans
        (hI i).2.2
    have hIdisj : ∀ i j : J, i ≠ j → Disjoint (I i) (I j) := by
      intro i j hij
      apply (hregions i.1 j.1 (by intro h; exact hij (Subtype.ext h))).mono
      · exact (hI i).1.trans
          (Finset.subset_union_left.trans Finset.subset_union_left)
      · exact (hI j).1.trans
          (Finset.subset_union_left.trans Finset.subset_union_left)
    obtain hlong | hcount :=
      exists_selected_path_with_even_return_or_transversal_count
        G I (n := n) (σ := σ - 4) (D := pathThreshold) (parity := k)
          hpath hfree hIcard (fun i => (hI i).2.1) hIdisj
    · obtain ⟨M, hM, u, v, p, r, j, hp, hplow, hpup, hpparity,
          hj, hr, hreven, hrlen, hdisj⟩ := hlong
      exfalso
      apply hcycle
      refine cycleGraph_isContained_of_selected_path_and_hubInteraction_return
        hk G AJ BJ DJ I M
          (fun i ↦ hscaffold i.1)
          (fun i ↦ hrob i.1)
          (fun i ↦ hmajorD i.1)
          (fun i ↦ by simpa [AJ] using hAcard i.1)
          hq htheta
          (fun i l hil ↦ hregions i.1 l.1 (by
            intro h
            exact hil (Subtype.ext h)))
          (fun i ↦ (hI i).1) hM
          p hp (hpath.trans hplow) r hr hdisj ?_ ?_ ?_
      · apply hbase p.length r.length hplow hpup
        exact hrlen.trans (Nat.mul_le_mul_left 2 hj)
      · rcases hreven with ⟨t, ht⟩
        omega
      · apply hcap p.length r.length hplow hpup
        exact hrlen.trans (Nat.mul_le_mul_left 2 hj)
    · simpa [J] using hcount
  · have hcard : Fintype.card J = 0 :=
      Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hJ)
    simp [J] at hcard
    simp [hcard]
    exact hn

/-- An eighth-degree polynomial is below `2^(4r)` from a concrete constant
onward.  This elementary estimate converts the extremal-order binary
logarithm into the eighth-root scale. -/
theorem sixteen_thousand_mul_pow_eight_le_two_pow_four_mul
    {r : ℕ} (hr : 16 ≤ r) :
    16384 * r ^ 8 ≤ 2 ^ (4 * r) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hsquare : (r + 1) ^ 2 ≤ 2 * r ^ 2 := by
        nlinarith
      have hpow := Nat.pow_le_pow_left hsquare 4
      have hstep : (r + 1) ^ 8 ≤ 16 * r ^ 8 := by
        calc
          (r + 1) ^ 8 = ((r + 1) ^ 2) ^ 4 := by ring
          _ ≤ (2 * r ^ 2) ^ 4 := hpow
          _ = 16 * r ^ 8 := by ring
      calc
        16384 * (r + 1) ^ 8 ≤ 16 * (16384 * r ^ 8) := by
          nlinarith
        _ ≤ 16 * 2 ^ (4 * r) := Nat.mul_le_mul_left 16 ih
        _ = 2 ^ (4 * (r + 1)) := by
          rw [show 4 * (r + 1) = 4 * r + 4 by ring, Nat.pow_add]
          norm_num
          ring

/-- Binary logarithm is at most four times the iterated eighth root once
that root is at least sixteen. -/
theorem log_two_le_four_mul_triple_sqrt
    {k : ℕ} (hr : 16 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt k))) :
    Nat.log 2 k ≤ 4 * Nat.sqrt (Nat.sqrt (Nat.sqrt k)) := by
  let s : ℕ := Nat.sqrt k
  let q : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt q
  have hrpos : 0 < r := by dsimp [r, q, s]; omega
  have hrSq : r ^ 2 ≤ q := by
    dsimp [r]
    exact Nat.sqrt_le' q
  have hqLt : q < (r + 1) ^ 2 := by
    dsimp [r]
    exact Nat.lt_succ_sqrt' q
  have hqLe : q ≤ 4 * r ^ 2 := by
    have hrSum : r + 1 ≤ 2 * r := by omega
    calc
      q ≤ (r + 1) ^ 2 := hqLt.le
      _ ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left hrSum 2
      _ = 4 * r ^ 2 := by ring
  have hsLt : s < (q + 1) ^ 2 := by
    dsimp [q]
    exact Nat.lt_succ_sqrt' s
  have hsLe : s ≤ 64 * r ^ 4 := by
    have hqpos : 0 < q := hrpos.trans_le (Nat.sqrt_le_self q)
    have hqSum : q + 1 ≤ 2 * q := by omega
    calc
      s ≤ (q + 1) ^ 2 := hsLt.le
      _ ≤ (2 * q) ^ 2 := Nat.pow_le_pow_left hqSum 2
      _ = 4 * q ^ 2 := by ring
      _ ≤ 4 * (4 * r ^ 2) ^ 2 := by gcongr
      _ = 64 * r ^ 4 := by ring
  have hkLt : k < (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.lt_succ_sqrt' k
  have hkLe : k ≤ 16384 * r ^ 8 := by
    have hspos : 0 < s := by
      exact hrpos.trans_le (Nat.sqrt_le_self q) |>.trans_le
        (Nat.sqrt_le_self s)
    have hsSum : s + 1 ≤ 2 * s := by omega
    calc
      k ≤ (s + 1) ^ 2 := hkLt.le
      _ ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left hsSum 2
      _ = 4 * s ^ 2 := by ring
      _ ≤ 4 * (64 * r ^ 4) ^ 2 := by gcongr
      _ = 16384 * r ^ 8 := by ring
  have hkPow : k ≤ 2 ^ (4 * r) :=
    hkLe.trans (sixteen_thousand_mul_pow_eight_le_two_pow_four_mul
      (by simpa [r, q, s] using hr))
  have hlog : Nat.log 2 k ≤ 4 * r :=
    (Nat.log_le_clog 2 k).trans (Nat.clog_le_of_le_pow hkPow)
  simpa [r, q, s] using hlog

/-- At any scale `P`, if the exact alternating side `q` is at least forty
times larger, then the hybrid selected-path estimate leaves fewer than `n`
parity-unbroken cores.  The quotient hypotheses are stated explicitly so
the lemma can be instantiated directly with `q=floor(k/P)`. -/
theorem unbroken_alternatingScaffold_card_lt_of_large_exact_scale
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {q P k n : ℕ}
    (hk : 3 ≤ k) (hn : 0 < n) (hnk : n ≤ k)
    (hP : 3 ≤ P) (hqlarge : 40 * (P + 1) ≤ q)
    (hquotLower : P * q ≤ k) (hquotUpper : k < P * (q + 1))
    (hlog : 4 * (Nat.log 2 k + 1) ≤ P)
    (hlabels : Fintype.card ι ≤ (k - 1) * (n - 1) + 1)
    (hfree : G.IndepSetFree n)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) 7)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)} < n := by
  have hJlabels :
      Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)} ≤
        (k - 1) * (n - 1) + 1 :=
    (Fintype.card_subtype_le _).trans hlabels
  have hkone : 1 ≤ k := by omega
  have hlogJ :
      Nat.log 2
          (Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}) ≤
        2 * (Nat.log 2 k + 1) :=
    (Nat.log_mono_right hJlabels).trans
      (log_extremal_order_le_two_mul_log_add_one hkone hnk)
  have hPqBase : 10 * P + 9 ≤ P * q := by
    have hq13 : 13 ≤ q := by omega
    have hmul : P * 13 ≤ P * q := Nat.mul_le_mul_left P hq13
    nlinarith
  have hbase : ∀ d s : ℕ,
      P ≤ d → d ≤ P + 1 →
      s ≤ 2 * Nat.log 2
        (Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}) →
      (d + s) + 6 * (d - 1) + 2 * (s + 1) ≤ k := by
    intro d s hdlo hdhi hs
    have hsP : s ≤ P := by
      calc
        s ≤ 2 * Nat.log 2
            (Fintype.card {i : ι //
              ¬ HasThreeDisjointAdjPairFamily G (A i)}) := hs
        _ ≤ 4 * (Nat.log 2 k + 1) := by
          calc
            2 * Nat.log 2
                (Fintype.card {i : ι //
                  ¬ HasThreeDisjointAdjPairFamily G (A i)}) ≤
              2 * (2 * (Nat.log 2 k + 1)) := Nat.mul_le_mul_left 2 hlogJ
            _ = 4 * (Nat.log 2 k + 1) := by ring
        _ ≤ P := hlog
    calc
      (d + s) + 6 * (d - 1) + 2 * (s + 1) ≤ 10 * P + 9 := by omega
      _ ≤ P * q := hPqBase
      _ ≤ k := hquotLower
  have hqPC : 9 * P ≤ q * (P - 2) := by
    have hq9P : 9 * P ≤ q := by omega
    have hfac : 1 ≤ P - 2 := by omega
    have hmul : q * 1 ≤ q * (P - 2) := Nat.mul_le_mul_left q hfac
    omega
  have hquotRoom : k ≤ 2 * (q - 4) * (P - 1) := by
    have hupperRoom : P * (q + 1) ≤ 2 * (q - 4) * (P - 1) := by
      have hqsub : q = (q - 4) + 4 := by omega
      have hPsub : P - 1 = (P - 2) + 1 := by omega
      have hPtwo : P = (P - 2) + 2 := by omega
      have hprod : q * (P - 2) =
          (q - 4) * (P - 2) + 4 * (P - 2) := by
        calc
          q * (P - 2) = ((q - 4) + 4) * (P - 2) := by rw [← hqsub]
          _ = (q - 4) * (P - 2) + 4 * (P - 2) := by ring
      nlinarith [hqPC, hprod, hqsub, hPsub, hPtwo]
    exact hquotUpper.le.trans hupperRoom
  have hcap : ∀ d s : ℕ,
      P ≤ d → d ≤ P + 1 →
      s ≤ 2 * Nat.log 2
        (Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)}) →
      (k - ((d + s) + 6 * (d - 1))) / 2 ≤ (q - 4) * (d - 1) := by
    intro d s hdlo _hdhi _hs
    have hd : P - 1 ≤ d - 1 := Nat.sub_le_sub_right hdlo 1
    calc
      (k - ((d + s) + 6 * (d - 1))) / 2 ≤ k / 2 :=
        Nat.div_le_div_right (Nat.sub_le _ _)
      _ ≤ (q - 4) * (P - 1) := by
        apply (Nat.div_le_iff_le_mul (by norm_num : 0 < 2)).2
        calc
          k ≤ 2 * (q - 4) * (P - 1) := hquotRoom
          _ = (q - 4) * (P - 1) * 2 := by ring
          _ ≤ (q - 4) * (P - 1) * 2 + 2 - 1 := by omega
      _ ≤ (q - 4) * (d - 1) := Nat.mul_le_mul_left _ hd
  have hcount :=
    unbroken_alternatingScaffold_selected_count_of_hybrid_lift_at_scale
      G A B D hk hn (by omega : 2 ≤ P) hfree hscaffold hrob hmajorD
        hAcard (fun i => by rw [hAcard i]) (by omega) (by norm_num)
        hregions hbase hcap hcycle
  by_contra hnot
  have hncard : n ≤
      Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)} := by
    omega
  have hcoef : 32 * (P + 1) < (q - 4) - 4 * (P + 1) := by omega
  have hlower : 32 * (P + 1) * n <
      ((q - 4) - 4 * (P + 1)) *
        Fintype.card {i : ι // ¬ HasThreeDisjointAdjPairFamily G (A i)} := by
    calc
      32 * (P + 1) * n < ((q - 4) - 4 * (P + 1)) * n :=
        (Nat.mul_lt_mul_right hn).2 hcoef
      _ ≤ ((q - 4) - 4 * (P + 1)) *
          Fintype.card {i : ι //
            ¬ HasThreeDisjointAdjPairFamily G (A i)} :=
        Nat.mul_le_mul_left _ hncard
  exact (hlower.trans hcount).false

/-- For a fixed divisor, the eighth-root exact core `q=floor(k/P)` is
eventually more than forty times the hybrid path scale
`P=8(floor(k^(1/8))+1)R^5`, and that scale also dominates every binary-log
detour appearing at extremal Ramsey order. -/
theorem eventually_divisor_eighthRoot_exact_scale_accounting_numerics
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let P : ℕ := 8 * (r + 1) * R ^ 5
      let q : ℕ := k / P
      16 ≤ r ∧ 3 ≤ P ∧ 80 * (P + 1) ≤ q ∧
        4 * (Nat.log 2 k + 1) ≤ P := by
  let R : ℕ := 4 * B
  let Q : ℕ := max 16 (40960 * R ^ 10)
  have hRpos : 0 < R := by dsimp [R]; omega
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  filter_upwards [htriple.eventually (eventually_ge_atTop Q)] with k hrQ
  let s : ℕ := Nat.sqrt k
  let u : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt u
  let P : ℕ := 8 * (r + 1) * R ^ 5
  let q : ℕ := k / P
  have hr16 : 16 ≤ r :=
    (le_max_left 16 (40960 * R ^ 10)).trans (by
      simpa [Q, r, u, s] using hrQ)
  have hrCoef : 40960 * R ^ 10 ≤ r :=
    (le_max_right 16 (40960 * R ^ 10)).trans (by
      simpa [Q, r, u, s] using hrQ)
  have hrpos : 0 < r := by omega
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPthree : 3 ≤ P := by
    have hRone : 1 ≤ R ^ 5 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 5 (Nat.ne_of_gt hRpos))
    dsimp [P]
    nlinarith
  have hr2u : r ^ 2 ≤ u := by
    dsimp [r]
    exact Nat.sqrt_le' u
  have hu2s : u ^ 2 ≤ s := by
    dsimp [u]
    exact Nat.sqrt_le' s
  have hs2k : s ^ 2 ≤ k := by
    dsimp [s]
    exact Nat.sqrt_le' k
  have hr4s : r ^ 4 ≤ s := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ u ^ 2 := Nat.pow_le_pow_left hr2u 2
      _ ≤ s := hu2s
  have hr8k : r ^ 8 ≤ k := by
    calc
      r ^ 8 = (r ^ 4) ^ 2 := by ring
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hr4s 2
      _ ≤ k := hs2k
  have hPLe : P ≤ 16 * r * R ^ 5 := by
    have ha : r + 1 ≤ 2 * r := by omega
    calc
      P = 8 * (r + 1) * R ^ 5 := rfl
      _ ≤ 8 * (2 * r) * R ^ 5 := by gcongr
      _ = 16 * r * R ^ 5 := by ring
  have hcoef : 40960 * R ^ 10 ≤ r ^ 6 :=
    hrCoef.trans (Nat.le_self_pow (by norm_num : (6 : ℕ) ≠ 0) r)
  have hPsucc : P + 1 ≤ 2 * P := by omega
  have hlargeProd : 80 * (P + 1) * P ≤ k := by
    calc
      80 * (P + 1) * P ≤ 80 * (2 * P) * P := by gcongr
      _ = 160 * P ^ 2 := by ring
      _ ≤ 160 * (16 * r * R ^ 5) ^ 2 := by gcongr
      _ = r ^ 2 * (40960 * R ^ 10) := by ring
      _ ≤ r ^ 2 * r ^ 6 := Nat.mul_le_mul_left (r ^ 2) hcoef
      _ = r ^ 8 := by ring
      _ ≤ k := hr8k
  have hqlarge : 80 * (P + 1) ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hPpos).2 (by
      simpa [Nat.mul_assoc] using hlargeProd)
  have hlogk : Nat.log 2 k ≤ 4 * r := by
    simpa [r, u, s] using log_two_le_four_mul_triple_sqrt hr16
  have hRpow : 2 ≤ R ^ 5 := by
    have hRtwo : 2 ≤ R := by omega
    exact hRtwo.trans (Nat.le_self_pow (by norm_num : (5 : ℕ) ≠ 0) R)
  have hlogP : 4 * (Nat.log 2 k + 1) ≤ P := by
    calc
      4 * (Nat.log 2 k + 1) ≤ 4 * (4 * r + 1) := by gcongr
      _ ≤ 8 * (r + 1) * R ^ 5 := by nlinarith
      _ = P := by rfl
  exact ⟨hr16, hPthree, hqlarge, hlogP⟩

/-- The exact eighth-root quotient eventually dominates the square of the
component parameter.  This stronger spare-power estimate pays for using one
additional hub in every full-core component. -/
theorem eventually_divisor_eighthRoot_exact_scale_square_room
    (B : ℕ) (hB : 16 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let P : ℕ := 8 * (r + 1) * R ^ 5
      let q : ℕ := k / P
      16 * (P + 1) ^ 2 ≤ q := by
  let R : ℕ := 4 * B
  let Q : ℕ := max 16 (262144 * R ^ 15)
  have hRpos : 0 < R := by dsimp [R]; omega
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  filter_upwards [htriple.eventually (eventually_ge_atTop Q)] with k hrQ
  let s : ℕ := Nat.sqrt k
  let u : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt u
  let P : ℕ := 8 * (r + 1) * R ^ 5
  let q : ℕ := k / P
  have hr16 : 16 ≤ r :=
    (le_max_left 16 (262144 * R ^ 15)).trans (by
      simpa [Q, r, u, s] using hrQ)
  have hrCoef : 262144 * R ^ 15 ≤ r :=
    (le_max_right 16 (262144 * R ^ 15)).trans (by
      simpa [Q, r, u, s] using hrQ)
  have hrpos : 0 < r := by omega
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hr2u : r ^ 2 ≤ u := by
    dsimp [r]
    exact Nat.sqrt_le' u
  have hu2s : u ^ 2 ≤ s := by
    dsimp [u]
    exact Nat.sqrt_le' s
  have hs2k : s ^ 2 ≤ k := by
    dsimp [s]
    exact Nat.sqrt_le' k
  have hr8k : r ^ 8 ≤ k := by
    calc
      r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
      _ ≤ (u ^ 2) ^ 2 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_left hr2u 2) 2
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hu2s 2
      _ ≤ k := hs2k
  have hPLe : P ≤ 16 * r * R ^ 5 := by
    have ha : r + 1 ≤ 2 * r := by omega
    calc
      P = 8 * (r + 1) * R ^ 5 := rfl
      _ ≤ 8 * (2 * r) * R ^ 5 := by gcongr
      _ = 16 * r * R ^ 5 := by ring
  have hPsucc : P + 1 ≤ 2 * P := by omega
  have hcoef : 262144 * R ^ 15 ≤ r ^ 5 :=
    hrCoef.trans (Nat.le_self_pow (by norm_num : (5 : ℕ) ≠ 0) r)
  have hlargeProd : 16 * (P + 1) ^ 2 * P ≤ k := by
    calc
      16 * (P + 1) ^ 2 * P ≤ 16 * (2 * P) ^ 2 * P := by gcongr
      _ = 64 * P ^ 3 := by ring
      _ ≤ 64 * (16 * r * R ^ 5) ^ 3 := by gcongr
      _ = r ^ 3 * (262144 * R ^ 15) := by ring
      _ ≤ r ^ 3 * r ^ 5 := Nat.mul_le_mul_left _ hcoef
      _ = r ^ 8 := by ring
      _ ≤ k := hr8k
  change 16 * (P + 1) ^ 2 ≤ k / P
  exact (Nat.le_div_iff_mul_le hPpos).2 (by
    simpa [Nat.mul_assoc] using hlargeProd)

/-- Eventual compact eighth-root decomposition with its exact core data and
the parity accounting already attached.  Thus every dense cycle-free Ramsey
counterexample is covered, up to the divisor-controlled remainder, by
pairwise-disjoint regions whose parity-unbroken subfamily has size `< n`. -/
theorem eventually_exists_divisor_eighthRoot_core_family_with_unbroken_card_lt_exact_scale
    (Bdiv : ℕ) (hBdiv : 16 ≤ Bdiv) :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, 3 ≤ n → n ≤ k →
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = (k - 1) * (n - 1) + 1 →
        G.IndepSetFree n →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
        let R : ℕ := 4 * Bdiv
        let P : ℕ := 8 * (r + 1) * R ^ 5
        let q : ℕ := k / P
        let K : ℕ := k / (4 * ((r + 1) * R ^ 5) ^ 2) + 1
        ∃ F : Finset (Finset V),
          ∃ A Bside D : F → Finset V,
          (∀ i : F,
            (A i).card = q ∧ (Bside i).card = q ∧
            Disjoint (A i) (Bside i) ∧
            Disjoint (A i ∪ Bside i) (D i) ∧
            (i : Finset V) = (A i ∪ Bside i) ∪ D i ∧
            (i : Finset V).card < 2 * q + K ∧
            IsCyclicAlternatingScaffold G q (A i) (Bside i) ∧
            RobustPairSet G (A i) (D i) (8 * P + 1)) ∧
          (∀ i j : F, i ≠ j →
            Disjoint ((A i ∪ Bside i) ∪ D i)
              ((A j ∪ Bside j) ∪ D j)) ∧
          ((Finset.univ : Finset _) \ F.biUnion id).card <
            16 * ((n - 1) * (((k - 1) / Bdiv - 1) + 1)) ∧
          Fintype.card {i : F //
            ¬ HasThreeDisjointAdjPairFamily G (A i)} < n := by
  filter_upwards
    [eventually_exists_disjoint_thin_divisor_eighthRoot_alternatingHub_family_exact_scale
      Bdiv hBdiv,
     eventually_divisor_eighthRoot_exact_scale_accounting_numerics
      Bdiv hBdiv]
      with k hfamily hnum
  intro n hn hnk V instV G instG hcardV hfree hcycle
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  let R : ℕ := 4 * Bdiv
  let P : ℕ := 8 * (r + 1) * R ^ 5
  let q : ℕ := k / P
  let K : ℕ := k / (4 * ((r + 1) * R ^ 5) ^ 2) + 1
  have hnum80 : 16 ≤ r ∧ 3 ≤ P ∧ 80 * (P + 1) ≤ q ∧
      4 * (Nat.log 2 k + 1) ≤ P := by
    simpa [r, R, P, q] using hnum
  have hnum' : 16 ≤ r ∧ 3 ≤ P ∧ 40 * (P + 1) ≤ q ∧
      4 * (Nat.log 2 k + 1) ≤ P :=
    ⟨hnum80.1, hnum80.2.1, by omega, hnum80.2.2.2⟩
  have hk64 : 64 ≤ k := by
    have hq160 : 160 ≤ q := by omega
    have hprod : 3 * 160 ≤ P * q :=
      Nat.mul_le_mul hnum'.2.1 hq160
    have hPpos0 : 0 < P := by omega
    have hPq : P * q ≤ k := by
      simpa [q, Nat.mul_comm] using Nat.div_mul_le_self k P
    exact (by norm_num : 64 ≤ 3 * 160).trans (hprod.trans hPq)
  have hroom : 3 * Nat.log 2 (Fintype.card V) + 1 ≤ k := by
    rw [hcardV]
    exact three_mul_log_extremal_order_add_one_le_of_64_le hk64 hnk
  obtain ⟨F, hhub, hdisj, _hcover, hleft⟩ :=
    hfamily G (by omega) hfree hroom hcycle
  have hchoice : ∀ i : F, ∃ A Bside D : Finset V,
      A.card = q ∧ Bside.card = q ∧ Disjoint A Bside ∧
      Disjoint (A ∪ Bside) D ∧
      (i : Finset V) = (A ∪ Bside) ∪ D ∧
      (i : Finset V).card < 2 * q + K ∧
      IsCyclicAlternatingScaffold G q A Bside ∧
      RobustPairSet G A D (8 * P + 1) := by
    intro i
    simpa [IsCompactAlternatingHub, r, R, P, q, K,
      Nat.mul_assoc] using hhub i.1 i.2
  choose A Bside D hdata using hchoice
  have hregions : ∀ i j : F, i ≠ j →
      Disjoint ((A i ∪ Bside i) ∪ D i)
        ((A j ∪ Bside j) ∪ D j) := by
    intro i j hij
    rw [← (hdata i).2.2.2.2.1, ← (hdata j).2.2.2.2.1]
    apply hdisj i i.2 j j.2
    intro h
    exact hij (Subtype.ext h)
  have hqfour : 4 ≤ q := by omega
  have hregionNe : ∀ H ∈ F, H.Nonempty := by
    intro H hH
    let i : F := ⟨H, hH⟩
    have hApos : 0 < (A i).card := by rw [(hdata i).1]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hApos
    refine ⟨v, ?_⟩
    change v ∈ (i : Finset V)
    rw [(hdata i).2.2.2.2.1]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hlabels : Fintype.card F ≤ (k - 1) * (n - 1) + 1 := by
    rw [← hcardV]
    simpa using card_family_le_of_nonempty_disjoint hregionNe hdisj
  have hPpos : 0 < P := by omega
  have hquotLower : P * q ≤ k := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self k P
  have hquotUpper : k < P * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ k hPpos
  have hPseven : 7 ≤ 8 * P + 1 := by
    have hRpos : 0 < R := by dsimp [R]; omega
    have hfactor : 1 ≤ (r + 1) * R ^ 5 := by
      exact Nat.mul_pos (by omega) (pow_pos hRpos 5)
    have hPeq : P = 8 * ((r + 1) * R ^ 5) := by
      dsimp [P]
      ring
    omega
  have hunbroken : Fintype.card {i : F //
      ¬ HasThreeDisjointAdjPairFamily G (A i)} < n := by
    apply unbroken_alternatingScaffold_card_lt_of_large_exact_scale
      G A Bside D (q := q) (P := P) (k := k) (n := n)
        (by omega) (by omega) hnk hnum'.2.1 hnum'.2.2.1
        hquotLower hquotUpper hnum'.2.2.2 hlabels hfree
    · intro i
      exact (hdata i).2.2.2.2.2.2.1
    · intro i
      exact (hdata i).2.2.2.2.2.2.2.mono_threshold hPseven
    · intro i
      exact (hdata i).2.2.2.1
    · intro i
      exact (hdata i).1
    · exact hregions
    · exact hcycle
  refine ⟨F, A, Bside, D, hdata, hregions, ?_, hunbroken⟩
  simpa [r, R, P, q, K, Nat.mul_assoc] using hleft

/-! ## Arbitrary finite scaffold splicing -/

/-- Join an arbitrary finite family of pairwise-disjoint paths in one major
region.  One fresh common neighbour is used before each supplied path and
one after the last path.  Besides the exact length, the conclusion records
support provenance; this is the induction invariant needed for the general
doubled-tree hub router. -/
theorem exists_path_joining_disjoint_major_paths_fin
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B D : Finset V} {theta m : ℕ}
    (hrob : RobustPairSet G A D theta)
    (hmajorD : Disjoint (A ∪ B) D)
    (htheta : m + 1 ≤ theta)
    (u v : Fin m → V) (p : ∀ i : Fin m, G.Walk (u i) (v i))
    (hu : ∀ i, u i ∈ A) (hv : ∀ i, v i ∈ A)
    (hp : ∀ i, (p i).IsPath)
    (hploc : ∀ i w, w ∈ (p i).support → w ∈ A ∪ B)
    (hpdisj : ∀ i j, i ≠ j →
      (p i).support.Disjoint (p j).support)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hxavoid : ∀ i, x ∉ (p i).support)
    (hyavoid : ∀ i, y ∉ (p i).support) :
    ∃ q : G.Walk x y,
      ∃ E : Finset V, E ⊆ D ∧ E.card ≤ m + 1 ∧
      q.IsPath ∧
      q.length = (∑ i, (p i).length) + 2 * (m + 1) ∧
      (∀ w ∈ q.support, w ∈ A ∪ B ∨ w ∈ D) ∧
      ∀ w ∈ q.support,
        w = x ∨ w = y ∨ (∃ i, w ∈ (p i).support) ∨ w ∈ E := by
  classical
  induction m generalizing theta D x with
  | zero =>
      have hthetaPos : 0 < theta := by omega
      obtain ⟨z, hzD, _hzempty, hxz, hzy⟩ :=
        exists_fresh_commonNeighbor_of_pair G (hrob x hx y hy)
          (F := ∅) (by simpa using hthetaPos)
      let q : G.Walk x y :=
        SimpleGraph.Walk.cons hxz
          (SimpleGraph.Walk.cons hzy SimpleGraph.Walk.nil)
      have hzx : z ≠ x := by
        intro h
        exact (Finset.disjoint_left.mp hmajorD)
          (Finset.mem_union_left _ hx) (h ▸ hzD)
      have hzyNe : z ≠ y := by
        intro h
        exact (Finset.disjoint_left.mp hmajorD)
          (Finset.mem_union_left _ hy) (h ▸ hzD)
      refine ⟨q, {z}, by simpa using hzD, by simp, ?_, ?_, ?_, ?_⟩
      · simp [q, SimpleGraph.Walk.cons_isPath_iff,
          hxy, hzx.symm, hzyNe]
      · simp [q]
      · intro w hw
        simp [q] at hw
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (Finset.mem_union_left _ hx)
        · exact Or.inr hzD
        · exact Or.inl (Finset.mem_union_left _ hy)
      · intro w hw
        simp [q] at hw
        rcases hw with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (by simp)))
        · exact Or.inr (Or.inl rfl)
  | succ m ih =>
      let i0 : Fin (m + 1) := 0
      let u0 : V := u i0
      let v0 : V := v i0
      let p0 : G.Walk u0 v0 := p i0
      obtain ⟨z, hzD, _hzempty, hxz, hzu⟩ :=
        exists_fresh_commonNeighbor_of_pair G (hrob x hx u0 (hu i0))
          (F := ∅) (by simpa using (show 0 < theta by omega))
      have hzMajor : z ∉ A ∪ B := fun hz =>
        (Finset.disjoint_left.mp hmajorD) hz hzD
      have hzP0 : z ∉ p0.support := fun hz =>
        hzMajor (hploc i0 z hz)
      have hxP0 : x ∉ p0.support := hxavoid i0
      have hxzNe : x ≠ z := by
        intro h
        exact hzMajor (h ▸ Finset.mem_union_left _ hx)
      let pz : G.Walk z v0 := SimpleGraph.Walk.cons hzu p0
      have hpz : pz.IsPath := by
        change (SimpleGraph.Walk.cons hzu p0).IsPath
        exact (hp i0).cons hzP0
      have hxPz : x ∉ pz.support := by
        simp only [pz, SimpleGraph.Walk.support_cons, List.mem_cons]
        intro h
        rcases h with h | h
        · exact hxzNe h
        · exact hxP0 h
      let front : G.Walk x v0 := SimpleGraph.Walk.cons hxz pz
      have hfront : front.IsPath := by
        change (SimpleGraph.Walk.cons hxz pz).IsPath
        exact hpz.cons hxPz
      let u' : Fin m → V := fun i => u i.succ
      let v' : Fin m → V := fun i => v i.succ
      let p' : ∀ i : Fin m, G.Walk (u' i) (v' i) := fun i => p i.succ
      let D' : Finset V := D \ {z}
      have hrob' : RobustPairSet G A D' (theta - 1) := by
        simpa [D'] using hrob.sdiff_right (F := {z})
      have hmajorD' : Disjoint (A ∪ B) D' :=
        hmajorD.mono_right Finset.sdiff_subset
      have htheta' : m + 1 ≤ theta - 1 := by omega
      have hv0y : v0 ≠ y := by
        intro h
        exact hyavoid i0 (h ▸ p0.end_mem_support)
      have hv0avoid : ∀ i, v0 ∉ (p' i).support := by
        intro i hv0mem
        apply hpdisj i0 i.succ
        · intro heq
          have hval := congrArg Fin.val heq
          simp [i0] at hval
        · exact p0.end_mem_support
        · exact hv0mem
      obtain ⟨rest, Erest, hErestSub, hErestCard, hrest, hrestlen,
          hrestloc, hrestsupp⟩ :=
        ih hrob' hmajorD' htheta' u' v' p'
          (fun i => hu i.succ) (fun i => hv i.succ)
          (fun i => hp i.succ)
          (fun (i : Fin m) w hw => hploc i.succ w hw)
          (fun (i j : Fin m) hij => hpdisj i.succ j.succ (by
            intro heq
            exact hij (Fin.succ_injective _ heq)))
          (hv i0) hv0y hv0avoid (fun i => hyavoid i.succ)
      have hv0notTail : v0 ∉ rest.support.tail := by
        have hn := hrest.support_nodup
        rw [← rest.cons_tail_support] at hn
        exact hn.notMem
      have hfrontRest : front.support.Disjoint rest.support.tail := by
        rw [List.disjoint_left]
        intro w hwfront hwrestTail
        have hwrest : w ∈ rest.support := List.mem_of_mem_tail hwrestTail
        have hwfront' : w = x ∨ w = z ∨ w ∈ p0.support := by
          simpa [front, pz] using hwfront
        rcases hrestsupp w hwrest with hwv0 | hwy | ⟨i, hwi⟩ | hwErest
        · subst w
          exact hv0notTail hwrestTail
        · subst w
          rcases hwfront' with h | h | h
          · exact hxy h.symm
          · exact hzMajor (h ▸ Finset.mem_union_left _ hy)
          · exact hyavoid i0 h
        · rcases hwfront' with h | h | h
          · subst w
            exact hxavoid i.succ hwi
          · subst w
            exact hzMajor (hploc i.succ z hwi)
          · apply hpdisj i0 i.succ
            · intro heq
              have hval := congrArg Fin.val heq
              simp [i0] at hval
            · exact h
            · exact hwi
        · have hwD' : w ∈ D' := hErestSub hwErest
          rcases hwfront' with h | h | h
          · subst w
            exact (Finset.disjoint_left.mp hmajorD')
              (Finset.mem_union_left _ hx) hwD'
          · subst w
            exact (Finset.mem_sdiff.mp hwD').2 (by simp)
          · exact (Finset.disjoint_left.mp hmajorD')
              (hploc i0 w h) hwD'
      let q : G.Walk x y := front.append rest
      let E : Finset V := insert z Erest
      have hq : q.IsPath :=
        isPath_append_of_support_disjoint_tail G hfront hrest hfrontRest
      have hEsub : E ⊆ D := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hzD
        · exact Finset.sdiff_subset (hErestSub hw)
      have hEcard : E.card ≤ m + 2 :=
        (Finset.card_insert_le z Erest).trans (by omega)
      refine ⟨q, E, hEsub, hEcard, hq, ?_, ?_, ?_⟩
      · dsimp [q]
        rw [SimpleGraph.Walk.length_append, hrestlen,
          Fin.sum_univ_succ]
        have hp0len : p0.length = (p 0).length := by rfl
        have hpsum : (∑ i, (p' i).length) =
            ∑ i : Fin m, (p i.succ).length := by rfl
        rw [hp0len, hpsum]
        simp [front, pz]
        omega
      · intro w hw
        have hw' : w ∈ front.support ∨ w ∈ rest.support.tail := by
          simpa [q, SimpleGraph.Walk.support_append] using hw
        rcases hw' with hwfront | hwrest
        · have hwfront' : w = x ∨ w = z ∨ w ∈ p0.support := by
            simpa [front, pz] using hwfront
          rcases hwfront' with rfl | rfl | hwP
          · exact Or.inl (Finset.mem_union_left _ hx)
          · exact Or.inr hzD
          · exact Or.inl (hploc i0 w hwP)
        · rcases hrestloc w (List.mem_of_mem_tail hwrest) with hwM | hwD
          · exact Or.inl hwM
          · exact Or.inr (Finset.mem_sdiff.mp hwD).1
      · intro w hw
        have hw' : w ∈ front.support ∨ w ∈ rest.support.tail := by
          simpa [q, SimpleGraph.Walk.support_append] using hw
        rcases hw' with hwfront | hwrest
        · have hwfront' : w = x ∨ w = z ∨ w ∈ p0.support := by
            simpa [front, pz] using hwfront
          rcases hwfront' with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (by simpa [E, h])))
          · exact Or.inr (Or.inr (Or.inl ⟨i0, h⟩))
        · rcases hrestsupp w (List.mem_of_mem_tail hwrest) with
            hwv0 | hwy | ⟨i, hwi⟩ | hwErest
          · have hwP0 : w ∈ p0.support := by
              rw [hwv0]
              exact p0.end_mem_support
            exact Or.inr (Or.inr (Or.inl ⟨i0, hwP0⟩))
          · exact Or.inr (Or.inl hwy)
          · exact Or.inr (Or.inr (Or.inl ⟨i.succ, hwi⟩))
          · exact Or.inr (Or.inr (Or.inr
              (Finset.mem_insert_of_mem hwErest)))

/-- Cut a cyclic alternating scaffold at a finite family of selected-side
anchors, retain every positive linear gap, and splice the resulting major
paths through fresh common neighbours.  The route may meet the cut set only
at its two prescribed endpoints and avoids every canonical opposite-side
mate of a cut vertex. -/
theorem exists_near_spanning_route_avoiding_scaffold_cuts
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q theta R : ℕ} {A B D : Finset V}
    (hq : 0 < q) (a b : Fin q → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (haA : ∀ i, a i ∈ A) (hbB : ∀ i, b i ∈ B)
    (hAB : Disjoint A B)
    (hab : ∀ i, G.Adj (a i) (b i))
    (hba : ∀ i, G.Adj (b i) (a (finCyclicSucc hq i)))
    (hrob : RobustPairSet G A D theta)
    (hmajorD : Disjoint (A ∪ B) D)
    (C : Finset (Fin q))
    (hRmin : C.card + 1 ≤ R)
    (hRmax : R ≤ q - 2 * C.card - 1)
    (htheta : C.card + 2 ≤ theta)
    {ix iy : Fin q} (hix : ix ∈ C) (hiy : iy ∈ C)
    (hxy : a ix ≠ a iy) :
    ∃ p : G.Walk (a ix) (a iy),
        ∃ E : Finset V, E ⊆ D ∧
        E.card ≤ orderedPositiveGapCount C + 1 ∧
        p.IsPath ∧
        p.length = 2 * R + 2 * (orderedPositiveGapCount C + 1) ∧
        (∀ w ∈ p.support, w ∈ A ∪ B ∨ w ∈ D) ∧
        (∀ w ∈ p.support, w ∈ D → w ∈ E) ∧
        (∀ d ∈ C, b d ∉ p.support) ∧
        ∀ d ∈ C, a d ∈ p.support → a d = a ix ∨ a d = a iy := by
  classical
  have hsupport :
      ((Finset.univ : Finset (Fin (C.card + 1))).filter
        fun j => orderedGapCapacity C j ≠ 0).card ≤ R := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans <| by
      simpa using hRmin
  obtain ⟨m, hmeq, hm, u, v, major, hu, hv, hmajorPath, hmajorLoc,
      hmajorDisj, hmajorLen, hmajorAvoid⟩ :=
    exists_disjoint_scaffold_gap_paths G hq a b ha hb haA hbB hAB hab hba
      C hsupport hRmax
  subst m
  have hmtheta : orderedPositiveGapCount C + 1 ≤ theta := by omega
  have hxavoid : ∀ i, a ix ∉ (major i).support := by
    intro i
    exact (hmajorAvoid i ix hix).1
  have hyavoid : ∀ i, a iy ∉ (major i).support := by
    intro i
    exact (hmajorAvoid i iy hiy).1
  obtain ⟨p, E, hEsub, hEcard, hp, hplen, hploc, hpsupport⟩ :=
    exists_path_joining_disjoint_major_paths_fin G hrob hmajorD hmtheta
      u v major hu hv hmajorPath hmajorLoc hmajorDisj
      (haA ix) (haA iy) hxy hxavoid hyavoid
  refine ⟨p, E, hEsub, hEcard, hp, ?_, hploc, ?_, ?_, ?_⟩
  · rw [hplen, hmajorLen]
  · intro w hw hwD
    rcases hpsupport w hw with h | h | ⟨i, hi⟩ | hE
    · exact ((Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (h ▸ haA ix)) hwD).elim
    · exact ((Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (h ▸ haA iy)) hwD).elim
    · exact ((Finset.disjoint_left.mp hmajorD)
        (hmajorLoc i w hi) hwD).elim
    · exact hE
  · intro d hd hbd
    rcases hpsupport (b d) hbd with h | h | ⟨i, hi⟩ | hD
    · exact (Finset.disjoint_left.mp hAB) (haA ix) (h ▸ hbB d)
    · exact (Finset.disjoint_left.mp hAB) (haA iy) (h ▸ hbB d)
    · exact (hmajorAvoid i d hd).2 hi
    · exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_right _ (hbB d)) (hEsub hD)
  · intro d hd had
    rcases hpsupport (a d) had with h | h | ⟨i, hi⟩ | hD
    · exact Or.inl h
    · exact Or.inr h
    · exact ((hmajorAvoid i d hd).1 hi).elim
    · exact ((Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (haA d)) (hEsub hD)).elim

/-- Route all visits to one alternating hub.  One distinguished visit uses
all ordered scaffold gaps outside the complete attachment cut set; every
other visit uses a fresh two-edge route in the connector reservoir.  The
support-intersection conclusion is stated against the canonical mate
relation used by full-core handles. -/
theorem exists_repeated_visit_routes_via_alternatingScaffold
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q theta t : ℕ} {A B D : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hrob : RobustPairSet G A D theta)
    (hmajorD : Disjoint (A ∪ B) D)
    (htheta : 4 * (t + 1) + 2 ≤ theta)
    (x y : Fin (t + 1) → V)
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A)
    (hxy : ∀ i, x i ≠ y i)
    (hpairs : ∀ i j, i ≠ j →
      x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j) :
    ∃ m : ℕ, m ≤ 2 * (t + 1) + 1 ∧
      ∀ R : ℕ, 2 * (t + 1) + 1 ≤ R →
      R ≤ q - 4 * (t + 1) - 1 →
      ∃ route : ∀ i : Fin (t + 1), G.Walk (x i) (y i),
        (∀ i, (route i).IsPath) ∧
        (∀ i j, i ≠ j →
          (route i).support.Disjoint (route j).support) ∧
        (route 0).length = 2 * R + 2 * (m + 1) ∧
        (∀ i : Fin t, (route i.succ).length = 2) ∧
        (∀ i w, w ∈ (route i).support →
          w ∈ A ∪ B ∨ w ∈ D) ∧
        ∀ i j z,
          (z = x j ∨ z = y j ∨
            IsCanonicalScaffoldMate G hscaffold z (x j) ∨
            IsCanonicalScaffoldMate G hscaffold z (y j)) →
          z ∈ (route i).support → z = x i ∨ z = y i := by
  classical
  rcases hcanonical : cyclicAlternatingScaffoldData G hscaffold with
    ⟨hq, a, b, hA, hB, ha, hb, hAB, hab, hba⟩
  have haA : ∀ i, a i ∈ A := by
    intro i
    rw [hA]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hbB : ∀ i, b i ∈ B := by
    intro i
    rw [hB]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let ea : Fin q ≃ A :=
    Equiv.ofBijective (fun i : Fin q => (⟨a i, haA i⟩ : A))
      ⟨fun i j h => ha (Subtype.ext_iff.mp h), by
        intro z
        have hz : z.1 ∈ Finset.univ.image a := by simpa [hA] using z.2
        rcases Finset.mem_image.mp hz with ⟨i, _hi, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩
  let ix : Fin (t + 1) → Fin q := fun i => ea.symm ⟨x i, hx i⟩
  let iy : Fin (t + 1) → Fin q := fun i => ea.symm ⟨y i, hy i⟩
  have haix : ∀ i, a (ix i) = x i := by
    intro i
    exact congrArg Subtype.val (ea.apply_symm_apply ⟨x i, hx i⟩)
  have haiy : ∀ i, a (iy i) = y i := by
    intro i
    exact congrArg Subtype.val (ea.apply_symm_apply ⟨y i, hy i⟩)
  let C : Finset (Fin q) :=
    Finset.univ.image ix ∪ Finset.univ.image iy
  have hixC : ∀ i, ix i ∈ C := by
    intro i
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hiyC : ∀ i, iy i ∈ C := by
    intro i
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hCcard : C.card ≤ 2 * (t + 1) := by
    calc
      C.card ≤ (Finset.univ.image ix).card +
          (Finset.univ.image iy).card := Finset.card_union_le _ _
      _ ≤ (t + 1) + (t + 1) := Nat.add_le_add
        (Finset.card_image_le.trans_eq (by simp))
        (Finset.card_image_le.trans_eq (by simp))
      _ = 2 * (t + 1) := by ring
  let m : ℕ := orderedPositiveGapCount C
  have hmC : m ≤ C.card + 1 := by
    calc
      m ≤ (Finset.univ : Finset (Fin (C.card + 1))).card := by
        dsimp [m, orderedPositiveGapCount]
        apply Finset.card_le_card
        intro j _hj
        exact Finset.mem_univ j
      _ = C.card + 1 := by simp
  have hmout : m ≤ 2 * (t + 1) + 1 :=
    hmC.trans (Nat.add_le_add_right hCcard 1)
  refine ⟨m, hmout, ?_⟩
  intro R hRmin hRmax
  have hRmin' : C.card + 1 ≤ R := by omega
  have hRmax' : R ≤ q - 2 * C.card - 1 := by
    have hfour : 2 * C.card ≤ 4 * (t + 1) := by omega
    omega
  have htheta' : C.card + 2 ≤ theta := by omega
  obtain ⟨long, E, hEsub, hEcard, hlong, hlongLen,
      hlongLoc, hlongD, hlongB, hlongA⟩ :=
    exists_near_spanning_route_avoiding_scaffold_cuts G hq a b ha hb
      haA hbB hAB hab hba hrob hmajorD C hRmin' hRmax' htheta'
      (hixC 0) (hiyC 0) (by simpa [haix, haiy] using hxy 0)
  have hlongLen' : long.length = 2 * R + 2 * (m + 1) := by
    simpa [m] using hlongLen
  let long' : G.Walk (x 0) (y 0) := long.copy (haix 0) (haiy 0)
  let left : Fin t → V := fun i => x i.succ
  let right : Fin t → V := fun i => y i.succ
  have hpairsD : ∀ i : Fin t, theta ≤
      (Erdos163.FiniteDefect.commonNeighbors G ![left i, right i] D).card := by
    intro i
    simpa [left, right] using hrob (x i.succ) (hx i.succ)
      (y i.succ) (hy i.succ)
  have hbudgetD : E.card + t ≤ theta := by omega
  obtain ⟨z, hzinj, hz⟩ :=
    exists_fresh_middle_vertices_fin G left right hpairsD hbudgetD
  have hzD : ∀ i, z i ∈ D := fun i => (hz i).1
  have hzE : ∀ i, z i ∉ E := fun i => (hz i).2.1
  have hleftz : ∀ i, G.Adj (left i) (z i) := fun i => (hz i).2.2.1
  have hzright : ∀ i, G.Adj (z i) (right i) := fun i => (hz i).2.2.2
  let short (i : Fin t) : G.Walk (x i.succ) (y i.succ) :=
    SimpleGraph.Walk.cons (hleftz i)
      (SimpleGraph.Walk.cons (hzright i) SimpleGraph.Walk.nil)
  have hshortPath : ∀ i, (short i).IsPath := by
    intro i
    have hzx : z i ≠ x i.succ := by
      intro h
      exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hx i.succ)) (h ▸ hzD i)
    have hzy : z i ≠ y i.succ := by
      intro h
      exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hy i.succ)) (h ▸ hzD i)
    simp [short, left, right, SimpleGraph.Walk.cons_isPath_iff,
      hxy i.succ, hzx.symm, hzy]
  have hlongShort : ∀ i, long'.support.Disjoint (short i).support := by
    intro i w hwlong hwshort
    have hw : w = x i.succ ∨ w = z i ∨ w = y i.succ := by
      simpa [short] using hwshort
    rcases hw with rfl | rfl | rfl
    · rcases hlongA (ix i.succ) (hixC i.succ)
          (by simpa [long', haix] using hwlong) with h | h
      · exact (hpairs 0 i.succ (Fin.succ_ne_zero i).symm).1
          (by simpa [haix] using h.symm)
      · exact (hpairs 0 i.succ (Fin.succ_ne_zero i).symm).2.2.1
          (by simpa [haix, haiy] using h.symm)
    · exact hzE i (hlongD (z i) (by simpa [long'] using hwlong) (hzD i))
    · rcases hlongA (iy i.succ) (hiyC i.succ)
          (by simpa [long', haiy] using hwlong) with h | h
      · exact (hpairs 0 i.succ (Fin.succ_ne_zero i).symm).2.1
          (by simpa [haix, haiy] using h.symm)
      · exact (hpairs 0 i.succ (Fin.succ_ne_zero i).symm).2.2.2
          (by simpa [haiy] using h.symm)
  have hshortDisj : ∀ i j, i ≠ j →
      (short i).support.Disjoint (short j).support := by
    intro i j hij w hwi hwj
    have hwi' : w = x i.succ ∨ w = z i ∨ w = y i.succ := by
      simpa [short] using hwi
    have hwj' : w = x j.succ ∨ w = z j ∨ w = y j.succ := by
      simpa [short] using hwj
    have hsne : i.succ ≠ j.succ := by
      intro h
      exact hij (Fin.succ_injective _ h)
    rcases hwi' with hxi | hzi | hyi <;>
      rcases hwj' with hxj | hzj | hyj
    · exact (hpairs i.succ j.succ hsne).1 (hxi.symm.trans hxj)
    · exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hx i.succ))
        (hxi.symm ▸ hzj.symm ▸ hzD j)
    · exact (hpairs i.succ j.succ hsne).2.1 (hxi.symm.trans hyj)
    · exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hx j.succ))
        (hxj.symm ▸ hzi.symm ▸ hzD i)
    · exact hij (hzinj (hzi.symm.trans hzj))
    · exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hy j.succ))
        (hyj.symm ▸ hzi.symm ▸ hzD i)
    · exact (hpairs i.succ j.succ hsne).2.2.1 (hyi.symm.trans hxj)
    · exact (Finset.disjoint_left.mp hmajorD)
        (Finset.mem_union_left _ (hy i.succ))
        (hyi.symm ▸ hzj.symm ▸ hzD j)
    · exact (hpairs i.succ j.succ hsne).2.2.2 (hyi.symm.trans hyj)
  let route : ∀ i : Fin (t + 1), G.Walk (x i) (y i) :=
    Fin.cases long' short
  have hroutePath : ∀ i, (route i).IsPath := by
    intro i
    induction i using Fin.cases with
    | zero =>
        simpa [route, long', SimpleGraph.Walk.isPath_copy] using hlong
    | succ i => simpa [route] using hshortPath i
  have hrouteDisj : ∀ i j, i ≠ j →
      (route i).support.Disjoint (route j).support := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa [route] using hlongShort j
    | succ i =>
        induction j using Fin.cases with
        | zero => simpa [route] using (hlongShort i).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              exact hij (congrArg Fin.succ h)
            simpa [route] using hshortDisj i j hij'
  have hrouteLoc : ∀ i w, w ∈ (route i).support →
      w ∈ A ∪ B ∨ w ∈ D := by
    intro i
    induction i using Fin.cases with
    | zero =>
        simpa [route, long', SimpleGraph.Walk.support_copy] using hlongLoc
    | succ i =>
        intro w hw
        have hw' : w = x i.succ ∨ w = z i ∨ w = y i.succ := by
          simpa [route, short] using hw
        rcases hw' with rfl | rfl | rfl
        · exact Or.inl (Finset.mem_union_left _ (hx i.succ))
        · exact Or.inr (hzD i)
        · exact Or.inl (Finset.mem_union_left _ (hy i.succ))
  refine ⟨route, hroutePath, hrouteDisj, ?_, ?_,
    hrouteLoc, ?_⟩
  · simpa [route, long', SimpleGraph.Walk.length_copy] using hlongLen'
  · intro i
    simp [route, short]
  · intro i j w hspecial hzroute
    have anchor_or_mate :
        w = x j ∨ w = y j ∨
          (∃ d ∈ C, b d = w) := by
      rcases hspecial with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right
        unfold IsCanonicalScaffoldMate at h
        rw [hcanonical] at h
        rcases h with ⟨d, hdz, hda⟩
        have hd : d = ix j := ha (hda.trans (haix j).symm)
        exact ⟨ix j, hixC j, by simpa [hd] using hdz⟩
      · right; right
        unfold IsCanonicalScaffoldMate at h
        rw [hcanonical] at h
        rcases h with ⟨d, hdz, hda⟩
        have hd : d = iy j := ha (hda.trans (haiy j).symm)
        exact ⟨iy j, hiyC j, by simpa [hd] using hdz⟩
    induction i using Fin.cases with
    | zero =>
        rcases anchor_or_mate with h | h | ⟨d, hdC, hdz⟩
        · subst w
          rcases hlongA (ix j) (hixC j)
              (by simpa [route, long', haix] using hzroute) with h | h
          · exact Or.inl (by simpa [haix] using h)
          · exact Or.inr (by simpa [haix, haiy] using h)
        · subst w
          rcases hlongA (iy j) (hiyC j)
              (by simpa [route, long', haiy] using hzroute) with h | h
          · exact Or.inl (by simpa [haix, haiy] using h)
          · exact Or.inr (by simpa [haiy] using h)
        · exact (hlongB d hdC
            (by simpa [route, long', hdz] using hzroute)).elim
    | succ i =>
        have hzshort : w = x i.succ ∨ w = z i ∨ w = y i.succ := by
          simpa [route, short] using hzroute
        rcases anchor_or_mate with hxj | hyj | ⟨d, hdC, hbd⟩
        · rcases hzshort with h | h | h
          · exact Or.inl h
          · exact ((Finset.disjoint_left.mp hmajorD)
              (Finset.mem_union_left _ (hx j))
              (hxj.symm ▸ h.symm ▸ hzD i)).elim
          · exact Or.inr h
        · rcases hzshort with h | h | h
          · exact Or.inl h
          · exact ((Finset.disjoint_left.mp hmajorD)
              (Finset.mem_union_left _ (hy j))
              (hyj.symm ▸ h.symm ▸ hzD i)).elim
          · exact Or.inr h
        · have hbmem : w ∈ B := hbd ▸ hbB d
          rcases hzshort with h | h | h
          · exact ((Finset.disjoint_left.mp hAB) (hx i.succ)
              (h.symm ▸ hbmem)).elim
          · exact ((Finset.disjoint_left.mp hmajorD)
              (Finset.mem_union_right _ hbmem)
              (h.symm ▸ hzD i)).elim
          · exact ((Finset.disjoint_left.mp hAB) (hy i.succ)
              (h.symm ▸ hbmem)).elim

/-- Fintype-indexed form of the repeated-visit routing scheme.  The
distinguished long visit is selected once, before its requested gap length
is supplied; hence the correction `m` is fixed for every admissible `R`. -/
theorem exists_repeated_visit_route_scheme_fintype
    {V J : Type*} [Fintype V] [Fintype J] [Nonempty J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q theta : ℕ} {A B D : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hrob : RobustPairSet G A D theta)
    (hmajorD : Disjoint (A ∪ B) D)
    (htheta : 4 * Fintype.card J + 2 ≤ theta)
    (x y : J → V)
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A)
    (hxy : ∀ i, x i ≠ y i)
    (hpairs : ∀ i j, i ≠ j →
      x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j) :
    ∃ m : ℕ, m ≤ 2 * Fintype.card J + 1 ∧
      ∃ j₀ : J, ∀ R : ℕ,
        2 * Fintype.card J + 1 ≤ R →
        R ≤ q - 4 * Fintype.card J - 1 →
        ∃ route : ∀ j : J, G.Walk (x j) (y j),
          (∀ j, (route j).IsPath) ∧
          (∀ i j, i ≠ j →
            (route i).support.Disjoint (route j).support) ∧
          (route j₀).length = 2 * R + 2 * (m + 1) ∧
          (∀ j, j ≠ j₀ → (route j).length = 2) ∧
          (∀ j w, w ∈ (route j).support →
            w ∈ A ∪ B ∨ w ∈ D) ∧
          ∀ i j w,
            (w = x j ∨ w = y j ∨
              IsCanonicalScaffoldMate G hscaffold w (x j) ∨
              IsCanonicalScaffoldMate G hscaffold w (y j)) →
            w ∈ (route i).support → w = x i ∨ w = y i := by
  classical
  let t : ℕ := Fintype.card J - 1
  have hcardPos : 0 < Fintype.card J := Fintype.card_pos
  have htcard : t + 1 = Fintype.card J := by
    dsimp [t]
    omega
  let e : Fin (t + 1) ≃ J :=
    (finCongr htcard).trans (Fintype.equivFin J).symm
  let x' : Fin (t + 1) → V := fun i => x (e i)
  let y' : Fin (t + 1) → V := fun i => y (e i)
  have htheta' : 4 * (t + 1) + 2 ≤ theta := by
    simpa [htcard] using htheta
  have hx' : ∀ i, x' i ∈ A := fun i => hx (e i)
  have hy' : ∀ i, y' i ∈ A := fun i => hy (e i)
  have hxy' : ∀ i, x' i ≠ y' i := fun i => hxy (e i)
  have hpairs' : ∀ i j, i ≠ j →
      x' i ≠ x' j ∧ x' i ≠ y' j ∧ y' i ≠ x' j ∧ y' i ≠ y' j := by
    intro i j hij
    exact hpairs (e i) (e j) (fun h => hij (e.injective h))
  obtain ⟨m, hm, hscheme⟩ :=
    exists_repeated_visit_routes_via_alternatingScaffold
      G hscaffold hrob hmajorD htheta' x' y' hx' hy' hxy' hpairs'
  let j₀ : J := e 0
  refine ⟨m, by simpa [htcard] using hm, j₀, ?_⟩
  intro R hRmin hRmax
  obtain ⟨r, hrPath, hrDisj, hrLong, hrShort, hrLoc, hrSpecial⟩ :=
    hscheme R (by simpa [htcard] using hRmin)
      (by simpa [htcard] using hRmax)
  let route : ∀ j : J, G.Walk (x j) (y j) := fun j =>
    (r (e.symm j)).copy
      (by simpa [x'] using congrArg x (e.apply_symm_apply j))
      (by simpa [y'] using congrArg y (e.apply_symm_apply j))
  refine ⟨route, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [route, SimpleGraph.Walk.isPath_copy] using hrPath (e.symm j)
  · intro i j hij
    have hij' : e.symm i ≠ e.symm j := fun h =>
      hij (e.symm.injective h)
    simpa [route, SimpleGraph.Walk.support_copy] using
      hrDisj (e.symm i) (e.symm j) hij'
  · have hz : e.symm j₀ = 0 := by simp [j₀]
    simp only [route, SimpleGraph.Walk.length_copy]
    rw [hz]
    exact hrLong
  · intro j hj
    have hj' : e.symm j ≠ 0 := by
      intro h
      apply hj
      apply e.symm.injective
      simpa [j₀] using h
    induction hidx : e.symm j using Fin.cases with
    | zero => exact (hj' hidx).elim
    | succ i =>
        simp only [route, SimpleGraph.Walk.length_copy]
        rw [hidx]
        exact hrShort i
  · intro j w hw
    exact hrLoc (e.symm j) w
      (by simpa [route, SimpleGraph.Walk.support_copy] using hw)
  · intro i j w hspecial hw
    have hspecial' :
        w = x' (e.symm j) ∨ w = y' (e.symm j) ∨
          IsCanonicalScaffoldMate G hscaffold w (x' (e.symm j)) ∨
          IsCanonicalScaffoldMate G hscaffold w (y' (e.symm j)) := by
      simpa [x', y'] using hspecial
    have hout := hrSpecial (e.symm i) (e.symm j) w hspecial'
      (by simpa [route, SimpleGraph.Walk.support_copy] using hw)
    simpa [x', y'] using hout

/-- Hubs which occur in a finite request family. -/
def VisitedHub {J ι : Type*} (hub : J → ι) :=
  {c : ι // ∃ j, hub j = c}

/-- The request fiber belonging to a visited hub. -/
def HubFiber {J ι : Type*} (hub : J → ι) (c : VisitedHub hub) :=
  {j : J // hub j = c.1}

noncomputable instance visitedHubFintype
    {J ι : Type*} [Fintype J] [Fintype ι] (hub : J → ι) :
    Fintype (VisitedHub hub) := by
  change Fintype {c : ι // ∃ j, hub j = c}
  exact Fintype.ofFinite _

noncomputable instance hubFiberFintype
    {J ι : Type*} [Fintype J] (hub : J → ι) (c : VisitedHub hub) :
    Fintype (HubFiber hub c) := by
  change Fintype {j : J // hub j = c.1}
  exact Fintype.ofFinite _

/-
/-- Group the reusable repeated-visit schemes over all hubs that actually
occur.  Routes in different fibers are disjoint by region disjointness;
inside one fiber this is exactly the preceding Fintype scheme. -/
theorem exists_grouped_repeated_visit_route_scheme
    {V J ι : Type*} [Fintype V] [Fintype J] [Fintype ι]
    [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q theta : ℕ} (hub : J → ι)
    (A B D : ι → Finset V)
    (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hrob : ∀ c, RobustPairSet G (A c) (D c) theta)
    (hmajorD : ∀ c, Disjoint (A c ∪ B c) (D c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (htheta : ∀ c : VisitedHub hub,
      4 * Fintype.card (HubFiber hub c) + 2 ≤ theta)
    (x y : J → V)
    (hx : ∀ j, x j ∈ A (hub j)) (hy : ∀ j, y j ∈ A (hub j))
    (hxy : ∀ j, x j ≠ y j)
    (hpairs : ∀ i j, i ≠ j →
      x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j) :
    ∃ m : VisitedHub hub → ℕ,
      (∀ c, m c ≤ 2 * Fintype.card (HubFiber hub c) + 1) ∧
      ∃ j₀ : ∀ c, HubFiber hub c,
      ∀ R : VisitedHub hub → ℕ,
        (∀ c, 2 * Fintype.card (HubFiber hub c) + 1 ≤ R c) →
        (∀ c, R c ≤ q - 4 * Fintype.card (HubFiber hub c) - 1) →
        ∃ route : ∀ j : J, G.Walk (x j) (y j),
          (∀ j, (route j).IsPath) ∧
          (∀ i j, i ≠ j →
            (route i).support.Disjoint (route j).support) ∧
          (∀ c, (route (j₀ c).1).length =
            2 * R c + 2 * (m c + 1)) ∧
          (∀ c (j : HubFiber hub c), j ≠ j₀ c →
            (route j.1).length = 2) ∧
          (∀ j w, w ∈ (route j).support →
            w ∈ A (hub j) ∪ B (hub j) ∨ w ∈ D (hub j)) ∧
          ∀ i j w,
            (w = x j ∨ w = y j ∨
              IsCanonicalScaffoldMate G (hscaffold (hub j)) w (x j) ∨
              IsCanonicalScaffoldMate G (hscaffold (hub j)) w (y j)) →
            w ∈ (route i).support → w = x i ∨ w = y i := by
  classical
  have hfiberNonempty : ∀ c : VisitedHub hub, Nonempty (HubFiber hub c) := by
    intro c
    rcases c.2 with ⟨j, hj⟩
    exact ⟨⟨j, hj⟩⟩
  have hlocal : ∀ c : VisitedHub hub,
      ∃ m : ℕ, m ≤ 2 * Fintype.card (HubFiber hub c) + 1 ∧
        ∃ j₀ : HubFiber hub c, ∀ R : ℕ,
          2 * Fintype.card (HubFiber hub c) + 1 ≤ R →
          R ≤ q - 4 * Fintype.card (HubFiber hub c) - 1 →
          ∃ route : ∀ j : HubFiber hub c,
              G.Walk (x j.1) (y j.1),
            (∀ j : HubFiber hub c, (route j).IsPath) ∧
            (∀ i j : HubFiber hub c, i ≠ j →
              (route i).support.Disjoint (route j).support) ∧
            (route j₀).length = 2 * R + 2 * (m + 1) ∧
            (∀ j : HubFiber hub c, j ≠ j₀ → (route j).length = 2) ∧
            (∀ (j : HubFiber hub c) (w : V), w ∈ (route j).support →
              w ∈ A c.1 ∪ B c.1 ∨ w ∈ D c.1) ∧
            ∀ (i j : HubFiber hub c) (w : V),
              (w = x j.1 ∨ w = y j.1 ∨
                IsCanonicalScaffoldMate G (hscaffold c.1) w (x j.1) ∨
                IsCanonicalScaffoldMate G (hscaffold c.1) w (y j.1)) →
              w ∈ (route i).support → w = x i.1 ∨ w = y i.1 := by
    intro c
    letI : Nonempty (HubFiber hub c) := hfiberNonempty c
    apply exists_repeated_visit_route_scheme_fintype
      G (hscaffold c.1) (hrob c.1) (hmajorD c.1) (htheta c)
        (fun j : HubFiber hub c => x j.1)
        (fun j : HubFiber hub c => y j.1)
    · intro j
      simpa [j.2] using hx j.1
    · intro j
      simpa [j.2] using hy j.1
    · exact fun j => hxy j.1
    · intro i j hij
      exact hpairs i.1 j.1 (fun h => hij (Subtype.ext h))
  choose m hm j₀ hscheme using hlocal
  refine ⟨m, hm, j₀, ?_⟩
  intro R hRmin hRmax
  choose routesAt hlocalPath hlocalDisj hlocalLong hlocalShort
      hlocalLoc hlocalSpecial using fun c : VisitedHub hub =>
    hscheme c (R c) (hRmin c) (hRmax c)
  let owner (j : J) : VisitedHub hub := ⟨hub j, ⟨j, rfl⟩⟩
  let inFiber (j : J) : HubFiber hub (owner j) := ⟨j, rfl⟩
  let route : ∀ j : J, G.Walk (x j) (y j) := fun j =>
    routesAt (owner j) (inFiber j)
  refine ⟨route, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hlocalPath (owner j) (inFiber j)
  · intro i j hij
    by_cases hh : hub i = hub j
    · have howner : owner i = owner j := Subtype.ext hh
      cases howner
      apply hlocalDisj (owner i) (inFiber i) (inFiber j)
      intro h
      exact hij (congrArg Subtype.val h)
    · intro w hwi hwj
      have hwi' : w ∈ (A (hub i) ∪ B (hub i)) ∪ D (hub i) := by
        rcases hlocalLoc (owner i) (inFiber i) w hwi with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      have hwj' : w ∈ (A (hub j) ∪ B (hub j)) ∪ D (hub j) := by
        rcases hlocalLoc (owner j) (inFiber j) w hwj with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      exact Finset.disjoint_left.mp (hregions (hub i) (hub j) hh) hwi' hwj'
  · intro c
    have howner : owner (j₀ c).1 = c := Subtype.ext (j₀ c).2
    change (routesAt (owner (j₀ c).1) (inFiber (j₀ c).1)).length = _
    cases howner
    have hin : inFiber (j₀ c).1 = j₀ c := Subtype.ext rfl
    rw [hin]
    exact hlocalLong c
  · intro c j hj
    have howner : owner j.1 = c := Subtype.ext j.2
    change (routesAt (owner j.1) (inFiber j.1)).length = 2
    cases howner
    have hin : inFiber j.1 = j := Subtype.ext rfl
    rw [hin]
    exact hlocalShort c j hj
  · intro j w hw
    exact hlocalLoc (owner j) (inFiber j) w hw
  · intro i j w hspecial hw
    by_cases hh : hub i = hub j
    · have howner : owner i = owner j := Subtype.ext hh
      let j' : HubFiber hub (owner i) := ⟨j, by simpa [owner] using hh.symm⟩
      have hspecial' :
          w = x j'.1 ∨ w = y j'.1 ∨
            IsCanonicalScaffoldMate G (hscaffold (owner i).1) w (x j'.1) ∨
            IsCanonicalScaffoldMate G (hscaffold (owner i).1) w (y j'.1) := by
        simpa [j', owner, hh] using hspecial
      exact hlocalSpecial (owner i) (inFiber i) j' w hspecial'
        (by simpa [route] using hw)
    · exfalso
      have hwi' : w ∈ (A (hub i) ∪ B (hub i)) ∪ D (hub i) := by
        rcases hlocalLoc (owner i) (inFiber i) w hw with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      have hwjAB : w ∈ A (hub j) ∪ B (hub j) := by
        rcases hspecial with rfl | rfl | h | h
        · exact Finset.mem_union_left _ (hx j)
        · exact Finset.mem_union_left _ (hy j)
        · exact Finset.mem_union_right _
            (IsCanonicalScaffoldMate.mem_left G h)
        · exact Finset.mem_union_right _
            (IsCanonicalScaffoldMate.mem_left G h)
      exact Finset.disjoint_left.mp (hregions (hub i) (hub j) hh) hwi'
        (Finset.mem_union_left _ hwjAB)
-/

/-- The fiber of requests made at a specified hub. -/
def HubRequestFiber {J ι : Type*} (hub : J → ι) (c : ι) :=
  {j : J // hub j = c}

noncomputable instance hubRequestFiberFintype
    {J ι : Type*} [Fintype J] (hub : J → ι) (c : ι) :
    Fintype (HubRequestFiber hub c) := by
  change Fintype {j : J // hub j = c}
  exact Fintype.ofFinite _

/-- Group the reusable repeated-visit schemes over the fibers of an ordinary
hub map.  Empty fibers carry cost zero and are ignored; this formulation
keeps all transports in the nondependent hub type `ι`. -/
theorem exists_grouped_repeated_visit_route_scheme
    {V J ι : Type*} [Fintype V] [Fintype J] [Fintype ι]
    [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q theta : ℕ} (hub : J → ι)
    (A B D : ι → Finset V)
    (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hrob : ∀ c, RobustPairSet G (A c) (D c) theta)
    (hmajorD : ∀ c, Disjoint (A c ∪ B c) (D c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (htheta : ∀ c, Nonempty (HubRequestFiber hub c) →
      4 * Fintype.card (HubRequestFiber hub c) + 2 ≤ theta)
    (x y : J → V)
    (hx : ∀ j, x j ∈ A (hub j)) (hy : ∀ j, y j ∈ A (hub j))
    (hxy : ∀ j, x j ≠ y j)
    (hpairs : ∀ i j, i ≠ j →
      x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j) :
    ∃ m : ι → ℕ,
      (∀ c, Nonempty (HubRequestFiber hub c) →
        m c ≤ 2 * Fintype.card (HubRequestFiber hub c) + 1) ∧
      (∀ c, ¬ Nonempty (HubRequestFiber hub c) → m c = 0) ∧
      ∀ R : ι → ℕ,
        (∀ c, Nonempty (HubRequestFiber hub c) →
          2 * Fintype.card (HubRequestFiber hub c) + 1 ≤ R c) →
        (∀ c, Nonempty (HubRequestFiber hub c) →
          R c ≤ q - 4 * Fintype.card (HubRequestFiber hub c) - 1) →
        ∃ route : ∀ j : J, G.Walk (x j) (y j),
          (∀ j, (route j).IsPath) ∧
          (∀ i j, i ≠ j →
            (route i).support.Disjoint (route j).support) ∧
          (∀ c (hc : Nonempty (HubRequestFiber hub c)),
            ∃ j₀ : HubRequestFiber hub c,
              (route j₀.1).length = 2 * R c + 2 * (m c + 1) ∧
              ∀ j : HubRequestFiber hub c, j ≠ j₀ →
                (route j.1).length = 2) ∧
          (∀ j w, w ∈ (route j).support →
            w ∈ A (hub j) ∪ B (hub j) ∨ w ∈ D (hub j)) ∧
          ∀ i j w,
            (w = x j ∨ w = y j ∨
              IsCanonicalScaffoldMate G (hscaffold (hub j)) w (x j) ∨
              IsCanonicalScaffoldMate G (hscaffold (hub j)) w (y j)) →
            w ∈ (route i).support → w = x i ∨ w = y i := by
  classical
  have hlocal (c : ι) (hc : Nonempty (HubRequestFiber hub c)) :
      ∃ m : ℕ, m ≤ 2 * Fintype.card (HubRequestFiber hub c) + 1 ∧
        ∃ j₀ : HubRequestFiber hub c, ∀ R : ℕ,
          2 * Fintype.card (HubRequestFiber hub c) + 1 ≤ R →
          R ≤ q - 4 * Fintype.card (HubRequestFiber hub c) - 1 →
          ∃ route : ∀ j : HubRequestFiber hub c,
              G.Walk (x j.1) (y j.1),
            (∀ j : HubRequestFiber hub c, (route j).IsPath) ∧
            (∀ i j : HubRequestFiber hub c, i ≠ j →
              (route i).support.Disjoint (route j).support) ∧
            (route j₀).length = 2 * R + 2 * (m + 1) ∧
            (∀ j : HubRequestFiber hub c, j ≠ j₀ → (route j).length = 2) ∧
            (∀ (j : HubRequestFiber hub c) (w : V), w ∈ (route j).support →
              w ∈ A c ∪ B c ∨ w ∈ D c) ∧
            ∀ (i j : HubRequestFiber hub c) (w : V),
              (w = x j.1 ∨ w = y j.1 ∨
                IsCanonicalScaffoldMate G (hscaffold c) w (x j.1) ∨
                IsCanonicalScaffoldMate G (hscaffold c) w (y j.1)) →
              w ∈ (route i).support → w = x i.1 ∨ w = y i.1 := by
    letI : Nonempty (HubRequestFiber hub c) := hc
    apply exists_repeated_visit_route_scheme_fintype
      G (hscaffold c) (hrob c) (hmajorD c) (htheta c hc)
        (fun j : HubRequestFiber hub c => x j.1)
        (fun j : HubRequestFiber hub c => y j.1)
    · intro j
      simpa [j.2] using hx j.1
    · intro j
      simpa [j.2] using hy j.1
    · exact fun j => hxy j.1
    · intro i j hij
      exact hpairs i.1 j.1 (fun h => hij (Subtype.ext h))
  let visited (c : ι) : Prop := Nonempty (HubRequestFiber hub c)
  let m : ι → ℕ := fun c => if hc : visited c then (hlocal c hc).choose else 0
  have hm : ∀ c, Nonempty (HubRequestFiber hub c) →
      m c ≤ 2 * Fintype.card (HubRequestFiber hub c) + 1 := by
    intro c hc
    simpa [m, visited, hc] using (hlocal c hc).choose_spec.1
  have hmempty : ∀ c, ¬ Nonempty (HubRequestFiber hub c) → m c = 0 := by
    intro c hc
    simp [m, visited, hc]
  refine ⟨m, hm, hmempty, ?_⟩
  intro R hRmin hRmax
  have hvisit (j : J) : visited (hub j) := ⟨⟨j, rfl⟩⟩
  have hdata (c : ι) (hc : visited c) :
      ∃ j₀ : HubRequestFiber hub c, ∀ R : ℕ,
        2 * Fintype.card (HubRequestFiber hub c) + 1 ≤ R →
        R ≤ q - 4 * Fintype.card (HubRequestFiber hub c) - 1 →
        ∃ route : ∀ j : HubRequestFiber hub c,
            G.Walk (x j.1) (y j.1),
          (∀ j : HubRequestFiber hub c, (route j).IsPath) ∧
          (∀ i j : HubRequestFiber hub c, i ≠ j →
            (route i).support.Disjoint (route j).support) ∧
          (route j₀).length = 2 * R + 2 * (m c + 1) ∧
          (∀ j : HubRequestFiber hub c, j ≠ j₀ → (route j).length = 2) ∧
          (∀ (j : HubRequestFiber hub c) (w : V), w ∈ (route j).support →
            w ∈ A c ∪ B c ∨ w ∈ D c) ∧
          ∀ (i j : HubRequestFiber hub c) (w : V),
            (w = x j.1 ∨ w = y j.1 ∨
              IsCanonicalScaffoldMate G (hscaffold c) w (x j.1) ∨
              IsCanonicalScaffoldMate G (hscaffold c) w (y j.1)) →
            w ∈ (route i).support → w = x i.1 ∨ w = y i.1 := by
    let m₀ : ℕ := (hlocal c hc).choose
    have hm₀ := (hlocal c hc).choose_spec
    let j₀ : HubRequestFiber hub c := hm₀.2.choose
    have hs := hm₀.2.choose_spec
    have hmc : m c = m₀ := by simp [m, m₀, visited, hc]
    rw [hmc]
    exact ⟨j₀, hs⟩
  choose j₀ scheme using fun c : ι => fun hc : visited c => hdata c hc
  have hchosen (c : ι) (hc : visited c) :=
    scheme c hc (R c) (hRmin c hc) (hRmax c hc)
  choose routesAt routesPath routesDisj routesLong routesShort
      routesLoc routesSpecial using fun c : ι => fun hc : visited c => hchosen c hc
  let route : ∀ j : J, G.Walk (x j) (y j) := fun j =>
    routesAt (hub j) (hvisit j) ⟨j, rfl⟩
  have routesAt_eq (c d : ι) (hc : visited c) (hd : visited d)
      (hcd : c = d) (i : HubRequestFiber hub c)
      (j : HubRequestFiber hub d) (hij : i.1 = j.1) :
      HEq (routesAt c hc i) (routesAt d hd j) := by
    subst d
    have hindex : j = i := Subtype.ext hij.symm
    subst j
    have hproof : hd = hc := Subsingleton.elim _ _
    subst hd
    exact HEq.rfl
  refine ⟨route, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact routesPath (hub j) (hvisit j) ⟨j, rfl⟩
  · intro i j hij
    by_cases hh : hub i = hub j
    · have hne :
          (⟨i, hh⟩ : HubRequestFiber hub (hub j)) ≠ ⟨j, rfl⟩ := by
        intro h
        exact hij (congrArg Subtype.val h)
      have hei : route i =
          routesAt (hub j) (hvisit j) ⟨i, hh⟩ := by
        dsimp [route]
        exact eq_of_heq <| routesAt_eq (hub i) (hub j) (hvisit i) (hvisit j) hh
          ⟨i, rfl⟩ ⟨i, hh⟩ rfl
      rw [hei]
      exact routesDisj (hub j) (hvisit j) ⟨i, hh⟩ ⟨j, rfl⟩ hne
    · intro w hwi hwj
      have hwi' : w ∈ (A (hub i) ∪ B (hub i)) ∪ D (hub i) := by
        rcases routesLoc (hub i) (hvisit i) ⟨i, rfl⟩ w hwi with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      have hwj' : w ∈ (A (hub j) ∪ B (hub j)) ∪ D (hub j) := by
        rcases routesLoc (hub j) (hvisit j) ⟨j, rfl⟩ w hwj with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      exact Finset.disjoint_left.mp (hregions (hub i) (hub j) hh) hwi' hwj'
  · intro c hc
    refine ⟨j₀ c hc, ?_, ?_⟩
    · have heq : route (j₀ c hc).1 = routesAt c hc (j₀ c hc) := by
        dsimp [route]
        exact eq_of_heq <| routesAt_eq (hub (j₀ c hc).1) c
          (hvisit (j₀ c hc).1) hc (j₀ c hc).2
          ⟨(j₀ c hc).1, rfl⟩ (j₀ c hc) rfl
      rw [heq]
      exact routesLong c hc
    · intro j hj
      have heq : route j.1 = routesAt c hc j := by
        dsimp [route]
        exact eq_of_heq <| routesAt_eq (hub j.1) c (hvisit j.1) hc j.2
          ⟨j.1, rfl⟩ j rfl
      rw [heq]
      exact routesShort c hc j hj
  · intro j w hw
    exact routesLoc (hub j) (hvisit j) ⟨j, rfl⟩ w hw
  · intro i j w hspecial hw
    by_cases hh : hub i = hub j
    · have hout := routesSpecial (hub j) (hvisit j)
          (⟨i, hh⟩ : HubRequestFiber hub (hub j)) ⟨j, rfl⟩ w
          (by simpa using hspecial)
          (by
            have hei : route i =
                routesAt (hub j) (hvisit j) ⟨i, hh⟩ := by
              dsimp [route]
              exact eq_of_heq <| routesAt_eq (hub i) (hub j)
                (hvisit i) (hvisit j) hh ⟨i, rfl⟩ ⟨i, hh⟩ rfl
            rw [← hei]
            exact hw)
      simpa using hout
    · exfalso
      have hwi' : w ∈ (A (hub i) ∪ B (hub i)) ∪ D (hub i) := by
        rcases routesLoc (hub i) (hvisit i) ⟨i, rfl⟩ w hw with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      have hwjAB : w ∈ A (hub j) ∪ B (hub j) := by
        rcases hspecial with rfl | rfl | h | h
        · exact Finset.mem_union_left _ (hx j)
        · exact Finset.mem_union_left _ (hy j)
        · exact Finset.mem_union_right _ (IsCanonicalScaffoldMate.mem_left G h)
        · exact Finset.mem_union_right _ (IsCanonicalScaffoldMate.mem_left G h)
      exact Finset.disjoint_left.mp (hregions (hub i) (hub j) hh) hwi'
        (Finset.mem_union_left _ hwjAB)

/-- A finite request family is the sigma type of its nonempty hub fibers. -/
noncomputable def requestSigmaEquiv
    {J ι : Type*} [Fintype J] [Fintype ι] (hub : J → ι) :
    J ≃ Σ c : ι, HubRequestFiber hub c :=
  (Equiv.sigmaFiberEquiv hub).symm

theorem sum_eq_sum_hubFibers
    {J ι M : Type*} [Fintype J] [Fintype ι]
    [AddCommMonoid M] (hub : J → ι) (f : J → M) :
    (∑ j, f j) = ∑ c : ι, ∑ j : HubRequestFiber hub c, f j.1 := by
  classical
  have h := (requestSigmaEquiv hub).sum_comp
    (fun z : Σ c : ι, HubRequestFiber hub c => f z.2.1)
  change (∑ j, f j) =
    ∑ z : Σ c : ι, HubRequestFiber hub c, f z.2.1 at h
  simpa only [Fintype.sum_sigma] using h

/-- The nonzero indices of `Fin L`, in increasing order. -/
def finTailIndex {L : ℕ} (hL : 0 < L) (j : Fin (L - 1)) : Fin L :=
  ⟨j.val + 1, by omega⟩

theorem finTailIndex_injective {L : ℕ} (hL : 0 < L) :
    Function.Injective (finTailIndex hL) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [finTailIndex] at hv
  omega

theorem finTailIndex_ne_zero {L : ℕ} (hL : 0 < L) (j : Fin (L - 1)) :
    finTailIndex hL j ≠ ⟨0, hL⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp [finTailIndex] at hv

theorem sum_fin_eq_head_add_tail {L : ℕ} (hL : 0 < L) (f : Fin L → ℕ) :
    (∑ i, f i) = f ⟨0, hL⟩ +
      ∑ j : Fin (L - 1), f (finTailIndex hL j) := by
  have hcard : L - 1 + 1 = L := by omega
  let e : Fin (L - 1 + 1) ≃ Fin L := finCongr hcard
  have hsum := e.sum_comp f
  rw [Fin.sum_univ_succ] at hsum
  calc
    (∑ i, f i) = f (Fin.cast hcard 0) +
        ∑ j : Fin (L - 1), f (Fin.cast hcard j.succ) := by
      simpa [e] using hsum.symm
    _ = f ⟨0, hL⟩ + ∑ j : Fin (L - 1), f (finTailIndex hL j) := by
      congr 1

/-- Exact total length of a grouped repeated-visit route family. -/
theorem sum_grouped_repeated_route_lengths
    {V J ι : Type*} [Fintype V] [Fintype J] [Fintype ι]
    (G : SimpleGraph V) (hub : J → ι)
    (x y : J → V) (m R : ι → ℕ)
    (route : ∀ j : J, G.Walk (x j) (y j))
    (hmempty : ∀ c, ¬ Nonempty (HubRequestFiber hub c) → m c = 0)
    (hRempty : ∀ c, ¬ Nonempty (HubRequestFiber hub c) → R c = 0)
    (hlength : ∀ c (hc : Nonempty (HubRequestFiber hub c)),
      ∃ j₀ : HubRequestFiber hub c,
        (route j₀.1).length = 2 * R c + 2 * (m c + 1) ∧
        ∀ j : HubRequestFiber hub c, j ≠ j₀ →
          (route j.1).length = 2) :
    (∑ j, (route j).length) =
      2 * ∑ c : ι,
        (R c + m c + Fintype.card (HubRequestFiber hub c)) := by
  classical
  rw [sum_eq_sum_hubFibers hub (fun j => (route j).length)]
  have hfiber : ∀ c : ι,
      (∑ j : HubRequestFiber hub c, (route j.1).length) =
        2 * (R c + m c + Fintype.card (HubRequestFiber hub c)) := by
    intro c
    by_cases hc : Nonempty (HubRequestFiber hub c)
    · obtain ⟨j₀, hlong, hshort⟩ := hlength c hc
      have hdecomp :
          (∑ j : HubRequestFiber hub c, (route j.1).length) =
            (∑ j ∈ (Finset.univ : Finset (HubRequestFiber hub c)).erase j₀,
              (route j.1).length) + (route j₀.1).length := by
        symm
        exact Finset.sum_erase_add _ _ (Finset.mem_univ j₀)
      rw [hdecomp, hlong]
      have herase :
          (∑ j ∈ (Finset.univ : Finset (HubRequestFiber hub c)).erase j₀,
              (route j.1).length) =
            2 * (Fintype.card (HubRequestFiber hub c) - 1) := by
        calc
          _ = ∑ _j ∈
              (Finset.univ : Finset (HubRequestFiber hub c)).erase j₀, 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hshort j (Finset.ne_of_mem_erase hj)
          _ = 2 * (Fintype.card (HubRequestFiber hub c) - 1) := by
            simp [Nat.mul_comm]
      rw [herase]
      have hcardPos : 0 < Fintype.card (HubRequestFiber hub c) :=
        Fintype.card_pos
      omega
    · have hcardZero : Fintype.card (HubRequestFiber hub c) = 0 := by
        by_contra hne
        have hpos : 0 < Fintype.card (HubRequestFiber hub c) :=
          Nat.pos_of_ne_zero hne
        exact hc (Fintype.card_pos_iff.mp hpos)
      have hunivCard :
          (Finset.univ : Finset (HubRequestFiber hub c)).card = 0 := by
        simpa using hcardZero
      have huniv : (Finset.univ : Finset (HubRequestFiber hub c)) = ∅ :=
        Finset.card_eq_zero.mp hunivCard
      simp only [huniv, Finset.sum_empty,
        hcardZero, hmempty c hc, hRempty c hc, add_zero, mul_zero]
  simp_rw [hfiber]
  rw [Finset.mul_sum]

/-- Fintype-indexed exact allocation under coordinatewise upper bounds. -/
theorem exists_fintype_weights_sum_eq_le_fun
    {ι : Type*} [Fintype ι] (cap : ι → ℕ) {z : ℕ}
    (hz : z ≤ ∑ i, cap i) :
    ∃ r : ι → ℕ, (∑ i, r i) = z ∧ ∀ i, r i ≤ cap i := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcap : z ≤ ∑ j : Fin (Fintype.card ι), cap (e j) := by
    have hsum := e.sum_comp cap
    rw [hsum]
    exact hz
  obtain ⟨r, hrsum, hrle⟩ :=
    exists_fin_weights_sum_eq_le_fun (fun j => cap (e j)) hcap
  let r' : ι → ℕ := fun i => r (e.symm i)
  refine ⟨r', ?_, ?_⟩
  · have hsum := e.sum_comp r'
    have her : ∀ j, r' (e j) = r j := by intro j; simp [r']
    calc
      (∑ i, r' i) = ∑ j, r' (e j) := hsum.symm
      _ = ∑ j, r j := by simp only [her]
      _ = z := hrsum
  · intro i
    have hi := hrle (e.symm i)
    simpa [r'] using hi

/-- Exact Fintype allocation between coordinatewise lower and upper bounds. -/
theorem exists_fintype_weights_sum_eq_between
    {ι : Type*} [Fintype ι] (lo hi : ι → ℕ) {z : ℕ}
    (hlohi : ∀ i, lo i ≤ hi i)
    (hlo : (∑ i, lo i) ≤ z) (hhi : z ≤ ∑ i, hi i) :
    ∃ r : ι → ℕ, (∑ i, r i) = z ∧
      ∀ i, lo i ≤ r i ∧ r i ≤ hi i := by
  classical
  let spare : ι → ℕ := fun i => hi i - lo i
  have hsplit : (∑ i, lo i) + ∑ i, spare i = ∑ i, hi i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [spare]
    have hi := hlohi i
    omega
  have hzspare : z - ∑ i, lo i ≤ ∑ i, spare i := by omega
  obtain ⟨w, hwsum, hwle⟩ :=
    exists_fintype_weights_sum_eq_le_fun spare hzspare
  let r : ι → ℕ := fun i => lo i + w i
  refine ⟨r, ?_, ?_⟩
  · rw [show (∑ i, r i) = (∑ i, lo i) + ∑ i, w i by
        simp [r, Finset.sum_add_distrib]]
    rw [hwsum]
    omega
  · intro i
    constructor
    · simp [r]
    · dsimp [r]
      have hi := hwle i
      have hbound := hlohi i
      dsimp [spare] at hi
      omega

/-- The request-fiber cardinalities partition the whole request type. -/
theorem sum_card_hubRequestFibers
    {J ι : Type*} [Fintype J] [Fintype ι] (hub : J → ι) :
    (∑ c : ι, Fintype.card (HubRequestFiber hub c)) = Fintype.card J := by
  have h := sum_eq_sum_hubFibers hub (fun _j : J => (1 : ℕ))
  simpa using h.symm

/-- The anchor/mate invariant exported by the repeated-hub router is exactly
the external-intersection invariant required by the cyclic path-handle
assembler. -/
theorem internal_routes_meet_path_handles_only_at_incident_endpoints
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) {L : ℕ} (hL : 2 ≤ L)
    (hub : Fin L → ι) (A B D : ι → Finset V)
    {q : ℕ} (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (x y : Fin L → V)
    (h : ∀ e : Fin L, G.Walk (x e) (y e))
    (hhMate : ∀ e z, z ∈ (h e).support →
      z = x e ∨ IsCanonicalScaffoldMate G (hscaffold (hub e)) z (x e) ∨
      z = y e ∨ IsCanonicalScaffoldMate G
        (hscaffold (hub (finCyclicSucc (by omega : 0 < L) e))) z (y e))
    (ha : ∀ i, y (finCyclicPred (by omega : 0 < L) i) ∈ A (hub i))
    (hb : ∀ i, x i ∈ A (hub i))
    (hpairs : ∀ i j, i ≠ j →
      y (finCyclicPred (by omega : 0 < L) i) ≠
          y (finCyclicPred (by omega : 0 < L) j) ∧
      y (finCyclicPred (by omega : 0 < L) i) ≠ x j ∧
      x i ≠ y (finCyclicPred (by omega : 0 < L) j) ∧
      x i ≠ x j)
    (r : ∀ i : Fin L,
      G.Walk (y (finCyclicPred (by omega : 0 < L) i)) (x i))
    (hrSpecial : ∀ i j z,
      (z = y (finCyclicPred (by omega : 0 < L) j) ∨ z = x j ∨
        IsCanonicalScaffoldMate G (hscaffold (hub j)) z
          (y (finCyclicPred (by omega : 0 < L) j)) ∨
        IsCanonicalScaffoldMate G (hscaffold (hub j)) z (x j)) →
      z ∈ (r i).support →
      z = y (finCyclicPred (by omega : 0 < L) i) ∨ z = x i) :
    ∀ i e z, z ∈ (r i).support → z ∈ (h e).support →
      (e = finCyclicPred (by omega : 0 < L) i ∧ z = y e) ∨
        (e = i ∧ z = x e) := by
  classical
  let pred : Fin L → Fin L := finCyclicPred (by omega)
  let next : Fin L → Fin L := finCyclicSucc (by omega)
  have hpredNext : ∀ e, pred (next e) = e := by
    intro e
    exact finCyclicPred_finCyclicSucc (by omega) e
  have hmateAnchorImpossible : ∀ i j z,
      IsCanonicalScaffoldMate G (hscaffold (hub j)) z
        (y (pred j)) ∨
      IsCanonicalScaffoldMate G (hscaffold (hub j)) z (x j) →
      z = y (pred i) ∨ z = x i → False := by
    intro i j z hz hout
    have hzB : z ∈ B (hub j) := hz.elim
      (IsCanonicalScaffoldMate.mem_left G)
      (IsCanonicalScaffoldMate.mem_left G)
    have hzA : z ∈ A (hub i) := by
      rcases hout with h | h
      · exact h ▸ ha i
      · exact h ▸ hb i
    by_cases hij : hub i = hub j
    · exact (Finset.disjoint_left.mp (by
          rcases hscaffold (hub i) with ⟨_, _, _, _, _, _, _, hAB, _, _⟩
          exact hAB)) hzA (by simpa [hij] using hzB)
    · exact Finset.disjoint_left.mp (hregions (hub i) (hub j) hij)
        (Finset.mem_union_left _ (Finset.mem_union_left _ hzA))
        (Finset.mem_union_left _ (Finset.mem_union_right _ hzB))
  intro i e z hzR hzH
  rcases hhMate e z hzH with hxz | hmx | hyz | hmy
  · have hout := hrSpecial i e z (Or.inr (Or.inl hxz)) hzR
    have hei : e = i := by
      by_contra hne
      rcases hout with hout | hout
      · exact (hpairs e i hne).2.2.1 (hxz.symm.trans hout)
      · exact (hpairs e i hne).2.2.2 (hxz.symm.trans hout)
    exact Or.inr ⟨hei, hxz⟩
  · exact (hmateAnchorImpossible i e z (Or.inr hmx)
      (hrSpecial i e z (Or.inr (Or.inr (Or.inr hmx))) hzR)).elim
  · let j : Fin L := next e
    have haEq : y e = y (pred j) := by simp [j, hpredNext]
    have hout := hrSpecial i j z (Or.inl (hyz.trans haEq)) hzR
    have hij : i = j := by
      by_contra hne
      have hne' : j ≠ i := Ne.symm hne
      rcases hout with hout | hout
      · exact (hpairs j i hne').1
          (by simpa [haEq] using hyz.symm.trans hout)
      · exact (hpairs j i hne').2.1
          (by simpa [haEq] using hyz.symm.trans hout)
    left
    refine ⟨?_, hyz⟩
    rw [hij]
    change e = pred (next e)
    exact (hpredNext e).symm
  · let j : Fin L := next e
    have hm' : IsCanonicalScaffoldMate G (hscaffold (hub j)) z
        (y (pred j)) := by
      simpa [j, hpredNext] using hmy
    exact (hmateAnchorImpossible i j z (Or.inl hm')
      (hrSpecial i j z (Or.inr (Or.inr (Or.inl hm'))) hzR)).elim

/-- A cyclic selected-handle family whose initial hub is not revisited can be
completed by one parity-breaking root route and the reusable grouped
repeated-visit schemes at all remaining hubs.  The correction `corr` is
chosen before either the root length or the per-hub scales are supplied. -/
theorem cycleGraph_isContained_of_grouped_repeated_routes_and_handles
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m q theta k : ℕ} (hm : 1 ≤ m) (hub : Fin (m + 1) → ι)
    (hrootFresh : ∀ j : Fin m, hub j.succ ≠ hub 0)
    (A B D : ι → Finset V)
    (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hrob : ∀ c, RobustPairSet G (A c) (D c) theta)
    (hmajorD : ∀ c, Disjoint (A c ∪ B c) (D c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (htheta : ∀ c,
      Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
        4 * Fintype.card
            (HubRequestFiber (fun j : Fin m => hub j.succ) c) + 2 ≤ theta)
    (hmatch : HasThreeDisjointAdjPairFamily G (A (hub 0)))
    (x y : Fin (m + 1) → V)
    (h : ∀ e : Fin (m + 1), G.Walk (x e) (y e))
    (hhPath : ∀ e, (h e).IsPath)
    (hhNonempty : ∀ e, 1 ≤ (h e).length)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (hhMate : ∀ e z, z ∈ (h e).support →
      z = x e ∨ IsCanonicalScaffoldMate G (hscaffold (hub e)) z (x e) ∨
      z = y e ∨ IsCanonicalScaffoldMate G
        (hscaffold (hub (finCyclicSucc (by omega : 0 < m + 1) e))) z (y e))
    (ha : ∀ i,
      y (finCyclicPred (by omega : 0 < m + 1) i) ∈ A (hub i))
    (hb : ∀ i, x i ∈ A (hub i))
    (hab : ∀ i, y (finCyclicPred (by omega : 0 < m + 1) i) ≠ x i)
    (hpairs : ∀ i j, i ≠ j →
      y (finCyclicPred (by omega : 0 < m + 1) i) ≠
          y (finCyclicPred (by omega : 0 < m + 1) j) ∧
      y (finCyclicPred (by omega : 0 < m + 1) i) ≠ x j ∧
      x i ≠ y (finCyclicPred (by omega : 0 < m + 1) j) ∧
      x i ≠ x j)
    (hk : 3 ≤ k) :
    ∃ corr : ι → ℕ,
      (∀ c,
        Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
          corr c ≤ 2 * Fintype.card
            (HubRequestFiber (fun j : Fin m => hub j.succ) c) + 1) ∧
      (∀ c,
        ¬ Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
          corr c = 0) ∧
      ∀ (ell : ℕ) (R : ι → ℕ),
        5 ≤ ell → ell ≤ (A (hub 0)).card → ell + 1 ≤ theta →
        (∀ c,
          ¬ Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
            R c = 0) →
        (∀ c,
          Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
            2 * Fintype.card
                (HubRequestFiber (fun j : Fin m => hub j.succ) c) + 1 ≤ R c) →
        (∀ c,
          Nonempty (HubRequestFiber (fun j : Fin m => hub j.succ) c) →
            R c ≤ q - 4 * Fintype.card
                (HubRequestFiber (fun j : Fin m => hub j.succ) c) - 1) →
        (∑ e : Fin (m + 1), (h e).length) + ell +
            2 * ∑ c : ι,
              (R c + corr c + Fintype.card
                (HubRequestFiber (fun j : Fin m => hub j.succ) c)) = k →
        _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  let pred : Fin (m + 1) → Fin (m + 1) := finCyclicPred (by omega)
  let next : Fin (m + 1) → Fin (m + 1) := finCyclicSucc (by omega)
  let ar : Fin (m + 1) → V := fun i => y (pred i)
  let br : Fin (m + 1) → V := x
  let tailHub : Fin m → ι := fun j => hub j.succ
  let arTail : Fin m → V := fun j => ar j.succ
  let brTail : Fin m → V := fun j => br j.succ
  obtain ⟨corr, hcorr, hcorrEmpty, hscheme⟩ :=
    exists_grouped_repeated_visit_route_scheme
      G tailHub A B D hscaffold hrob hmajorD hregions htheta
        arTail brTail
        (fun j => by simpa [arTail, tailHub, ar, pred] using ha j.succ)
        (fun j => by simpa [brTail, tailHub, br] using hb j.succ)
        (fun j => by simpa [arTail, brTail, ar, br, pred] using hab j.succ)
        (fun i j hij => by
          have hsij : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
          simpa [arTail, brTail, ar, br, pred] using hpairs i.succ j.succ hsij)
  refine ⟨corr, hcorr, hcorrEmpty, ?_⟩
  intro ell R hell hellA hellTheta hRempty hRmin hRmax hlen
  obtain ⟨M, hM, hMcard, hMA⟩ := hmatch
  let F : Finset V := {ar 0, br 0}
  have hFcard : F.card < M.card := by
    have htwo : F.card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨e, heM, he₁F, he₂F, heAdj⟩ :=
    exists_adjPair_avoiding_of_disjointAdjPairFamily G M F hM hFcard
  have heA := hMA e heM
  have he₁data : e.1 ≠ ar 0 ∧ e.1 ≠ br 0 := by
    simpa [F] using he₁F
  have he₂data : e.2 ≠ ar 0 ∧ e.2 ≠ br 0 := by
    simpa [F] using he₂F
  obtain ⟨p₀, hp₀Path, hp₀Len, hp₀Loc⟩ :=
    exists_path_between_of_robustPairSet_and_parity_edge G
      (hrob (hub 0)) (by simpa [ar, pred] using ha 0) heA.1 heA.2
      (by simpa [br] using hb 0) heAdj
      he₁data.1.symm he₂data.1.symm
      (by simpa [ar, br, pred] using hab 0)
      he₁data.2 he₂data.2 hell hellA hellTheta
  obtain ⟨pTail, hpTailPath, hpTailDisj, hpTailLength,
      hpTailLoc, hpTailSpecial⟩ :=
    hscheme R hRmin hRmax
  have hpTailSum : (∑ j : Fin m, (pTail j).length) =
      2 * ∑ c : ι,
        (R c + corr c + Fintype.card (HubRequestFiber tailHub c)) := by
    exact sum_grouped_repeated_route_lengths G tailHub arTail brTail corr R
      pTail hcorrEmpty hRempty hpTailLength
  have hp₀Tail : ∀ j,
      p₀.support.Disjoint (pTail j).support := by
    intro j z hz₀ hzj
    have hz₀' : z ∈ (A (hub 0) ∪ B (hub 0)) ∪ D (hub 0) := by
      rcases hp₀Loc z hz₀ with hz | hz
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
      · exact Finset.mem_union_right _ hz
    have hzj' : z ∈ (A (hub j.succ) ∪ B (hub j.succ)) ∪ D (hub j.succ) := by
      rcases hpTailLoc j z hzj with hz | hz
      · exact Finset.mem_union_left _ (by simpa [tailHub] using hz)
      · exact Finset.mem_union_right _ (by simpa [tailHub] using hz)
    exact Finset.disjoint_left.mp
      (hregions (hub 0) (hub j.succ) (Ne.symm (hrootFresh j))) hz₀' hzj'
  let route : ∀ i : Fin (m + 1), G.Walk (ar i) (br i) :=
    Fin.cases p₀ pTail
  have hroutePath : ∀ i, (route i).IsPath := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [route] using hp₀Path
    | succ j => simpa [route, arTail, brTail] using hpTailPath j
  have hrouteDisj : ∀ i j, i ≠ j →
      (route i).support.Disjoint (route j).support := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa [route] using hp₀Tail j
    | succ i =>
        induction j using Fin.cases with
        | zero => simpa [route] using (hp₀Tail i).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              exact hij (congrArg Fin.succ h)
            simpa [route] using hpTailDisj i j hij'
  have hrouteSpecial : ∀ i j z,
      (z = ar j ∨ z = br j ∨
        IsCanonicalScaffoldMate G (hscaffold (hub j)) z (ar j) ∨
        IsCanonicalScaffoldMate G (hscaffold (hub j)) z (br j)) →
      z ∈ (route i).support → z = ar i ∨ z = br i := by
    intro i j z hspecial hzroute
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero =>
            rcases hspecial with hza | hzb | hma | hmb
            · exact Or.inl hza
            · exact Or.inr hzb
            · exfalso
              have hzB := IsCanonicalScaffoldMate.mem_left G hma
              rcases hp₀Loc z (by simpa [route] using hzroute) with hzA | hzD
              · rcases hscaffold (hub 0) with ⟨_, _, _, _, _, _, _, hAB, _, _⟩
                exact Finset.disjoint_left.mp hAB hzA hzB
              · exact Finset.disjoint_left.mp (hmajorD (hub 0))
                  (Finset.mem_union_right _ hzB) hzD
            · exfalso
              have hzB := IsCanonicalScaffoldMate.mem_left G hmb
              rcases hp₀Loc z (by simpa [route] using hzroute) with hzA | hzD
              · rcases hscaffold (hub 0) with ⟨_, _, _, _, _, _, _, hAB, _, _⟩
                exact Finset.disjoint_left.mp hAB hzA hzB
              · exact Finset.disjoint_left.mp (hmajorD (hub 0))
                  (Finset.mem_union_right _ hzB) hzD
        | succ j =>
            exfalso
            have hz₀ : z ∈ (A (hub 0) ∪ B (hub 0)) ∪ D (hub 0) := by
              rcases hp₀Loc z (by simpa [route] using hzroute) with hz | hz
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
              · exact Finset.mem_union_right _ hz
            have hzj : z ∈ (A (hub j.succ) ∪ B (hub j.succ)) ∪ D (hub j.succ) := by
              apply Finset.mem_union_left
              rcases hspecial with rfl | rfl | hz | hz
              · exact Finset.mem_union_left _ (by simpa only [ar] using ha j.succ)
              · exact Finset.mem_union_left _ (by simpa only [br] using hb j.succ)
              · exact Finset.mem_union_right _
                  (IsCanonicalScaffoldMate.mem_left G hz)
              · exact Finset.mem_union_right _
                  (IsCanonicalScaffoldMate.mem_left G hz)
            exact Finset.disjoint_left.mp
              (hregions (hub 0) (hub j.succ) (Ne.symm (hrootFresh j))) hz₀ hzj
    | succ i =>
        induction j using Fin.cases with
        | zero =>
            exfalso
            have hzi : z ∈ (A (hub i.succ) ∪ B (hub i.succ)) ∪ D (hub i.succ) := by
              rcases hpTailLoc i z (by simpa [route] using hzroute) with hz | hz
              · exact Finset.mem_union_left _ (by simpa [tailHub] using hz)
              · exact Finset.mem_union_right _ (by simpa [tailHub] using hz)
            have hz₀ : z ∈ (A (hub 0) ∪ B (hub 0)) ∪ D (hub 0) := by
              apply Finset.mem_union_left
              rcases hspecial with rfl | rfl | hz | hz
              · exact Finset.mem_union_left _ (by simpa [ar] using ha 0)
              · exact Finset.mem_union_left _ (by simpa [br] using hb 0)
              · exact Finset.mem_union_right _
                  (IsCanonicalScaffoldMate.mem_left G hz)
              · exact Finset.mem_union_right _
                  (IsCanonicalScaffoldMate.mem_left G hz)
            exact Finset.disjoint_left.mp
              (hregions (hub i.succ) (hub 0) (hrootFresh i)) hzi hz₀
        | succ j =>
            have hout := hpTailSpecial i j z
              (by simpa [arTail, brTail, tailHub] using hspecial)
              (by simpa [route] using hzroute)
            simpa [arTail, brTail] using hout
  have hrExternal : ∀ i e z, z ∈ (route i).support → z ∈ (h e).support →
      (e = pred i ∧ z = y e) ∨ (e = i ∧ z = x e) := by
    simpa [ar, br, pred, next] using
      (internal_routes_meet_path_handles_only_at_incident_endpoints
        G (by omega : 2 ≤ m + 1) hub A B D hscaffold hregions x y h hhMate
          ha hb hpairs route (by simpa [ar, br, pred] using hrouteSpecial))
  have hrouteSum : (∑ i : Fin (m + 1), (route i).length) =
      ell + 2 * ∑ c : ι,
        (R c + corr c + Fintype.card (HubRequestFiber tailHub c)) := by
    rw [Fin.sum_univ_succ]
    simp only [route, Fin.cases_zero, Fin.cases_succ, hp₀Len]
    exact congrArg (ell + ·) hpTailSum
  let S : ℕ := ∑ e : Fin (m + 1), (h e).length
  have htailSum :
      (∑ i : Fin (m + 1), (h (pred i)).tail.length) + (m + 1) = S := by
    calc
      (∑ i : Fin (m + 1), (h (pred i)).tail.length) + (m + 1) =
          ∑ i : Fin (m + 1), ((h (pred i)).tail.length + 1) := by
            simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin (m + 1), (h (pred i)).length := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (h (pred i)).length_tail_add_one (by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          exact hhNonempty (pred i))
      _ = S := by
        let ep : Fin (m + 1) ≃ Fin (m + 1) :=
          Equiv.ofBijective pred ⟨finCyclicPred_injective (by omega), by
            intro e
            exact ⟨next e, finCyclicPred_finCyclicSucc (by omega) e⟩⟩
        have hsum := ep.sum_comp (fun e : Fin (m + 1) => (h e).length)
        change (∑ i : Fin (m + 1), (h (pred i)).length) =
          ∑ e : Fin (m + 1), (h e).length at hsum
        simpa [S] using hsum
  have htotal :
      (∑ i : Fin (m + 1),
        ((h (pred i)).tail.append (route i)).length) + (m + 1) = k := by
    simp_rw [SimpleGraph.Walk.length_append]
    rw [Finset.sum_add_distrib, hrouteSum]
    dsimp [S] at htailSum
    simpa [tailHub] using (by omega :
      (∑ i : Fin (m + 1), (h (pred i)).tail.length) +
          (ell + 2 * ∑ c : ι,
            (R c + corr c + Fintype.card
              (HubRequestFiber (fun j : Fin m => hub j.succ) c))) +
          (m + 1) = k)
  apply cycleGraph_isContained_of_disjoint_path_handles_and_internal_routes_val
    G (by omega : 2 ≤ m + 1) hk x y h hhPath hhNonempty hhDisj route
      hroutePath hrouteDisj (by simpa [pred] using hrExternal)
  · have heq :
        (∑ i : Fin (m + 1),
          ((h (pred i)).tail.append (route i)).length) + (m + 1 - 1) =
            k - 1 := by omega
    rw [heq]
    omega
  · simpa [pred] using htotal

/-- Closed-walk interface to the grouped repeated-hub assembler.  Selected
full-core handles are chosen globally first.  Their total length `S` and all
gap corrections are then exposed, together with sharp elementary bounds, so
that a later numerical allocation can choose the exact target length. -/
theorem exists_closed_walk_grouped_repeated_route_scheme
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) {u : ι} (w : H.Walk u u)
    {m q theta R k : ℕ} (hwlen : w.length = m + 1) (hm : 1 ≤ m)
    (hwfresh : ∀ j : Fin m, w.getVert (j.val + 1) ≠ u)
    (A B D : ι → Finset V)
    (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hrob : ∀ c, RobustPairSet G (A c) (D c) theta)
    (hmajorD : ∀ c, Disjoint (A c ∪ B c) (D c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (htheta : ∀ c,
      Nonempty
        (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
      4 * Fintype.card
          (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) + 2 ≤
        theta)
    (hmatch : HasThreeDisjointAdjPairFamily G (A u))
    (hhandleBudget : 4 * w.length < R / 4)
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hk : 3 ≤ k) :
    ∃ S : ℕ, ∃ corr : ι → ℕ,
      m + 1 ≤ S ∧ S ≤ 3 * (m + 1) ∧
      (∀ c,
        Nonempty
            (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
          corr c ≤ 2 * Fintype.card
            (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) + 1) ∧
      (∀ c,
        ¬ Nonempty
            (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
          corr c = 0) ∧
      ∀ (ell : ℕ) (scale : ι → ℕ),
        5 ≤ ell → ell ≤ (A u).card → ell + 1 ≤ theta →
        (∀ c,
          ¬ Nonempty
              (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
            scale c = 0) →
        (∀ c,
          Nonempty
              (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
            2 * Fintype.card
                (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) +
              1 ≤ scale c) →
        (∀ c,
          Nonempty
              (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) →
            scale c ≤ q - 4 * Fintype.card
                (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c) -
              1) →
        S + ell + 2 * ∑ c : ι,
            (scale c + corr c + Fintype.card
              (HubRequestFiber (fun j : Fin m => w.getVert (j.val + 1)) c)) =
          k →
        _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  have hwlong : 2 ≤ w.length := by omega
  obtain ⟨xc, yc, hc, hhc, hinc, hhcDisj, _hhEmpty, hhcMate⟩ :=
    exists_cyclic_selected_path_handles_along_closed_walk_avoiding
      G H A B hscaffold
        (fun i j hij => (hregions i j hij).mono
          Finset.subset_union_left Finset.subset_union_left)
        ∅ w hwlong (by simpa using hhandleBudget) hlarge
  let toWalk : Fin (m + 1) → Fin w.length := fun i => Fin.cast hwlen.symm i
  let hub : Fin (m + 1) → ι := fun i => w.getVert i.val
  let x : Fin (m + 1) → V := fun i => xc (toWalk i)
  let y : Fin (m + 1) → V := fun i => yc (toWalk i)
  let h : ∀ i : Fin (m + 1), G.Walk (x i) (y i) :=
    fun i => hc (toWalk i)
  let pred : Fin (m + 1) → Fin (m + 1) := finCyclicPred (by omega)
  let next : Fin (m + 1) → Fin (m + 1) := finCyclicSucc (by omega)
  have htoPred : ∀ i, toWalk (pred i) =
      finCyclicPred (by omega : 0 < w.length) (toWalk i) := by
    intro i
    apply Fin.ext
    by_cases hi : i.val = 0
    · simp [toWalk, pred, finCyclicPred, hwlen, hi]
    · simp [toWalk, pred, finCyclicPred, hwlen, hi]
  have hpredNext : ∀ i, pred (next i) = i := by
    intro i
    exact finCyclicPred_finCyclicSucc (by omega) i
  have hnextGet : ∀ i,
      w.getVert (next i).val = w.getVert (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < m + 1
    · have hmod : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt hi
      simp [next, finCyclicSucc, hmod]
    · have hiTop : i.val + 1 = m + 1 := by omega
      have hnextZero : (next i).val = 0 := by
        simp [next, finCyclicSucc, hiTop]
      rw [hnextZero, hiTop, ← hwlen, w.getVert_zero, w.getVert_length]
  have hh : ∀ i,
      x i ∈ A (hub i) ∧
      y i ∈ A (w.getVert (i.val + 1)) ∧
      (h i).IsPath ∧ 1 ≤ (h i).length ∧ (h i).length ≤ 3 := by
    intro i
    have hi := hhc (toWalk i)
    simpa [x, y, h, hub, toWalk] using hi
  have hin : ∀ i, y (pred i) ∈ A (hub i) := by
    intro i
    have hi := hinc (toWalk i)
    rw [← htoPred i] at hi
    have hval : (toWalk i).val = i.val := rfl
    rw [hval] at hi
    simpa [y, hub] using hi
  have hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support := by
    intro i j hij
    apply hhcDisj (toWalk i) (toWalk j)
    intro heq
    apply hij
    apply Fin.ext
    simpa [toWalk] using congrArg Fin.val heq
  have hhMate : ∀ i z, z ∈ (h i).support →
      z = x i ∨ IsCanonicalScaffoldMate G (hscaffold (hub i)) z (x i) ∨
      z = y i ∨ IsCanonicalScaffoldMate G (hscaffold (hub (next i))) z (y i) := by
    intro i z hz
    rcases hhcMate (toWalk i) z (by simpa [h] using hz) with hz | hz | hz | hz
    · exact Or.inl (by simpa [x] using hz)
    · exact Or.inr (Or.inl (by simpa [x, hub, toWalk] using hz))
    · exact Or.inr (Or.inr (Or.inl (by simpa [y] using hz)))
    · right; right; right
      have hval : (toWalk i).val = i.val := rfl
      rw [hval, ← hnextGet i] at hz
      simpa [y, hub, toWalk] using hz
  obtain ⟨hab, hpairs⟩ :=
    cyclic_path_handle_endpoints_pairwise
      (by omega : 2 ≤ m + 1) x y h
      (fun i => (hh i).2.2.1) (fun i => (hh i).2.2.2.1) hhDisj
  let S : ℕ := ∑ i : Fin (m + 1), (h i).length
  have hSlower : m + 1 ≤ S := by
    calc
      m + 1 = ∑ _i : Fin (m + 1), 1 := by simp
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (hh i).2.2.2.1
  have hSupper : S ≤ 3 * (m + 1) := by
    calc
      S ≤ ∑ _i : Fin (m + 1), 3 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (hh i).2.2.2.2
      _ = 3 * (m + 1) := by simp [Nat.mul_comm]
  have hroot : hub 0 = u := by simp [hub]
  have hrootFresh' : ∀ j : Fin m, hub j.succ ≠ hub 0 := by
    intro j
    simpa [hub] using hwfresh j
  obtain ⟨corr, hcorr, hcorrEmpty, hcomplete⟩ :=
    cycleGraph_isContained_of_grouped_repeated_routes_and_handles
      G hm hub hrootFresh' A B D hscaffold hrob hmajorD hregions
        (by simpa [hub] using htheta)
        (by simpa [hroot] using hmatch) x y h
        (fun i => (hh i).2.2.1) (fun i => (hh i).2.2.2.1) hhDisj
        (by simpa [next] using hhMate) hin (fun i => (hh i).1)
        (by simpa [pred] using hab) (by simpa [pred] using hpairs) hk
  refine ⟨S, corr, hSlower, hSupper, ?_, ?_, ?_⟩
  · simpa [hub] using hcorr
  · simpa [hub] using hcorrEmpty
  · intro ell scale hell hellA hellTheta hscaleEmpty hscaleMin hscaleMax hlen
    apply hcomplete ell scale hell
      (by simpa [hroot] using hellA) hellTheta
      (by simpa [hub] using hscaleEmpty)
      (by simpa [hub] using hscaleMin)
      (by simpa [hub] using hscaleMax)
    simpa [S, hub] using hlen

/-- An arbitrary connected auxiliary graph on at least `t` full alternating
cores forces the target cycle once the repeated-visit and total-capacity
budgets fit.  No auxiliary maximum-degree hypothesis is used. -/
theorem cycleGraph_isContained_of_connected_largeFullCoreMatching_repeated_of_card_ge
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph ι) {t q theta R k : ℕ}
    (hconn : H.Connected) (ht : 2 ≤ t) (htcard : t ≤ Fintype.card ι)
    (A B D : ι → Finset V)
    (hscaffold : ∀ c, IsCyclicAlternatingScaffold G q (A c) (B c))
    (hrob : ∀ c, RobustPairSet G (A c) (D c) theta)
    (hmajorD : ∀ c, Disjoint (A c ∪ B c) (D c))
    (hregions : ∀ c d, c ≠ d →
      Disjoint ((A c ∪ B c) ∪ D c) ((A d ∪ B d) ∪ D d))
    (hAcard : ∀ c, (A c).card = q)
    (hmatch : ∀ c, HasThreeDisjointAdjPairFamily G (A c))
    (htheta : 4 * (2 * (t - 1) - 1) + 3 ≤ theta)
    (hqLocal : 6 * (2 * (t - 1) - 1) + 2 ≤ q)
    (hhandleBudget : 8 * (t - 1) < R / 4)
    (hlarge : ∀ i j, H.Adj i j →
      HasCrossMatchingAtLeast G (A i ∪ B i) (A j ∪ B j) R)
    (hk : 3 ≤ k)
    (hbase : 18 * (2 * (t - 1)) ≤ k)
    (hcapacity : k / 2 ≤
      (t - 1) * (q - 4 * (2 * (t - 1) - 1) - 1)) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  obtain ⟨u, w, hwlen, hwsupp, hwfresh⟩ :=
    Erdos551.SimpleGraph.Connected.exists_closed_walk_length_twice_sub_one_fresh_root_of_le_card
      H hconn (by omega) htcard
  let visits : ℕ := w.length - 1
  have hvisitsEq : visits = 2 * (t - 1) - 1 := by
    dsimp [visits]
    rw [hwlen]
  have hvisits : 1 ≤ visits := by rw [hvisitsEq]; omega
  have hwlen' : w.length = visits + 1 := by
    dsimp [visits]
    omega
  have hwfresh' : ∀ j : Fin visits, w.getVert (j.val + 1) ≠ u := by
    simpa [visits] using hwfresh
  let tailHub : Fin visits → ι := fun j => w.getVert (j.val + 1)
  obtain ⟨S, corr, hSlower, hSupper, hcorr, hcorrEmpty, hcomplete⟩ :=
    exists_closed_walk_grouped_repeated_route_scheme
      G H w hwlen' hvisits hwfresh' A B D hscaffold hrob hmajorD hregions
        (by
          intro c hc
          have hcard : Fintype.card
              (HubRequestFiber (fun j : Fin visits => w.getVert (j.val + 1)) c) ≤
                visits := by
            calc
              Fintype.card
                  (HubRequestFiber (fun j : Fin visits => w.getVert (j.val + 1)) c) ≤
                  Fintype.card (Fin visits) := by
                    apply Fintype.card_le_of_injective
                      (fun z : HubRequestFiber
                        (fun j : Fin visits => w.getVert (j.val + 1)) c => z.1)
                    intro a b hab
                    exact Subtype.ext hab
              _ = visits := Fintype.card_fin visits
          have htheta' : 4 * visits + 3 ≤ theta := by
            simpa [hvisitsEq] using htheta
          omega)
        (hmatch u) (by rw [hwlen]; omega) hlarge hk
  let count : ι → ℕ := fun c => Fintype.card (HubRequestFiber tailHub c)
  have hcountSum : (∑ c : ι, count c) = visits := by
    simpa [count] using sum_card_hubRequestFibers tailHub
  have hcountLe : ∀ c, count c ≤ visits := by
    intro c
    dsimp [count]
    calc
      Fintype.card (HubRequestFiber tailHub c) ≤ Fintype.card (Fin visits) :=
        Fintype.card_le_of_injective (fun z : HubRequestFiber tailHub c => z.1)
          (fun a b hab => Subtype.ext hab)
      _ = visits := Fintype.card_fin visits
  have hcountZero : ∀ c, ¬ Nonempty (HubRequestFiber tailHub c) →
      count c = 0 := by
    intro c hc
    by_contra hne
    have hpos : 0 < count c := Nat.pos_of_ne_zero hne
    exact hc (Fintype.card_pos_iff.mp (by simpa [count] using hpos))
  let corrSum : ℕ := ∑ c : ι, corr c
  have hcorrSum : corrSum ≤ 3 * visits := by
    calc
      corrSum ≤ ∑ c : ι, 3 * count c := by
        apply Finset.sum_le_sum
        intro c _hc
        by_cases hc : Nonempty (HubRequestFiber tailHub c)
        · have hpos : 0 < count c := by
            simpa [count] using (Fintype.card_pos (h := hc))
          have hcorr' := hcorr c
          have hcorr'' : corr c ≤ 2 * count c + 1 := by
            simpa [tailHub, count] using hcorr' hc
          omega
        · simpa [hcorrEmpty c (by simpa [tailHub] using hc), hcountZero c hc]
      _ = 3 * visits := by rw [← Finset.mul_sum, hcountSum]
  let lo : ι → ℕ := fun c =>
    if Nonempty (HubRequestFiber tailHub c) then 2 * count c + 1 else 0
  let hi : ι → ℕ := fun c =>
    if Nonempty (HubRequestFiber tailHub c) then q - 4 * count c - 1 else 0
  have hloSum : (∑ c : ι, lo c) ≤ 3 * visits := by
    calc
      (∑ c : ι, lo c) ≤ ∑ c : ι, 3 * count c := by
        apply Finset.sum_le_sum
        intro c _hc
        by_cases hc : Nonempty (HubRequestFiber tailHub c)
        · have hpos : 0 < count c := by
            simpa [count] using (Fintype.card_pos (h := hc))
          simp [lo, hc]
          omega
        · simp [lo, hc]
      _ = 3 * visits := by rw [← Finset.mul_sum, hcountSum]
  have hlohi : ∀ c, lo c ≤ hi c := by
    intro c
    by_cases hc : Nonempty (HubRequestFiber tailHub c)
    · have hle := hcountLe c
      have hq' : 6 * visits + 2 ≤ q := by simpa [hvisitsEq] using hqLocal
      simp [lo, hi, hc]
      omega
    · simp [lo, hi, hc]
  let K : Finset ι := w.support.toFinset.erase u
  have hu : u ∈ w.support.toFinset := by simpa using w.start_mem_support
  have hKcard : K.card = t - 1 := by
    dsimp [K]
    rw [Finset.card_erase_of_mem hu]
    have hcard : w.support.toFinset.card = t := by
      have hfin : w.support.toFinset =
          @List.toFinset ι (Classical.decEq ι) w.support := by
        ext c
        simp
      rw [hfin]
      exact hwsupp
    rw [hcard]
  have hcover : ∀ c ∈ K, Nonempty (HubRequestFiber tailHub c) := by
    intro c hc
    have hcSupp : c ∈ w.support :=
      List.mem_toFinset.mp (Finset.mem_of_mem_erase hc)
    have hcu : c ≠ u := Finset.ne_of_mem_erase hc
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hcSupp
    have hnpos : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := by omega
      subst n
      exact hcu (by simpa using hn.symm)
    have hnlt : n < w.length := by
      by_contra hnnot
      have hneq : n = w.length := by omega
      subst n
      exact hcu (by simpa using hn.symm)
    let j : Fin visits := ⟨n - 1, by dsimp [visits]; omega⟩
    refine ⟨⟨j, ?_⟩⟩
    simpa [tailHub, j, show n - 1 + 1 = n by omega] using hn
  have hhiSum :
      (t - 1) * (q - 4 * visits - 1) ≤ ∑ c : ι, hi c := by
    calc
      (t - 1) * (q - 4 * visits - 1) =
          ∑ _c ∈ K, (q - 4 * visits - 1) := by
            simp [hKcard, Nat.mul_comm]
      _ ≤ ∑ c ∈ K, hi c := by
        apply Finset.sum_le_sum
        intro c hc
        have hcne := hcover c hc
        have hle := hcountLe c
        simp [hi, hcne]
        omega
      _ ≤ ∑ c : ι, hi c :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ K)
  let ell : ℕ := if (k - S) % 2 = 0 then 6 else 5
  have hell : 5 ≤ ell := by
    dsimp [ell]
    split_ifs <;> omega
  have hellsix : ell ≤ 6 := by
    dsimp [ell]
    split_ifs <;> omega
  have hbase' : 18 * (visits + 1) ≤ k := by
    rw [hvisitsEq]
    have heq : 2 * (t - 1) - 1 + 1 = 2 * (t - 1) := by omega
    rw [heq]
    exact hbase
  have hSell : S + ell ≤ k := by omega
  have hdiffEven : (k - S - ell) % 2 = 0 := by
    dsimp [ell]
    split_ifs with he
    · omega
    · have hmod : (k - S) % 2 = 1 := by
        have hlt := Nat.mod_lt (k - S) (by omega : 0 < 2)
        omega
      omega
  let total : ℕ := (k - S - ell) / 2
  have htotalEq : k - S - ell = 2 * total := by
    have hdivmod := Nat.div_add_mod (k - S - ell) 2
    dsimp [total]
    omega
  have htotalLarge : 7 * visits ≤ total := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega
  have htotalHalf : total ≤ k / 2 := by
    dsimp [total]
    have hsub : k - S - ell = k - (S + ell) := by omega
    rw [hsub]
    exact Nat.div_le_div_right (Nat.sub_le k (S + ell))
  let z : ℕ := total - corrSum - visits
  have hloz : (∑ c : ι, lo c) ≤ z := by
    dsimp [z]
    omega
  have hzhigh : z ≤ ∑ c : ι, hi c := by
    calc
      z ≤ total := by dsimp [z]; omega
      _ ≤ k / 2 := htotalHalf
      _ ≤ (t - 1) * (q - 4 * visits - 1) := by
        simpa [hvisitsEq] using hcapacity
      _ ≤ ∑ c : ι, hi c := hhiSum
  obtain ⟨scale, hscaleSum, hscale⟩ :=
    exists_fintype_weights_sum_eq_between lo hi hlohi hloz hzhigh
  have hscaleEmpty : ∀ c, ¬ Nonempty (HubRequestFiber tailHub c) →
      scale c = 0 := by
    intro c hc
    have hcBounds := hscale c
    simp [lo, hi, hc] at hcBounds
    omega
  have hscaleMin : ∀ c, Nonempty (HubRequestFiber tailHub c) →
      2 * Fintype.card (HubRequestFiber tailHub c) + 1 ≤ scale c := by
    intro c hc
    have hcBounds := (hscale c).1
    simpa [lo, hc, count] using hcBounds
  have hscaleMax : ∀ c, Nonempty (HubRequestFiber tailHub c) →
      scale c ≤ q - 4 * Fintype.card (HubRequestFiber tailHub c) - 1 := by
    intro c hc
    have hcBounds := (hscale c).2
    simpa [hi, hc, count] using hcBounds
  apply hcomplete ell scale hell
  · rw [hAcard u]
    have hq' : 6 * visits + 2 ≤ q := by simpa [hvisitsEq] using hqLocal
    omega
  · have ht' : 7 ≤ theta := by
      have hv : 1 ≤ visits := hvisits
      have htheta' : 4 * visits + 3 ≤ theta := by
        simpa [hvisitsEq] using htheta
      omega
    omega
  · simpa [tailHub] using hscaleEmpty
  · simpa [tailHub] using hscaleMin
  · simpa [tailHub] using hscaleMax
  · have htriple :
        (∑ c : ι, (scale c + corr c + count c)) =
          z + corrSum + visits := by
      rw [show (∑ c : ι, (scale c + corr c + count c)) =
          (∑ c : ι, scale c) + (∑ c : ι, corr c) +
            ∑ c : ι, count c by simp [Finset.sum_add_distrib]]
      rw [hscaleSum, hcountSum]
    have htarget : S + ell + 2 * (z + corrSum + visits) = k := by
      dsimp [z]
      omega
    rw [show (∑ c : ι, (scale c + corr c +
        Fintype.card (HubRequestFiber
          (fun j : Fin visits => w.getVert (j.val + 1)) c))) =
          z + corrSum + visits by simpa [tailHub, count] using htriple]
    exact htarget

/-- A sidewise selected auxiliary cycle has the same asymptotically full
length capacity as a selected-side cycle.  Short full-core handles contribute
only a linear base cost; one root hub corrects parity, while the remaining
`m` scaffolds contribute independently up to `q-5` units of half-length. -/
theorem cycleGraph_isContained_of_selectedCrossEdgeGraph_sidewise_cycle
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m q theta k : ℕ} (hm : 2 ≤ m) (hk : 3 ≤ k)
    (A B D I : ι → Finset V)
    (M : Finset (SelectedCrossEdge V ι))
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hside : ∀ i, I i ⊆ A i ∨ I i ⊆ B i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hq : 8 ≤ q) (htheta : 7 ≤ theta)
    (hcopy : _root_.SimpleGraph.cycleGraph (m + 1) ⊑
      SelectedCrossEdgeGraph M)
    (hbase : 18 * (m + 1) ≤ k)
    (hcapacity : k / 2 ≤ m * (q - 5)) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  obtain ⟨f, hfinj, x, y, h, hh, hhDisj, hhMate, ha, hb, hab, hpairs⟩ :=
    exists_sidewise_selected_path_handles_of_cycle
      G hm A B D I M hscaffold hregions hside hM hcopy
  let tailHub : Fin m → ι := fun j => f j.succ
  have htailInj : Function.Injective tailHub := by
    intro i j hij
    exact Fin.succ_injective _ (hfinj hij)
  have hrootFresh : ∀ j : Fin m, f j.succ ≠ f 0 := by
    intro j hEq
    have := hfinj hEq
    exact Fin.succ_ne_zero j this
  have hfiberCard : ∀ c, Fintype.card (HubRequestFiber tailHub c) ≤ 1 := by
    intro c
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    intro u v
    apply Subtype.ext
    apply htailInj
    exact u.property.trans v.property.symm
  obtain ⟨corr, hcorr, hcorrEmpty, hcomplete⟩ :=
    cycleGraph_isContained_of_grouped_repeated_routes_and_handles
      G (by omega) f hrootFresh A B D hscaffold hrob hmajorD hregions
        (by
          intro c hc
          have hcard := hfiberCard c
          have hpos : 0 < Fintype.card (HubRequestFiber tailHub c) :=
            Fintype.card_pos (h := hc)
          simpa [tailHub] using (by omega :
            4 * Fintype.card (HubRequestFiber tailHub c) + 2 ≤ theta))
        (hmatch (f 0)) x y h (fun e => (hh e).1)
        (fun e => (hh e).2.1) hhDisj hhMate ha hb hab hpairs hk
  let S : ℕ := ∑ e : Fin (m + 1), (h e).length
  have hSlower : m + 1 ≤ S := by
    calc
      m + 1 = ∑ _e : Fin (m + 1), 1 := by simp
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro e _he
        exact (hh e).2.1
  have hSupper : S ≤ 3 * (m + 1) := by
    calc
      S ≤ ∑ _e : Fin (m + 1), 3 := by
        apply Finset.sum_le_sum
        intro e _he
        exact (hh e).2.2
      _ = 3 * (m + 1) := by simp [Nat.mul_comm]
  let count : ι → ℕ := fun c => Fintype.card (HubRequestFiber tailHub c)
  have hcountSum : (∑ c : ι, count c) = m := by
    simpa [count] using sum_card_hubRequestFibers tailHub
  have hcountZero : ∀ c, ¬ Nonempty (HubRequestFiber tailHub c) →
      count c = 0 := by
    intro c hc
    by_contra hne
    have hpos : 0 < count c := Nat.pos_of_ne_zero hne
    exact hc (Fintype.card_pos_iff.mp (by simpa [count] using hpos))
  let corrSum : ℕ := ∑ c : ι, corr c
  have hcorrSum : corrSum ≤ 3 * m := by
    calc
      corrSum ≤ ∑ c : ι, 3 * count c := by
        apply Finset.sum_le_sum
        intro c _hc
        by_cases hc : Nonempty (HubRequestFiber tailHub c)
        · have hpos : 0 < count c := by
            simpa [count] using (Fintype.card_pos (h := hc))
          have hle := hfiberCard c
          have hcorr' : corr c ≤ 2 * count c + 1 := by
            simpa [tailHub, count] using hcorr c hc
          omega
        · simpa [hcorrEmpty c (by simpa [tailHub] using hc), hcountZero c hc]
      _ = 3 * m := by rw [← Finset.mul_sum, hcountSum]
  let lo : ι → ℕ := fun c => 3 * count c
  let hi : ι → ℕ := fun c => (q - 5) * count c
  have hloSum : (∑ c : ι, lo c) = 3 * m := by
    simp [lo, ← Finset.mul_sum, hcountSum]
  have hhiSum : (∑ c : ι, hi c) = (q - 5) * m := by
    simp [hi, ← Finset.mul_sum, hcountSum]
  have hlohi : ∀ c, lo c ≤ hi c := by
    intro c
    dsimp [lo, hi]
    exact Nat.mul_le_mul_right (count c) (by omega)
  let ell : ℕ := if (k - S) % 2 = 0 then 6 else 5
  have hell : 5 ≤ ell := by
    dsimp [ell]
    split_ifs <;> omega
  have hellsix : ell ≤ 6 := by
    dsimp [ell]
    split_ifs <;> omega
  have hSell : S + ell ≤ k := by omega
  have hdiffEven : (k - S - ell) % 2 = 0 := by
    dsimp [ell]
    split_ifs with he
    · omega
    · have hmod : (k - S) % 2 = 1 := by
        have hlt := Nat.mod_lt (k - S) (by omega : 0 < 2)
        omega
      omega
  let total : ℕ := (k - S - ell) / 2
  have htotalEq : k - S - ell = 2 * total := by
    have hdivmod := Nat.div_add_mod (k - S - ell) 2
    dsimp [total]
    omega
  have htotalLarge : 7 * m ≤ total := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega
  have htotalHalf : total ≤ k / 2 := by
    dsimp [total]
    have hsub : k - S - ell = k - (S + ell) := by omega
    rw [hsub]
    exact Nat.div_le_div_right (Nat.sub_le k (S + ell))
  let z : ℕ := total - corrSum - m
  have hloz : (∑ c : ι, lo c) ≤ z := by
    rw [hloSum]
    dsimp [z]
    omega
  have hzhigh : z ≤ ∑ c : ι, hi c := by
    rw [hhiSum]
    calc
      z ≤ total := by dsimp [z]; omega
      _ ≤ k / 2 := htotalHalf
      _ ≤ m * (q - 5) := hcapacity
      _ = (q - 5) * m := Nat.mul_comm _ _
  obtain ⟨scale, hscaleSum, hscale⟩ :=
    exists_fintype_weights_sum_eq_between lo hi hlohi hloz hzhigh
  have hscaleEmpty : ∀ c, ¬ Nonempty (HubRequestFiber tailHub c) →
      scale c = 0 := by
    intro c hc
    have hcBounds := hscale c
    have hz := hcountZero c hc
    simp [lo, hi, hz] at hcBounds
    omega
  have hscaleMin : ∀ c, Nonempty (HubRequestFiber tailHub c) →
      2 * Fintype.card (HubRequestFiber tailHub c) + 1 ≤ scale c := by
    intro c hc
    have hpos : 0 < count c := by
      simpa [count] using (Fintype.card_pos (h := hc))
    have hle := hfiberCard c
    have hcBounds := (hscale c).1
    dsimp [lo] at hcBounds
    simpa [count] using (by omega : 2 * count c + 1 ≤ scale c)
  have hscaleMax : ∀ c, Nonempty (HubRequestFiber tailHub c) →
      scale c ≤ q - 4 * Fintype.card (HubRequestFiber tailHub c) - 1 := by
    intro c hc
    have hpos : 0 < count c := by
      simpa [count] using (Fintype.card_pos (h := hc))
    have hle := hfiberCard c
    have hle' : count c ≤ 1 := by simpa [count] using hle
    have hcBounds := (hscale c).2
    dsimp [hi] at hcBounds
    have hcount : count c = 1 := by omega
    have htarget : scale c ≤ q - 4 * count c - 1 := by
      rw [hcount] at hcBounds ⊢
      simp only [Nat.mul_one] at hcBounds
      omega
    simpa [count] using htarget
  apply hcomplete ell scale hell
  · rw [hAcard (f 0)]
    omega
  · omega
  · simpa [tailHub] using hscaleEmpty
  · simpa [tailHub] using hscaleMin
  · simpa [tailHub] using hscaleMax
  · have htriple :
        (∑ c : ι, (scale c + corr c + count c)) =
          z + corrSum + m := by
      rw [show (∑ c : ι, (scale c + corr c + count c)) =
          (∑ c : ι, scale c) + (∑ c : ι, corr c) +
            ∑ c : ι, count c by simp [Finset.sum_add_distrib]]
      rw [hscaleSum, hcountSum]
    have htarget : S + ell + 2 * (z + corrSum + m) = k := by
      dsimp [z]
      omega
    rw [show (∑ c : ι, (scale c + corr c +
        Fintype.card (HubRequestFiber (fun j : Fin m => f j.succ) c))) =
          z + corrSum + m by simpa [tailHub, count] using htriple]
    exact htarget


/-- Average-degree bound for a globally selected system whose displayed
class in each hub is allowed to be either whole scaffold side.  A medium
cycle in the selected auxiliary graph is closed by the preceding sidewise
exact-capacity lift. -/
theorem card_selectedCrossEdgeSystem_lt_of_cycleFree_sidewise_scaffold
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D I : ι → Finset V) (q theta : ℕ)
    (M : Finset (SelectedCrossEdge V ι))
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hside : ∀ i, I i ⊆ A i ∨ I i ⊆ B i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hq : 8 ≤ q) (htheta : 7 ≤ theta)
    {b D₀ δ k : ℕ} (hb : 2 ≤ b) (hD₀ : 3 ≤ D₀) (hk : 3 ≤ k)
    (hmargin : 2 * ((8 * (D₀ + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D₀ ≤ l →
      l ≤ 8 * (D₀ + 1) + 2 * Nat.log b (Fintype.card ι) →
      18 * l ≤ k ∧ k / 2 ≤ (l - 1) * (q - 5))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    M.card < 4 * δ * Fintype.card ι := by
  classical
  by_contra hnot
  have hδ : 0 < δ := by omega
  have hlarge : 4 * δ * Fintype.card ι ≤ M.card := by omega
  have hsupp : (SelectedCrossEdgeGraph M).support.ncard ≤
      Fintype.card ι := by
    simpa using Set.ncard_le_ncard
      (Set.subset_univ (SelectedCrossEdgeGraph M).support)
  have hdense : (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
      2 * (SelectedCrossEdgeGraph M).edgeFinset.card := by
    rw [card_edgeFinset_selectedCrossEdgeGraph hM]
    calc
      (8 * δ) * (SelectedCrossEdgeGraph M).support.ncard ≤
          (8 * δ) * Fintype.card ι := Nat.mul_le_mul_left _ hsupp
      _ = 2 * (4 * δ * Fintype.card ι) := by ring
      _ ≤ 2 * M.card := Nat.mul_le_mul_left 2 hlarge
  have hMne : M.Nonempty := by
    apply Finset.card_pos.mp
    have hcardι : 0 < Fintype.card ι := Fintype.card_pos
    exact (Nat.mul_pos (Nat.mul_pos (by omega) hδ) hcardι).trans_le hlarge
  have hE : (SelectedCrossEdgeGraph M).edgeFinset.Nonempty := by
    rw [← Finset.card_pos, card_edgeFinset_selectedCrossEdgeGraph hM]
    exact Finset.card_pos.mpr hMne
  obtain ⟨l, hD₀l, hlupper, hcopy⟩ :=
    exists_medium_cycle_of_edge_density
      (SelectedCrossEdgeGraph M) b D₀ δ hb hE hdense hmargin
  obtain ⟨hbase, hcap⟩ := hfit l hD₀l hlupper
  let m : ℕ := l - 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hml : m + 1 = l := by dsimp [m]; omega
  apply hcycle
  apply cycleGraph_isContained_of_selectedCrossEdgeGraph_sidewise_cycle
    G hm hk A B D I M hscaffold hrob hmajorD hAcard hregions
      hside hM hmatch hq htheta
  · rw [hml]
    exact hcopy
  · simpa [hml] using hbase
  · simpa [m] using hcap

/-- Two different bounded natural numbers differ in one of the binary
positions below `log₂ N + 1`. -/
theorem exists_testBit_ne_below_succ_log
    {N x y : ℕ} (hx : x < N) (hy : y < N) (hxy : x ≠ y) :
    ∃ t < Nat.log 2 N + 1, x.testBit t ≠ y.testBit t := by
  by_contra hno
  push_neg at hno
  apply hxy
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < Nat.log 2 N + 1
  · exact hno t ht
  · have hNpow : N < 2 ^ (Nat.log 2 N + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
    have hpowmono : 2 ^ (Nat.log 2 N + 1) ≤ 2 ^ t := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hxt : x < 2 ^ t := hx.trans (hNpow.trans_le hpowmono)
    have hyt : y < 2 ^ t := hy.trans (hNpow.trans_le hpowmono)
    rw [Nat.testBit_eq_false_of_lt hxt, Nat.testBit_eq_false_of_lt hyt]

/-- The two constant side choices and both orientations of every binary
coordinate form a logarithmic separating family of side assignments. -/
abbrev SideCoverIndex (ι : Type*) [Fintype ι] :=
  Bool ⊕ (Fin (Nat.log 2 (Fintype.card ι) + 1) × Bool)

noncomputable def sideCoverChoosesB
    {ι : Type*} [Fintype ι] (s : SideCoverIndex ι) (i : ι) : Bool :=
  match s with
  | Sum.inl b => b
  | Sum.inr tb =>
      if (Fintype.equivFin ι i).val.testBit tb.1.val = tb.2 then false else true

noncomputable def sideCoverClass
    {V ι : Type*} [Fintype ι]
    (A B : ι → Finset V) (s : SideCoverIndex ι) (i : ι) : Finset V :=
  if sideCoverChoosesB s i then B i else A i

theorem sideCoverClass_subset_one_side
    {V ι : Type*} [Fintype ι]
    (A B : ι → Finset V) (s : SideCoverIndex ι) (i : ι) :
    sideCoverClass A B s i ⊆ A i ∨ sideCoverClass A B s i ⊆ B i := by
  classical
  unfold sideCoverClass
  split <;> simp_all

theorem exists_sideCoverClass_containing_two_fullCore_vertices
    {V ι : Type*} [Fintype ι]
    (A B : ι → Finset V) {i j : ι} (hij : i ≠ j)
    {x y : V} (hx : x ∈ A i ∪ B i) (hy : y ∈ A j ∪ B j) :
    ∃ s : SideCoverIndex ι,
      x ∈ sideCoverClass A B s i ∧ y ∈ sideCoverClass A B s j := by
  classical
  by_cases hxA : x ∈ A i
  · by_cases hyA : y ∈ A j
    · refine ⟨Sum.inl false, ?_, ?_⟩ <;>
        simp [sideCoverClass, sideCoverChoosesB, hxA, hyA]
    · have hyB : y ∈ B j := (Finset.mem_union.mp hy).resolve_left hyA
      let ei : Fin (Fintype.card ι) := Fintype.equivFin ι i
      let ej : Fin (Fintype.card ι) := Fintype.equivFin ι j
      have heij : ei.val ≠ ej.val := by
        intro h
        exact hij ((Fintype.equivFin ι).injective (Fin.ext h))
      obtain ⟨t, ht, hbit⟩ := exists_testBit_ne_below_succ_log
        ei.isLt ej.isLt heij
      let ft : Fin (Nat.log 2 (Fintype.card ι) + 1) := ⟨t, ht⟩
      let bit : Bool := ei.val.testBit t
      refine ⟨Sum.inr (ft, bit), ?_, ?_⟩
      · simp [sideCoverClass, sideCoverChoosesB, ei, ft, bit, hxA]
      · have hne : ej.val.testBit t ≠ bit := by simpa [bit] using hbit.symm
        simp [sideCoverClass, sideCoverChoosesB, ej, ft, bit, hne, hyB]
  · have hxB : x ∈ B i := (Finset.mem_union.mp hx).resolve_left hxA
    by_cases hyA : y ∈ A j
    · let ei : Fin (Fintype.card ι) := Fintype.equivFin ι i
      let ej : Fin (Fintype.card ι) := Fintype.equivFin ι j
      have heij : ei.val ≠ ej.val := by
        intro h
        exact hij ((Fintype.equivFin ι).injective (Fin.ext h))
      obtain ⟨t, ht, hbit⟩ := exists_testBit_ne_below_succ_log
        ei.isLt ej.isLt heij
      let ft : Fin (Nat.log 2 (Fintype.card ι) + 1) := ⟨t, ht⟩
      let bit : Bool := ej.val.testBit t
      refine ⟨Sum.inr (ft, bit), ?_, ?_⟩
      · have hne : ei.val.testBit t ≠ bit := by simpa [bit] using hbit
        simp [sideCoverClass, sideCoverChoosesB, ei, ft, bit, hne, hxB]
      · simp [sideCoverClass, sideCoverChoosesB, ej, ft, bit, hyA]
    · have hyB : y ∈ B j := (Finset.mem_union.mp hy).resolve_left hyA
      refine ⟨Sum.inl true, ?_, ?_⟩ <;>
        simp [sideCoverClass, sideCoverChoosesB, hxB, hyB]

@[simp] theorem card_sideCoverIndex (ι : Type*) [Fintype ι] :
    Fintype.card (SideCoverIndex ι) =
      2 + 2 * (Nat.log 2 (Fintype.card ι) + 1) := by
  simp [SideCoverIndex, Nat.mul_comm]

/-- A selected system on the full alternating cores is the disjoint union
of only logarithmically many sidewise selected systems.  Applying the
sidewise density theorem to every binary color bounds the original full-core
system. -/
theorem card_selectedCrossEdgeSystem_le_of_cycleFree_fullCore
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D I : ι → Finset V) (q theta : ℕ)
    (M : Finset (SelectedCrossEdge V ι))
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hIfull : ∀ i, I i ⊆ A i ∪ B i)
    (hM : IsSelectedCrossEdgeSystem G I M)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hq : 8 ≤ q) (htheta : 7 ≤ theta)
    {b D₀ δ k : ℕ} (hb : 2 ≤ b) (hD₀ : 3 ≤ D₀) (hk : 3 ≤ k)
    (hmargin : 2 * ((8 * (D₀ + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D₀ ≤ l →
      l ≤ 8 * (D₀ + 1) + 2 * Nat.log b (Fintype.card ι) →
      18 * l ≤ k ∧ k / 2 ≤ (l - 1) * (q - 5))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    M.card ≤
      (2 + 2 * (Nat.log 2 (Fintype.card ι) + 1)) *
        (4 * δ * Fintype.card ι) := by
  classical
  let S := SideCoverIndex ι
  have hcover : ∀ e ∈ M, ∃ s : S,
      e.2.1 ∈ sideCoverClass A B s e.1.1 ∧
        e.2.2 ∈ sideCoverClass A B s e.1.2 := by
    intro e he
    have hedata := hM.1 e he
    apply exists_sideCoverClass_containing_two_fullCore_vertices A B hedata.1
    · exact hIfull e.1.1 hedata.2.1
    · exact hIfull e.1.2 hedata.2.2.1
  let color : SelectedCrossEdge V ι → S := fun e =>
    if he : e ∈ M then Classical.choose (hcover e he) else Sum.inl false
  have hcolor : ∀ e ∈ M,
      e.2.1 ∈ sideCoverClass A B (color e) e.1.1 ∧
        e.2.2 ∈ sideCoverClass A B (color e) e.1.2 := by
    intro e he
    simpa [color, he] using Classical.choose_spec (hcover e he)
  let Is : S → ι → Finset V := fun s i => I i ∩ sideCoverClass A B s i
  let Ms : S → Finset (SelectedCrossEdge V ι) := fun s =>
    M.filter fun e => color e = s
  have hIside : ∀ s i, Is s i ⊆ A i ∨ Is s i ⊆ B i := by
    intro s i
    rcases sideCoverClass_subset_one_side A B s i with hA | hB
    · exact Or.inl (Finset.inter_subset_right.trans hA)
    · exact Or.inr (Finset.inter_subset_right.trans hB)
  have hMs : ∀ s, IsSelectedCrossEdgeSystem G (Is s) (Ms s) := by
    intro s
    constructor
    · intro e he
      have heM : e ∈ M := (Finset.mem_filter.mp he).1
      have hedata := hM.1 e heM
      have hecolor : color e = s := (Finset.mem_filter.mp he).2
      have heclass := hcolor e heM
      exact ⟨hedata.1,
        Finset.mem_inter.mpr ⟨hedata.2.1, hecolor ▸ heclass.1⟩,
        Finset.mem_inter.mpr ⟨hedata.2.2.1, hecolor ▸ heclass.2⟩,
        hedata.2.2.2⟩
    constructor
    · intro e he f hf hef
      exact hM.2.1 e (Finset.mem_filter.mp he).1
        f (Finset.mem_filter.mp hf).1 hef
    · intro e he f hf hpairs
      exact hM.2.2 e (Finset.mem_filter.mp he).1
        f (Finset.mem_filter.mp hf).1 hpairs
  have hfiber : ∀ s : S, (Ms s).card ≤ 4 * δ * Fintype.card ι := by
    intro s
    exact (card_selectedCrossEdgeSystem_lt_of_cycleFree_sidewise_scaffold
      G A B D (Is s) q theta (Ms s) hscaffold hrob hmajorD hAcard
        hregions (hIside s) (hMs s) hmatch hq htheta hb hD₀ hk
        hmargin hfit hcycle).le
  have hcardEq : M.card = ∑ s : S, (Ms s).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := M) (t := (Finset.univ : Finset S)) (f := color)
      (fun _ _ => Finset.mem_univ _)]
  calc
    M.card = ∑ s : S, (Ms s).card := hcardEq
    _ ≤ ∑ _s : S, (4 * δ * Fintype.card ι) := by
      exact Finset.sum_le_sum fun s _hs => hfiber s
    _ = Fintype.card S * (4 * δ * Fintype.card ι) := by simp
    _ = (2 + 2 * (Nat.log 2 (Fintype.card ι) + 1)) *
        (4 * δ * Fintype.card ι) := by rw [card_sideCoverIndex]

/-! ## Exact-scale full-core components -/

/-- Remove one arbitrary vertex from a finite set, doing nothing only when the
set is empty.  This is the canonical one-vertex slack used in every retained
selected core. -/
noncomputable def trimOneFinset {V : Type*} [DecidableEq V]
    (S : Finset V) : Finset V :=
  if hS : S.Nonempty then S.erase hS.choose else S

/-- Choose exactly `t` vertices from a finite set when that many are
available.  The empty fallback makes the definition total; all uses below
supply the cardinality hypothesis. -/
noncomputable def shrinkFinset {V : Type*} [DecidableEq V]
    (S : Finset V) (t : ℕ) : Finset V :=
  if h : t ≤ S.card then Classical.choose (Finset.exists_subset_card_eq h)
  else ∅

theorem shrinkFinset_subset {V : Type*} [DecidableEq V]
    (S : Finset V) (t : ℕ) : shrinkFinset S t ⊆ S := by
  classical
  by_cases h : t ≤ S.card
  · simpa [shrinkFinset, h] using
      (Classical.choose_spec (Finset.exists_subset_card_eq h)).1
  · simp [shrinkFinset, h]

theorem card_shrinkFinset {V : Type*} [DecidableEq V]
    (S : Finset V) {t : ℕ} (h : t ≤ S.card) :
    (shrinkFinset S t).card = t := by
  classical
  simpa [shrinkFinset, h] using
    (Classical.choose_spec (Finset.exists_subset_card_eq h)).2

theorem card_fullCore_eq_two_mul_of_alternatingScaffold
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {q : ℕ} {A B : Finset V}
    (hscaffold : IsCyclicAlternatingScaffold G q A B)
    (hAcard : A.card = q) :
    (A ∪ B).card = 2 * q := by
  classical
  rcases hscaffold with ⟨_hq, _a, b, _hAe, hBe,
    _ha, hb, hAB, _hab, _hba⟩
  rw [Finset.card_union_of_disjoint hAB, hAcard, hBe,
    Finset.card_image_of_injective _ hb]
  simp
  omega

theorem trimOneFinset_subset {V : Type*} [DecidableEq V]
    (S : Finset V) : trimOneFinset S ⊆ S := by
  classical
  by_cases hS : S.Nonempty
  · simp only [trimOneFinset, dif_pos hS]
    exact Finset.erase_subset _ _
  · simp [trimOneFinset, hS]

/-- If the original set has at most `q` vertices and `q` is positive, trimming
one vertex leaves at most `q-1` vertices. -/
theorem card_trimOneFinset_le_pred {V : Type*} [DecidableEq V]
    (S : Finset V) {q : ℕ} (hq : 0 < q) (hcard : S.card ≤ q) :
    (trimOneFinset S).card ≤ q - 1 := by
  classical
  by_cases hS : S.Nonempty
  · have hmem : hS.choose ∈ S := hS.choose_spec
    simp only [trimOneFinset, dif_pos hS, Finset.card_erase_of_mem hmem]
    omega
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [trimOneFinset, hS, hEmpty]

/-- Degree-two pruning with an additional arbitrary thinning of every core.
The only required invariant is that the retained set stays outside the
canonical repeated-attachment set. -/
theorem degree_largeCrossMatchingGraph_le_two_of_subset_sdiff_repeated
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : ι → Finset V) {R C : ℕ}
    (hWU : ∀ i, W i ⊆ U i \ RepeatedAttachmentFinset G U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcard : ∀ i, (U i).card ≤ C) (hR : C < 3 * R) (i : ι) :
    (LargeCrossMatchingGraph G W R).degree i ≤ 2 := by
  have hbudget : R * (LargeCrossMatchingGraph G W R).degree i ≤ (U i).card := by
    apply mul_degree_largeCrossMatchingGraph_le_card_of_no_repeated_attachment
      G U W R
    · intro j
      exact (hWU j).trans Finset.sdiff_subset
    · exact hdisj
    · intro a b c hab hac hbc x hx y hy z hz hxy hxz
      have hx' := hWU a hx
      apply no_repeated_attachment_outside_RepeatedAttachmentFinset
        G U a b c hab hac hbc x
      · exact (Finset.mem_sdiff.mp hx').1
      · exact (Finset.mem_sdiff.mp hx').2
      · exact hy
      · exact hz
      · exact hxy
      · exact hxz
  by_contra hnot
  have hdeg : 3 ≤ (LargeCrossMatchingGraph G W R).degree i := by omega
  have h3R : 3 * R ≤ R * (LargeCrossMatchingGraph G W R).degree i := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left R hdeg
  exact (not_lt_of_ge (hbudget.trans (hcard i))) (hR.trans_le h3R)

/-- A cycle-free full-alternating-core large-matching component has at most
`L` labels whenever the repeated-walk lift fits.  Unlike the earlier path
version, this scale-free component theorem has no maximum-degree hypothesis. -/
theorem ncard_component_lt_succ_of_cycleFree_fullCore_at_scale
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D W : ι → Finset V) {q theta R k L : ℕ}
    (hL : 0 < L)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hWU : ∀ i, W i ⊆ A i ∪ B i)
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (htheta : 4 * (2 * L - 1) + 3 ≤ theta)
    (hqLocal : 6 * (2 * L - 1) + 2 ≤ q)
    (hhandleBudget : 8 * L < R / 4)
    (hk : 3 ≤ k) (hbase : 18 * (2 * L) ≤ k)
    (hcapacity : k / 2 ≤ L * (q - 4 * (2 * L - 1) - 1))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G)
    (c : (LargeCrossMatchingGraph G W R).ConnectedComponent) :
    c.supp.ncard < L + 1 := by
  let H : SimpleGraph ι := LargeCrossMatchingGraph G W R
  let Kgraph : SimpleGraph c := c.toSimpleGraph
  let Ac : c → Finset V := fun i => A i.1
  let Bc : c → Finset V := fun i => B i.1
  let Dc : c → Finset V := fun i => D i.1
  have hKlarge : ∀ i j : c, Kgraph.Adj i j →
      HasCrossMatchingAtLeast G (Ac i ∪ Bc i) (Ac j ∪ Bc j) R := by
    intro i j hij
    apply HasCrossMatchingAtLeast.mono_sets
      (hasCrossMatchingAtLeast_of_largeCrossMatchingGraph_adj
        (G := G) (U := W) (m := R) ?_)
      (hWU i.1) (hWU j.1)
    apply (c.toSimpleGraph_adj i.property j.property).mp
    simpa [Kgraph, H] using hij
  have hKregions : ∀ i j : c, i ≠ j →
      Disjoint ((Ac i ∪ Bc i) ∪ Dc i) ((Ac j ∪ Bc j) ∪ Dc j) := by
    intro i j hij
    apply hregions i.1 j.1
    intro h
    exact hij (Subtype.ext h)
  have hcard : Fintype.card c < L + 1 := by
    by_contra hnot
    apply hcycle
    apply cycleGraph_isContained_of_connected_largeFullCoreMatching_repeated_of_card_ge
      G Kgraph c.connected_toSimpleGraph (t := L + 1) (q := q)
        (theta := theta) (R := R) (k := k) (by omega) (by omega)
        Ac Bc Dc
    · intro i
      exact hscaffold i.1
    · intro i
      exact hrob i.1
    · intro i
      exact hmajorD i.1
    · exact hKregions
    · intro i
      exact hAcard i.1
    · intro i
      exact hmatch i.1
    · simpa using htheta
    · simpa using hqLocal
    · simpa using hhandleBudget
    · exact hKlarge
    · exact hk
    · simpa using hbase
    · simpa using hcapacity
  have hcCard : Fintype.card c = c.supp.ncard := by
    calc
      Fintype.card c = Fintype.card c.supp := by
        apply Fintype.card_congr
        exact
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      _ = c.supp.ncard := Set.fintypeCard_eq_ncard c.supp
  simpa [hcCard] using hcard

/-- The exact quotient relations at the eighth-root scale discharge every
numerical hypothesis of the repeated-walk component lift with scale `P` and
matching threshold `floor(q/2)`. -/
theorem exact_scale_fullCore_component_numerics
    {P q k : ℕ} (hP : 3 ≤ P) (hqlarge : 80 * (P + 1) ≤ q)
    (hquotLower : P * q ≤ k) (hquotUpper : k < P * (q + 1)) :
    let R := q / 2
    6 * (2 * P - 1) + 2 ≤ q ∧ 8 * P < R / 4 ∧
      18 * (2 * P) ≤ k ∧
      k / 2 ≤ P * (q - 4 * (2 * P - 1) - 1) := by
  let R : ℕ := q / 2
  have hqLocal : 6 * (2 * P - 1) + 2 ≤ q := by omega
  have hhandle : 8 * P < R / 4 := by
    dsimp [R]
    omega
  have hq36 : 36 ≤ q := by omega
  have hbase : 18 * (2 * P) ≤ k := by
    calc
      18 * (2 * P) = P * 36 := by ring
      _ ≤ P * q := Nat.mul_le_mul_left P hq36
      _ ≤ k := hquotLower
  have hqroom : q + 1 ≤ 2 * (q - 4 * (2 * P - 1) - 1) := by omega
  have hkraw : k ≤ 2 * (P * (q - 4 * (2 * P - 1) - 1)) := by
    calc
      k ≤ P * (q + 1) := hquotUpper.le
      _ ≤ P * (2 * (q - 4 * (2 * P - 1) - 1)) :=
        Nat.mul_le_mul_left P hqroom
      _ = 2 * (P * (q - 4 * (2 * P - 1) - 1)) := by ring
  have hhalf : k / 2 ≤ P * (q - 4 * (2 * P - 1) - 1) :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hkraw)
  exact ⟨hqLocal, hhandle, hbase, hhalf⟩

/-- At the exact quotient scale, delete the repeated attachments and one
additional vertex from every selected core.  A maximum selected cross-edge
system then supplies one sparse exceptional set.  Its large-matching graph
has arbitrary degree but every component uses at most `P` labels, different
components are ambiently anticomplete after the deletion, and the union of
the retained cores in every component has at most `k-1` vertices.

This is the deterministic stability partition immediately preceding the
final absorption/counting argument. -/
theorem exists_sparse_selected_separator_with_small_exact_scale_blocks
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {q P theta k : ℕ}
    (hP : 3 ≤ P) (hqlarge : 80 * (P + 1) ≤ q)
    (hqdef : q = k / P)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (htheta : 4 * (2 * P - 1) + 3 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let Z := RepeatedAttachmentFinset G A
    let I : ι → Finset V := fun i => trimOneFinset (A i \ Z)
    ∃ M : Finset (SelectedCrossEdge V ι),
      IsSelectedCrossEdgeSystem G I M ∧
      (∀ N : Finset (SelectedCrossEdge V ι),
        IsSelectedCrossEdgeSystem G I N → N.card ≤ M.card) ∧
      let E := selectedCrossGlobalEndpointFinset M
      let U : ι → Finset V := fun i => I i \ E
      let H : SimpleGraph ι := LargeCrossMatchingGraph G U (q / 2)
      ∃ X : Finset V,
        X.card ≤ (2 * (q / 2) + 2) * M.card ∧ E ⊆ X ∧
        (∀ c d : H.ConnectedComponent, c ≠ d →
          ∀ i ∈ c.supp, ∀ j ∈ d.supp,
            ∀ a ∈ I i \ X, ∀ b ∈ I j \ X, ¬ G.Adj a b) ∧
        ∀ c : H.ConnectedComponent,
          (c.supp.toFinset.biUnion fun i => I i \ X).card ≤ k - 1 := by
  classical
  let Z := RepeatedAttachmentFinset G A
  let I : ι → Finset V := fun i => trimOneFinset (A i \ Z)
  obtain ⟨M, hM, hmax⟩ := exists_maximal_selectedCrossEdgeSystem G I
  refine ⟨M, hM, hmax, ?_⟩
  let E := selectedCrossGlobalEndpointFinset M
  let U : ι → Finset V := fun i => I i \ E
  let H : SimpleGraph ι := LargeCrossMatchingGraph G U (q / 2)
  have hIdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j) := by
    intro i j hij
    apply (hregions i j hij).mono
    · exact (trimOneFinset_subset (A i \ Z)).trans
        (Finset.sdiff_subset.trans
          (Finset.subset_union_left.trans Finset.subset_union_left))
    · exact (trimOneFinset_subset (A j \ Z)).trans
        (Finset.sdiff_subset.trans
          (Finset.subset_union_left.trans Finset.subset_union_left))
  obtain ⟨X, hXcard, hEX, hsep⟩ :=
    exists_sparse_selected_exceptional_set_separating_largeCrossMatching_components
      G I M hM hmax hIdisj (q / 2)
  have hPpos : 0 < P := by omega
  have hquotLower : P * q ≤ k := by
    rw [hqdef]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k P
  have hquotUpper : k < P * (q + 1) := by
    simpa [hqdef] using Nat.lt_mul_div_succ k hPpos
  have hnum := exact_scale_fullCore_component_numerics
    hP hqlarge hquotLower hquotUpper
  dsimp only at hnum
  have hUsub : ∀ i, U i ⊆ A i ∪ B i := by
    intro i
    exact Finset.sdiff_subset.trans
      ((trimOneFinset_subset (A i \ Z)).trans
        (Finset.sdiff_subset.trans Finset.subset_union_left))
  have hcomp : ∀ c : H.ConnectedComponent, c.supp.ncard < P + 1 := by
    intro c
    apply ncard_component_lt_succ_of_cycleFree_fullCore_at_scale
      G A B D U (q := q) (theta := theta) (R := q / 2) (k := k)
        (L := P) (by omega) hscaffold hrob hmajorD hAcard hregions
        hUsub hmatch htheta hnum.1 hnum.2.1 (by omega)
        hnum.2.2.1 hnum.2.2.2 hcycle
  have hpiece : ∀ i, (I i \ X).card ≤ q - 1 := by
    intro i
    change (trimOneFinset (A i \ Z) \ X).card ≤ q - 1
    apply (Finset.card_le_card Finset.sdiff_subset).trans
    apply card_trimOneFinset_le_pred (S := A i \ Z) (q := q) (by omega)
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (hAcard i)
  have hblocks : ∀ c : H.ConnectedComponent,
      (c.supp.toFinset.biUnion fun i => I i \ X).card ≤ k - 1 := by
    apply card_component_biUnion_le_pred_of_exact_cores
      H (fun i => I i \ X) (C := P) (tau := q) (k := k)
        hPpos hpiece hqdef hcomp
  exact ⟨X, hXcard, hEX, hsep, hblocks⟩

/-- The exact quotient relations also support a genuinely source-scale
matching threshold `64(P+1)`, rather than a fixed fraction of the core. -/
theorem source_scale_fullCore_component_numerics
    {P q k : ℕ} (hP : 3 ≤ P) (hqlarge : 80 * (P + 1) ≤ q)
    (hquotLower : P * q ≤ k) (hquotUpper : k < P * (q + 1)) :
    let R := 64 * (P + 1)
    6 * (2 * P - 1) + 2 ≤ q ∧ 8 * P < R / 4 ∧
      18 * (2 * P) ≤ k ∧
      k / 2 ≤ P * (q - 4 * (2 * P - 1) - 1) := by
  let R : ℕ := 64 * (P + 1)
  have hqLocal : 6 * (2 * P - 1) + 2 ≤ q := by omega
  have hhandle : 8 * P < R / 4 := by
    dsimp [R]
    omega
  have hq36 : 36 ≤ q := by omega
  have hbase : 18 * (2 * P) ≤ k := by
    calc
      18 * (2 * P) = P * 36 := by ring
      _ ≤ P * q := Nat.mul_le_mul_left P hq36
      _ ≤ k := hquotLower
  have hqroom : q + 1 ≤ 2 * (q - 4 * (2 * P - 1) - 1) := by omega
  have hkraw : k ≤ 2 * (P * (q - 4 * (2 * P - 1) - 1)) := by
    calc
      k ≤ P * (q + 1) := hquotUpper.le
      _ ≤ P * (2 * (q - 4 * (2 * P - 1) - 1)) :=
        Nat.mul_le_mul_left P hqroom
      _ = 2 * (P * (q - 4 * (2 * P - 1) - 1)) := by ring
  have hhalf : k / 2 ≤ P * (q - 4 * (2 * P - 1) - 1) :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hkraw)
  exact ⟨hqLocal, hhandle, hbase, hhalf⟩

/-- One additional component hub creates enough routing slack once the exact
core order dominates `P²`.  For even `P`, put `C=P/2+1`; then the repeated
walk lift works at source-scale matching threshold `64(C+1)`. -/
theorem one_extra_fullCore_component_numerics
    {P q k : ℕ} (hP : 3 ≤ P) (hPeven : 2 * (P / 2) = P)
    (hqlarge : 16 * (P + 1) ^ 2 ≤ q)
    (hquotLower : P * q ≤ k) (hquotUpper : k < P * (q + 1)) :
    let C := P / 2 + 1
    let R := 64 * (C + 1)
    4 * (2 * C - 1) + 3 ≤ 8 * P + 1 ∧
      6 * (2 * C - 1) + 2 ≤ q ∧
      8 * C < R / 4 ∧
      18 * (2 * C) ≤ k ∧
      k / 2 ≤ C * (q - 4 * (2 * C - 1) - 1) := by
  let C : ℕ := P / 2 + 1
  let R : ℕ := 64 * (C + 1)
  have hCeq : 2 * C = P + 2 := by
    dsimp [C]
    omega
  have hrobust : 4 * (2 * C - 1) + 3 ≤ 8 * P + 1 := by omega
  have hqroom : 4 * P + 5 ≤ q := by nlinarith [hqlarge]
  have hqLocal : 6 * (2 * C - 1) + 2 ≤ q := by
    nlinarith [hqlarge]
  have hhandle : 8 * C < R / 4 := by
    dsimp [R]
    omega
  have hbaseRaw : 18 * (2 * C) ≤ P * q := by
    nlinarith [hqlarge]
  have hbase : 18 * (2 * C) ≤ k := hbaseRaw.trans hquotLower
  have hinner : q - 4 * (2 * C - 1) - 1 = q - (4 * P + 5) := by
    omega
  have hsub : q - (4 * P + 5) + (4 * P + 5) = q :=
    Nat.sub_add_cancel hqroom
  have hcapRaw : P * (q + 1) ≤
      2 * (C * (q - (4 * P + 5))) := by
    nlinarith [hqlarge]
  have hkraw : k ≤ 2 * (C * (q - 4 * (2 * C - 1) - 1)) := by
    rw [hinner]
    exact hquotUpper.le.trans hcapRaw
  have hhalf : k / 2 ≤ C * (q - 4 * (2 * C - 1) - 1) :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hkraw)
  exact ⟨hrobust, hqLocal, hhandle, hbase, hhalf⟩

/-- Full-core source-scale separator.  It retains both alternating sides,
uses the logarithmic selected-system bound, and has matching threshold only
`64(P+1)`.  Components still have at most `P` hub labels; their displayed
full-core union is recorded with the sharp deterministic bound
`P(2q-1)`. -/
theorem exists_sparse_fullCore_source_scale_separator
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {q P theta k : ℕ}
    (hP : 3 ≤ P) (hqlarge : 80 * (P + 1) ≤ q)
    (hqdef : q = k / P)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (htheta : 4 * (2 * P - 1) + 3 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    {b D₀ δ : ℕ} (hb : 2 ≤ b) (hD₀ : 3 ≤ D₀)
    (hmargin : 2 * ((8 * (D₀ + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D₀ ≤ l →
      l ≤ 8 * (D₀ + 1) + 2 * Nat.log b (Fintype.card ι) →
      18 * l ≤ k ∧ k / 2 ≤ (l - 1) * (q - 5))
    (hk : 3 ≤ k)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let I : ι → Finset V := fun i => trimOneFinset (A i ∪ B i)
    ∃ M : Finset (SelectedCrossEdge V ι),
      IsSelectedCrossEdgeSystem G I M ∧
      (∀ N : Finset (SelectedCrossEdge V ι),
        IsSelectedCrossEdgeSystem G I N → N.card ≤ M.card) ∧
      M.card ≤
        (2 + 2 * (Nat.log 2 (Fintype.card ι) + 1)) *
          (4 * δ * Fintype.card ι) ∧
      let E := selectedCrossGlobalEndpointFinset M
      let U : ι → Finset V := fun i => I i \ E
      let R := 64 * (P + 1)
      let H : SimpleGraph ι := LargeCrossMatchingGraph G U R
      ∃ X : Finset V,
        X.card ≤ (2 * R + 2) * M.card ∧ E ⊆ X ∧
        (∀ c d : H.ConnectedComponent, c ≠ d →
          ∀ i ∈ c.supp, ∀ j ∈ d.supp,
            ∀ a ∈ I i \ X, ∀ b ∈ I j \ X, ¬ G.Adj a b) ∧
        (∀ c : H.ConnectedComponent, c.supp.ncard < P + 1) ∧
        ∀ c : H.ConnectedComponent,
          (c.supp.toFinset.biUnion fun i => I i \ X).card ≤
            P * (2 * q - 1) := by
  classical
  let I : ι → Finset V := fun i => trimOneFinset (A i ∪ B i)
  obtain ⟨M, hM, hmax⟩ := exists_maximal_selectedCrossEdgeSystem G I
  refine ⟨M, hM, hmax, ?_, ?_⟩
  · apply card_selectedCrossEdgeSystem_le_of_cycleFree_fullCore
      G A B D I q theta M hscaffold hrob hmajorD hAcard hregions
        (fun i => (trimOneFinset_subset (A i ∪ B i))) hM hmatch
        (by omega) (by omega) hb hD₀ hk hmargin hfit hcycle
  let E := selectedCrossGlobalEndpointFinset M
  let U : ι → Finset V := fun i => I i \ E
  let R : ℕ := 64 * (P + 1)
  let H : SimpleGraph ι := LargeCrossMatchingGraph G U R
  have hIdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j) := by
    intro i j hij
    apply (hregions i j hij).mono
    · exact (trimOneFinset_subset (A i ∪ B i)).trans Finset.subset_union_left
    · exact (trimOneFinset_subset (A j ∪ B j)).trans Finset.subset_union_left
  obtain ⟨X, hXcard, hEX, hsep⟩ :=
    exists_sparse_selected_exceptional_set_separating_largeCrossMatching_components
      G I M hM hmax hIdisj R
  have hPpos : 0 < P := by omega
  have hquotLower : P * q ≤ k := by
    rw [hqdef]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k P
  have hquotUpper : k < P * (q + 1) := by
    simpa [hqdef] using Nat.lt_mul_div_succ k hPpos
  have hnum := source_scale_fullCore_component_numerics
    hP hqlarge hquotLower hquotUpper
  dsimp only at hnum
  have hUsub : ∀ i, U i ⊆ A i ∪ B i := by
    intro i
    exact Finset.sdiff_subset.trans (trimOneFinset_subset (A i ∪ B i))
  have hcomp : ∀ c : H.ConnectedComponent, c.supp.ncard < P + 1 := by
    intro c
    apply ncard_component_lt_succ_of_cycleFree_fullCore_at_scale
      G A B D U (q := q) (theta := theta) (R := R) (k := k)
        (L := P) (by omega) hscaffold hrob hmajorD hAcard hregions
        hUsub hmatch htheta hnum.1 hnum.2.1 (by omega)
        hnum.2.2.1 hnum.2.2.2 hcycle
  have hpiece : ∀ i, (I i \ X).card ≤ 2 * q - 1 := by
    intro i
    apply (Finset.card_le_card Finset.sdiff_subset).trans
    apply card_trimOneFinset_le_pred (S := A i ∪ B i) (q := 2 * q) (by omega)
    calc
      (A i ∪ B i).card ≤ (A i).card + (B i).card := Finset.card_union_le _ _
      _ = q + q := by
        rw [hAcard i]
        rcases hscaffold i with ⟨_hq, _a, bfun, _hAe, hBe,
          _ha, hbfun, _hAB, _hab, _hba⟩
        rw [hBe, Finset.card_image_of_injective _ hbfun]
        simp
      _ = 2 * q := by omega
  have hblocks : ∀ c : H.ConnectedComponent,
      (c.supp.toFinset.biUnion fun i => I i \ X).card ≤
        P * (2 * q - 1) := by
    intro c
    have hunion : (c.supp.toFinset.biUnion fun i => I i \ X).card ≤
        c.supp.toFinset.card * (2 * q - 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro i _hi
      exact hpiece i
    have hsupp : c.supp.toFinset.card = c.supp.ncard := by
      simpa using (Set.ncard_eq_toFinset_card c.supp).symm
    have hlabels : c.supp.toFinset.card ≤ P := by
      rw [hsupp]
      have := hcomp c
      omega
    exact hunion.trans (Nat.mul_le_mul_right _ hlabels)
  exact ⟨X, hXcard, hEX, hsep, hcomp, hblocks⟩

/-- Capacity-correct full-core separator.  It uses one more than half of the
exact quotient parameter for routing, but thins each full core to
`floor(k/C)` vertices and removes one further vertex.  Consequently every
large-matching component is an actual stable block of order at most `k-1`.
The discarded per-hub fringe is exposed explicitly for the final absorption
count. -/
theorem exists_sparse_fullCore_separator_with_small_blocks_one_extra
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : ι → Finset V) {q P theta k : ℕ}
    (hP : 3 ≤ P) (hPeven : 2 * (P / 2) = P)
    (hqlarge : 16 * (P + 1) ^ 2 ≤ q)
    (hqdef : q = k / P)
    (hscaffold : ∀ i, IsCyclicAlternatingScaffold G q (A i) (B i))
    (hrob : ∀ i, RobustPairSet G (A i) (D i) theta)
    (hmajorD : ∀ i, Disjoint (A i ∪ B i) (D i))
    (hAcard : ∀ i, (A i).card = q)
    (htheta : 8 * P + 1 ≤ theta)
    (hregions : ∀ i j, i ≠ j →
      Disjoint ((A i ∪ B i) ∪ D i) ((A j ∪ B j) ∪ D j))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (A i))
    {b D₀ δ : ℕ} (hb : 2 ≤ b) (hD₀ : 3 ≤ D₀)
    (hmargin : 2 * ((8 * (D₀ + 1)) * b *
      (Nat.log b (Fintype.card ι) + 1)) < δ)
    (hfit : ∀ l : ℕ, D₀ ≤ l →
      l ≤ 8 * (D₀ + 1) + 2 * Nat.log b (Fintype.card ι) →
      18 * l ≤ k ∧ k / 2 ≤ (l - 1) * (q - 5))
    (hk : 3 ≤ k)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    let C := P / 2 + 1
    let tau := k / C
    let I : ι → Finset V := fun i =>
      trimOneFinset (shrinkFinset (A i ∪ B i) tau)
    ∃ M : Finset (SelectedCrossEdge V ι),
      IsSelectedCrossEdgeSystem G I M ∧
      (∀ N : Finset (SelectedCrossEdge V ι),
        IsSelectedCrossEdgeSystem G I N → N.card ≤ M.card) ∧
      M.card ≤
        (2 + 2 * (Nat.log 2 (Fintype.card ι) + 1)) *
          (4 * δ * Fintype.card ι) ∧
      (∀ i, ((A i ∪ B i) \ I i).card = 2 * q - (tau - 1)) ∧
      let E := selectedCrossGlobalEndpointFinset M
      let U : ι → Finset V := fun i => I i \ E
      let R := 64 * (C + 1)
      let H : SimpleGraph ι := LargeCrossMatchingGraph G U R
      ∃ X : Finset V,
        X.card ≤ (2 * R + 2) * M.card ∧ E ⊆ X ∧
        (∀ c d : H.ConnectedComponent, c ≠ d →
          ∀ i ∈ c.supp, ∀ j ∈ d.supp,
            ∀ a ∈ I i \ X, ∀ b ∈ I j \ X, ¬ G.Adj a b) ∧
        (∀ c : H.ConnectedComponent, c.supp.ncard < C + 1) ∧
        ∀ c : H.ConnectedComponent,
          (c.supp.toFinset.biUnion fun i => I i \ X).card ≤ k - 1 := by
  classical
  let C : ℕ := P / 2 + 1
  let tau : ℕ := k / C
  let I : ι → Finset V := fun i =>
    trimOneFinset (shrinkFinset (A i ∪ B i) tau)
  have hPpos : 0 < P := by omega
  have hCpos : 0 < C := by dsimp [C]; omega
  have hCeq : 2 * C = P + 2 := by dsimp [C]; omega
  have hquotLower : P * q ≤ k := by
    rw [hqdef]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k P
  have hquotUpper : k < P * (q + 1) := by
    simpa [hqdef] using Nat.lt_mul_div_succ k hPpos
  have hk2qC : k ≤ 2 * q * C := by
    have hupper := hquotUpper.le
    nlinarith [hqlarge]
  have htaule : tau ≤ 2 * q := by
    dsimp [tau]
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk2qC
  have hCleP : C ≤ P := by dsimp [C]; omega
  have hPleK : P ≤ k := by
    have hqpos : 0 < q := by nlinarith [hqlarge]
    calc
      P ≤ P * q := Nat.le_mul_of_pos_right P hqpos
      _ ≤ k := hquotLower
  have htaupos : 0 < tau := by
    dsimp [tau]
    exact Nat.div_pos (hCleP.trans hPleK) hCpos
  have hfullcard : ∀ i, (A i ∪ B i).card = 2 * q := by
    intro i
    exact card_fullCore_eq_two_mul_of_alternatingScaffold
      G (hscaffold i) (hAcard i)
  have hshrink : ∀ i,
      (shrinkFinset (A i ∪ B i) tau).card = tau := by
    intro i
    apply card_shrinkFinset
    rw [hfullcard i]
    exact htaule
  have hIcard : ∀ i, (I i).card = tau - 1 := by
    intro i
    have hnonempty : (shrinkFinset (A i ∪ B i) tau).Nonempty := by
      rw [← Finset.card_pos, hshrink i]
      exact htaupos
    simp [I, trimOneFinset, hnonempty, Finset.card_erase_of_mem hnonempty.choose_spec,
      hshrink i]
  have hfringe : ∀ i, ((A i ∪ B i) \ I i).card = 2 * q - (tau - 1) := by
    intro i
    rw [Finset.card_sdiff_of_subset]
    · rw [hfullcard i, hIcard i]
    · exact (trimOneFinset_subset _).trans (shrinkFinset_subset _ _)
  obtain ⟨M, hM, hmax⟩ := exists_maximal_selectedCrossEdgeSystem G I
  have hq8 : 8 ≤ q := by nlinarith [hqlarge]
  have htheta7 : 7 ≤ theta := by omega
  refine ⟨M, hM, hmax, ?_, hfringe, ?_⟩
  · apply card_selectedCrossEdgeSystem_le_of_cycleFree_fullCore
      G A B D I q theta M hscaffold hrob hmajorD hAcard hregions
        (fun i => (trimOneFinset_subset _).trans (shrinkFinset_subset _ _))
        hM hmatch hq8 htheta7 hb hD₀ hk hmargin hfit hcycle
  let E := selectedCrossGlobalEndpointFinset M
  let U : ι → Finset V := fun i => I i \ E
  let R : ℕ := 64 * (C + 1)
  let H : SimpleGraph ι := LargeCrossMatchingGraph G U R
  have hIdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j) := by
    intro i j hij
    apply (hregions i j hij).mono
    · exact ((trimOneFinset_subset _).trans (shrinkFinset_subset _ _)).trans
        Finset.subset_union_left
    · exact ((trimOneFinset_subset _).trans (shrinkFinset_subset _ _)).trans
        Finset.subset_union_left
  obtain ⟨X, hXcard, hEX, hsep⟩ :=
    exists_sparse_selected_exceptional_set_separating_largeCrossMatching_components
      G I M hM hmax hIdisj R
  have hnum := one_extra_fullCore_component_numerics
    hP hPeven hqlarge hquotLower hquotUpper
  dsimp only at hnum
  have hUsub : ∀ i, U i ⊆ A i ∪ B i := by
    intro i
    exact Finset.sdiff_subset.trans
      ((trimOneFinset_subset _).trans (shrinkFinset_subset _ _))
  have hcomp : ∀ c : H.ConnectedComponent, c.supp.ncard < C + 1 := by
    intro c
    apply ncard_component_lt_succ_of_cycleFree_fullCore_at_scale
      G A B D U (q := q) (theta := theta) (R := R) (k := k)
        (L := C) (by omega) hscaffold hrob hmajorD hAcard hregions
        hUsub hmatch (hnum.1.trans htheta) hnum.2.1 hnum.2.2.1 hk
        hnum.2.2.2.1 hnum.2.2.2.2 hcycle
  have hpiece : ∀ i, (I i \ X).card ≤ tau - 1 := by
    intro i
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (hIcard i)
  have hblocks : ∀ c : H.ConnectedComponent,
      (c.supp.toFinset.biUnion fun i => I i \ X).card ≤ k - 1 := by
    apply card_component_biUnion_le_pred_of_exact_cores
      H (fun i => I i \ X) (C := C) (tau := tau) (k := k)
        hCpos hpiece rfl hcomp
  exact ⟨X, hXcard, hEX, hsep, hcomp, hblocks⟩

/-! ## Coverage accounting for the eventual stability family -/

/-- A finite family split into good and bad regions loses vertices from only
four sources after retaining a trimmed good core: the original uncovered
set, all bad regions, the discarded part of every good region, and the one
global exceptional set.  The statement deliberately uses only upper bounds,
so it can be instantiated by the exact eighth-root scaffold data without
unfolding any graph structure. -/
theorem card_compl_good_trimmed_union_le
    {V : Type*} [Fintype V]
    {F : Finset (Finset V)} (Good : F → Prop)
    (I : {i : F // Good i} → Finset V) (X : Finset V)
    {L u regionBound discardBound E : ℕ}
    (hleft : ((Finset.univ : Finset V) \ F.biUnion id).card ≤ L)
    (hbad : Fintype.card {i : F // ¬ Good i} ≤ u)
    (hregion : ∀ i : F, (i : Finset V).card ≤ regionBound)
    (hdiscard : ∀ i : {i : F // Good i},
      ((i.1 : Finset V) \ I i).card ≤ discardBound)
    (hX : X.card ≤ E) :
    ((Finset.univ : Finset V) \
        (Finset.univ : Finset {i : F // Good i}).biUnion
          (fun i => I i \ X)).card ≤
      L + u * regionBound +
        Fintype.card {i : F // Good i} * discardBound + E := by
  classical
  let BadUnion : Finset V :=
    (Finset.univ : Finset {i : F // ¬ Good i}).biUnion
      (fun i => (i.1 : Finset V))
  let DiscardUnion : Finset V :=
    (Finset.univ : Finset {i : F // Good i}).biUnion
      (fun i => (i.1 : Finset V) \ I i)
  let Left : Finset V := (Finset.univ : Finset V) \ F.biUnion id
  let Charge : Finset V := ((Left ∪ BadUnion) ∪ DiscardUnion) ∪ X
  have hsub :
      (Finset.univ : Finset V) \
          (Finset.univ : Finset {i : F // Good i}).biUnion
            (fun i => I i \ X) ⊆ Charge := by
    intro v hv
    have hvnot : v ∉ (Finset.univ : Finset {i : F // Good i}).biUnion
        (fun i => I i \ X) := (Finset.mem_sdiff.mp hv).2
    by_cases hvF : v ∈ F.biUnion id
    · rcases Finset.mem_biUnion.mp hvF with ⟨H, hHF, hvH⟩
      let i : F := ⟨H, hHF⟩
      by_cases hi : Good i
      · let j : {i : F // Good i} := ⟨i, hi⟩
        by_cases hvI : v ∈ I j
        · have hvX : v ∈ X := by
            by_contra hvX
            apply hvnot
            exact Finset.mem_biUnion.mpr
              ⟨j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hvI, hvX⟩⟩
          exact Finset.mem_union_right _ hvX
        · have hvD : v ∈ DiscardUnion := by
            apply Finset.mem_biUnion.mpr
            refine ⟨j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, hvI⟩⟩
            simpa [j, i] using hvH
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hvD)
      · have hvB : v ∈ BadUnion := by
          let j : {i : F // ¬ Good i} := ⟨i, hi⟩
          exact Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ _, by simpa [j, i] using hvH⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hvB))
    · have hvL : v ∈ Left := Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, hvF⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hvL))
  have hBadCard : BadUnion.card ≤ u * regionBound := by
    calc
      BadUnion.card ≤
          (Finset.univ : Finset {i : F // ¬ Good i}).card * regionBound := by
        apply Finset.card_biUnion_le_card_mul
        intro i _hi
        exact hregion i.1
      _ = Fintype.card {i : F // ¬ Good i} * regionBound := by simp
      _ ≤ u * regionBound := Nat.mul_le_mul_right _ hbad
  have hDiscardCard : DiscardUnion.card ≤
      Fintype.card {i : F // Good i} * discardBound := by
    calc
      DiscardUnion.card ≤
          (Finset.univ : Finset {i : F // Good i}).card * discardBound := by
        apply Finset.card_biUnion_le_card_mul
        intro i _hi
        exact hdiscard i
      _ = Fintype.card {i : F // Good i} * discardBound := by simp
  have hChargeCard : Charge.card ≤
      Left.card + BadUnion.card + DiscardUnion.card + X.card := by
    calc
      Charge.card ≤ ((Left ∪ BadUnion) ∪ DiscardUnion).card + X.card :=
        Finset.card_union_le _ _
      _ ≤ (Left ∪ BadUnion).card + DiscardUnion.card + X.card := by
        exact Nat.add_le_add_right
          (Finset.card_union_le (Left ∪ BadUnion) DiscardUnion) X.card
      _ ≤ Left.card + BadUnion.card + DiscardUnion.card + X.card := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le Left BadUnion)
            DiscardUnion.card) X.card
  calc
    ((Finset.univ : Finset V) \
        (Finset.univ : Finset {i : F // Good i}).biUnion
          (fun i => I i \ X)).card ≤ Charge.card := Finset.card_le_card hsub
    _ ≤ Left.card + BadUnion.card + DiscardUnion.card + X.card := hChargeCard
    _ ≤ L + u * regionBound +
        Fintype.card {i : F // Good i} * discardBound + E := by
      have hLeft : Left.card ≤ L := by simpa [Left] using hleft
      omega

/-- The square-room quotient estimate supplies every numerical hypothesis of
the logarithmic selected-edge density theorem when its BFS depth is the
source scale `P`.  The explicit `delta` is one more than the required margin,
which keeps the later exceptional-set accounting polynomial. -/
theorem one_extra_fullCore_density_numerics
    {P q k s : ℕ} (hP : 3 ≤ P) (hqlarge : 16 * (P + 1) ^ 2 ≤ q)
    (hquotLower : P * q ≤ k) (hquotUpper : k < P * (q + 1))
    (hlog : 2 * Nat.log 2 s ≤ P) :
    let δ := 32 * (P + 1) * (Nat.log 2 s + 1) + 1
    2 * ((8 * (P + 1)) * 2 * (Nat.log 2 s + 1)) < δ ∧
      ∀ l : ℕ, P ≤ l →
        l ≤ 8 * (P + 1) + 2 * Nat.log 2 s →
        18 * l ≤ k ∧ k / 2 ≤ (l - 1) * (q - 5) := by
  let δ := 32 * (P + 1) * (Nat.log 2 s + 1) + 1
  have hmargin :
      2 * ((8 * (P + 1)) * 2 * (Nat.log 2 s + 1)) < δ := by
    dsimp [δ]
    ring_nf
    omega
  refine ⟨hmargin, ?_⟩
  intro l hl hlu
  have hq256 : 256 ≤ q := by nlinarith [hqlarge]
  have hl12 : l ≤ 12 * P := by omega
  have hbase : 18 * l ≤ k := by
    calc
      18 * l ≤ 216 * P := by omega
      _ ≤ P * q := by nlinarith
      _ ≤ k := hquotLower
  have hroom : P * (q + 1) ≤ 2 * ((P - 1) * (q - 5)) := by
    have hPsub : P - 1 + 1 = P := by omega
    have hqsub : q - 5 + 5 = q := by omega
    nlinarith [hqlarge]
  have hkraw : k ≤ 2 * ((l - 1) * (q - 5)) := by
    calc
      k ≤ P * (q + 1) := hquotUpper.le
      _ ≤ 2 * ((P - 1) * (q - 5)) := hroom
      _ ≤ 2 * ((l - 1) * (q - 5)) := by
        gcongr
  have hhalf : k / 2 ≤ (l - 1) * (q - 5) :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hkraw)
  exact ⟨hbase, hhalf⟩

/-- Component blocks may become empty after one global deletion.  Erasing the
empty image gives the same covered union and retains all separation, disjoint-
ness, and capacity conclusions, without requiring a wasteful per-core bound
on the global exceptional set. -/
theorem exists_nonempty_anticomplete_largeCrossMatching_component_block_family
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (H : SimpleGraph ι)
    (U : ι → Finset V) (X : Finset V) {k : ℕ}
    (hUdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hsep : ∀ c d : H.ConnectedComponent, c ≠ d →
        ∀ i ∈ c.supp, ∀ j ∈ d.supp,
          ∀ a ∈ U i \ X, ∀ b ∈ U j \ X, ¬ G.Adj a b)
    (hcard : ∀ c : H.ConnectedComponent,
        (c.supp.toFinset.biUnion fun i => U i \ X).card ≤ k - 1) :
    let block : H.ConnectedComponent → Finset V :=
      fun c => c.supp.toFinset.biUnion fun i => U i \ X
    ∃ F : Finset (Finset V),
      F = (Finset.univ.image block).erase ∅ ∧
      (∀ A ∈ F, A.Nonempty) ∧ DisjointFinsetFamily F ∧
      PairwiseAnticomplete G F ∧
      (∀ A ∈ F, A.card ≤ k - 1) ∧
      F.biUnion id = (Finset.univ : Finset ι).biUnion fun i => U i \ X := by
  classical
  let block : H.ConnectedComponent → Finset V :=
    fun c => c.supp.toFinset.biUnion fun i => U i \ X
  let F₀ : Finset (Finset V) := Finset.univ.image block
  let F : Finset (Finset V) := F₀.erase ∅
  have hmem (c : H.ConnectedComponent) (v : V) :
      v ∈ block c ↔ ∃ i : ι, i ∈ c.supp ∧ v ∈ U i \ X := by
    simp [block]
  refine ⟨F, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    have hne : A ≠ ∅ := (Finset.mem_erase.mp hA).1
    exact Finset.nonempty_iff_ne_empty.mpr hne
  · intro A hA B hB hAB
    rcases Finset.mem_image.mp (Finset.mem_erase.mp hA).2 with ⟨c, _hc, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_erase.mp hB).2 with ⟨d, _hd, rfl⟩
    have hcd : c ≠ d := by
      intro h
      apply hAB
      subst d
      rfl
    rw [Finset.disjoint_left]
    intro v hvc hvd
    rcases (hmem c v).1 hvc with ⟨i, hic, hvi⟩
    rcases (hmem d v).1 hvd with ⟨j, hjd, hvj⟩
    by_cases hij : i = j
    · subst j
      exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hic hjd)
    · exact (Finset.disjoint_left.mp (hUdisj i j hij))
        (Finset.mem_sdiff.mp hvi).1 (Finset.mem_sdiff.mp hvj).1
  · intro A hA B hB hAB a ha b hb hab
    rcases Finset.mem_image.mp (Finset.mem_erase.mp hA).2 with ⟨c, _hc, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_erase.mp hB).2 with ⟨d, _hd, rfl⟩
    have hcd : c ≠ d := by
      intro h
      apply hAB
      subst d
      rfl
    rcases (hmem c a).1 ha with ⟨i, hic, hai⟩
    rcases (hmem d b).1 hb with ⟨j, hjd, hbj⟩
    exact hsep c d hcd i hic j hjd a hai b hbj hab
  · intro A hA
    rcases Finset.mem_image.mp (Finset.mem_erase.mp hA).2 with ⟨c, _hc, rfl⟩
    exact hcard c
  · ext v
    constructor
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨A, hAF, hvA⟩
      rcases Finset.mem_image.mp (Finset.mem_erase.mp hAF).2 with ⟨c, _hc, rfl⟩
      rcases (hmem c v).1 hvA with ⟨i, _hic, hvi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvi⟩
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨i, _hi, hvi⟩
      let c : H.ConnectedComponent := H.connectedComponentMk i
      have hvblock : v ∈ block c := (hmem c v).2
        ⟨i, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, hvi⟩
      have hne : block c ≠ ∅ := by
        exact Finset.nonempty_iff_ne_empty.mp ⟨v, hvblock⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨block c, Finset.mem_erase.mpr
        ⟨hne, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩, hvblock⟩

/-- Exact equal-sized cores in pairwise-disjoint regions bound the number of
regions by the ambient order. -/
theorem mul_card_le_ambient_of_disjoint_equal_core_family
    {V ι : Type*} [Fintype V] [Fintype ι]
    (A : ι → Finset V) (q : ℕ)
    (hcard : ∀ i, (A i).card = q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    q * Fintype.card ι ≤ Fintype.card V := by
  classical
  have hpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint A := by
    intro i _hi j _hj hij
    exact hdisj i j hij
  calc
    q * Fintype.card ι = ∑ i : ι, (A i).card := by
      simp [hcard, Nat.mul_comm]
    _ = ((Finset.univ : Finset ι).biUnion A).card := by
      simpa using (Finset.card_biUnion hpair).symm
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := by simp

/-- If `E` is already contained in the later global deletion `X`, deleting
`E` before `X` has no further effect. -/
theorem sdiff_sdiff_eq_sdiff_of_subset
    {V : Type*} [DecidableEq V] (S E X : Finset V) (hEX : E ⊆ X) :
    (S \ E) \ X = S \ X := by
  ext v
  simp only [Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, fun hvE => h.2 (hEX hvE)⟩, h.2⟩

/-- Eventual source-scale stability output.  The blocks are nonempty,
pairwise disjoint and anticomplete, each has order at most `k-1`, and the
displayed explicit polynomial accounts for every omitted vertex. -/
theorem eventually_exists_one_extra_component_seed_family
    (Bdiv : ℕ) (hBdiv : 16 ≤ Bdiv) :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, 3 ≤ n → n ≤ k →
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = (k - 1) * (n - 1) + 1 →
        G.IndepSetFree n →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
        let R : ℕ := 4 * Bdiv
        let P : ℕ := 8 * (r + 1) * R ^ 5
        let q : ℕ := k / P
        let K : ℕ := k / (4 * ((r + 1) * R ^ 5) ^ 2) + 1
        let C : ℕ := P / 2 + 1
        let tau : ℕ := k / C
        let N : ℕ := Fintype.card V
        let jBound : ℕ := N / q
        let deltaN : ℕ := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
        let selectedBound : ℕ :=
          (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
        let exceptionalBound : ℕ :=
          (2 * (64 * (C + 1)) + 2) * selectedBound
        let leftBound : ℕ :=
          16 * ((n - 1) * (((k - 1) / Bdiv - 1) + 1))
        let regionBound : ℕ := 2 * q + K
        let discardBound : ℕ := (2 * q - (tau - 1)) + K
        ∃ Q : Finset (Finset V),
          (∀ A ∈ Q, A.Nonempty) ∧ DisjointFinsetFamily Q ∧
          PairwiseAnticomplete G Q ∧
          (∀ A ∈ Q, A.card ≤ k - 1) ∧
          ((Finset.univ : Finset V) \ Q.biUnion id).card ≤
            leftBound + (n - 1) * regionBound +
              jBound * discardBound + exceptionalBound := by
  filter_upwards
    [eventually_exists_divisor_eighthRoot_core_family_with_unbroken_card_lt_exact_scale
      Bdiv hBdiv,
     eventually_divisor_eighthRoot_exact_scale_accounting_numerics Bdiv hBdiv,
     eventually_divisor_eighthRoot_exact_scale_square_room Bdiv hBdiv]
      with k hfamily haccount hsquare
  intro n hn hnk V instV G instG hcardV hfree hcycle
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  let R : ℕ := 4 * Bdiv
  let P : ℕ := 8 * (r + 1) * R ^ 5
  let q : ℕ := k / P
  let K : ℕ := k / (4 * ((r + 1) * R ^ 5) ^ 2) + 1
  let C : ℕ := P / 2 + 1
  let tau : ℕ := k / C
  let N : ℕ := Fintype.card V
  let jBound : ℕ := N / q
  let deltaN : ℕ := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
  let selectedBound : ℕ :=
    (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
  let exceptionalBound : ℕ :=
    (2 * (64 * (C + 1)) + 2) * selectedBound
  let leftBound : ℕ :=
    16 * ((n - 1) * (((k - 1) / Bdiv - 1) + 1))
  let regionBound : ℕ := 2 * q + K
  let discardBound : ℕ := (2 * q - (tau - 1)) + K
  have hnum : 16 ≤ r ∧ 3 ≤ P ∧ 80 * (P + 1) ≤ q ∧
      4 * (Nat.log 2 k + 1) ≤ P := by
    simpa [r, R, P, q] using haccount
  have hsquare' : 16 * (P + 1) ^ 2 ≤ q := by
    simpa [r, R, P, q] using hsquare
  obtain ⟨F, A, Bside, D, hdata, hregions, hleft, hunbroken⟩ :=
    hfamily n hn hnk G hcardV hfree hcycle
  let Good : F → Prop := fun i => HasThreeDisjointAdjPairFamily G (A i)
  let J := {i : F // Good i}
  let AJ : J → Finset V := fun i => A i.1
  let BJ : J → Finset V := fun i => Bside i.1
  let DJ : J → Finset V := fun i => D i.1
  have hP : 3 ≤ P := hnum.2.1
  have hqpos : 0 < q := by nlinarith [hsquare']
  have hPeven : 2 * (P / 2) = P := by
    apply Nat.two_mul_div_two_of_even
    refine ⟨4 * (r + 1) * R ^ 5, ?_⟩
    dsimp [P]
    ring
  have hquotLower : P * q ≤ k := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self k P
  have hquotUpper : k < P * (q + 1) := by
    have hPpos : 0 < P := by omega
    simpa [q] using Nat.lt_mul_div_succ k hPpos
  have hAcard : ∀ i : F, (A i).card = q := fun i => (hdata i).1
  have hAdisj : ∀ i j : F, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    exact (hregions i j hij).mono
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (Finset.subset_union_left.trans Finset.subset_union_left)
  have hFmul : q * Fintype.card F ≤ N := by
    simpa [N] using
      (mul_card_le_ambient_of_disjoint_equal_core_family A q hAcard hAdisj)
  have hJF : Fintype.card J ≤ Fintype.card F := by
    apply Fintype.card_le_of_injective (fun i : J => i.1)
    exact Subtype.val_injective
  have hJmul : q * Fintype.card J ≤ N :=
    (Nat.mul_le_mul_left q hJF).trans hFmul
  have hJbound : Fintype.card J ≤ jBound := by
    dsimp [jBound]
    exact (Nat.le_div_iff_mul_le hqpos).2 (by
      simpa [Nat.mul_comm] using hJmul)
  have hJN : Fintype.card J ≤ N := by
    have hqone : 1 ≤ q := hqpos
    nlinarith
  have hlogJN : Nat.log 2 (Fintype.card J) ≤ Nat.log 2 N :=
    Nat.log_mono_right hJN
  have hlogN : Nat.log 2 N ≤ 2 * (Nat.log 2 k + 1) := by
    simpa [N, hcardV] using
      (log_extremal_order_le_two_mul_log_add_one (k := k) (n := n)
        (by omega) hnk)
  have hlogJ : 2 * Nat.log 2 (Fintype.card J) ≤ P := by
    calc
      2 * Nat.log 2 (Fintype.card J) ≤ 2 * Nat.log 2 N :=
        Nat.mul_le_mul_left 2 hlogJN
      _ ≤ 4 * (Nat.log 2 k + 1) := by omega
      _ ≤ P := hnum.2.2.2
  have hleft' :
      ((Finset.univ : Finset V) \ F.biUnion id).card ≤ leftBound := by
    simpa [leftBound] using hleft.le
  have hbad : Fintype.card {i : F // ¬ Good i} ≤ n - 1 := by
    have hlt : Fintype.card {i : F // ¬ Good i} < n := by
      simpa [Good] using hunbroken
    omega
  have hregion : ∀ i : F, (i : Finset V).card ≤ regionBound := by
    intro i
    have hi := (hdata i).2.2.2.2.2.1
    simpa [regionBound] using hi.le
  classical
  by_cases hJne : Nonempty J
  · letI : Nonempty J := hJne
    let I : J → Finset V := fun i =>
      trimOneFinset (shrinkFinset (AJ i ∪ BJ i) tau)
    let deltaJ : ℕ :=
      32 * (P + 1) * (Nat.log 2 (Fintype.card J) + 1) + 1
    have hdensity := one_extra_fullCore_density_numerics
      hP hsquare' hquotLower hquotUpper hlogJ
    dsimp only at hdensity
    have hout := exists_sparse_fullCore_separator_with_small_blocks_one_extra
      (q := q) (P := P) (theta := 8 * P + 1) (k := k)
      (b := 2) (D₀ := P) (δ := deltaJ) G AJ BJ DJ
      hP hPeven hsquare' (by rfl)
      (fun i => (hdata i.1).2.2.2.2.2.2.1)
      (fun i => (hdata i.1).2.2.2.2.2.2.2)
      (fun i => (hdata i.1).2.2.2.1)
      (fun i => (hdata i.1).1)
      (by omega)
      (by
        intro i j hij
        apply hregions i.1 j.1
        intro h
        exact hij (Subtype.ext h))
      (fun i => i.2) (by norm_num) hP hdensity.1 hdensity.2 (by omega) hcycle
    dsimp only at hout
    obtain ⟨M, hM, hmax, hMcard, hfringe, X, hXcard, hEX, hsep,
      hcomp, hblocks⟩ := hout
    have hIdisj : ∀ i j : J, i ≠ j → Disjoint (I i) (I j) := by
      intro i j hij
      apply (hregions i.1 j.1 (by
        intro h
        exact hij (Subtype.ext h))).mono
      · exact ((trimOneFinset_subset _).trans (shrinkFinset_subset _ _)).trans
          Finset.subset_union_left
      · exact ((trimOneFinset_subset _).trans (shrinkFinset_subset _ _)).trans
          Finset.subset_union_left
    obtain ⟨Q, hQdef, hQne, hQdisj, hQanti, hQcard, hQunion⟩ :=
      exists_nonempty_anticomplete_largeCrossMatching_component_block_family
        G _ I X hIdisj hsep hblocks
    have hDcard : ∀ i : J, (DJ i).card ≤ K := by
      intro i
      have hregionEq := (hdata i.1).2.2.2.2.1
      have hregionLt := (hdata i.1).2.2.2.2.2.1
      have hcoreCard : (AJ i ∪ BJ i).card = 2 * q := by
        calc
          (AJ i ∪ BJ i).card = (AJ i).card + (BJ i).card :=
            Finset.card_union_of_disjoint (hdata i.1).2.2.1
          _ = q + q := by
            rw [(hdata i.1).1, (hdata i.1).2.1]
          _ = 2 * q := by omega
      have hregionCard : (i.1 : Finset V).card =
          (AJ i ∪ BJ i).card + (DJ i).card := by
        calc
          (i.1 : Finset V).card = ((AJ i ∪ BJ i) ∪ DJ i).card := by
            simpa [AJ, BJ, DJ] using congrArg Finset.card hregionEq
          _ = (AJ i ∪ BJ i).card + (DJ i).card :=
            Finset.card_union_of_disjoint (hdata i.1).2.2.2.1
      change (i.1 : Finset V).card < 2 * q + K at hregionLt
      omega
    have hdiscard : ∀ i : J,
        ((i.1 : Finset V) \ I i).card ≤ discardBound := by
      intro i
      have hregionEq := (hdata i.1).2.2.2.2.1
      have hsub : (i.1 : Finset V) \ I i ⊆
          ((AJ i ∪ BJ i) \ I i) ∪ DJ i := by
        intro v hv
        rw [hregionEq] at hv
        rcases Finset.mem_sdiff.mp hv with ⟨hvreg, hvI⟩
        rcases Finset.mem_union.mp hvreg with hvcore | hvD
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvcore, hvI⟩)
        · exact Finset.mem_union_right _ hvD
      calc
        ((i.1 : Finset V) \ I i).card ≤
            (((AJ i ∪ BJ i) \ I i) ∪ DJ i).card := Finset.card_le_card hsub
        _ ≤ ((AJ i ∪ BJ i) \ I i).card + (DJ i).card :=
          Finset.card_union_le _ _
        _ ≤ (2 * q - (tau - 1)) + K :=
          Nat.add_le_add (by
            simpa [I, C, tau, AJ, BJ] using (hfringe i).le)
            (hDcard i)
        _ = discardBound := by rfl
    have hdelta : deltaJ ≤ deltaN := by
      dsimp [deltaJ, deltaN]
      gcongr
    have hselected : M.card ≤ selectedBound := by
      calc
        M.card ≤
            (2 + 2 * (Nat.log 2 (Fintype.card J) + 1)) *
              (4 * deltaJ * Fintype.card J) := hMcard
        _ ≤ (2 + 2 * (Nat.log 2 N + 1)) *
              (4 * deltaN * jBound) := by gcongr
        _ = selectedBound := by rfl
    have hXbound : X.card ≤ exceptionalBound := by
      calc
        X.card ≤ (2 * (64 * (C + 1)) + 2) * M.card := by
          simpa [C] using hXcard
        _ ≤ (2 * (64 * (C + 1)) + 2) * selectedBound := by
          gcongr
        _ = exceptionalBound := by rfl
    have hcov := card_compl_good_trimmed_union_le
      (V := V) (F := F) Good I X
      (L := leftBound) (u := n - 1) (regionBound := regionBound)
      (discardBound := discardBound) (E := exceptionalBound)
      hleft' hbad hregion hdiscard hXbound
    refine ⟨Q, hQne, hQdisj, hQanti, hQcard, ?_⟩
    rw [hQunion]
    exact hcov.trans (by
      gcongr)
  · have hJempty : IsEmpty J := ⟨fun i => hJne ⟨i⟩⟩
    letI : IsEmpty J := hJempty
    have hJcard : Fintype.card J = 0 := Fintype.card_eq_zero
    let I : J → Finset V := fun i =>
      trimOneFinset (shrinkFinset (AJ i ∪ BJ i) tau)
    have hdiscard : ∀ i : J,
        ((i.1 : Finset V) \ I i).card ≤ discardBound := by
      intro i
      exact isEmptyElim i
    have hcov := card_compl_good_trimmed_union_le
      (V := V) (F := F) Good I ∅
      (L := leftBound) (u := n - 1) (regionBound := regionBound)
      (discardBound := discardBound) (E := 0)
      hleft' hbad hregion hdiscard (by simp)
    refine ⟨∅, by simp, ?_, ?_, by simp, ?_⟩
    · intro A hA
      simp at hA
    · intro A hA
      simp at hA
    · have hcov' : (Finset.univ : Finset V).card ≤
          leftBound + (n - 1) * regionBound := by
        simpa [hJcard] using hcov
      calc
        ((Finset.univ : Finset V) \ (∅ : Finset V)).card =
            (Finset.univ : Finset V).card := by simp
        _ ≤ leftBound + (n - 1) * regionBound := hcov'
        _ ≤ (leftBound + (n - 1) * regionBound) +
            (jBound * discardBound + exceptionalBound) := Nat.le_add_right _ _
        _ = leftBound + (n - 1) * regionBound +
            jBound * discardBound + exceptionalBound := by ring

/-- Four independent quarter-budget estimates combine into the final global
coverage estimate.  Writing the selected and exceptional bounds as a
coefficient times `jBound` isolates all asymptotic work in one coefficient. -/
theorem one_extra_coverage_sum_le_of_four_charges
    {S N q jBound leftBound unbrokenBound discardBound
      exceptionalCoef : ℕ}
    (hj : q * jBound ≤ N)
    (hleft : 4 * S * leftBound ≤ N)
    (hunbroken : 4 * S * unbrokenBound ≤ N)
    (hdiscard : 4 * S * discardBound ≤ q)
    (hexceptional : 4 * S * exceptionalCoef ≤ q) :
    S * (leftBound + unbrokenBound +
      jBound * discardBound + exceptionalCoef * jBound) ≤ N := by
  have hdiscard' : 4 * S * (jBound * discardBound) ≤ N := by
    calc
      4 * S * (jBound * discardBound) = jBound * (4 * S * discardBound) := by ring
      _ ≤ jBound * q := Nat.mul_le_mul_left _ hdiscard
      _ = q * jBound := by ring
      _ ≤ N := hj
  have hexceptional' : 4 * S * (exceptionalCoef * jBound) ≤ N := by
    calc
      4 * S * (exceptionalCoef * jBound) =
          jBound * (4 * S * exceptionalCoef) := by ring
      _ ≤ jBound * q := Nat.mul_le_mul_left _ hexceptional
      _ = q * jBound := by ring
      _ ≤ N := hj
  have hsum : 4 * S * (leftBound + unbrokenBound +
      jBound * discardBound + exceptionalCoef * jBound) ≤ 4 * N := by
    calc
      4 * S * (leftBound + unbrokenBound +
          jBound * discardBound + exceptionalCoef * jBound) =
          4 * S * leftBound + 4 * S * unbrokenBound +
            4 * S * (jBound * discardBound) +
              4 * S * (exceptionalCoef * jBound) := by ring
      _ ≤ N + N + N + N := by omega
      _ = 4 * N := by ring
  nlinarith

/-- Deterministic wrapper reducing the explicit source-scale coverage formula
to three local asymptotic estimates: the thin-core fringe, the connector
reservoir, and the selected-endpoint coefficient. -/
theorem one_extra_explicit_coverage_bound_small
    {S B P q K C tau k n N : ℕ}
    (hS : 1 ≤ S) (hn : 3 ≤ n) (hqpos : 0 < q)
    (hqdef : q = k / P) (hN : N = (k - 1) * (n - 1) + 1)
    (hB : 256 * S ≤ B) (hk : 256 * S + 1 ≤ k)
    (hP : 16 * S + 1 ≤ P) (hKle : K ≤ 2 * q)
    (hfringe : 8 * S * (2 * q - (tau - 1)) ≤ q)
    (hKsmall : 8 * S * K ≤ q)
    (hexceptional :
      4 * S * ((2 * (64 * (C + 1)) + 2) *
        (2 + 2 * (Nat.log 2 N + 1)) *
          (4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1))) ≤ q) :
    let jBound := N / q
    let deltaN := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
    let selectedBound :=
      (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
    let exceptionalBound :=
      (2 * (64 * (C + 1)) + 2) * selectedBound
    let leftBound := 16 * ((n - 1) * (((k - 1) / B - 1) + 1))
    let regionBound := 2 * q + K
    let discardBound := (2 * q - (tau - 1)) + K
    S * (leftBound + (n - 1) * regionBound +
      jBound * discardBound + exceptionalBound) ≤ N := by
  let jBound : ℕ := N / q
  let deltaN : ℕ := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
  let selectedBound : ℕ :=
    (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
  let exceptionalBound : ℕ :=
    (2 * (64 * (C + 1)) + 2) * selectedBound
  let leftBound : ℕ :=
    16 * ((n - 1) * (((k - 1) / B - 1) + 1))
  let regionBound : ℕ := 2 * q + K
  let discardBound : ℕ := (2 * q - (tau - 1)) + K
  let exceptionalCoef : ℕ :=
    (2 * (64 * (C + 1)) + 2) *
      (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN)
  have hj : q * jBound ≤ N := by
    dsimp [jBound]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N q
  have hleft : 4 * S * leftBound ≤ N := by
    let x : ℕ := (k - 1) / B
    let y : ℕ := (x - 1) + 1
    have hy : y ≤ x + 1 := by
      dsimp [y]
      exact Nat.add_le_add_right (Nat.sub_le x 1) 1
    have hBx : B * x ≤ k - 1 := by
      dsimp [x]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (k - 1) B
    have hxquarter : 4 * (64 * S * x) ≤ k - 1 := by
      calc
        4 * (64 * S * x) = (256 * S) * x := by ring
        _ ≤ B * x := Nat.mul_le_mul_right x hB
        _ ≤ k - 1 := hBx
    have honequarter : 4 * (64 * S) ≤ k - 1 := by
      have : 256 * S ≤ k - 1 := by omega
      simpa [show 4 * (64 * S) = 256 * S by ring] using this
    have hcoef : 64 * S * y ≤ k - 1 := by
      have hxy : 64 * S * y ≤ 64 * S * x + 64 * S := by
        calc
          64 * S * y ≤ 64 * S * (x + 1) := Nat.mul_le_mul_left _ hy
          _ = 64 * S * x + 64 * S := by ring
      omega
    have hmul := Nat.mul_le_mul_right (n - 1) hcoef
    change 4 * S * (16 * ((n - 1) * y)) ≤ N
    rw [hN]
    calc
      4 * S * (16 * ((n - 1) * y)) =
          (64 * S * y) * (n - 1) := by ring
      _ ≤ (k - 1) * (n - 1) := hmul
      _ ≤ (k - 1) * (n - 1) + 1 := Nat.le_add_right _ _
  have hunbroken : 4 * S * ((n - 1) * regionBound) ≤ N := by
    have hregion : regionBound ≤ 4 * q := by
      dsimp [regionBound]
      omega
    have hPq : P * q ≤ k := by
      rw [hqdef]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self k P
    have hcoeflt : 4 * S * regionBound < P * q := by
      have hq : 4 * S * regionBound ≤ 16 * S * q := by
        calc
          4 * S * regionBound ≤ 4 * S * (4 * q) :=
            Nat.mul_le_mul_left _ hregion
          _ = 16 * S * q := by ring
      have hstrict : 16 * S * q < P * q := by
        exact Nat.mul_lt_mul_of_pos_right (by omega) hqpos
      exact hq.trans_lt hstrict
    have hcoef : 4 * S * regionBound ≤ k - 1 := by omega
    have hmul := Nat.mul_le_mul_right (n - 1) hcoef
    rw [hN]
    nlinarith
  have hdiscard : 4 * S * discardBound ≤ q := by
    dsimp [discardBound]
    have hadd : 8 * S * ((2 * q - (tau - 1)) + K) ≤ 2 * q := by
      calc
        8 * S * ((2 * q - (tau - 1)) + K) =
            8 * S * (2 * q - (tau - 1)) + 8 * S * K := by ring
        _ ≤ q + q := Nat.add_le_add hfringe hKsmall
        _ = 2 * q := by ring
    nlinarith
  have hexceptional : 4 * S * exceptionalCoef ≤ q := by
    simpa [exceptionalCoef, deltaN, Nat.mul_assoc] using hexceptional
  have hExceptionalEq : exceptionalBound = exceptionalCoef * jBound := by
    dsimp [exceptionalBound, selectedBound, exceptionalCoef]
    ring
  change S * (leftBound + (n - 1) * regionBound +
    jBound * discardBound + exceptionalBound) ≤ N
  rw [hExceptionalEq]
  exact one_extra_coverage_sum_le_of_four_charges hj hleft hunbroken
    hdiscard hexceptional

/-- At the eighth-root scale the exact quotient eventually dominates any
fixed multiple of the fourth power of `P+1`.  This spare power pays for the
two logarithmic colors and the source-scale separator simultaneously. -/
theorem eventually_divisor_eighthRoot_exact_scale_fourth_room
    (B T : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let P : ℕ := 8 * (r + 1) * R ^ 5
      let q : ℕ := k / P
      T * (P + 1) ^ 4 ≤ q := by
  let R : ℕ := 4 * B
  let A : ℕ := 16 * T * 16 ^ 5 * R ^ 25
  let Q : ℕ := max 16 A
  have hRpos : 0 < R := by dsimp [R]; omega
  have htriple : Tendsto
      (fun k : ℕ => Nat.sqrt (Nat.sqrt (Nat.sqrt k))) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)
  filter_upwards [htriple.eventually (eventually_ge_atTop Q)] with k hrQ
  let s : ℕ := Nat.sqrt k
  let u : ℕ := Nat.sqrt s
  let r : ℕ := Nat.sqrt u
  let P : ℕ := 8 * (r + 1) * R ^ 5
  let q : ℕ := k / P
  have hr16 : 16 ≤ r :=
    (le_max_left 16 A).trans (by simpa [Q, r, u, s] using hrQ)
  have hrA : A ≤ r :=
    (le_max_right 16 A).trans (by simpa [Q, r, u, s] using hrQ)
  have hrpos : 0 < r := by omega
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hr2u : r ^ 2 ≤ u := by
    dsimp [r]
    exact Nat.sqrt_le' u
  have hu2s : u ^ 2 ≤ s := by
    dsimp [u]
    exact Nat.sqrt_le' s
  have hs2k : s ^ 2 ≤ k := by
    dsimp [s]
    exact Nat.sqrt_le' k
  have hr8k : r ^ 8 ≤ k := by
    calc
      r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
      _ ≤ (u ^ 2) ^ 2 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_left hr2u 2) 2
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hu2s 2
      _ ≤ k := hs2k
  have hPLe : P ≤ 16 * r * R ^ 5 := by
    have ha : r + 1 ≤ 2 * r := by omega
    calc
      P = 8 * (r + 1) * R ^ 5 := rfl
      _ ≤ 8 * (2 * r) * R ^ 5 := by gcongr
      _ = 16 * r * R ^ 5 := by ring
  have hPsucc : P + 1 ≤ 2 * P := by omega
  have hcoef : A ≤ r ^ 3 :=
    hrA.trans (Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) r)
  have hlargeProd : T * (P + 1) ^ 4 * P ≤ k := by
    calc
      T * (P + 1) ^ 4 * P ≤ T * (2 * P) ^ 4 * P := by gcongr
      _ = 16 * T * P ^ 5 := by ring
      _ ≤ 16 * T * (16 * r * R ^ 5) ^ 5 := by gcongr
      _ = r ^ 5 * A := by simp [A]; ring
      _ ≤ r ^ 5 * r ^ 3 := Nat.mul_le_mul_left _ hcoef
      _ = r ^ 8 := by ring
      _ ≤ k := hr8k
  change T * (P + 1) ^ 4 ≤ k / P
  exact (Nat.le_div_iff_mul_le hPpos).2 (by
    simpa [Nat.mul_assoc] using hlargeProd)

/-- The one-extra thinning loses a vanishing fraction of one exact core, and
the compact connector reservoir has the same property.  The proof uses only
the exact quotient inequalities for `P=8a` and the elementary identity
`C=4a+1`. -/
theorem one_extra_fringe_connector_numerics
    {S a k : ℕ} (hS : 1 ≤ S) (ha : 64 * S ≤ a) :
    let P : ℕ := 8 * a
    let q : ℕ := k / P
    let C : ℕ := P / 2 + 1
    let tau : ℕ := k / C
    let K : ℕ := k / (4 * a ^ 2) + 1
    64 * S * a ≤ q →
      K ≤ 2 * q ∧
      8 * S * (2 * q - (tau - 1)) ≤ q ∧
      8 * S * K ≤ q := by
  dsimp only
  intro hqscale
  let P : ℕ := 8 * a
  let q : ℕ := k / P
  let C : ℕ := P / 2 + 1
  let tau : ℕ := k / C
  let K : ℕ := k / (4 * a ^ 2) + 1
  have hqscale' : 64 * S * a ≤ q := by
    simpa [q, P] using hqscale
  have hapos : 0 < a := by omega
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hqpos : 0 < q := by
    have : 0 < 64 * S * a := by positivity
    omega
  have hq16S : 16 * S ≤ q := by
    have h64S : 64 * S ≤ 64 * S * a := by
      exact Nat.le_mul_of_pos_right _ hapos
    omega
  have hPq : P * q ≤ k := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k P
  have hkP : k < P * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ k hPpos
  have hPeven : 2 * (P / 2) = P := by
    apply Nat.two_mul_div_two_of_even
    refine ⟨4 * a, ?_⟩
    dsimp [P]
    ring
  have hCeq : C = 4 * a + 1 := by
    dsimp [C]
    rw [show (8 * a) / 2 = 4 * a by omega]
  let D : ℕ := 4 * a ^ 2
  let z : ℕ := k / D
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDz : D * z ≤ k := by
    dsimp [z]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k D
  have haz : a * z < 2 * (q + 1) := by
    by_contra hnot
    have hlo : 2 * (q + 1) ≤ a * z := by omega
    have hmul := Nat.mul_le_mul_left (4 * a) hlo
    have hEqD : (4 * a) * (a * z) = D * z := by dsimp [D]; ring
    have hEqP : (4 * a) * (2 * (q + 1)) = P * (q + 1) := by
      dsimp [P]
      ring
    rw [hEqD, hEqP] at hmul
    omega
  have hzsmall : 16 * S * z ≤ q := by
    have hmul : 32 * S * z ≤ a * z := by
      calc
        32 * S * z ≤ (64 * S) * z := by gcongr; omega
        _ ≤ a * z := Nat.mul_le_mul_right z ha
    nlinarith
  have hKsmall : 8 * S * K ≤ q := by
    have hK : K = z + 1 := by rfl
    rw [hK]
    have hzhalf : 8 * S * z ≤ q / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      have := hzsmall
      nlinarith
    have hShalf : 8 * S ≤ q / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      nlinarith [hq16S]
    nlinarith
  have hKle : K ≤ 2 * q := by
    have hfac : K ≤ 8 * S * K := by
      have : 1 ≤ 8 * S := by omega
      nlinarith
    exact hfac.trans (hKsmall.trans (Nat.le_mul_of_pos_left q (by omega)))
  have hCpos : 0 < C := by rw [hCeq]; positivity
  have hCt : C * tau ≤ k := by
    dsimp [tau]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self k C
  have hkC : k < C * (tau + 1) := by
    dsimp [tau]
    exact Nat.lt_mul_div_succ k hCpos
  have htUpper : tau ≤ 2 * q + 1 := by
    have h4at : 4 * a * tau ≤ C * tau := by
      rw [hCeq]
      gcongr
      omega
    by_contra hnot
    have ht : 2 * (q + 1) ≤ tau := by omega
    have hmul := Nat.mul_le_mul_left (4 * a) ht
    have hEq : 4 * a * (2 * (q + 1)) = P * (q + 1) := by
      dsimp [P]
      ring
    rw [hEq] at hmul
    omega
  have htpos : 0 < tau := by
    have hCleP : C ≤ P := by rw [hCeq]; dsimp [P]; omega
    have hPlek : P ≤ k := by
      calc
        P ≤ P * q := Nat.le_mul_of_pos_right P hqpos
        _ ≤ k := hPq
    dsimp [tau]
    exact Nat.div_pos (hCleP.trans hPlek) hCpos
  let f : ℕ := 2 * q - (tau - 1)
  have htPred : tau - 1 ≤ 2 * q := by omega
  have hfid : f + (tau - 1) = 2 * q := by
    dsimp [f]
    exact Nat.sub_add_cancel htPred
  have hsum : f + tau + 1 = 2 * q + 2 := by omega
  have hfringe : 8 * S * f ≤ q := by
    by_contra hnot
    have hqf : q < 8 * S * f := by omega
    have hfpos : 0 < f := by
      by_contra hf
      have hfzero : f = 0 := Nat.eq_zero_of_not_pos hf
      rw [hfzero, Nat.mul_zero] at hqf
      omega
    have hfa : 8 * a < f := by
      have hraw : 8 * S * (8 * a) < 8 * S * f := by
        calc
          8 * S * (8 * a) = 64 * S * a := by ring
          _ ≤ q := hqscale'
          _ < 8 * S * f := hqf
      exact (Nat.mul_lt_mul_left (by positivity : 0 < 8 * S)).mp (by
        simpa [Nat.mul_assoc] using hraw)
    rw [hCeq] at hkC
    dsimp [P] at hPq
    nlinarith
  refine ⟨hKle, ?_, hKsmall⟩
  simpa [f] using hfringe

/-- For every fixed accuracy denominator `S`, all four error terms in the
one-extra source-scale separator are eventually at most `1/S` of the
ambient extremal order.  The deliberately loose constant leaves the proof
as elementary natural-number arithmetic: the logarithmic exceptional
coefficient is bounded by a fourth power of the exact component scale. -/
theorem eventually_one_extra_explicit_coverage_bound_small
    (S : ℕ) (hS : 1 ≤ S) :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, 3 ≤ n → n ≤ k →
      let B : ℕ := 256 * S
      let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
      let R : ℕ := 4 * B
      let a : ℕ := (r + 1) * R ^ 5
      let P : ℕ := 8 * a
      let q : ℕ := k / P
      let K : ℕ := k / (4 * a ^ 2) + 1
      let C : ℕ := P / 2 + 1
      let tau : ℕ := k / C
      let N : ℕ := (k - 1) * (n - 1) + 1
      let jBound : ℕ := N / q
      let deltaN : ℕ := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
      let selectedBound : ℕ :=
        (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
      let exceptionalBound : ℕ :=
        (2 * (64 * (C + 1)) + 2) * selectedBound
      let leftBound : ℕ :=
        16 * ((n - 1) * (((k - 1) / B - 1) + 1))
      let regionBound : ℕ := 2 * q + K
      let discardBound : ℕ := (2 * q - (tau - 1)) + K
      S * (leftBound + (n - 1) * regionBound +
        jBound * discardBound + exceptionalBound) ≤ N := by
  let B : ℕ := 256 * S
  let T : ℕ := 600000 * S
  have hB : 16 ≤ B := by dsimp [B]; nlinarith
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  filter_upwards
    [eventually_divisor_eighthRoot_exact_scale_accounting_numerics B hB,
     eventually_divisor_eighthRoot_exact_scale_fourth_room B T (by omega),
     eventually_ge_atTop (256 * S + 1)]
      with k haccount hroom hk
  intro n hn hnk
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  let R : ℕ := 4 * B
  let a : ℕ := (r + 1) * R ^ 5
  let P : ℕ := 8 * a
  let q : ℕ := k / P
  let K : ℕ := k / (4 * a ^ 2) + 1
  let C : ℕ := P / 2 + 1
  let tau : ℕ := k / C
  let N : ℕ := (k - 1) * (n - 1) + 1
  have haccount' : 16 ≤ r ∧ 3 ≤ P ∧ 80 * (P + 1) ≤ q ∧
      4 * (Nat.log 2 k + 1) ≤ P := by
    simpa [r, R, a, P, q, Nat.mul_assoc] using haccount
  have hroom' : T * (P + 1) ^ 4 ≤ q := by
    simpa [r, R, a, P, q, Nat.mul_assoc] using hroom
  have hRpos : 0 < R := by dsimp [R, B]; positivity
  have hRpow : R ≤ R ^ 5 := by
    have hRone : 1 ≤ R := hRpos
    calc
      R = R * 1 := by omega
      _ ≤ R * R ^ 4 := by
        gcongr
        have : 0 < R ^ 4 := pow_pos hRpos 4
        omega
      _ = R ^ 5 := by ring
  have ha : 64 * S ≤ a := by
    calc
      64 * S ≤ B := by dsimp [B]; nlinarith
      _ ≤ R := by dsimp [R]; nlinarith
      _ ≤ R ^ 5 := hRpow
      _ ≤ (r + 1) * R ^ 5 := by
        exact Nat.le_mul_of_pos_left _ (by omega)
      _ = a := by rfl
  have hqscale : 64 * S * a ≤ q := by
    calc
      64 * S * a ≤ T * (P + 1) ^ 4 := by
        have haP : a ≤ P + 1 := by dsimp [P]; omega
        have haPow : a ≤ (P + 1) ^ 4 := by
          exact haP.trans (Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) (P + 1))
        have hST : 64 * S ≤ T := by dsimp [T]; nlinarith
        exact Nat.mul_le_mul hST haPow
      _ ≤ q := hroom'
  have hqpos : 0 < q := by
    have : 0 < 64 * S * a := by positivity
    omega
  obtain ⟨hKle, hfringe, hKsmall⟩ :=
    one_extra_fringe_connector_numerics hS ha (k := k) hqscale
  have hlogN : Nat.log 2 N ≤ 2 * (Nat.log 2 k + 1) := by
    simpa [N] using
      (log_extremal_order_le_two_mul_log_add_one (k := k) (n := n)
        (by omega) hnk)
  have hlogNP : Nat.log 2 N ≤ P := by
    omega
  have hCone : C + 1 ≤ 2 * (P + 1) := by
    dsimp [C]
    omega
  have hfirst : 2 * (64 * (C + 1)) + 2 ≤ 258 * (P + 1) := by
    nlinarith
  have hsecond : 2 + 2 * (Nat.log 2 N + 1) ≤ 4 * (P + 1) := by
    nlinarith
  have hthird :
      4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1) ≤
        132 * (P + 1) ^ 2 := by
    have hlogSucc : Nat.log 2 N + 1 ≤ P + 1 := by omega
    have hmul : (P + 1) * (Nat.log 2 N + 1) ≤ (P + 1) ^ 2 := by
      calc
        (P + 1) * (Nat.log 2 N + 1) ≤ (P + 1) * (P + 1) := by gcongr
        _ = (P + 1) ^ 2 := by ring
    have hPone : 1 ≤ (P + 1) ^ 2 := by
      have : 0 < (P + 1) ^ 2 := pow_pos (by omega) 2
      omega
    calc
      4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1) =
          128 * ((P + 1) * (Nat.log 2 N + 1)) + 4 := by ring
      _ ≤ 128 * (P + 1) ^ 2 + 4 := by gcongr
      _ ≤ 128 * (P + 1) ^ 2 + 4 * (P + 1) ^ 2 := by
        exact Nat.add_le_add_left (by
          simpa using Nat.mul_le_mul_left 4 hPone) _
      _ = 132 * (P + 1) ^ 2 := by ring
  have hexceptionalCoef :
      4 * S * ((2 * (64 * (C + 1)) + 2) *
        (2 + 2 * (Nat.log 2 N + 1)) *
          (4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1))) ≤
        T * (P + 1) ^ 4 := by
    calc
      4 * S * ((2 * (64 * (C + 1)) + 2) *
          (2 + 2 * (Nat.log 2 N + 1)) *
            (4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1))) ≤
          4 * S * (258 * (P + 1) * (4 * (P + 1)) *
            (132 * (P + 1) ^ 2)) := by gcongr
      _ = (544896 * S) * (P + 1) ^ 4 := by ring
      _ ≤ T * (P + 1) ^ 4 := by
        exact Nat.mul_le_mul_right ((P + 1) ^ 4) (by
          dsimp [T]
          exact Nat.mul_le_mul_right S (by norm_num))
  have hexceptional :
      4 * S * ((2 * (64 * (C + 1)) + 2) *
        (2 + 2 * (Nat.log 2 N + 1)) *
          (4 * (32 * (P + 1) * (Nat.log 2 N + 1) + 1))) ≤ q :=
    hexceptionalCoef.trans hroom'
  have hPscale : 16 * S + 1 ≤ P := by
    calc
      16 * S + 1 ≤ 64 * S := by omega
      _ ≤ a := ha
      _ ≤ 8 * a := Nat.le_mul_of_pos_left a (by omega)
      _ = P := by rfl
  simpa [B, r, R, a, P, q, K, C, tau, N] using
    (one_extra_explicit_coverage_bound_small
      (S := S) (B := B) (P := P) (q := q) (K := K) (C := C)
      (tau := tau) (k := k) (n := n) (N := N)
      hS hn hqpos rfl rfl (by rfl) hk hPscale hKle hfringe hKsmall
      hexceptional)

/-- Clean asymptotic stability interface extracted from the source-scale
construction: for every fixed denominator `S`, all sufficiently large
targets yield nonempty disjoint anticomplete blocks of size at most `k-1`
whose uncovered remainder has size at most `1/S` of the extremal order. -/
theorem eventually_exists_anticomplete_seed_family_covering_fraction
    (S : ℕ) (hS : 1 ≤ S) :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, 3 ≤ n → n ≤ k →
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = (k - 1) * (n - 1) + 1 →
        G.IndepSetFree n →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        ∃ Q : Finset (Finset V),
          (∀ A ∈ Q, A.Nonempty) ∧ DisjointFinsetFamily Q ∧
          PairwiseAnticomplete G Q ∧
          (∀ A ∈ Q, A.card ≤ k - 1) ∧
          S * ((Finset.univ : Finset V) \ Q.biUnion id).card ≤
            Fintype.card V := by
  let B : ℕ := 256 * S
  have hB : 16 ≤ B := by dsimp [B]; nlinarith
  filter_upwards
    [eventually_exists_one_extra_component_seed_family B hB,
     eventually_one_extra_explicit_coverage_bound_small S hS]
      with k hfamily hcoverage
  intro n hn hnk V instV G instG hcardV hfree hcycle
  let r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt k))
  let R : ℕ := 4 * B
  let a : ℕ := (r + 1) * R ^ 5
  let P : ℕ := 8 * a
  let q : ℕ := k / P
  let K : ℕ := k / (4 * a ^ 2) + 1
  let C : ℕ := P / 2 + 1
  let tau : ℕ := k / C
  let N : ℕ := (k - 1) * (n - 1) + 1
  let jBound : ℕ := N / q
  let deltaN : ℕ := 32 * (P + 1) * (Nat.log 2 N + 1) + 1
  let selectedBound : ℕ :=
    (2 + 2 * (Nat.log 2 N + 1)) * (4 * deltaN * jBound)
  let exceptionalBound : ℕ :=
    (2 * (64 * (C + 1)) + 2) * selectedBound
  let leftBound : ℕ :=
    16 * ((n - 1) * (((k - 1) / B - 1) + 1))
  let regionBound : ℕ := 2 * q + K
  let discardBound : ℕ := (2 * q - (tau - 1)) + K
  obtain ⟨Q, hQne, hQdisj, hQanti, hQcard, hQleft⟩ :=
    hfamily n hn hnk G hcardV hfree hcycle
  have hcov : S * (leftBound + (n - 1) * regionBound +
      jBound * discardBound + exceptionalBound) ≤ N := by
    simpa [B, r, R, a, P, q, K, C, tau, jBound, deltaN,
      selectedBound, exceptionalBound, leftBound, regionBound, discardBound, N,
      Nat.mul_assoc] using
      hcoverage n hn hnk
  refine ⟨Q, hQne, hQdisj, hQanti, hQcard, ?_⟩
  calc
    S * ((Finset.univ : Finset V) \ Q.biUnion id).card ≤
        S * (leftBound + (n - 1) * regionBound +
          jBound * discardBound + exceptionalBound) :=
      Nat.mul_le_mul_left S (by
        simpa [r, R, a, P, q, K, C, tau, N, jBound, deltaN,
          selectedBound, exceptionalBound, leftBound, regionBound,
          discardBound, hcardV, Nat.mul_assoc] using hQleft)
    _ ≤ N := hcov
    _ = Fintype.card V := by simpa [N] using hcardV.symm

/-! ## Deficit filtering of the asymptotic seed family -/

/-- A vertex contained in `A` has at most `|A|-1` neighbours in `A`. -/
theorem degreeIn_le_card_pred_of_mem
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {v : V} (hv : v ∈ A) :
    degreeIn G A v ≤ A.card - 1 := by
  classical
  have hsub : A.filter (fun w => G.Adj v w) ⊆ A.erase v := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hw'.2.ne.symm, hw'.1⟩
  calc
    degreeIn G A v = (A.filter fun w => G.Adj v w).card := rfl
    _ ≤ (A.erase v).card := Finset.card_le_card hsub
    _ = A.card - 1 := Finset.card_erase_of_mem hv

/-- Total missing internal degree relative to the extremal block capacity
`k-1`.  This vertex-sum form avoids truncated subtraction at the family
level. -/
def blockDeficit
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : ℕ :=
  ∑ v ∈ A, ((k - 1) - degreeIn G A v)

/-- Handshaking turns a block deficit into the exact complement of twice
the block's internal edge count. -/
theorem blockDeficit_add_twice_edges
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {A : Finset V} (hA : A.card ≤ k - 1) :
    blockDeficit G k A + 2 * (inducedEdgeFinsetOn G A).card =
      (k - 1) * A.card := by
  classical
  rw [← sum_degreeIn_eq_twice_card_inducedEdgeFinsetOn G A]
  unfold blockDeficit
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ A, ((k - 1 - degreeIn G A x) + degreeIn G A x)) =
        ∑ _x ∈ A, (k - 1) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Nat.sub_add_cancel]
      exact (degreeIn_le_card_pred_of_mem G A hv).trans
        ((Nat.sub_le A.card 1).trans hA)
    _ = (k - 1) * A.card := by simp [Nat.mul_comm]

/-- Exact deficit identity across a disjoint anticomplete family. -/
theorem sum_blockDeficit_add_twice_union_edges
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {Q : Finset (Finset V)}
    (hdisj : DisjointFinsetFamily Q) (hanti : PairwiseAnticomplete G Q)
    (hcard : ∀ A ∈ Q, A.card ≤ k - 1) :
    (∑ A ∈ Q, blockDeficit G k A) +
        2 * (inducedEdgeFinsetOn G (Q.biUnion id)).card =
      (k - 1) * (Q.biUnion id).card := by
  classical
  have hpair : (Q : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    exact hdisj A (by simpa using hA) B (by simpa using hB) hAB
  rw [card_inducedEdgeFinsetOn_biUnion_eq_sum G hdisj hanti,
    Finset.mul_sum]
  calc
    (∑ A ∈ Q, blockDeficit G k A) +
        ∑ A ∈ Q, 2 * (inducedEdgeFinsetOn G A).card =
        ∑ A ∈ Q,
          (blockDeficit G k A + 2 * (inducedEdgeFinsetOn G A).card) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ A ∈ Q, (k - 1) * A.card := by
      apply Finset.sum_congr rfl
      intro A hA
      exact blockDeficit_add_twice_edges G (hcard A hA)
    _ = (k - 1) * ∑ A ∈ Q, A.card := by
      rw [Finset.mul_sum]
    _ = (k - 1) * (Q.biUnion id).card := by
      congr 1
      simpa only [id_eq] using (Finset.card_biUnion hpair).symm

/-- At extremal order, a `1/16777216` uncovered fraction forces the total
missing-degree mass of the anticomplete seed family below
`1/1048576` of its maximum possible mass.  This is the discrete Turán-to-
stability handoff. -/
theorem blockDeficit_mass_small_of_extremal_fraction_coverage
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k n : ℕ} {Q : Finset (Finset V)}
    (hk : 8388609 ≤ k) (hn : 3 ≤ n)
    (horder : Fintype.card V = (k - 1) * (n - 1) + 1)
    (hfree : G.IndepSetFree n)
    (hdisj : DisjointFinsetFamily Q) (hanti : PairwiseAnticomplete G Q)
    (hcard : ∀ A ∈ Q, A.card ≤ k - 1)
    (hcover : 16777216 * ((Finset.univ : Finset V) \ Q.biUnion id).card ≤
      Fintype.card V) :
    1048576 * (∑ A ∈ Q, blockDeficit G k A) ≤
      (k - 1) * (Q.biUnion id).card := by
  classical
  let x : ℕ := k - 1
  let t : ℕ := x / 2097152
  let d : ℕ := x - t
  let U : Finset V := Q.biUnion id
  let L : Finset V := (Finset.univ : Finset V) \ U
  let N : ℕ := x * (n - 1) + 1
  have hx : x = k - 1 := rfl
  have hxlarge : 8388608 ≤ x := by dsimp [x]; omega
  have ht : 4 ≤ t := by
    dsimp [t]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2097152)).2 (by
      simpa using hxlarge)
  have htpos : 0 < t := by omega
  have htx : t ≤ x := by
    dsimp [t]
    exact Nat.div_le_self x 2097152
  have hxlt : x < 2097152 * (t + 1) := by
    dsimp [t]
    exact Nat.lt_mul_div_succ x (by norm_num)
  have hxle : x ≤ 4194304 * t := by nlinarith
  have hNcard : N = Fintype.card V := by
    simpa [N, x] using horder.symm
  have hcov' : 16777216 * L.card ≤ N := by
    simpa [L, U, hNcard] using hcover
  have hNupper : N ≤ 4194304 * (t * (n - 1)) + 1 := by
    dsimp [N]
    have hmul := Nat.mul_le_mul_right (n - 1) hxle
    nlinarith
  have hfourL : 4 * L.card ≤ t * (n - 1) := by
    have hraw := hcov'.trans hNupper
    nlinarith
  have htquarter : t ≤ 4 * (t - 1) := by omega
  have htquarter' : t * (n - 1) ≤ 4 * ((t - 1) * (n - 1)) := by
    calc
      t * (n - 1) ≤ (4 * (t - 1)) * (n - 1) :=
        Nat.mul_le_mul_right _ htquarter
      _ = 4 * ((t - 1) * (n - 1)) := by ring
  have hLsmall : L.card ≤ (t - 1) * (n - 1) + 1 := by
    have := hfourL.trans htquarter'
    nlinarith
  have hsplit :
      (n - 1) * (d + 1) + ((t - 1) * (n - 1) + 1) = N := by
    have hdt : d + 1 + (t - 1) = x := by
      dsimp [d]
      omega
    calc
      (n - 1) * (d + 1) + ((t - 1) * (n - 1) + 1) =
          ((d + 1) + (t - 1)) * (n - 1) + 1 := by ring
      _ = x * (n - 1) + 1 := by rw [hdt]
      _ = N := by rfl
  have hpartition : U.card + L.card = N := by
    have hUcard : U.card ≤ Fintype.card V := by
      simpa using Finset.card_le_card (Finset.subset_univ U)
    calc
      U.card + L.card = U.card + (Fintype.card V - U.card) := by
        dsimp [L]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        simp
      _ = Fintype.card V := Nat.add_sub_of_le hUcard
      _ = N := hNcard.symm
  have hsize : (n - 1) * (d + 1) ≤ U.card := by
    have hsumle : (n - 1) * (d + 1) + L.card ≤ N := by
      calc
      (n - 1) * (d + 1) + L.card ≤
          (n - 1) * (d + 1) + ((t - 1) * (n - 1) + 1) :=
        Nat.add_le_add_left hLsmall _
      _ = N := hsplit
    rw [← hpartition] at hsumle
    omega
  have hdense : d * U.card ≤
      2 * (inducedEdgeFinsetOn G U).card := by
    have hdense' := avg_degree_induce_ge_of_indepSetFree
      G (S := U) (d := d) (n := n) (by omega) hfree hsize
    simpa [card_inducedEdgeFinsetOn_eq_card_induce_finset G U] using hdense'
  have hidentity := sum_blockDeficit_add_twice_union_edges
    G hdisj hanti hcard
  have hdef : (∑ A ∈ Q, blockDeficit G k A) ≤ t * U.card := by
    have hd : d = (k - 1) - t := by rfl
    rw [hd] at hdense
    have hmass : ((k - 1) - t) * U.card + t * U.card =
        (k - 1) * U.card := by
      rw [← Nat.add_mul, Nat.sub_add_cancel]
      simpa [x] using htx
    dsimp [U] at hdense ⊢
    dsimp [U] at hmass
    omega
  calc
    1048576 * (∑ A ∈ Q, blockDeficit G k A) ≤
        1048576 * (t * U.card) := Nat.mul_le_mul_left 1048576 hdef
    _ = (1048576 * t) * U.card := by ring
    _ ≤ x * U.card := by
      gcongr
      calc
        1048576 * t ≤ 2097152 * t := by gcongr; norm_num
        _ ≤ x := by
          dsimp [t]
          simpa [Nat.mul_comm] using Nat.div_mul_le_self x 2097152
    _ = (k - 1) * (Q.biUnion id).card := by rfl

/-- Blocks whose missing-degree mass is at most a `1/4096` fraction of the
capacity mass. -/
def LowDeficitBlock
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Prop :=
  4096 * blockDeficit G k A ≤ (k - 1) * A.card

/-- The high-deficit blocks occupy at most `1/256` of the seed union. -/
theorem highDeficit_seed_union_small
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {Q : Finset (Finset V)} (hk : 2 ≤ k)
    (hdisj : DisjointFinsetFamily Q)
    (hmass : 1048576 * (∑ A ∈ Q, blockDeficit G k A) ≤
      (k - 1) * (Q.biUnion id).card) :
    256 * ((Q.filter fun A => ¬ LowDeficitBlock G k A).biUnion id).card ≤
      (Q.biUnion id).card := by
  classical
  let Bad : Finset (Finset V) := Q.filter fun A => ¬ LowDeficitBlock G k A
  have hBadSub : Bad ⊆ Q := Finset.filter_subset _ _
  have hBadDisj : (Bad : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    exact hdisj A (hBadSub (by simpa using hA))
      B (hBadSub (by simpa using hB)) hAB
  have hbadEach : ∀ A ∈ Bad,
      (k - 1) * A.card ≤ 4096 * blockDeficit G k A := by
    intro A hA
    have hnot := (Finset.mem_filter.mp hA).2
    unfold LowDeficitBlock at hnot
    omega
  have hsumSub : (∑ A ∈ Bad, blockDeficit G k A) ≤
      ∑ A ∈ Q, blockDeficit G k A := by
    exact Finset.sum_le_sum_of_subset hBadSub
  have hbadMass : (k - 1) * (Bad.biUnion id).card ≤
      4096 * (∑ A ∈ Q, blockDeficit G k A) := by
    calc
      (k - 1) * (Bad.biUnion id).card =
          ∑ A ∈ Bad, (k - 1) * A.card := by
        rw [Finset.card_biUnion hBadDisj, Finset.mul_sum]
        simp only [id_eq]
      _ ≤ ∑ A ∈ Bad, 4096 * blockDeficit G k A := by
        exact Finset.sum_le_sum fun A hA => hbadEach A hA
      _ = 4096 * (∑ A ∈ Bad, blockDeficit G k A) := by
        rw [Finset.mul_sum]
      _ ≤ 4096 * (∑ A ∈ Q, blockDeficit G k A) :=
        Nat.mul_le_mul_left 4096 hsumSub
  have hscaled : (k - 1) *
      (256 * (Bad.biUnion id).card) ≤
      (k - 1) * (Q.biUnion id).card := by
    calc
      (k - 1) * (256 * (Bad.biUnion id).card) =
          256 * ((k - 1) * (Bad.biUnion id).card) := by ring
      _ ≤ 256 * (4096 * (∑ A ∈ Q, blockDeficit G k A)) :=
        Nat.mul_le_mul_left 256 hbadMass
      _ = 1048576 * (∑ A ∈ Q, blockDeficit G k A) := by ring
      _ ≤ (k - 1) * (Q.biUnion id).card := hmass
  change 256 * (Bad.biUnion id).card ≤ (Q.biUnion id).card
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- Vertices whose internal degree is below `31/32` of the extremal block
capacity. -/
noncomputable def lowInternalDegreeVertices
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Finset V :=
  A.filter fun v => 32 * degreeIn G A v < 31 * (k - 1)

noncomputable def denseTrim
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Finset V :=
  A \ lowInternalDegreeVertices G k A

/-- In a low-deficit block, fewer than one vertex in 128 has internal
degree below `31/32` of capacity. -/
theorem oneHundredTwentyEight_mul_lowInternalDegreeVertices_card_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {A : Finset V} (hk : 2 ≤ k)
    (hcard : A.card ≤ k - 1) (hgood : LowDeficitBlock G k A) :
    128 * (lowInternalDegreeVertices G k A).card ≤ A.card := by
  classical
  let Z : Finset V := lowInternalDegreeVertices G k A
  have hZsub : Z ⊆ A := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hpoint : ∀ v ∈ Z,
      k - 1 ≤ 32 * ((k - 1) - degreeIn G A v) := by
    intro v hv
    have hvA : v ∈ A := hZsub hv
    have hdeg : degreeIn G A v ≤ k - 1 :=
      (degreeIn_le_card_pred_of_mem G A hvA).trans
        ((Nat.sub_le A.card 1).trans hcard)
    have hv' : v ∈ lowInternalDegreeVertices G k A := by simpa [Z] using hv
    have hlow := (Finset.mem_filter.mp hv').2
    omega
  have hsumZ : (k - 1) * Z.card ≤
      32 * blockDeficit G k A := by
    calc
      (k - 1) * Z.card = ∑ _v ∈ Z, (k - 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ Z, 32 * ((k - 1) - degreeIn G A v) := by
        exact Finset.sum_le_sum fun v hv => hpoint v hv
      _ = 32 * ∑ v ∈ Z, ((k - 1) - degreeIn G A v) := by
        rw [Finset.mul_sum]
      _ ≤ 32 * blockDeficit G k A := by
        apply Nat.mul_le_mul_left
        unfold blockDeficit
        exact Finset.sum_le_sum_of_subset hZsub
  have hscaled : (k - 1) * (128 * Z.card) ≤
      (k - 1) * A.card := by
    calc
      (k - 1) * (128 * Z.card) = 128 * ((k - 1) * Z.card) := by ring
      _ ≤ 128 * (32 * blockDeficit G k A) := Nat.mul_le_mul_left 128 hsumZ
      _ = 4096 * blockDeficit G k A := by ring
      _ ≤ (k - 1) * A.card := hgood
  change 128 * Z.card ≤ A.card
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- Trimming the few low-degree vertices from a nonempty low-deficit block
leaves a nonempty subblock of order at most `k-1` in which every vertex has
doubled internal degree at least `k`. -/
theorem denseTrim_properties
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {A : Finset V} (hk : 5 ≤ k) (hne : A.Nonempty)
    (hcard : A.card ≤ k - 1) (hgood : LowDeficitBlock G k A) :
    (denseTrim G k A).Nonempty ∧
      denseTrim G k A ⊆ A ∧
      (denseTrim G k A).card ≤ k - 1 ∧
      ∀ v ∈ denseTrim G k A,
        k ≤ 2 * degreeIn G (denseTrim G k A) v ∧
        123 * (k - 1) ≤
          128 * degreeIn G (denseTrim G k A) v := by
  classical
  let Z : Finset V := lowInternalDegreeVertices G k A
  let B : Finset V := denseTrim G k A
  have hZsub : Z ⊆ A := by
    intro v hv
    have hv' : v ∈ lowInternalDegreeVertices G k A := by simpa [Z] using hv
    exact (Finset.mem_filter.mp hv').1
  have h128 : 128 * Z.card ≤ A.card := by
    simpa [Z] using
      (oneHundredTwentyEight_mul_lowInternalDegreeVertices_card_le
        G (by omega) hcard hgood)
  have hZlt : Z.card < A.card := by
    have hApos : 0 < A.card := Finset.card_pos.mpr hne
    by_contra hnot
    have hAZ : A.card ≤ Z.card := by omega
    nlinarith
  have hBdef : B = A \ Z := by rfl
  have hBcard : B.card = A.card - Z.card := by
    rw [hBdef, Finset.card_sdiff_of_subset hZsub]
  have hBpos : 0 < B.card := by omega
  have hBne : B.Nonempty := Finset.card_pos.mp hBpos
  have hBsub : B ⊆ A := by
    rw [hBdef]
    exact Finset.sdiff_subset
  have hBcap : B.card ≤ k - 1 :=
    (Finset.card_le_card hBsub).trans hcard
  refine ⟨by simpa [B] using hBne, by simpa [B] using hBsub,
    by simpa [B] using hBcap, ?_⟩
  intro v hvB
  have hvB' : v ∈ B := by simpa [B] using hvB
  have hvA : v ∈ A := hBsub hvB'
  have hvZ : v ∉ Z := by
    rw [hBdef] at hvB'
    exact (Finset.mem_sdiff.mp hvB').2
  have hnotlow : ¬32 * degreeIn G A v < 31 * (k - 1) := by
    intro hlow
    apply hvZ
    have : v ∈ lowInternalDegreeVertices G k A :=
      Finset.mem_filter.mpr ⟨hvA, hlow⟩
    simpa [Z] using this
  have hdegA : 31 * (k - 1) ≤ 32 * degreeIn G A v := by omega
  have hloss := degreeIn_le_degreeIn_add_card_loss G hBsub v
  have hdiff : A.card - B.card = Z.card := by
    rw [hBcard]
    omega
  rw [hdiff] at hloss
  have hZcap : 128 * Z.card ≤ k - 1 := h128.trans hcard
  have hgoalB : k ≤ 2 * degreeIn G B v := by
    omega
  have hstrongB : 123 * (k - 1) ≤ 128 * degreeIn G B v := by
    omega
  exact ⟨by simpa [B] using hgoalB, by simpa [B] using hstrongB⟩

/-- The common neighborhood of a pair inside a finite target is exactly the
intersection of their two target-neighborhoods. -/
theorem commonNeighbors_pair_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (a b : V) :
    Erdos163.FiniteDefect.commonNeighbors G ![a, b] B =
      (B.filter fun x => G.Adj a x) ∩ (B.filter fun x => G.Adj b x) := by
  ext x
  simp [Erdos163.FiniteDefect.commonNeighbors,
    Erdos163.Defect.commonNeighbors, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  aesop

/-- The quantitative degree conclusion of `denseTrim_properties` makes the
whole trimmed block a robust pair set.  Inclusion--exclusion loses at most
one copy of the block capacity, leaving `57/64` of the target scale as a
common-neighborhood reservoir. -/
theorem robustPairSet_of_scaled_internal_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} {k : ℕ}
    (hcard : B.card ≤ k - 1)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    RobustPairSet G B B (57 * (k - 1) / 64) := by
  classical
  intro a ha b hb
  let A : Finset V := B.filter fun x => G.Adj a x
  let C : Finset V := B.filter fun x => G.Adj b x
  have hA : A.card = degreeIn G B a := rfl
  have hC : C.card = degreeIn G B b := rfl
  have hU : (A ∪ C).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hsum := Finset.card_union_add_card_inter A C
  rw [commonNeighbors_pair_eq_inter]
  change 57 * (k - 1) / 64 ≤ (A ∩ C).card
  have ha' := hdeg a ha
  have hb' := hdeg b hb
  rw [← hA] at ha'
  rw [← hC] at hb'
  have hscaled : 57 * (k - 1) ≤ 64 * (A ∩ C).card := by
    omega
  apply Nat.div_le_of_le_mul
  simpa [Nat.mul_comm] using hscaled

/-- The same scaled degree bound gives all balanced-routing capacity
inequalities used below. -/
theorem dense_block_balanced_routing_capacities
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} {k : ℕ} (hk : 1000 ≤ k) (hne : B.Nonempty)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    k / 2 + 5 ≤ B.card ∧
      k / 2 + 5 ≤ 57 * (k - 1) / 64 := by
  obtain ⟨v, hv⟩ := hne
  have hvdeg := hdeg v hv
  have hvupper : degreeIn G B v ≤ B.card := Finset.card_filter_le _ _
  constructor <;> omega

/-- A trimmed dense block is parity-broken in the strong form used by the
all-length router: it contains three pairwise vertex-disjoint edges. -/
theorem hasThreeDisjointAdjPairFamily_of_scaled_internal_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} {k : ℕ} (hk : 7 ≤ k) (hBne : B.Nonempty)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    HasThreeDisjointAdjPairFamily G B := by
  classical
  let H : SimpleGraph B := G.induce (B : Set V)
  letI : Nonempty B := hBne.to_subtype
  have hpoint : ∀ v : B, 5 ≤ H.degree v := by
    intro v
    have hv := hdeg v v.2
    change 5 ≤ (G.induce (B : Set V)).degree v
    rw [degree_induce_finset_eq_degreeIn G B v]
    omega
  have hmin : 5 ≤ H.minDegree := H.le_minDegree_of_forall_le_degree 5 hpoint
  exact hasThreeDisjointAdjPairFamily_of_induce_minDegree G B hBne
    (by simpa [H] using hmin)

/-- Two robust dense blocks and two disjoint outside handles close an exact
cycle.  The first block uses an explicit parity-breaking matching edge, so
no Ramsey-sized lower bound on that block is needed. -/
theorem cycleGraph_isContained_of_two_matched_robust_sets_path_handles
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {U₁ T₁ U₂ T₂ : Finset V} {θ₁ θ₂ ℓ t k : ℕ} (hk : 3 ≤ k)
    (hrob₁ : RobustPairSet G U₁ T₁ θ₁) (hrob₂ : RobustPairSet G U₂ T₂ θ₂)
    (hregions : Disjoint (U₁ ∪ T₁) (U₂ ∪ T₂))
    (hmatch : HasThreeDisjointAdjPairFamily G U₁)
    {a b c d u v y z : V}
    {h₁ : G.Walk u v} {h₂ : G.Walk y z}
    (ha : a ∈ U₁) (hb : b ∈ U₁) (hc : c ∈ U₂) (hd : d ∈ U₂)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hh₁ : h₁.IsPath) (hh₂ : h₂.IsPath)
    (h₁outside : ∀ w ∈ h₁.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (h₂outside : ∀ w ∈ h₂.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (hhandles : h₁.support.Disjoint h₂.support)
    (hbu : G.Adj b u) (hvc : G.Adj v c)
    (hdy : G.Adj d y) (hza : G.Adj z a)
    (hℓ : 5 ≤ ℓ) (hℓU : ℓ ≤ U₁.card) (hℓθ : ℓ + 1 ≤ θ₁)
    (hU₂ : t + 2 ≤ U₂.card) (hθ₂ : 2 * (t + 1) + 1 ≤ θ₂)
    (hlen : ℓ + h₁.length + 2 * (t + 1) + h₂.length + 4 = k) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  classical
  obtain ⟨M, hM, hMcard, hMU⟩ := hmatch
  let F : Finset V := {a, b}
  have hFcard : F.card < M.card := by
    have : F.card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨e, heM, he₁F, he₂F, heAdj⟩ :=
    exists_adjPair_avoiding_of_disjointAdjPairFamily G M F hM hFcard
  have heU := hMU e heM
  have he₁ : e.1 ≠ a ∧ e.1 ≠ b := by simpa [F] using he₁F
  have he₂ : e.2 ≠ a ∧ e.2 ≠ b := by simpa [F] using he₂F
  obtain ⟨p, hp, hplen, hploc⟩ :=
    exists_path_between_of_robustPairSet_and_parity_edge G hrob₁
      ha heU.1 heU.2 hb heAdj he₁.1.symm he₂.1.symm hab
      he₁.2 he₂.2 hℓ hℓU hℓθ
  obtain ⟨q, hq, hqlen, _hqavoid, hqloc⟩ :=
    exists_even_path_between_of_robustPairSet_avoiding G (F := ∅) (r := t)
      hrob₂ hc hd (by simp) (by simp) hcd (by simpa) (by simpa using hθ₂)
  have hpq : p.support.Disjoint q.support := by
    intro w hwp hwq
    have hw₁ : w ∈ U₁ ∪ T₁ := by
      rcases hploc w hwp with hw | hw
      · exact Finset.mem_union_left _ hw
      · exact Finset.mem_union_right _ hw
    have hw₂ : w ∈ U₂ ∪ T₂ := by
      rcases hqloc w hwq with hw | hw
      · exact Finset.mem_union_left _ hw
      · exact Finset.mem_union_right _ hw
    exact Finset.disjoint_left.mp hregions hw₁ hw₂
  have hph₁ : p.support.Disjoint h₁.support := by
    intro w hwp hwh
    apply (h₁outside w hwh).1
    rcases hploc w hwp with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ hw
  have hph₂ : p.support.Disjoint h₂.support := by
    intro w hwp hwh
    apply (h₂outside w hwh).1
    rcases hploc w hwp with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ hw
  have hh₁q : h₁.support.Disjoint q.support := by
    intro w hwh hwq
    apply (h₁outside w hwh).2
    rcases hqloc w hwq with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ hw
  have hqh₂ : q.support.Disjoint h₂.support := by
    intro w hwq hwh
    apply (h₂outside w hwh).2
    rcases hqloc w hwq with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ hw
  apply cycleGraph_isContained_of_two_path_handles_and_disjoint_paths
    G hk hp hh₁ hq hh₂ hph₁ hpq hph₂ hh₁q hhandles hqh₂
      hbu hvc hdy hza
  omega

/-- Balanced specialization for handles of length at most two.  Roughly half
of the target cycle is routed in each dense block; consequently this version
only needs fixed positive-density capacity rather than `k-O(1)` vertices in
one block. -/
theorem cycleGraph_isContained_of_two_dense_robust_sets_short_path_handles
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {U₁ T₁ U₂ T₂ : Finset V} {θ₁ θ₂ k : ℕ} (hk : 64 ≤ k)
    (hrob₁ : RobustPairSet G U₁ T₁ θ₁) (hrob₂ : RobustPairSet G U₂ T₂ θ₂)
    (hregions : Disjoint (U₁ ∪ T₁) (U₂ ∪ T₂))
    (hmatch : HasThreeDisjointAdjPairFamily G U₁)
    {a b c d u v y z : V}
    {h₁ : G.Walk u v} {h₂ : G.Walk y z}
    (ha : a ∈ U₁) (hb : b ∈ U₁) (hc : c ∈ U₂) (hd : d ∈ U₂)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hh₁ : h₁.IsPath) (hh₂ : h₂.IsPath)
    (h₁len : h₁.length ≤ 2) (h₂len : h₂.length ≤ 2)
    (h₁outside : ∀ w ∈ h₁.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (h₂outside : ∀ w ∈ h₂.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (hhandles : h₁.support.Disjoint h₂.support)
    (hbu : G.Adj b u) (hvc : G.Adj v c)
    (hdy : G.Adj d y) (hza : G.Adj z a)
    (hU₁ : k / 2 + 4 ≤ U₁.card) (hθ₁ : k / 2 + 5 ≤ θ₁)
    (hU₂ : k / 4 ≤ U₂.card) (hθ₂ : k / 2 ≤ θ₂) :
    _root_.SimpleGraph.cycleGraph k ⊑ G := by
  let t := k / 4 - 2
  let ℓ := k - (h₁.length + 2 * (t + 1) + h₂.length + 4)
  apply cycleGraph_isContained_of_two_matched_robust_sets_path_handles
    G (by omega) hrob₁ hrob₂ hregions hmatch ha hb hc hd hab hcd
      hh₁ hh₂ h₁outside h₂outside hhandles hbu hvc hdy hza
      (ℓ := ℓ) (t := t)
  · dsimp [ℓ, t]
    omega
  · dsimp [ℓ, t]
    omega
  · dsimp [ℓ, t]
    omega
  · dsimp [t]
    omega
  · dsimp [t]
    omega
  · dsimp [ℓ]
    omega

/-- In a `Cₖ`-free graph, two disjoint short outside handles between the
same two dense robust blocks must repeat an attachment at one end. -/
theorem repeated_attachment_or_intersecting_handles_of_cycleFree_two_dense_robust_sets
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {U₁ T₁ U₂ T₂ : Finset V} {θ₁ θ₂ k : ℕ} (hk : 64 ≤ k)
    (hrob₁ : RobustPairSet G U₁ T₁ θ₁) (hrob₂ : RobustPairSet G U₂ T₂ θ₂)
    (hregions : Disjoint (U₁ ∪ T₁) (U₂ ∪ T₂))
    (hmatch : HasThreeDisjointAdjPairFamily G U₁)
    {a b c d u v y z : V}
    {h₁ : G.Walk u v} {h₂ : G.Walk y z}
    (ha : a ∈ U₁) (hb : b ∈ U₁) (hc : c ∈ U₂) (hd : d ∈ U₂)
    (hh₁ : h₁.IsPath) (hh₂ : h₂.IsPath)
    (h₁len : h₁.length ≤ 2) (h₂len : h₂.length ≤ 2)
    (h₁outside : ∀ w ∈ h₁.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (h₂outside : ∀ w ∈ h₂.support, w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (hbu : G.Adj b u) (hvc : G.Adj v c)
    (hdy : G.Adj d y) (hza : G.Adj z a)
    (hU₁ : k / 2 + 4 ≤ U₁.card) (hθ₁ : k / 2 + 5 ≤ θ₁)
    (hU₂ : k / 4 ≤ U₂.card) (hθ₂ : k / 2 ≤ θ₂)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    a = b ∨ c = d ∨ ¬ h₁.support.Disjoint h₂.support := by
  by_cases hab : a = b
  · exact Or.inl hab
  by_cases hcd : c = d
  · exact Or.inr (Or.inl hcd)
  by_cases hhandles : h₁.support.Disjoint h₂.support
  · exfalso
    apply hcycle
    exact cycleGraph_isContained_of_two_dense_robust_sets_short_path_handles
      G hk hrob₁ hrob₂ hregions hmatch ha hb hc hd hab hcd
        hh₁ hh₂ h₁len h₂len h₁outside h₂outside hhandles
        hbu hvc hdy hza hU₁ hθ₁ hU₂ hθ₂
  · exact Or.inr (Or.inr hhandles)

/-- Every pairwise-disjoint short-handle family between two dense robust
blocks has one common attachment vertex on one of its two sides. -/
theorem exists_common_attachment_of_cycleFree_short_path_handles_between_dense_robust_sets
    {V κ : Type*} [Fintype V] [Fintype κ] [Nonempty κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {U₁ T₁ U₂ T₂ : Finset V} {θ₁ θ₂ k : ℕ} (hk : 64 ≤ k)
    (hrob₁ : RobustPairSet G U₁ T₁ θ₁) (hrob₂ : RobustPairSet G U₂ T₂ θ₂)
    (hregions : Disjoint (U₁ ∪ T₁) (U₂ ∪ T₂))
    (hmatch : HasThreeDisjointAdjPairFamily G U₁)
    (left right u v : κ → V) (h : ∀ i : κ, G.Walk (u i) (v i))
    (hleft : ∀ i, left i ∈ U₁) (hright : ∀ i, right i ∈ U₂)
    (hpath : ∀ i, (h i).IsPath) (hlen : ∀ i, (h i).length ≤ 2)
    (houtside : ∀ i w, w ∈ (h i).support →
      w ∉ U₁ ∪ T₁ ∧ w ∉ U₂ ∪ T₂)
    (hleftAdj : ∀ i, G.Adj (left i) (u i))
    (hrightAdj : ∀ i, G.Adj (v i) (right i))
    (hdisj : ∀ i j, i ≠ j → (h i).support.Disjoint (h j).support)
    (hU₁ : k / 2 + 4 ≤ U₁.card) (hθ₁ : k / 2 + 5 ≤ θ₁)
    (hU₂ : k / 4 ≤ U₂.card) (hθ₂ : k / 2 ≤ θ₂)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    (∃ a : V, ∀ i : κ, left i = a) ∨ ∃ b : V, ∀ i : κ, right i = b := by
  apply exists_common_left_or_right_of_pairwise_left_eq_or_right_eq left right
  intro i j
  by_cases hij : i = j
  · subst j
    exact Or.inl rfl
  have hbad :=
    repeated_attachment_or_intersecting_handles_of_cycleFree_two_dense_robust_sets
      G hk hrob₁ hrob₂ hregions hmatch
      (a := left j) (b := left i) (c := right i) (d := right j)
      (h₁ := h i) (h₂ := (h j).reverse)
      (hleft j) (hleft i) (hright i) (hright j)
      (hpath i) (hpath j).reverse (hlen i) (by simpa using hlen j)
      (houtside i)
      (by
        intro w hw
        apply houtside j w
        simpa [SimpleGraph.Walk.support_reverse] using hw)
      (hleftAdj i) (hrightAdj i)
      (hrightAdj j).symm (hleftAdj j).symm
      hU₁ hθ₁ hU₂ hθ₂ hcycle
  rcases hbad with hleftEq | hrightEq | hinter
  · exact Or.inl hleftEq.symm
  · exact Or.inr hrightEq
  · exact (hinter (by
      intro w hwi hwj
      apply (hdisj i j hij) hwi
      simpa [SimpleGraph.Walk.support_reverse] using hwj)).elim

/-- One attachment chosen for every ordered pair of dense robust blocks meets
every member of an arbitrary pairwise-disjoint short-handle family. -/
theorem exists_global_exceptional_set_meeting_short_path_handles_of_cycleFree_dense_family
    {V ι κ : Type*} [Fintype V] [Nonempty V] [Fintype ι] [Fintype κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U T : ι → Finset V) (θ : ι → ℕ) {k : ℕ} (hk : 64 ≤ k)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) (θ i))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (U i))
    (hU : ∀ i, k / 2 + 4 ≤ (U i).card)
    (hθ : ∀ i, k / 2 + 5 ≤ θ i)
    (hregions : ∀ i j, i ≠ j →
      Disjoint (U i ∪ T i) (U j ∪ T j))
    (src dst : κ → ι) (left right u v : κ → V)
    (h : ∀ a : κ, G.Walk (u a) (v a))
    (hsrcne : ∀ a, src a ≠ dst a)
    (hleft : ∀ a, left a ∈ U (src a))
    (hright : ∀ a, right a ∈ U (dst a))
    (hpath : ∀ a, (h a).IsPath) (hlen : ∀ a, (h a).length ≤ 2)
    (houtside : ∀ a w, w ∈ (h a).support →
      w ∉ U (src a) ∪ T (src a) ∧ w ∉ U (dst a) ∪ T (dst a))
    (hleftAdj : ∀ a, G.Adj (left a) (u a))
    (hrightAdj : ∀ a, G.Adj (v a) (right a))
    (hdisj : ∀ a b, a ≠ b → (h a).support.Disjoint (h b).support)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    ∃ X : Finset V, X.card ≤ (Fintype.card ι) ^ 2 ∧
      ∀ a : κ, left a ∈ X ∨ right a ∈ X := by
  classical
  have hpair : ∀ i j : ι, i ≠ j → ∃ x : V,
      (∀ a : κ, src a = i → dst a = j → left a = x) ∨
        (∀ a : κ, src a = i → dst a = j → right a = x) := by
    intro i j hij
    let K := {a : κ // src a = i ∧ dst a = j}
    by_cases hK : Nonempty K
    · letI : Nonempty K := hK
      obtain ⟨x, hx⟩ | ⟨x, hx⟩ :=
        exists_common_attachment_of_cycleFree_short_path_handles_between_dense_robust_sets
          G hk (hrob i) (hrob j) (hregions i j hij) (hmatch i)
          (fun a : K => left a.1) (fun a : K => right a.1)
          (fun a : K => u a.1) (fun a : K => v a.1)
          (fun a : K => h a.1)
          (fun a : K => by simpa [a.2.1] using hleft a.1)
          (fun a : K => by simpa [a.2.2] using hright a.1)
          (fun a : K => hpath a.1) (fun a : K => hlen a.1)
          (by
            intro a w hw
            simpa [a.2.1, a.2.2] using houtside a.1 w hw)
          (fun a : K => hleftAdj a.1) (fun a : K => hrightAdj a.1)
          (by
            intro a b hab
            apply hdisj a.1 b.1
            intro heq
            apply hab
            exact Subtype.ext heq)
          (hU i) (hθ i)
          (by have hi := hU j; omega)
          (by have hi := hθ j; omega) hcycle
      · refine ⟨x, Or.inl ?_⟩
        intro a hsrc hdst
        let a' : K := ⟨a, hsrc, hdst⟩
        exact hx a'
      · refine ⟨x, Or.inr ?_⟩
        intro a hsrc hdst
        let a' : K := ⟨a, hsrc, hdst⟩
        exact hx a'
    · let x : V := Classical.choice inferInstance
      refine ⟨x, Or.inl ?_⟩
      intro a hsrc hdst
      exfalso
      exact hK ⟨⟨a, hsrc, hdst⟩⟩
  let cover : ι × ι → V := fun ij =>
    if hij : ij.1 ≠ ij.2 then Classical.choose (hpair ij.1 ij.2 hij)
    else Classical.choice inferInstance
  let X : Finset V := (Finset.univ : Finset (ι × ι)).image cover
  refine ⟨X, ?_, ?_⟩
  · calc
      X.card ≤ (Finset.univ : Finset (ι × ι)).card := Finset.card_image_le
      _ = Fintype.card ι * Fintype.card ι := by simp
      _ = (Fintype.card ι) ^ 2 := by ring
  · intro a
    have hsne : src a ≠ dst a := hsrcne a
    have hspec := Classical.choose_spec (hpair (src a) (dst a) hsne)
    have hmem : cover (src a, dst a) ∈ X :=
      Finset.mem_image.mpr ⟨(src a, dst a), Finset.mem_univ _, rfl⟩
    have hcover : cover (src a, dst a) =
        Classical.choose (hpair (src a) (dst a) hsne) := by
      simp [cover, hsne]
    rw [hcover] at hmem
    rcases hspec with hleftAll | hrightAll
    · left
      rw [hleftAll a rfl rfl]
      exact hmem
    · right
      rw [hrightAll a rfl rfl]
      exact hmem

/-- Handle-cover form of the dense-family cleanup: after deleting at most
the square of the number of block labels, no leftover component reaches two
different trimmed blocks. -/
theorem exists_exceptional_set_separating_leftover_of_dense_short_path_handle_cover
    {V ι κ : Type*} [Fintype V] [Nonempty V] [Fintype ι] [Fintype κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U T : ι → Finset V) (θ : ι → ℕ) (L : Finset V)
    {k : ℕ} (hk : 64 ≤ k)
    (hrob : ∀ i, RobustPairSet G (U i) (T i) (θ i))
    (hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (U i))
    (hU : ∀ i, k / 2 + 4 ≤ (U i).card)
    (hθ : ∀ i, k / 2 + 5 ≤ θ i)
    (hregions : ∀ i j, i ≠ j → Disjoint (U i ∪ T i) (U j ∪ T j))
    (src dst : κ → ι) (left right u v : κ → V)
    (h : ∀ a : κ, G.Walk (u a) (v a))
    (hsrcne : ∀ a, src a ≠ dst a)
    (hleft : ∀ a, left a ∈ U (src a))
    (hright : ∀ a, right a ∈ U (dst a))
    (hpath : ∀ a, (h a).IsPath) (hlen : ∀ a, (h a).length ≤ 2)
    (houtside : ∀ a w, w ∈ (h a).support →
      w ∉ U (src a) ∪ T (src a) ∧ w ∉ U (dst a) ∪ T (dst a))
    (hleftAdj : ∀ a, G.Adj (left a) (u a))
    (hrightAdj : ∀ a, G.Adj (v a) (right a))
    (hdisj : ∀ a b, a ≠ b → (h a).support.Disjoint (h b).support)
    (hcover : ∀ i j : ι, i ≠ j → ∀ x y : L,
      (G.induce (L : Set V)).Reachable x y →
      ∀ a ∈ U i, G.Adj x.1 a →
      ∀ b ∈ U j, G.Adj y.1 b →
      ∃ q : κ, src q = i ∧ dst q = j ∧ left q = a ∧ right q = b)
    (hcycle : ¬ _root_.SimpleGraph.cycleGraph k ⊑ G) :
    ∃ X : Finset V, X.card ≤ (Fintype.card ι) ^ 2 ∧
      ∀ i j : ι, i ≠ j → ∀ x y : L,
        (G.induce (L : Set V)).Reachable x y →
        (∃ a ∈ U i \ X, G.Adj x.1 a) →
        (∃ b ∈ U j \ X, G.Adj y.1 b) → False := by
  obtain ⟨X, hXcard, hXmeet⟩ :=
    exists_global_exceptional_set_meeting_short_path_handles_of_cycleFree_dense_family
      G U T θ hk hrob hmatch hU hθ hregions src dst left right u v h
      hsrcne hleft hright hpath hlen houtside hleftAdj hrightAdj hdisj hcycle
  refine ⟨X, hXcard, ?_⟩
  intro i j hij x y hxy
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
  obtain ⟨q, hsrc, hdst, hleftq, hrightq⟩ :=
    hcover i j hij x y hxy a (Finset.mem_sdiff.mp ha).1 hxa
      b (Finset.mem_sdiff.mp hb).1 hyb
  rcases hXmeet q with hleftX | hrightX
  · exact (Finset.mem_sdiff.mp ha).2 (hleftq ▸ hleftX)
  · exact (Finset.mem_sdiff.mp hb).2 (hrightq ▸ hrightX)

/-! ## Dense-path absorption data -/

theorem card_filter_attach_eq
    {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.attach.filter fun x => p x.1).card = (s.filter p).card := by
  rw [Finset.filter_attach, Finset.card_map, Finset.card_attach]

/-- A finite family of pairwise vertex-disjoint paths outside a dense block,
with two globally distinct attachment vertices in the block for each path.
The two attachments are indexed by `Fin 2`; coordinate zero attaches to the
initial endpoint and coordinate one to the terminal endpoint. -/
structure ShortAbsorbableFamily
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (B : Finset V) where
  start : J → V
  finish : J → V
  path : ∀ j : J, G.Walk (start j) (finish j)
  isPath : ∀ j, (path j).IsPath
  length_le_two : ∀ j, (path j).length ≤ 2
  attach : J × Fin 2 → V
  attach_mem : ∀ q, attach q ∈ B
  attach_injective : Function.Injective attach
  start_adj : ∀ j, G.Adj (attach (j, 0)) (start j)
  finish_adj : ∀ j, G.Adj (finish j) (attach (j, 1))
  support_outside : ∀ j v, v ∈ (path j).support → v ∉ B
  support_disjoint : ∀ i j, i ≠ j →
    (path i).support.Disjoint (path j).support

noncomputable def ShortAbsorbableFamily.vertices
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Finset V := by
  classical
  exact (Finset.univ : Finset J).biUnion fun j => (A.path j).support.toFinset

noncomputable def ShortAbsorbableFamily.attachments
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Finset V := by
  classical
  exact (Finset.univ : Finset (J × Fin 2)).image A.attach

theorem ShortAbsorbableFamily.attachments_subset
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.attachments ⊆ B := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨q, _hq, rfl⟩
  exact A.attach_mem q

/-- There are exactly two globally reserved attachment vertices per absorbed
path. -/
theorem ShortAbsorbableFamily.card_attachments
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.attachments.card = 2 * Fintype.card J := by
  classical
  rw [ShortAbsorbableFamily.attachments,
    Finset.card_image_of_injective _ A.attach_injective]
  simp [Nat.mul_comm]

theorem ShortAbsorbableFamily.path_support_card
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (j : J) :
    (A.path j).support.toFinset.card = (A.path j).length + 1 := by
  rw [List.toFinset_card_of_nodup (A.isPath j).support_nodup,
    (A.path j).length_support]

theorem ShortAbsorbableFamily.pairwiseDisjoint_support_toFinset
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    ((Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun j => (A.path j).support.toFinset) := by
  intro i _hi j _hj hij
  rw [Function.onFun, Finset.disjoint_left]
  intro v hvi hvj
  exact (List.disjoint_left.mp (A.support_disjoint i j hij))
    (List.mem_toFinset.mp hvi) (List.mem_toFinset.mp hvj)

/-- Exact outside-vertex count: disjoint path supports add without loss. -/
theorem ShortAbsorbableFamily.card_vertices
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.vertices.card = ∑ j : J, ((A.path j).length + 1) := by
  classical
  rw [ShortAbsorbableFamily.vertices,
    Finset.card_biUnion A.pairwiseDisjoint_support_toFinset]
  apply Finset.sum_congr rfl
  intro j _hj
  exact A.path_support_card j

theorem ShortAbsorbableFamily.index_card_le_vertices_card
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Fintype.card J ≤ A.vertices.card := by
  rw [A.card_vertices]
  calc
    Fintype.card J = ∑ _j : J, 1 := by simp
    _ ≤ ∑ j : J, ((A.path j).length + 1) := by
      exact Finset.sum_le_sum fun _j _hj => by omega

theorem ShortAbsorbableFamily.disjoint_block_vertices
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Disjoint B A.vertices := by
  classical
  rw [Finset.disjoint_left]
  intro v hvB hvA
  rcases Finset.mem_biUnion.mp hvA with ⟨j, _hj, hvj⟩
  exact A.support_outside j v (List.mem_toFinset.mp hvj) hvB

/-- The absorbed graph has the expected order because the dense block and
all outside path supports are disjoint. -/
theorem ShortAbsorbableFamily.card_block_union_vertices
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    (B ∪ A.vertices).card = B.card + A.vertices.card := by
  exact Finset.card_union_of_disjoint A.disjoint_block_vertices

noncomputable def ShortAbsorbableFamily.remaining
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Finset V := B \ A.attachments

def ShortAbsorbableFamily.proxyAdj
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    (A.remaining ⊕ J) → (A.remaining ⊕ J) → Prop
  | Sum.inl x, Sum.inl y => G.Adj x.1 y.1
  | Sum.inl x, Sum.inr j =>
      G.Adj x.1 (A.attach (j, 0)) ∧ G.Adj x.1 (A.attach (j, 1))
  | Sum.inr j, Sum.inl x =>
      G.Adj x.1 (A.attach (j, 0)) ∧ G.Adj x.1 (A.attach (j, 1))
  | Sum.inr _, Sum.inr _ => False

theorem ShortAbsorbableFamily.proxyAdj_symm
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Symmetric A.proxyAdj := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact hxy.symm
      | inr j => exact hxy
  | inr i =>
      cases y with
      | inl y => exact hxy
      | inr j => exact hxy.elim

theorem ShortAbsorbableFamily.proxyAdj_irrefl
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Irreflexive A.proxyAdj := by
  intro x
  cases x with
  | inl x =>
      change ¬G.Adj x.1 x.1
      exact G.loopless.irrefl x.1
  | inr i => exact id

noncomputable def ShortAbsorbableFamily.proxyGraph
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    SimpleGraph (A.remaining ⊕ J) :=
  SimpleGraph.fromRel A.proxyAdj

@[simp] theorem ShortAbsorbableFamily.proxyGraph_adj
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (x y : A.remaining ⊕ J) :
    A.proxyGraph.Adj x y ↔ A.proxyAdj x y := by
  change x ≠ y ∧ (A.proxyAdj x y ∨ A.proxyAdj y x) ↔ A.proxyAdj x y
  constructor
  · rintro ⟨_hxy, h | h⟩
    · exact h
    · exact A.proxyAdj_symm h
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hxy
    subst y
    exact A.proxyAdj_irrefl x h

theorem ShortAbsorbableFamily.card_remaining
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.remaining.card = B.card - 2 * Fintype.card J := by
  classical
  rw [ShortAbsorbableFamily.remaining,
    Finset.card_sdiff_of_subset A.attachments_subset,
    A.card_attachments]

theorem ShortAbsorbableFamily.card_proxyVertex
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    Fintype.card (A.remaining ⊕ J) = B.card - Fintype.card J := by
  rw [Fintype.card_sum, Fintype.card_coe, A.card_remaining]
  have hattachCard : 2 * Fintype.card J ≤ B.card := by
    rw [← A.card_attachments]
    exact Finset.card_le_card A.attachments_subset
  omega

theorem ShortAbsorbableFamily.degreeIn_remaining_le_proxy_degree_left
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) (x : A.remaining) :
    degreeIn G A.remaining x.1 ≤ A.proxyGraph.degree (Sum.inl x) := by
  classical
  let S : Finset A.remaining :=
    (Finset.univ : Finset A.remaining).filter fun y => G.Adj x.1 y.1
  let e : A.remaining ↪ (A.remaining ⊕ J) :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hsub : S.map e ⊆ A.proxyGraph.neighborFinset (Sum.inl x) := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hzAdj : G.Adj x.1 z.1 := (Finset.mem_filter.mp hz).2
    apply (SimpleGraph.mem_neighborFinset _ _ _).2
    apply (A.proxyGraph_adj _ _).2
    exact hzAdj
  calc
    degreeIn G A.remaining x.1 = S.card := by
      change (A.remaining.filter fun y => G.Adj x.1 y).card =
        (A.remaining.attach.filter fun y => G.Adj x.1 y.1).card
      rw [Finset.filter_attach, Finset.card_map, Finset.card_attach]
    _ = (S.map e).card := (Finset.card_map e).symm
    _ ≤ (A.proxyGraph.neighborFinset (Sum.inl x)).card :=
      Finset.card_le_card hsub
    _ = A.proxyGraph.degree (Sum.inl x) :=
      by rw [SimpleGraph.card_neighborFinset_eq_degree]

theorem ShortAbsorbableFamily.common_remaining_le_proxy_degree
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) (j : J) :
    (Erdos163.FiniteDefect.commonNeighbors G
      ![A.attach (j, 0), A.attach (j, 1)] A.remaining).card ≤
      A.proxyGraph.degree (Sum.inr j) := by
  classical
  let C : Finset A.remaining :=
    (Finset.univ : Finset A.remaining).filter fun x =>
      G.Adj x.1 (A.attach (j, 0)) ∧ G.Adj x.1 (A.attach (j, 1))
  let e : A.remaining ↪ (A.remaining ⊕ J) :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hsub : C.map e ⊆ A.proxyGraph.neighborFinset (Sum.inr j) := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hzAdj := (Finset.mem_filter.mp hz).2
    apply (SimpleGraph.mem_neighborFinset _ _ _).2
    apply (A.proxyGraph_adj _ _).2
    exact hzAdj
  have hcardC :
      (Erdos163.FiniteDefect.commonNeighbors G
        ![A.attach (j, 0), A.attach (j, 1)] A.remaining).card = C.card := by
    rw [commonNeighbors_pair_eq_inter]
    change
      ((A.remaining.filter fun x => G.Adj (A.attach (j, 0)) x) ∩
        (A.remaining.filter fun x => G.Adj (A.attach (j, 1)) x)).card =
      (A.remaining.attach.filter fun x =>
        G.Adj x.1 (A.attach (j, 0)) ∧ G.Adj x.1 (A.attach (j, 1))).card
    rw [← Finset.filter_and]
    simp_rw [G.adj_comm]
    exact (card_filter_attach_eq A.remaining fun x =>
      G.Adj x (A.attach (j, 0)) ∧ G.Adj x (A.attach (j, 1))).symm
  calc
    (Erdos163.FiniteDefect.commonNeighbors G
        ![A.attach (j, 0), A.attach (j, 1)] A.remaining).card = C.card := hcardC
    _ = (C.map e).card := (Finset.card_map e).symm
    _ ≤ (A.proxyGraph.neighborFinset (Sum.inr j)).card :=
      Finset.card_le_card hsub
    _ = A.proxyGraph.degree (Sum.inr j) :=
      by rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- Under the quantitative dense-block hypothesis, every vertex of the proxy
graph has degree at least half of the proxy order.  This is the numerical
heart of KLS dense absorption. -/
theorem ShortAbsorbableFamily.two_mul_proxy_degree_ge_card
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) {k : ℕ} (hk : 1000 ≤ k)
    (htotal : B.card + A.vertices.card = k)
    (hsmall : 10 * A.vertices.card ≤ B.card)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    ∀ x : A.remaining ⊕ J,
      Fintype.card (A.remaining ⊕ J) ≤ 2 * A.proxyGraph.degree x := by
  classical
  have hp : Fintype.card J ≤ A.vertices.card := A.index_card_le_vertices_card
  have hremSub : A.remaining ⊆ B := by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).1
  have hremLoss : B.card - A.remaining.card = 2 * Fintype.card J := by
    rw [A.card_remaining]
    have hattachCard : 2 * Fintype.card J ≤ B.card := by
      rw [← A.card_attachments]
      exact Finset.card_le_card A.attachments_subset
    omega
  intro x
  rw [A.card_proxyVertex]
  cases x with
  | inl x =>
      have hxB : x.1 ∈ B := hremSub x.2
      have hxstrong := hdeg x.1 hxB
      have hloss := degreeIn_le_degreeIn_add_card_loss G hremSub x.1
      rw [hremLoss] at hloss
      have hproxy := A.degreeIn_remaining_le_proxy_degree_left x
      omega
  | inr j =>
      let a : V := A.attach (j, 0)
      let b : V := A.attach (j, 1)
      have haB : a ∈ B := A.attach_mem (j, 0)
      have hbB : b ∈ B := A.attach_mem (j, 1)
      have haStrong := hdeg a haB
      have hbStrong := hdeg b hbB
      have haLoss := degreeIn_le_degreeIn_add_card_loss G hremSub a
      have hbLoss := degreeIn_le_degreeIn_add_card_loss G hremSub b
      rw [hremLoss] at haLoss hbLoss
      let Na : Finset V := A.remaining.filter fun v => G.Adj a v
      let Nb : Finset V := A.remaining.filter fun v => G.Adj b v
      have hNa : Na.card = degreeIn G A.remaining a := rfl
      have hNb : Nb.card = degreeIn G A.remaining b := rfl
      have hUnion : (Na ∪ Nb).card ≤ A.remaining.card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_filter.mp hv).1
        · exact (Finset.mem_filter.mp hv).1
      have hsum := Finset.card_union_add_card_inter Na Nb
      have hcommonEq :
          (Erdos163.FiniteDefect.commonNeighbors G ![a, b] A.remaining).card =
            (Na ∩ Nb).card := by
        rw [commonNeighbors_pair_eq_inter]
      have hproxy := A.common_remaining_le_proxy_degree j
      change
        (Erdos163.FiniteDefect.commonNeighbors G ![a, b] A.remaining).card ≤
          A.proxyGraph.degree (Sum.inr j) at hproxy
      rw [hNa, hNb, ← hcommonEq] at hsum
      rw [hcommonEq] at hproxy
      have hattachCard : 2 * Fintype.card J ≤ B.card := by
        rw [← A.card_attachments]
        exact Finset.card_le_card A.attachments_subset
      have hremEq : A.remaining.card + 2 * Fintype.card J = B.card := by
        rw [A.card_remaining]
        omega
      have hbj : B.card + Fintype.card J ≤ k := by omega
      have hdegreeSum :
          degreeIn G B a + degreeIn G B b ≤
            A.remaining.card + (Na ∩ Nb).card + 4 * Fintype.card J := by
        omega
      omega

theorem ShortAbsorbableFamily.proxyGraph_isHamiltonian
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) {k : ℕ} (hk : 1000 ≤ k)
    (htotal : B.card + A.vertices.card = k)
    (hsmall : 10 * A.vertices.card ≤ B.card)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    A.proxyGraph.IsHamiltonian := by
  classical
  have hp : Fintype.card J ≤ A.vertices.card := A.index_card_le_vertices_card
  have hcard := A.card_proxyVertex
  have hthree : 3 ≤ Fintype.card (A.remaining ⊕ J) := by
    rw [hcard]
    omega
  apply SimpleGraph.dirac_theorem (G := A.proxyGraph) hthree
  intro x
  exact A.two_mul_proxy_degree_ge_card hk htotal hsmall hdeg x

/-- The ambient route represented by one absorbed-path proxy. -/
def ShortAbsorbableFamily.absorbedRoute
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (j : J) : G.Walk (A.attach (j, 0)) (A.attach (j, 1)) :=
  Walk.cons (A.start_adj j) ((A.path j).concat (A.finish_adj j))

@[simp] theorem ShortAbsorbableFamily.absorbedRoute_support
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (j : J) :
    (A.absorbedRoute j).support =
      A.attach (j, 0) :: (A.path j).support ++ [A.attach (j, 1)] := by
  simp [ShortAbsorbableFamily.absorbedRoute]

@[simp] theorem ShortAbsorbableFamily.absorbedRoute_length
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (j : J) :
    (A.absorbedRoute j).length = (A.path j).length + 2 := by
  simp [ShortAbsorbableFamily.absorbedRoute]

theorem ShortAbsorbableFamily.absorbedRoute_isPath
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (j : J) :
    (A.absorbedRoute j).IsPath := by
  have hfinish : A.attach (j, 1) ∉ (A.path j).support := by
    intro h
    exact A.support_outside j _ h (A.attach_mem (j, 1))
  have hstartPath : A.attach (j, 0) ∉ (A.path j).support := by
    intro h
    exact A.support_outside j _ h (A.attach_mem (j, 0))
  have hstartFinish : A.attach (j, 0) ≠ A.attach (j, 1) := by
    intro h
    have hpairs := A.attach_injective h
    simpa using hpairs
  apply (A.isPath j).concat hfinish (A.finish_adj j) |>.cons
  simp [hstartPath, hstartFinish]

def ShortAbsorbableFamily.expansionStart
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.remaining ⊕ J → V
  | Sum.inl x => x.1
  | Sum.inr j => A.attach (j, 0)

def ShortAbsorbableFamily.expansionFinish
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    A.remaining ⊕ J → V
  | Sum.inl x => x.1
  | Sum.inr j => A.attach (j, 1)

def ShortAbsorbableFamily.expansionPath
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    ∀ x : A.remaining ⊕ J,
      G.Walk (A.expansionStart x) (A.expansionFinish x)
  | Sum.inl _ => Walk.nil
  | Sum.inr j => A.absorbedRoute j

theorem ShortAbsorbableFamily.expansionPath_isPath
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B) :
    ∀ x, (A.expansionPath x).IsPath
  | Sum.inl _ => Walk.IsPath.nil
  | Sum.inr j => A.absorbedRoute_isPath j

theorem ShortAbsorbableFamily.proxyAdj_expansion_endpoints
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    {x y : A.remaining ⊕ J} (hxy : A.proxyAdj x y) :
    G.Adj (A.expansionFinish x) (A.expansionStart y) := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact hxy
      | inr j => exact hxy.1
  | inr i =>
      cases y with
      | inl y => exact hxy.2.symm
      | inr j => exact hxy.elim

/-- Distinct proxy vertices expand to vertex-disjoint ambient paths. -/
theorem ShortAbsorbableFamily.expansionPath_support_disjoint
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    {x y : A.remaining ⊕ J} (hxy : x ≠ y) :
    (A.expansionPath x).support.Disjoint (A.expansionPath y).support := by
  classical
  rw [List.disjoint_left]
  intro v hvx hvy
  cases x with
  | inl x =>
      have hvx' : v = x.1 := by
        exact Walk.mem_support_nil_iff.mp hvx
      subst v
      cases y with
      | inl y =>
        have hxyv : x.1 = y.1 := by
            exact Walk.mem_support_nil_iff.mp hvy
        exact hxy (congrArg Sum.inl (Subtype.ext hxyv))
      | inr j =>
          have hxB : x.1 ∈ B := (Finset.mem_sdiff.mp x.2).1
          have hxNotAttach : x.1 ∉ A.attachments := (Finset.mem_sdiff.mp x.2).2
          have hvy' : x.1 = A.attach (j, 0) ∨
              x.1 ∈ (A.path j).support ∨ x.1 = A.attach (j, 1) := by
            change x.1 ∈ (A.absorbedRoute j).support at hvy
            rw [A.absorbedRoute_support] at hvy
            simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hvy
            tauto
          rcases hvy' with h0 | hpath | h1
          · apply hxNotAttach
            exact Finset.mem_image.mpr ⟨(j, 0), Finset.mem_univ _, h0.symm⟩
          · exact A.support_outside j x.1 hpath hxB
          · apply hxNotAttach
            exact Finset.mem_image.mpr ⟨(j, 1), Finset.mem_univ _, h1.symm⟩
  | inr i =>
      have hvx' : v = A.attach (i, 0) ∨
          v ∈ (A.path i).support ∨ v = A.attach (i, 1) := by
        change v ∈ (A.absorbedRoute i).support at hvx
        rw [A.absorbedRoute_support] at hvx
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hvx
        tauto
      cases y with
      | inl y =>
          have hyB : y.1 ∈ B := (Finset.mem_sdiff.mp y.2).1
          have hyNotAttach : y.1 ∉ A.attachments := (Finset.mem_sdiff.mp y.2).2
          have hvy' : v = y.1 := by
            exact Walk.mem_support_nil_iff.mp hvy
          subst v
          rcases hvx' with h0 | hpath | h1
          · apply hyNotAttach
            exact Finset.mem_image.mpr ⟨(i, 0), Finset.mem_univ _, h0.symm⟩
          · exact A.support_outside i y.1 hpath hyB
          · apply hyNotAttach
            exact Finset.mem_image.mpr ⟨(i, 1), Finset.mem_univ _, h1.symm⟩
      | inr j =>
          have hvy' : v = A.attach (j, 0) ∨
              v ∈ (A.path j).support ∨ v = A.attach (j, 1) := by
            change v ∈ (A.absorbedRoute j).support at hvy
            rw [A.absorbedRoute_support] at hvy
            simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hvy
            tauto
          have hij : i ≠ j := by
            intro h
            exact hxy (congrArg Sum.inr h)
          rcases hvx' with hi0 | hipath | hi1 <;>
            rcases hvy' with hj0 | hjpath | hj1
          · exact hij (congrArg Prod.fst (A.attach_injective (hi0.symm.trans hj0)))
          · exact A.support_outside j _ hjpath
              (hi0 ▸ A.attach_mem (i, 0))
          · exact hij (congrArg Prod.fst (A.attach_injective (hi0.symm.trans hj1)))
          · exact A.support_outside i _ hipath
              (hj0 ▸ A.attach_mem (j, 0))
          · exact (List.disjoint_left.mp (A.support_disjoint i j hij)) hipath hjpath
          · exact A.support_outside i _ hipath
              (hj1 ▸ A.attach_mem (j, 1))
          · exact hij (congrArg Prod.fst (A.attach_injective (hi1.symm.trans hj0)))
          · exact A.support_outside j _ hjpath
              (hi1 ▸ A.attach_mem (i, 1))
          · exact hij (congrArg Prod.fst (A.attach_injective (hi1.symm.trans hj1)))

/-- Expanding a Hamilton cycle of the proxy graph absorbs every short outside
path and produces an ambient cycle of the prescribed total order.  This is
the cycle-assembly half of the KLS dense absorption lemma. -/
theorem ShortAbsorbableFamily.cycleGraph_isContained_of_dense
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) {k : ℕ} (hk : 1000 ≤ k)
    (htotal : B.card + A.vertices.card = k)
    (hsmall : 10 * A.vertices.card ≤ B.card)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    cycleGraph k ⊑ G := by
  classical
  let q : ℕ := Fintype.card (A.remaining ⊕ J)
  have hp : Fintype.card J ≤ A.vertices.card := A.index_card_le_vertices_card
  have hthree : 3 ≤ q := by
    change 3 ≤ Fintype.card (A.remaining ⊕ J)
    rw [A.card_proxyVertex]
    omega
  have hham := A.proxyGraph_isHamiltonian hk htotal hsmall hdeg
  obtain ⟨z, w, hw⟩ := hham (by omega)
  have hwlen : w.length = q := by
    simpa [q] using hw.length_eq
  let visit : Fin q → A.remaining ⊕ J :=
    fun i => w.getVert (i.val + 1)
  have hvisitInj : Function.Injective visit := by
    intro i j hij
    apply Fin.ext
    have hindex := hw.isCycle.getVert_injOn
      (x₁ := i.val + 1) (x₂ := j.val + 1)
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simpa [visit] using hij)
    omega
  have hvisitBij : Function.Bijective visit :=
    (Fintype.bijective_iff_injective_and_card visit).2
      ⟨hvisitInj, by simp [q]⟩
  let e : Fin q ≃ (A.remaining ⊕ J) := Equiv.ofBijective visit hvisitBij
  have he_apply : ∀ i : Fin q, e i = visit i := by
    intro i
    rfl
  let a : Fin q → V := fun i => A.expansionStart (e i)
  let b : Fin q → V := fun i => A.expansionFinish (e i)
  let pth : ∀ i : Fin q, G.Walk (a i) (b i) :=
    fun i => A.expansionPath (e i)
  have hproxyCross : ∀ i j : Fin q, j.val = i.val + 1 →
      A.proxyAdj (e i) (e j) := by
    intro i j hij
    rw [← A.proxyGraph_adj]
    have hi : i.val + 1 < w.length := by
      rw [hwlen]
      omega
    have hadj := w.adj_getVert_succ hi
    simpa [he_apply, visit, hij] using hadj
  have hproxyClose : ∀ i j : Fin q, i.val + 1 = q → j.val = 0 →
      A.proxyAdj (e i) (e j) := by
    intro i j hi hj
    rw [← A.proxyGraph_adj]
    have hadj := w.adj_getVert_succ (i := 0) (by omega : 0 < w.length)
    have hlast : w.getVert (i.val + 1) = w.getVert 0 := by
      rw [hi, ← hwlen, w.getVert_length, w.getVert_zero]
    simpa [he_apply, visit, hj, hlast] using hadj
  have hsumProxy :
      (∑ x : A.remaining ⊕ J, (A.expansionPath x).length) =
        A.vertices.card + Fintype.card J := by
    rw [Fintype.sum_sum_type]
    have hinl : ∀ x : A.remaining,
        (A.expansionPath (Sum.inl x)).length = 0 := by intro x; rfl
    have hinr : ∀ j : J,
        (A.expansionPath (Sum.inr j)).length = (A.path j).length + 2 := by
      intro j
      exact A.absorbedRoute_length j
    simp_rw [hinl, hinr]
    simp only [Finset.sum_const_zero, zero_add]
    rw [A.card_vertices]
    simp_rw [show ∀ j : J, (A.path j).length + 2 =
        ((A.path j).length + 1) + 1 by intro j; omega]
    rw [Finset.sum_add_distrib]
    simp
  have hsum : (∑ i : Fin q, (pth i).length) =
      A.vertices.card + Fintype.card J := by
    change (∑ i : Fin q, (A.expansionPath (e i)).length) = _
    exact (e.sum_comp fun x => (A.expansionPath x).length).trans hsumProxy
  have hattachCard : 2 * Fintype.card J ≤ B.card := by
    rw [← A.card_attachments]
    exact Finset.card_le_card A.attachments_subset
  have hqCard : q = B.card - Fintype.card J := by
    exact A.card_proxyVertex
  apply cycleGraph_isContained_of_cyclic_cross_edges_and_disjoint_paths_val
      G (by omega : 0 < q) (by omega : 3 ≤ k) a b pth
  · intro i
    exact A.expansionPath_isPath (e i)
  · intro i j hij
    exact A.expansionPath_support_disjoint (e.injective.ne hij)
  · intro i j hij
    exact A.proxyAdj_expansion_endpoints (hproxyCross i j hij)
  · intro i j hi hj
    exact A.proxyAdj_expansion_endpoints (hproxyClose i j hi hj)
  · rw [hsum]
    omega
  · rw [hsum, hqCard]
    omega

/-- Cleanup moves add at most three outside vertices at a time, so the first
move reaching the target may overshoot it by two.  Delete that many unused
dense-block vertices.  The stable block's `123/128` degree bound loses at
most two neighbours and still gives the `121/128` bound used by the proxy
Dirac argument. -/
theorem ShortAbsorbableFamily.cycleGraph_isContained_of_dense_near_target
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) {k : ℕ} (hk : 1000 ≤ k)
    (htotalLower : k ≤ B.card + A.vertices.card)
    (htotalUpper : B.card + A.vertices.card ≤ k + 2)
    (hsmall : 10 * A.vertices.card + 2 ≤ B.card)
    (hdeg : ∀ v ∈ B,
      123 * (k - 1) ≤ 128 * degreeIn G B v) :
    cycleGraph k ⊑ G := by
  classical
  let r : ℕ := B.card + A.vertices.card - k
  have hr : r ≤ 2 := by dsimp [r]; omega
  have hindex : Fintype.card J ≤ A.vertices.card := A.index_card_le_vertices_card
  have hattachCard : 2 * Fintype.card J ≤ B.card := by
    rw [← A.card_attachments]
    exact Finset.card_le_card A.attachments_subset
  have hremTwo : 2 ≤ A.remaining.card := by
    rw [A.card_remaining]
    omega
  have hrrem : r ≤ A.remaining.card := hr.trans hremTwo
  obtain ⟨D, hDrem, hDcard⟩ :=
    Finset.exists_subset_card_eq (s := A.remaining) hrrem
  have hDB : D ⊆ B := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hDrem hv)).1
  have hattachNotD : ∀ q : J × Fin 2, A.attach q ∉ D := by
    intro q hqD
    have hqRem := hDrem hqD
    exact (Finset.mem_sdiff.mp hqRem).2
      (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)
  let B' : Finset V := B \ D
  let A' : ShortAbsorbableFamily (J := J) G B' :=
    { start := A.start
      finish := A.finish
      path := A.path
      isPath := A.isPath
      length_le_two := A.length_le_two
      attach := A.attach
      attach_mem := fun q =>
        Finset.mem_sdiff.mpr ⟨A.attach_mem q, hattachNotD q⟩
      attach_injective := A.attach_injective
      start_adj := A.start_adj
      finish_adj := A.finish_adj
      support_outside := by
        intro j v hv hvB'
        exact A.support_outside j v hv (Finset.sdiff_subset hvB')
      support_disjoint := A.support_disjoint }
  have hB'card : B'.card = B.card - r := by
    dsimp [B']
    rw [Finset.card_sdiff_of_subset hDB, hDcard]
  have hvertices : A'.vertices = A.vertices := by
    rfl
  have htotal : B'.card + A'.vertices.card = k := by
    rw [hB'card, hvertices]
    dsimp [r]
    omega
  have hsmall' : 10 * A'.vertices.card ≤ B'.card := by
    rw [hvertices, hB'card]
    omega
  have hdeg' : ∀ v ∈ B',
      121 * (k - 1) ≤ 128 * degreeIn G B' v := by
    intro v hv
    have hvB : v ∈ B := Finset.sdiff_subset hv
    have hold := hdeg v hvB
    have hloss := degreeIn_le_degreeIn_add_card_loss
      G (show B' ⊆ B from Finset.sdiff_subset) v
    have hcardLoss : B.card - B'.card = r := by
      rw [hB'card]
      omega
    rw [hcardLoss] at hloss
    omega
  exact A'.cycleGraph_isContained_of_dense hk htotal hsmall' hdeg'

/-! ## Finite cleanup system for the KLS remainder -/

/-- Finite data for one cleanup move.  The bounded path itself is kept in
the validity predicate, so the type of candidates is finite even though
`Walk` is an inductive type. -/
structure CleanupMove (ι V : Type*) where
  block : ι
  attach₀ : V
  attach₁ : V
  support : Finset V
  deriving DecidableEq, Fintype

def CleanupMove.attach
    {ι V : Type*} (c : CleanupMove ι V) (t : Fin 2) : V :=
  ![c.attach₀, c.attach₁] t

def ValidCleanupMove
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (B : ι → Finset V) (L : Finset V)
    (c : CleanupMove ι V) : Prop :=
  c.attach₀ ∈ B c.block ∧ c.attach₁ ∈ B c.block ∧
    c.attach₀ ≠ c.attach₁ ∧ c.support.Nonempty ∧ c.support ⊆ L ∧
    ∃ x ∈ c.support, ∃ y ∈ c.support,
      ∃ p : G.Walk x y,
        p.IsPath ∧ p.length ≤ 2 ∧ p.support.toFinset = c.support ∧
          G.Adj c.attach₀ x ∧ G.Adj y c.attach₁

def IsCleanupFamily
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (B : ι → Finset V) (L : Finset V)
    (M : Finset (CleanupMove ι V)) : Prop :=
  (∀ c ∈ M, ValidCleanupMove G B L c) ∧
    ((M : Set (CleanupMove ι V)).PairwiseDisjoint CleanupMove.support) ∧
    ∀ c ∈ M, ∀ d ∈ M, c ≠ d → c.block = d.block →
      ∀ r s : Fin 2, c.attach r ≠ d.attach s

noncomputable def cleanupAbsorbed
    {V ι : Type*} [Fintype V]
    (M : Finset (CleanupMove ι V)) : Finset V :=
  M.biUnion CleanupMove.support

theorem isCleanupFamily_empty
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (B : ι → Finset V) (L : Finset V) :
    IsCleanupFamily G B L ∅ := by
  simp [IsCleanupFamily]

/-- Since both the vertex set and the candidate-record type are finite, a
cleanup family maximizing the number of absorbed vertices exists.  Such a
family is inclusion-maximal among valid cleanup families. -/
theorem exists_maximal_cleanupFamily
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (B : ι → Finset V) (L : Finset V) :
    ∃ M : Finset (CleanupMove ι V),
      IsCleanupFamily G B L M ∧
      ∀ c : CleanupMove ι V,
        IsCleanupFamily G B L (insert c M) → c ∈ M := by
  classical
  let Families : Finset (Finset (CleanupMove ι V)) :=
    Finset.univ.filter fun M => IsCleanupFamily G B L M
  have hFamilies : Families.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Families, isCleanupFamily_empty]
  obtain ⟨M, hMFamilies, hmax⟩ :=
    Finset.exists_max_image Families
      (fun N => (cleanupAbsorbed N).card) hFamilies
  have hM : IsCleanupFamily G B L M :=
    (Finset.mem_filter.mp hMFamilies).2
  refine ⟨M, hM, ?_⟩
  intro c hc
  by_contra hcM
  have hinsFamilies : insert c M ∈ Families := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hle := hmax (insert c M) hinsFamilies
  have hcsuppNonempty : c.support.Nonempty := (hc.1 c (by simp)).2.2.2.1
  have hdisj : Disjoint c.support (cleanupAbsorbed M) := by
    rw [Finset.disjoint_left]
    intro v hvc hvM
    rcases Finset.mem_biUnion.mp hvM with ⟨d, hdM, hvd⟩
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcM hdM
    exact (Finset.disjoint_left.mp
      (hc.2.1 (by simp) (by exact Finset.mem_insert_of_mem hdM) hcd)) hvc hvd
  have hscore :
      (cleanupAbsorbed (insert c M)).card =
        c.support.card + (cleanupAbsorbed M).card := by
    rw [cleanupAbsorbed, Finset.biUnion_insert]
    apply Finset.card_union_of_disjoint
    simpa [cleanupAbsorbed] using hdisj
  rw [hscore] at hle
  exact (Nat.not_succ_le_self (cleanupAbsorbed M).card) <| by
    have hcpos := Finset.card_pos.mpr hcsuppNonempty
    omega

/-- A chosen bounded path witnessing the validity of one finite cleanup
record. -/
structure CleanupPathWitness
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (c : CleanupMove ι V) where
  start : V
  finish : V
  start_mem : start ∈ c.support
  finish_mem : finish ∈ c.support
  path : G.Walk start finish
  isPath : path.IsPath
  length_le_two : path.length ≤ 2
  support_eq : path.support.toFinset = c.support
  start_adj : G.Adj c.attach₀ start
  finish_adj : G.Adj finish c.attach₁

noncomputable def ValidCleanupMove.pathWitness
    {V ι : Type*} [Fintype V]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {c : CleanupMove ι V} (hc : ValidCleanupMove G B L c) :
    CleanupPathWitness G c := by
  let x := Classical.choose hc.2.2.2.2.2
  have hx := Classical.choose_spec hc.2.2.2.2.2
  let y := Classical.choose hx.2
  have hy := Classical.choose_spec hx.2
  let p := Classical.choose hy.2
  have hp := Classical.choose_spec hy.2
  exact
    { start := x
      finish := y
      start_mem := hx.1
      finish_mem := hy.1
      path := p
      isPath := hp.1
      length_le_two := hp.2.1
      support_eq := hp.2.2.1
      start_adj := hp.2.2.2.1
      finish_adj := hp.2.2.2.2 }

abbrev CleanupFiber
    {V ι : Type*} [Fintype V]
    (M : Finset (CleanupMove ι V)) (i : ι) :=
  {c : CleanupMove ι V // c ∈ M ∧ c.block = i}

noncomputable def cleanupAbsorbedAt
    {V ι : Type*} [Fintype V]
    (M : Finset (CleanupMove ι V)) (i : ι) : Finset V :=
  (M.filter fun c => c.block = i).biUnion CleanupMove.support

theorem cleanupAbsorbedAt_subset_cleanupAbsorbed
    {V ι : Type*} [Fintype V]
    (M : Finset (CleanupMove ι V)) (i : ι) :
    cleanupAbsorbedAt M i ⊆ cleanupAbsorbed M := by
  classical
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨c, hc, hvc⟩
  exact Finset.mem_biUnion.mpr
    ⟨c, (Finset.mem_filter.mp hc).1, hvc⟩

/-- The moves assigned to one block are exactly a short absorbable family
for that block. -/
noncomputable def IsCleanupFamily.absorbableFamilyAt
    {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hBL : ∀ i, Disjoint (B i) L) (i : ι) :
    ShortAbsorbableFamily (J := CleanupFiber M i) G (B i) := by
  classical
  let J := CleanupFiber M i
  let witness : (j : J) → CleanupPathWitness G j.1 := fun j =>
    (hM.1 j.1 j.2.1).pathWitness
  refine
    { start := fun j => (witness j).start
      finish := fun j => (witness j).finish
      path := fun j => (witness j).path
      isPath := fun j => (witness j).isPath
      length_le_two := fun j => (witness j).length_le_two
      attach := fun q => q.1.1.attach q.2
      attach_mem := ?_
      attach_injective := ?_
      start_adj := ?_
      finish_adj := ?_
      support_outside := ?_
      support_disjoint := ?_ }
  · intro q
    rcases q with ⟨j, t⟩
    have hvalid := hM.1 j.1 j.2.1
    have hblock := j.2.2
    fin_cases t
    · simpa [CleanupMove.attach, hblock] using hvalid.1
    · simpa [CleanupMove.attach, hblock] using hvalid.2.1
  · rintro ⟨q, t⟩ ⟨r, s⟩ hqr
    have hmove : q = r := by
      apply Subtype.ext
      by_contra hmove
      have hsep := hM.2.2 q.1 q.2.1 r.1 r.2.1 hmove
        (q.2.2.trans r.2.2.symm) t s
      exact hsep hqr
    subst r
    apply Prod.ext
    · rfl
    have hvalid := hM.1 q.1 q.2.1
    fin_cases t <;> fin_cases s
    · rfl
    · exact (hvalid.2.2.1 (by simpa [CleanupMove.attach] using hqr)).elim
    · exact (hvalid.2.2.1 (by simpa [CleanupMove.attach] using hqr.symm)).elim
    · rfl
  · intro j
    simpa [CleanupMove.attach, witness] using (witness j).start_adj
  · intro j
    simpa [CleanupMove.attach, witness] using (witness j).finish_adj
  · intro j v hv hvB
    have hsupport : v ∈ j.1.support := by
      have := List.mem_toFinset.mpr hv
      rwa [(witness j).support_eq] at this
    have hvL : v ∈ L := (hM.1 j.1 j.2.1).2.2.2.2.1 hsupport
    exact (Finset.disjoint_left.mp (hBL i)) hvB hvL
  · intro j l hjl
    have hmove : j.1 ≠ l.1 := by
      intro h
      apply hjl
      exact Subtype.ext h
    apply List.disjoint_toFinset_iff_disjoint.mp
    rw [(witness j).support_eq, (witness l).support_eq]
    exact hM.2.1 (by simpa using j.2.1) (by simpa using l.2.1) hmove

theorem IsCleanupFamily.absorbableFamilyAt_vertices
    {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hBL : ∀ i, Disjoint (B i) L) (i : ι) :
    (hM.absorbableFamilyAt hBL i).vertices = cleanupAbsorbedAt M i := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨j, _hj, hvj⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j.1, Finset.mem_filter.mpr ⟨j.2.1, j.2.2⟩, ?_⟩
    have hw : v ∈ ((hM.absorbableFamilyAt hBL i).path j).support :=
      List.mem_toFinset.mp hvj
    change v ∈ ((hM.1 j.1 j.2.1).pathWitness.path).support at hw
    have hw' := List.mem_toFinset.mpr hw
    rw [(hM.1 j.1 j.2.1).pathWitness.support_eq] at hw'
    exact hw'
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨c, hc, hvc⟩
    let j : CleanupFiber M i := ⟨c, (Finset.mem_filter.mp hc)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    change v ∈ ((hM.1 c j.2.1).pathWitness.path).support.toFinset
    rw [(hM.1 c j.2.1).pathWitness.support_eq]
    exact hvc

/-- Restrict an absorbable family to a finite subset of its path indices. -/
def ShortAbsorbableFamily.restrict
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (Q : Finset J) : ShortAbsorbableFamily (J := Q) G B where
  start j := A.start j.1
  finish j := A.finish j.1
  path j := A.path j.1
  isPath j := A.isPath j.1
  length_le_two j := A.length_le_two j.1
  attach q := A.attach (q.1.1, q.2)
  attach_mem q := A.attach_mem (q.1.1, q.2)
  attach_injective := by
    intro q r hqr
    have hp : (q.1.1, q.2) = (r.1.1, r.2) := A.attach_injective hqr
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : J × Fin 2 => z.1) hp)
    · exact congrArg (fun z : J × Fin 2 => z.2) hp
  start_adj j := A.start_adj j.1
  finish_adj j := A.finish_adj j.1
  support_outside j := A.support_outside j.1
  support_disjoint i j hij := by
    apply A.support_disjoint i.1 j.1
    intro h
    apply hij
    exact Subtype.ext h

theorem ShortAbsorbableFamily.restrict_vertices_card
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} {B : Finset V} (A : ShortAbsorbableFamily (J := J) G B)
    (Q : Finset J) :
    (A.restrict Q).vertices.card =
      ∑ j ∈ Q, ((A.path j).length + 1) := by
  rw [(A.restrict Q).card_vertices]
  change (∑ j : Q, ((A.path j.1).length + 1)) = _
  exact Finset.sum_attach Q (fun j => (A.path j).length + 1)

/-- If some absorbable family would carry a dense block up to or beyond
`k`, take a minimal subfamily that does so.  Every move has at most three
vertices, hence this minimal subfamily has total order at most `k+2`, where
the near-target absorption theorem applies. -/
theorem ShortAbsorbableFamily.cycleGraph_isContained_of_total_ge
    {V J : Type*} [Fintype V] [Fintype J]
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (A : ShortAbsorbableFamily (J := J) G B) {k : ℕ} (hk : 1000 ≤ k)
    (hBcard : B.card ≤ k - 1)
    (htotal : k ≤ B.card + A.vertices.card)
    (hroom : 10 * (k - B.card + 2) + 2 ≤ B.card)
    (hdeg : ∀ v ∈ B,
      123 * (k - 1) ≤ 128 * degreeIn G B v) :
    cycleGraph k ⊑ G := by
  classical
  let weight : J → ℕ := fun j => (A.path j).length + 1
  let Candidates : Finset (Finset J) :=
    Finset.univ.filter fun Q => k ≤ B.card + ∑ j ∈ Q, weight j
  have hCandidates : Candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [weight, A.card_vertices] using htotal
  obtain ⟨Q, hQ, hQmin⟩ :=
    Finset.exists_min_image Candidates
      (fun Q => B.card + ∑ j ∈ Q, weight j) hCandidates
  have hQtarget : k ≤ B.card + ∑ j ∈ Q, weight j :=
    (Finset.mem_filter.mp hQ).2
  have hQne : Q.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne] at hQtarget
    omega
  obtain ⟨j, hjQ⟩ := hQne
  have heraseBelow : B.card + ∑ l ∈ Q.erase j, weight l < k := by
    by_contra hnot
    have heraseCandidate : Q.erase j ∈ Candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hmin := hQmin (Q.erase j) heraseCandidate
    have hweightPos : 0 < weight j := by simp [weight]
    have hsum :
        (∑ l ∈ Q.erase j, weight l) + weight j = ∑ l ∈ Q, weight l := by
      rw [Finset.sum_erase_add _ _ hjQ]
    omega
  have hweightThree : weight j ≤ 3 := by
    dsimp [weight]
    have := A.length_le_two j
    omega
  have hQupper : B.card + ∑ l ∈ Q, weight l ≤ k + 2 := by
    have hsum :
        (∑ l ∈ Q.erase j, weight l) + weight j = ∑ l ∈ Q, weight l := by
      rw [Finset.sum_erase_add _ _ hjQ]
    omega
  let A' := A.restrict Q
  have hvertices : A'.vertices.card = ∑ j ∈ Q, weight j := by
    simpa [A', weight] using A.restrict_vertices_card Q
  have houtsideBound : A'.vertices.card ≤ k - B.card + 2 := by
    rw [hvertices]
    omega
  apply A'.cycleGraph_isContained_of_dense_near_target hk
  · rw [hvertices]
    exact hQtarget
  · rw [hvertices]
    exact hQupper
  · exact (Nat.add_le_add_right
      (Nat.mul_le_mul_left 10 houtsideBound) 2).trans hroom
  · exact hdeg

noncomputable def cleanupAttachmentsAt
    {V ι : Type*} [Fintype V]
    (M : Finset (CleanupMove ι V)) (i : ι) : Finset V :=
  (M.filter fun c => c.block = i).biUnion fun c => {c.attach₀, c.attach₁}

/-- A valid move whose outside support is fresh and whose two attachments
are unused in its block can be adjoined to a cleanup family. -/
theorem IsCleanupFamily.insert_of_fresh
    {V ι : Type*} [Fintype V]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M) (c : CleanupMove ι V)
    (hc : ValidCleanupMove G B L c)
    (hsupport : Disjoint c.support (cleanupAbsorbed M))
    (hattach : ∀ t : Fin 2, c.attach t ∉ cleanupAttachmentsAt M c.block) :
    IsCleanupFamily G B L (insert c M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hc
    · exact hM.1 d hd
  · intro d hd e he hde
    simp only [Set.mem_insert_iff, Finset.coe_insert] at hd he
    rcases hd with rfl | hd <;> rcases he with rfl | he
    · exact (hde rfl).elim
    · apply hsupport.mono_right
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
    · exact (hsupport.mono_right (fun v hv =>
        Finset.mem_biUnion.mpr ⟨d, hd, hv⟩)).symm
    · exact hM.2.1 hd he hde
  · intro d hd e he hde hblock r s
    rcases Finset.mem_insert.mp hd with rfl | hdM
    · rcases Finset.mem_insert.mp he with rfl | heM
      · exact (hde rfl).elim
      · intro hae
        apply hattach r
        apply Finset.mem_biUnion.mpr
        refine ⟨e, Finset.mem_filter.mpr ⟨heM, hblock.symm⟩, ?_⟩
        fin_cases s <;> simp_all [CleanupMove.attach]
    · rcases Finset.mem_insert.mp he with rfl | heM
      · intro hae
        apply hattach s
        apply Finset.mem_biUnion.mpr
        refine ⟨d, Finset.mem_filter.mpr ⟨hdM, hblock⟩, ?_⟩
        fin_cases r <;> simp_all [CleanupMove.attach]
      · exact hM.2.2 d hdM e heM hde hblock r s

/-- Augmentation maximality in the geometric form used by cleanup: no valid
fresh move with unused attachments remains. -/
theorem no_fresh_validCleanupMove_of_maximal
    {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hmax : ∀ c : CleanupMove ι V,
      IsCleanupFamily G B L (insert c M) → c ∈ M) :
    ¬ ∃ c : CleanupMove ι V,
      ValidCleanupMove G B L c ∧
      Disjoint c.support (cleanupAbsorbed M) ∧
      ∀ t : Fin 2, c.attach t ∉ cleanupAttachmentsAt M c.block := by
  rintro ⟨c, hc, hsupp, hatt⟩
  have hcM := hmax c (hM.insert_of_fresh c hc hsupp hatt)
  have hself : c.support ⊆ cleanupAbsorbed M := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨c, hcM, hv⟩
  obtain ⟨v, hv⟩ := hc.2.2.2.1
  exact (Finset.disjoint_left.mp hsupp) hv (hself hv)

theorem IsCleanupFamily.absorbableFamilyAt_attachments
    {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hBL : ∀ i, Disjoint (B i) L) (i : ι) :
    (hM.absorbableFamilyAt hBL i).attachments =
      cleanupAttachmentsAt M i := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨q, _hq, hqv⟩
    rcases q with ⟨j, t⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j.1, Finset.mem_filter.mpr ⟨j.2.1, j.2.2⟩, ?_⟩
    fin_cases t
    · exact Finset.mem_insert.mpr (Or.inl (by
        simpa [IsCleanupFamily.absorbableFamilyAt, CleanupMove.attach] using hqv.symm))
    · exact Finset.mem_insert.mpr (Or.inr (by
        simpa [IsCleanupFamily.absorbableFamilyAt, CleanupMove.attach] using hqv.symm))
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨c, hc, hvc⟩
    let j : CleanupFiber M i := ⟨c, (Finset.mem_filter.mp hc)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvc
    rcases hvc with rfl | rfl
    · exact Finset.mem_image.mpr
        ⟨(j, 0), Finset.mem_univ _, by
          rfl⟩
    · exact Finset.mem_image.mpr
        ⟨(j, 1), Finset.mem_univ _, by
          rfl⟩

theorem cleanupAbsorbedAt_subset
    {V ι : Type*} [Fintype V]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M) (i : ι) :
    cleanupAbsorbedAt M i ⊆ L := by
  classical
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨c, hc, hvc⟩
  exact (hM.1 c (Finset.mem_filter.mp hc).1).2.2.2.2.1 hvc

theorem cleanupAbsorbedAt_disjoint_block
    {V ι : Type*} [Fintype V]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hBL : ∀ i, Disjoint (B i) L) (i : ι) :
    Disjoint (B i) (cleanupAbsorbedAt M i) :=
  (hBL i).mono_right (cleanupAbsorbedAt_subset hM i)

/-- Cleanup paths assigned to distinct blocks are disjoint.  This is the
blockwise form of the pairwise-disjoint-support condition in a cleanup
family. -/
theorem cleanupAbsorbedAt_disjoint_of_ne
    {V ι : Type*} [Fintype V]
    {G : SimpleGraph V} {B : ι → Finset V} {L : Finset V}
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M) {i j : ι} (hij : i ≠ j) :
    Disjoint (cleanupAbsorbedAt M i) (cleanupAbsorbedAt M j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rcases Finset.mem_biUnion.mp hvi with ⟨c, hc, hvc⟩
  rcases Finset.mem_biUnion.mp hvj with ⟨d, hd, hvd⟩
  have hcM := (Finset.mem_filter.mp hc).1
  have hdM := (Finset.mem_filter.mp hd).1
  have hci := (Finset.mem_filter.mp hc).2
  have hdj := (Finset.mem_filter.mp hd).2
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hij (hci.symm.trans hdj)
  exact Finset.disjoint_left.mp (hM.2.1 hcM hdM hcd) hvc hvd

/-- Source-faithful cleanup output.  Every enlarged block stays below `k`,
at least seven eighths of the target scale remain as unused attachments,
and the final remainder has no length-at-most-two path with two distinct
unused attachments in one block. -/
theorem exists_KLS_cleanup
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : ι → Finset V) (L : Finset V) {k : ℕ} (hk : 1000 ≤ k)
    (hBne : ∀ i, (B i).Nonempty)
    (hBL : ∀ i, Disjoint (B i) L)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hdeg : ∀ i, ∀ v ∈ B i,
      123 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (hcycle : ¬ cycleGraph k ⊑ G) :
    ∃ M : Finset (CleanupMove ι V),
      IsCleanupFamily G B L M ∧
      let A : ι → Finset V := fun i =>
        B i \ cleanupAttachmentsAt M i
      let R : Finset V := L \ cleanupAbsorbed M
      (∀ i, (B i).card + (cleanupAbsorbedAt M i).card < k) ∧
      (∀ i, 7 * k ≤ 8 * (A i).card) ∧
      ∀ i, ∀ a ∈ A i, ∀ b ∈ A i, a ≠ b →
        ∀ x y : V, ∀ p : G.Walk x y,
          p.IsPath → p.length ≤ 2 →
          (∀ v ∈ p.support, v ∈ R) →
          G.Adj a x → G.Adj y b → False := by
  classical
  obtain ⟨M, hM, hmax⟩ := exists_maximal_cleanupFamily G B L
  refine ⟨M, hM, ?_⟩
  let AF : ∀ i, ShortAbsorbableFamily (J := CleanupFiber M i) G (B i) :=
    fun i => hM.absorbableFamilyAt hBL i
  let A : ι → Finset V := fun i => B i \ cleanupAttachmentsAt M i
  let R : Finset V := L \ cleanupAbsorbed M
  have hroom : ∀ i, 10 * (k - (B i).card + 2) + 2 ≤ (B i).card := by
    intro i
    obtain ⟨v, hv⟩ := hBne i
    have hstrong := hdeg i v hv
    have hupper := degreeIn_le_card_pred_of_mem G (B i) hv
    omega
  have htotal : ∀ i, (B i).card + (cleanupAbsorbedAt M i).card < k := by
    intro i
    by_contra hnot
    apply hcycle
    apply (AF i).cycleGraph_isContained_of_total_ge hk (hBcard i)
    · rw [hM.absorbableFamilyAt_vertices hBL i]
      omega
    · exact hroom i
    · exact hdeg i
  have havailable : ∀ i, 7 * k ≤ 8 * (A i).card := by
    intro i
    have hattEq := hM.absorbableFamilyAt_attachments hBL i
    have hAeq : A i = (AF i).remaining := by
      simp [A, AF, ShortAbsorbableFamily.remaining, hattEq]
    have hvertices : (AF i).vertices.card = (cleanupAbsorbedAt M i).card := by
      rw [hM.absorbableFamilyAt_vertices hBL i]
    have hindex := (AF i).index_card_le_vertices_card
    have hrem := (AF i).card_remaining
    have habs := htotal i
    obtain ⟨v, hv⟩ := hBne i
    have hstrong := hdeg i v hv
    have hupper := degreeIn_le_card_pred_of_mem G (B i) hv
    rw [hAeq]
    rw [hrem]
    omega
  refine ⟨htotal, havailable, ?_⟩
  intro i a ha b hb hab x y p hp hplen hpR hax hyb
  have hattEq := hM.absorbableFamilyAt_attachments hBL i
  let c : CleanupMove ι V :=
    { block := i
      attach₀ := a
      attach₁ := b
      support := p.support.toFinset }
  have hcValid : ValidCleanupMove G B L c := by
    refine ⟨?_, ?_, hab, ?_, ?_, x, ?_, y, ?_, p, hp, hplen, rfl, hax, hyb⟩
    · exact (Finset.mem_sdiff.mp ha).1
    · exact (Finset.mem_sdiff.mp hb).1
    · exact ⟨x, by simp [c]⟩
    · intro v hv
      exact (Finset.mem_sdiff.mp (hpR v (List.mem_toFinset.mp hv))).1
    · simp [c]
    · simp [c]
  have hsupportFresh : Disjoint c.support (cleanupAbsorbed M) := by
    rw [Finset.disjoint_left]
    intro v hv hvc
    have hvR := hpR v (List.mem_toFinset.mp (by simpa [c] using hv))
    exact (Finset.mem_sdiff.mp hvR).2 hvc
  have hattachFresh : ∀ t : Fin 2,
      c.attach t ∉ cleanupAttachmentsAt M c.block := by
    intro t
    fin_cases t
    · simpa [c, CleanupMove.attach, ← hattEq] using (Finset.mem_sdiff.mp ha).2
    · simpa [c, CleanupMove.attach, ← hattEq] using (Finset.mem_sdiff.mp hb).2
  exact no_fresh_validCleanupMove_of_maximal hM hmax
    ⟨c, hcValid, hsupportFresh, hattachFresh⟩

/-! ## Diameter-two partition of the cleaned remainder -/

structure StarMove (V : Type*) where
  center : V
  support : Finset V
  deriving DecidableEq, Fintype

def ValidStarMove
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) (m : ℕ) (c : StarMove V) : Prop :=
  c.center ∈ c.support ∧ c.support ⊆ R ∧ c.support.card = m ∧
    ∀ v ∈ c.support, v ≠ c.center → G.Adj c.center v

def IsStarPacking
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) (m : ℕ) (P : Finset (StarMove V)) : Prop :=
  (∀ c ∈ P, ValidStarMove G R m c) ∧
    ((P : Set (StarMove V)).PairwiseDisjoint StarMove.support)

noncomputable def starCovered
    {V : Type*} [Fintype V] (P : Finset (StarMove V)) : Finset V :=
  P.biUnion StarMove.support

theorem exists_maximal_starPacking
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) (m : ℕ) :
    ∃ P : Finset (StarMove V), IsStarPacking G R m P ∧
      ∀ c : StarMove V, IsStarPacking G R m (insert c P) → c ∈ P := by
  classical
  let Families : Finset (Finset (StarMove V)) :=
    Finset.univ.filter fun P => IsStarPacking G R m P
  have hFamilies : Families.Nonempty := by
    refine ⟨∅, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [IsStarPacking, Function.onFun]
  obtain ⟨P, hPFamily, hmax⟩ := Finset.exists_max_image Families
    (fun Q => (starCovered Q).card) hFamilies
  have hP : IsStarPacking G R m P := (Finset.mem_filter.mp hPFamily).2
  refine ⟨P, hP, ?_⟩
  intro c hc
  by_contra hcP
  have hins : insert c P ∈ Families :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hle := hmax (insert c P) hins
  have hnonempty : c.support.Nonempty := by
    exact ⟨c.center, (hc.1 c (by simp)).1⟩
  have hdisj : Disjoint c.support (starCovered P) := by
    rw [Finset.disjoint_left]
    intro v hvc hvP
    rcases Finset.mem_biUnion.mp hvP with ⟨d, hdP, hvd⟩
    have hcd : c ≠ d := by intro h; subst d; exact hcP hdP
    exact (Finset.disjoint_left.mp
      (hc.2 (by simp) (by exact Finset.mem_insert_of_mem hdP) hcd)) hvc hvd
  have hscore : (starCovered (insert c P)).card =
      c.support.card + (starCovered P).card := by
    rw [starCovered, Finset.biUnion_insert]
    apply Finset.card_union_of_disjoint
    simpa [starCovered] using hdisj
  rw [hscore] at hle
  have hpos := Finset.card_pos.mpr hnonempty
  omega

theorem IsStarPacking.insert_of_fresh
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P) (c : StarMove V)
    (hc : ValidStarMove G R m c)
    (hfresh : Disjoint c.support (starCovered P)) :
    IsStarPacking G R m (insert c P) := by
  classical
  refine ⟨?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hc
    · exact hP.1 d hd
  · intro d hd e he hde
    simp only [Set.mem_insert_iff, Finset.coe_insert] at hd he
    rcases hd with rfl | hd <;> rcases he with rfl | he
    · exact (hde rfl).elim
    · apply hfresh.mono_right
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
    · exact (hfresh.mono_right fun v hv =>
        Finset.mem_biUnion.mpr ⟨d, hd, hv⟩).symm
    · exact hP.2 hd he hde

/-- After a maximal packing of `m`-vertex stars, every vertex in the
uncovered remainder has fewer than `m-1` neighbours there. -/
theorem degreeIn_starRemainder_lt
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V} {m : ℕ} (hm : 2 ≤ m)
    {P : Finset (StarMove V)} (hP : IsStarPacking G R m P)
    (hmax : ∀ c : StarMove V,
      IsStarPacking G R m (insert c P) → c ∈ P)
    {v : V} (hv : v ∈ R \ starCovered P) :
    degreeIn G (R \ starCovered P) v < m - 1 := by
  classical
  by_contra hnot
  let N : Finset V := (R \ starCovered P).filter fun w => G.Adj v w
  have hNm : m - 1 ≤ N.card := by simpa [N, degreeIn] using (by omega : m - 1 ≤ degreeIn G (R \ starCovered P) v)
  obtain ⟨T, hTN, hTcard⟩ := Finset.exists_subset_card_eq (s := N) hNm
  have hvT : v ∉ T := by
    intro hvT
    have hvN := hTN hvT
    exact G.loopless.irrefl v (Finset.mem_filter.mp hvN).2
  let c : StarMove V := { center := v, support := insert v T }
  have hcValid : ValidStarMove G R m c := by
    refine ⟨by simp [c], ?_, ?_, ?_⟩
    · intro x hx
      simp only [c, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact (Finset.mem_sdiff.mp hv).1
      · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hTN hx)).1).1
    · rw [show c.support = insert v T by rfl,
        Finset.card_insert_of_notMem hvT, hTcard]
      omega
    · intro x hx hxv
      simp only [c, Finset.mem_insert] at hx
      exact (Finset.mem_filter.mp (hTN (hx.resolve_left hxv))).2
  have hfresh : Disjoint c.support (starCovered P) := by
    rw [Finset.disjoint_left]
    intro x hx hxP
    simp only [c, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (Finset.mem_sdiff.mp hv).2 hxP
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hTN hx)).1).2 hxP
  have hcP := hmax c (hP.insert_of_fresh c hcValid hfresh)
  have hsub : c.support ⊆ starCovered P := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨c, hcP, hx⟩
  have hvc : v ∈ c.support := by simp [c]
  exact (Finset.disjoint_left.mp hfresh) hvc (hsub hvc)

/-- The finite index type consisting of the packed stars and the uncovered
vertices, the latter regarded as singleton parts. -/
abbrev StarPartIndex
    {V : Type*} [Fintype V] (P : Finset (StarMove V)) (R : Finset V) :=
  {c // c ∈ P} ⊕ {v // v ∈ R \ starCovered P}

/-- The part represented by a packed star or an uncovered singleton. -/
def starPart
    {V : Type*} [Fintype V] (P : Finset (StarMove V)) (R : Finset V) :
    StarPartIndex P R → Finset V
  | Sum.inl c => c.1.support
  | Sum.inr v => {v.1}

theorem starCovered_subset
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P) :
    starCovered P ⊆ R := by
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨c, hcP, hvc⟩
  exact (hP.1 c hcP).2.1 hvc

theorem starCovered_card_eq
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P) :
    (starCovered P).card = P.card * m := by
  classical
  rw [starCovered, Finset.card_biUnion hP.2]
  calc
    ∑ c ∈ P, c.support.card = ∑ _c ∈ P, m := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (hP.1 c hc).2.2.1
    _ = P.card * m := by simp

theorem starPart_nonempty
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} (hm : 1 ≤ m)
    {P : Finset (StarMove V)} (hP : IsStarPacking G R m P)
    (i : StarPartIndex P R) : (starPart P R i).Nonempty := by
  rcases i with c | v
  · have hcard := (hP.1 c.1 c.2).2.2.1
    apply Finset.card_pos.mp
    change 0 < c.1.support.card
    rw [hcard]
    exact hm
  · exact ⟨v.1, by simp [starPart]⟩

theorem starPart_subset
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P)
    (i : StarPartIndex P R) : starPart P R i ⊆ R := by
  rcases i with c | v
  · exact (hP.1 c.1 c.2).2.1
  · intro x hx
    have hxv : x = v.1 := by simpa [starPart] using hx
    subst x
    exact (Finset.mem_sdiff.mp v.2).1

theorem starPart_pairwise_disjoint
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P) :
    ∀ i j : StarPartIndex P R, i ≠ j →
      Disjoint (starPart P R i) (starPart P R j) := by
  classical
  intro i j hij
  rcases i with c | v <;> rcases j with d | w
  · apply hP.2 c.2 d.2
    intro hcd
    apply hij
    exact congrArg Sum.inl (Subtype.ext hcd)
  · change Disjoint c.1.support {w.1}
    rw [Finset.disjoint_singleton_right]
    intro hwc
    exact (Finset.mem_sdiff.mp w.2).2
      (Finset.mem_biUnion.mpr ⟨c.1, c.2, hwc⟩)
  · change Disjoint {v.1} d.1.support
    rw [Finset.disjoint_singleton_left]
    intro hvc
    exact (Finset.mem_sdiff.mp v.2).2
      (Finset.mem_biUnion.mpr ⟨d.1, d.2, hvc⟩)
  · change Disjoint {v.1} {w.1}
    rw [Finset.disjoint_singleton]
    intro hvw
    apply hij
    apply congrArg Sum.inr
    exact Subtype.ext hvw

theorem exists_starPart_of_mem
    {V : Type*} [Fintype V] {P : Finset (StarMove V)}
    {R : Finset V} {v : V} (hv : v ∈ R) :
    ∃ i : StarPartIndex P R, v ∈ starPart P R i := by
  classical
  by_cases hvC : v ∈ starCovered P
  · rcases Finset.mem_biUnion.mp hvC with ⟨c, hcP, hvc⟩
    exact ⟨Sum.inl ⟨c, hcP⟩, hvc⟩
  · exact ⟨Sum.inr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvC⟩⟩, by simp [starPart]⟩

/-- Every packed star, and every uncovered singleton, has ambient diameter
at most two in the strong form needed by cleanup: the witnessing simple path
stays wholly inside the part. -/
theorem exists_short_path_in_starPart
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : Finset V} {m : ℕ} {P : Finset (StarMove V)}
    (hP : IsStarPacking G R m P)
    (i : StarPartIndex P R) {x y : V}
    (hx : x ∈ starPart P R i) (hy : y ∈ starPart P R i) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 2 ∧
      ∀ z ∈ p.support, z ∈ starPart P R i := by
  classical
  rcases i with c | v
  · let o : V := c.1.center
    have hc := hP.1 c.1 c.2
    by_cases hxy : x = y
    · subst y
      refine ⟨SimpleGraph.Walk.nil, by simp, by simp, ?_⟩
      intro z hz
      simpa [starPart] using (show z = x by simpa using hz) ▸ hx
    by_cases hxo : x = o
    · subst x
      have hoy : G.Adj o y := hc.2.2.2 y hy (Ne.symm hxy)
      let p : G.Walk o y := SimpleGraph.Walk.cons hoy SimpleGraph.Walk.nil
      refine ⟨p, ?_, by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxy]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl
        · exact hc.1
        · exact hy
    by_cases hyo : y = o
    · subst y
      have hox : G.Adj o x := hc.2.2.2 x hx hxo
      let p : G.Walk x o := SimpleGraph.Walk.cons hox.symm SimpleGraph.Walk.nil
      refine ⟨p, ?_, by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxo]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hc.1
    · have hox : G.Adj o x := hc.2.2.2 x hx hxo
      have hoy : G.Adj o y := hc.2.2.2 y hy hyo
      have hoyne : o ≠ y := Ne.symm hyo
      let p : G.Walk x y := SimpleGraph.Walk.cons hox.symm
        (SimpleGraph.Walk.cons hoy SimpleGraph.Walk.nil)
      refine ⟨p, ?_, by simp [p], ?_⟩
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, hxo, hoyne, hxy]
      · intro z hz
        simp [p] at hz
        rcases hz with rfl | rfl | rfl
        · exact hx
        · exact hc.1
        · exact hy
  · have hxv : x = v.1 := by simpa [starPart] using hx
    have hyv : y = v.1 := by simpa [starPart] using hy
    subst x
    subst y
    refine ⟨SimpleGraph.Walk.nil, by simp, by simp, ?_⟩
    intro z hz
    have hzv : z = v.1 := Walk.mem_support_nil_iff.mp hz
    simpa [starPart, hzv]

/-- Quantitative KLS diameter-two partition.  Its number of parts is bounded
without division: multiplying by the star size costs at most the original
remainder plus the low-degree independent-set error. -/
theorem exists_diameterTwo_starPartition
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V} {m n : ℕ} (hm : 2 ≤ m)
    (hfree : G.IndepSetFree n) :
    ∃ P : Finset (StarMove V), IsStarPacking G R m P ∧
      (∀ i j : StarPartIndex P R, i ≠ j →
        Disjoint (starPart P R i) (starPart P R j)) ∧
      (∀ i : StarPartIndex P R, (starPart P R i).Nonempty) ∧
      (∀ i : StarPartIndex P R, starPart P R i ⊆ R) ∧
      (∀ v ∈ R, ∃ i : StarPartIndex P R, v ∈ starPart P R i) ∧
      (∀ i : StarPartIndex P R, ∀ x ∈ starPart P R i,
        ∀ y ∈ starPart P R i,
          ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 2 ∧
            ∀ z ∈ p.support, z ∈ starPart P R i) ∧
      m * Fintype.card (StarPartIndex P R) ≤
        R.card + m * ((n - 1) * (m - 1)) := by
  classical
  obtain ⟨P, hP, hmax⟩ := exists_maximal_starPacking G R m
  let Rem : Finset V := R \ starCovered P
  let H : SimpleGraph Rem := G.induce (Rem : Set V)
  have hHdeg : ∀ v : Rem, H.degree v ≤ m - 2 := by
    intro v
    have hlt := degreeIn_starRemainder_lt G hm hP hmax v.2
    change degreeIn G Rem v < m - 1 at hlt
    have heq : H.degree v = degreeIn G Rem v := by
      simpa [H, Rem] using degree_induce_finset_eq_degreeIn G Rem v
    rw [heq]
    omega
  obtain ⟨S, hSind, hScard⟩ :=
    exists_indepSet_card_mul_succ_ge_of_degree_le H hHdeg
  let e : Rem ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let T : Finset V := S.map e
  have hTcard : T.card = S.card := by simp [T]
  have hTind : G.IsIndepSet (T : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    rcases Finset.mem_map.mp hx with ⟨x', hxS, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hyS, rfl⟩
    have hne : x' ≠ y' := by
      intro h
      apply hxy
      exact congrArg Subtype.val h
    have hnot := (H.isIndepSet_iff.mp hSind) hxS hyS hne
    simpa [H, e] using hnot
  have hSlt : S.card < n := by
    rw [← hTcard]
    exact Erdos551.IndepSetFree.card_lt hfree hTind
  have hRemBound : Rem.card ≤ (n - 1) * (m - 1) := by
    have hsimp : (m - 2) + 1 = m - 1 := by omega
    have hbase : Rem.card ≤ S.card * (m - 1) := by
      simpa [H, hsimp] using hScard
    calc
      Rem.card ≤ S.card * (m - 1) := hbase
      _ ≤ (n - 1) * (m - 1) := by
        gcongr
        omega
  have hcovered : (starCovered P).card = P.card * m :=
    starCovered_card_eq hP
  have hcoveredLe : (starCovered P).card ≤ R.card :=
    Finset.card_le_card (starCovered_subset hP)
  have hindex : Fintype.card (StarPartIndex P R) = P.card + Rem.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  refine ⟨P, hP, starPart_pairwise_disjoint hP,
    fun i => starPart_nonempty (by omega) hP i,
    starPart_subset hP, ?_, ?_, ?_⟩
  · intro v hv
    exact exists_starPart_of_mem hv
  · intro i x hx y hy
    exact exists_short_path_in_starPart hP i hx hy
  · rw [hindex]
    calc
      m * (P.card + Rem.card) = (starCovered P).card + m * Rem.card := by
        rw [Nat.mul_add, hcovered, Nat.mul_comm m P.card]
      _ ≤ R.card + m * ((n - 1) * (m - 1)) := by
        exact Nat.add_le_add hcoveredLe (Nat.mul_le_mul_left m hRemBound)

/-! ## Injectively counted bipartite incidence graphs -/

/-- Two private endpoint vertices for every member of a finite edge-index
type.  They let us reuse the selected-cross-edge infrastructure purely as
an injective edge counter. -/
abbrev IncidenceEndpoint (D : Type*) := D × Fin 2

def incidenceSelectedRecord
    {D ι κ : Type*} (label : D ↪ (ι × κ)) (d : D) :
    SelectedCrossEdge (IncidenceEndpoint D) (ι ⊕ κ) :=
  ((Sum.inl (label d).1, Sum.inr (label d).2), ((d, 0), (d, 1)))

theorem incidenceSelectedRecord_injective
    {D ι κ : Type*} (label : D ↪ (ι × κ)) :
    Function.Injective (incidenceSelectedRecord label) := by
  intro d e h
  exact congrArg (fun r => r.2.1.1) h

def incidenceSelectedSystem
    {D ι κ : Type*} [Fintype D]
    (label : D ↪ (ι × κ)) :
    Finset (SelectedCrossEdge (IncidenceEndpoint D) (ι ⊕ κ)) :=
  Finset.univ.map ⟨incidenceSelectedRecord label,
    incidenceSelectedRecord_injective label⟩

/-- The dummy selected system really is valid.  Its unordered label pairs
are unique because every pair has one left and one right endpoint and the
displayed label map is injective. -/
theorem incidenceSelectedSystem_valid
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) :
    IsSelectedCrossEdgeSystem
      (⊤ : SimpleGraph (IncidenceEndpoint D))
      (fun _ : ι ⊕ κ => (Finset.univ : Finset (IncidenceEndpoint D)))
      (incidenceSelectedSystem label) := by
  classical
  let E : D ↪
      SelectedCrossEdge (IncidenceEndpoint D) (ι ⊕ κ) :=
    ⟨incidenceSelectedRecord label, incidenceSelectedRecord_injective label⟩
  constructor
  · intro r hr
    rcases Finset.mem_map.mp hr with ⟨d, _hd, rfl⟩
    refine ⟨by simp [incidenceSelectedRecord], by simp,
      by simp, ?_⟩
    simp [incidenceSelectedRecord]
  constructor
  · intro r hr s hs hrs
    rcases Finset.mem_map.mp hr with ⟨d, _hd, rfl⟩
    rcases Finset.mem_map.mp hs with ⟨e, _he, rfl⟩
    have hde : d ≠ e := by
      intro h
      exact hrs (congrArg E h)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hde (congrArg Prod.fst h)
    · intro h
      exact hde (congrArg Prod.fst h)
    · intro h
      exact hde (congrArg Prod.fst h)
    · intro h
      exact hde (congrArg Prod.fst h)
  · intro r hr s hs hpairs
    rcases Finset.mem_map.mp hr with ⟨d, _hd, rfl⟩
    rcases Finset.mem_map.mp hs with ⟨e, _he, rfl⟩
    apply congrArg E
    apply label.injective
    rcases Sym2.eq_iff.mp hpairs with hdir | hrev
    · apply Prod.ext
      · exact Sum.inl.inj hdir.1
      · exact Sum.inr.inj hdir.2
    · cases hrev.1

theorem incidenceSelectedSystem_card
    {D ι κ : Type*} [Fintype D]
    (label : D ↪ (ι × κ)) :
    (incidenceSelectedSystem label).card = Fintype.card D := by
  classical
  simp [incidenceSelectedSystem]

theorem finCyclicSucc_injective551 {q : ℕ} (hq : 0 < q) :
    Function.Injective (finCyclicSucc hq) := by
  intro i j hij
  have h := congrArg (finCyclicPred hq) hij
  simpa only [finCyclicPred_finCyclicSucc] using h

theorem finCyclicSucc_ne_self551 {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finCyclicSucc (by omega) i ≠ i := by
  intro hi
  have hval := congrArg Fin.val hi
  simp only [finCyclicSucc] at hval
  by_cases hlt : i.val + 1 < q
  · rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  · have heq : i.val + 1 = q := by omega
    rw [heq, Nat.mod_self] at hval
    omega

/-- Every finite injectively labelled bipartite incidence family therefore
produces a graph with exactly one edge per label. -/
theorem exists_bipartite_incidence_graph
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) :
    ∃ H : SimpleGraph (ι ⊕ κ),
      H.IsBipartite ∧ H.edgeFinset.card = Fintype.card D := by
  classical
  let M := incidenceSelectedSystem label
  let H : SimpleGraph (ι ⊕ κ) := SelectedCrossEdgeGraph M
  have hM := incidenceSelectedSystem_valid label
  refine ⟨H, ?_, ?_⟩
  · have hb : H.IsBipartiteWith
        (Set.range (Sum.inl : ι → ι ⊕ κ))
        (Set.range (Sum.inr : κ → ι ⊕ κ)) := by
      refine ⟨?_, ?_⟩
      · rw [Set.disjoint_left]
        rintro x ⟨i, rfl⟩ ⟨j, h⟩
        simp at h
      · intro x y hxy
        change (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj x y at hxy
        rw [SelectedCrossEdgeGraph, SimpleGraph.fromRel_adj] at hxy
        rcases hxy.2 with hxy | hxy
        · rcases hxy with ⟨e, he, hdir | hrev⟩
          · rcases Finset.mem_map.mp he with ⟨d, _hd, rfl⟩
            left
            rw [← hdir.1, ← hdir.2]
            simp [incidenceSelectedRecord]
          · rcases Finset.mem_map.mp he with ⟨d, _hd, rfl⟩
            right
            rw [← hrev.1, ← hrev.2]
            simp [incidenceSelectedRecord]
        · rcases hxy with ⟨e, he, hrev | hdir⟩
          · rcases Finset.mem_map.mp he with ⟨d, _hd, rfl⟩
            right
            rw [← hrev.1, ← hrev.2]
            simp [incidenceSelectedRecord]
          · rcases Finset.mem_map.mp he with ⟨d, _hd, rfl⟩
            left
            rw [← hdir.1, ← hdir.2]
            simp [incidenceSelectedRecord]
    exact hb.isBipartite
  · rw [show H.edgeFinset.card = M.card by
      exact card_edgeFinset_selectedCrossEdgeGraph hM]
    exact incidenceSelectedSystem_card label

/-- A cyclic family of short, mutually disjoint handles through the cleaned
remainder closes to an exact `k`-cycle through distinct dense blocks.  The
internal lengths are allocated between five and `k/2`; a parity-breaking
edge in every dense block supplies both parities. -/
theorem cycleGraph_isContained_of_dense_blocks_and_bounded_handles
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {q k H : ℕ} (hq : 2 ≤ q) (hk : 9 * q ≤ k)
    (hklarge : 1000 ≤ k) (hroom : (5 + H) * q ≤ k)
    (B : Fin q → Finset V)
    (hBne : ∀ i, (B i).Nonempty)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBdeg : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (x y : Fin q → V)
    (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hx : ∀ i, x i ∈ B i)
    (hy : ∀ i, y i ∈ B (finCyclicSucc (by omega : 0 < q) i))
    (hxy : ∀ i,
      y (finCyclicPred (by omega : 0 < q) i) ≠ x i)
    (hhPath : ∀ i, (h i).IsPath)
    (hhLower : ∀ i, 2 ≤ (h i).length)
    (hhUpper : ∀ i, (h i).length ≤ H)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (hhBlocks : ∀ i e z, z ∈ (h i).support → z ∈ B e →
      (e = i ∧ z = x i) ∨
        (e = finCyclicSucc (by omega : 0 < q) i ∧ z = y i)) :
    cycleGraph k ⊑ G := by
  classical
  let pred : Fin q → Fin q := finCyclicPred (by omega)
  let next : Fin q → Fin q := finCyclicSucc (by omega)
  let S : ℕ := ∑ i : Fin q, (h i).length
  have hSlo : 2 * q ≤ S := by
    calc
      2 * q = ∑ _i : Fin q, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin q, (h i).length := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hhLower i
  have hShi : S ≤ H * q := by
    calc
      S ≤ ∑ _i : Fin q, H := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hhUpper i
      _ = H * q := by simp [Nat.mul_comm]
  have hSk : S ≤ k := by
    calc
      S ≤ H * q := hShi
      _ ≤ (5 + H) * q := by gcongr; omega
      _ ≤ k := hroom
  have hlo : (∑ _i : Fin q, 5) ≤ k - S := by
    have hsum : 5 * q + S ≤ k := by
      calc
        5 * q + S ≤ 5 * q + H * q := Nat.add_le_add_left hShi _
        _ = (5 + H) * q := by ring
        _ ≤ k := hroom
    have hfive : 5 * q ≤ k - S := Nat.le_sub_of_add_le hsum
    simpa [Nat.mul_comm] using hfive
  have hhi : k - S ≤ ∑ _i : Fin q, k / 2 := by
    have htwo : k - S ≤ 2 * (k / 2) := by omega
    calc
      k - S ≤ 2 * (k / 2) := htwo
      _ ≤ q * (k / 2) := Nat.mul_le_mul_right (k / 2) hq
      _ = ∑ _i : Fin q, k / 2 := by simp
  obtain ⟨ell, hellsum, hell⟩ :=
    exists_fintype_weights_sum_eq_between
      (fun _i : Fin q => 5) (fun _i : Fin q => k / 2)
      (fun _i => by omega) hlo hhi
  have hcap : ∀ i, k / 2 + 5 ≤ (B i).card ∧
      k / 2 + 5 ≤ 57 * (k - 1) / 64 := by
    intro i
    exact dense_block_balanced_routing_capacities G hklarge
      (hBne i) (hBdeg i)
  have hmatch : ∀ i, HasThreeDisjointAdjPairFamily G (B i) := by
    intro i
    exact hasThreeDisjointAdjPairFamily_of_scaled_internal_degree
      G (by omega) (hBne i) (hBdeg i)
  have hrob : ∀ i,
      RobustPairSet G (B i) (B i) (57 * (k - 1) / 64) := by
    intro i
    exact robustPairSet_of_scaled_internal_degree G (hBcard i) (hBdeg i)
  have hendIn : ∀ i, y (pred i) ∈ B i := by
    intro i
    have hpnext : next (pred i) = i :=
      finCyclicSucc_finCyclicPred (by omega) i
    simpa [pred, next, hpnext] using hy (pred i)
  have hexistsRoute : ∀ i : Fin q,
      ∃ r : G.Walk (y (pred i)) (x i),
        r.IsPath ∧ r.length = ell i ∧
          ∀ z ∈ r.support, z ∈ B i := by
    intro i
    obtain ⟨M, hM, hMcard, hMB⟩ := hmatch i
    let F : Finset V := {y (pred i), x i}
    have hFcard : F.card < M.card := by
      have hFtwo : F.card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨e, heM, he₁F, he₂F, heAdj⟩ :=
      exists_adjPair_avoiding_of_disjointAdjPairFamily G M F hM hFcard
    have heB := hMB e heM
    have he₁neIn : y (pred i) ≠ e.1 := by
      intro heq
      exact he₁F (by simp [F, heq])
    have he₂neIn : y (pred i) ≠ e.2 := by
      intro heq
      exact he₂F (by simp [F, heq])
    have he₁neOut : e.1 ≠ x i := by
      intro heq
      exact he₁F (by simp [F, heq])
    have he₂neOut : e.2 ≠ x i := by
      intro heq
      exact he₂F (by simp [F, heq])
    obtain ⟨r, hr, hrlen, hrloc⟩ :=
      exists_path_between_of_robustPairSet_and_parity_edge G (hrob i)
        (hendIn i) heB.1 heB.2 (hx i) heAdj
        he₁neIn he₂neIn (hxy i) he₁neOut he₂neOut
        (hell i).1
        ((hell i).2.trans (by
          have hi := (hcap i).1
          omega : k / 2 ≤ (B i).card))
        ((Nat.add_le_add_right (hell i).2 1).trans (by
          have := (hcap i).2
          omega))
    exact ⟨r, hr, hrlen, fun z hz => (hrloc z hz).elim id id⟩
  choose route hroutePath hrouteLen hrouteLoc using hexistsRoute
  have hrouteDisj : ∀ i j, i ≠ j →
      (route i).support.Disjoint (route j).support := by
    intro i j hij z hzi hzj
    exact Finset.disjoint_left.mp (hBdisj i j hij)
      (hrouteLoc i z hzi) (hrouteLoc j z hzj)
  have hrouteExternal : ∀ i e z, z ∈ (route i).support →
      z ∈ (h e).support →
      (e = pred i ∧ z = y e) ∨ (e = i ∧ z = x e) := by
    intro i e z hzR hzH
    rcases hhBlocks e i z hzH (hrouteLoc i z hzR) with hout | hin
    · exact Or.inr ⟨hout.1.symm, hout.2⟩
    · left
      have hpred : pred i = e := by
        exact finCyclicSucc_injective551 (by omega) (by
          simpa [pred, next, hin.1] using
            (finCyclicSucc_finCyclicPred (by omega) i))
      exact ⟨hpred.symm, hin.2⟩
  have htailSum :
      (∑ i : Fin q, (h (pred i)).tail.length) + q = S := by
    calc
      (∑ i : Fin q, (h (pred i)).tail.length) + q =
          ∑ i : Fin q, ((h (pred i)).tail.length + 1) := by
            simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin q, (h (pred i)).length := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (h (pred i)).length_tail_add_one (by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          exact (hhLower (pred i)).trans' (by omega))
      _ = S := by
        let ep : Fin q ≃ Fin q :=
          Equiv.ofBijective pred ⟨finCyclicPred_injective (by omega), by
            intro e
            exact ⟨next e, finCyclicPred_finCyclicSucc (by omega) e⟩⟩
        have hsum := ep.sum_comp (fun e : Fin q => (h e).length)
        change (∑ i : Fin q, (h (pred i)).length) =
          ∑ e : Fin q, (h e).length at hsum
        simpa [S] using hsum
  have htotal :
      (∑ i : Fin q, ((h (pred i)).tail.append (route i)).length) + q = k := by
    simp_rw [SimpleGraph.Walk.length_append]
    rw [Finset.sum_add_distrib]
    have hrouteSum : (∑ i : Fin q, (route i).length) = k - S := by
      simpa only [hrouteLen] using hellsum
    omega
  apply cycleGraph_isContained_of_disjoint_path_handles_and_internal_routes_val
    G hq (by omega) x y h hhPath (fun i => (hhLower i).trans' (by omega))
      hhDisj route hroutePath hrouteDisj
      (by simpa [pred] using hrouteExternal)
  · have heq :
        (∑ i : Fin q, ((h (pred i)).tail.append (route i)).length) +
            (q - 1) = k - 1 := by omega
    rw [heq]
    omega
  · simpa [pred] using htotal

/-- The four-edge version used by the cleanup and remainder-incidence
arguments.  Keeping this wrapper records the original sharp accounting while
the bounded form above is also available for the final absorption step. -/
theorem cycleGraph_isContained_of_dense_blocks_and_short_handles
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {q k : ℕ} (hq : 2 ≤ q) (hk : 9 * q ≤ k) (hklarge : 1000 ≤ k)
    (B : Fin q → Finset V)
    (hBne : ∀ i, (B i).Nonempty)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBdeg : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (x y : Fin q → V)
    (h : ∀ i : Fin q, G.Walk (x i) (y i))
    (hx : ∀ i, x i ∈ B i)
    (hy : ∀ i, y i ∈ B (finCyclicSucc (by omega : 0 < q) i))
    (hxy : ∀ i,
      y (finCyclicPred (by omega : 0 < q) i) ≠ x i)
    (hhPath : ∀ i, (h i).IsPath)
    (hhLower : ∀ i, 2 ≤ (h i).length)
    (hhUpper : ∀ i, (h i).length ≤ 4)
    (hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support)
    (hhBlocks : ∀ i e z, z ∈ (h i).support → z ∈ B e →
      (e = i ∧ z = x i) ∨
        (e = finCyclicSucc (by omega : 0 < q) i ∧ z = y i)) :
    cycleGraph k ⊑ G := by
  classical
  exact cycleGraph_isContained_of_dense_blocks_and_bounded_handles
    G (H := 4) hq hk hklarge (by simpa using hk)
      B hBne hBcard hBdisj hBdeg x y h hx hy hxy hhPath hhLower hhUpper
      hhDisj hhBlocks

/-! ## Attachment incidence after cleanup -/

noncomputable def remainderAttachments
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (i : ι) : Finset V :=
  (A i).filter fun a => ∃ x ∈ R, G.Adj a x

theorem remainderAttachments_subset
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (i : ι) :
    remainderAttachments G A R i ⊆ A i := by
  classical
  intro a ha
  change a ∈ (A i).filter (fun a => ∃ x ∈ R, G.Adj a x) at ha
  exact Finset.mem_of_mem_filter a ha

noncomputable def remainderAttachmentNeighbor
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (i : ι)
    (a : {a // a ∈ remainderAttachments G A R i}) : V :=
  Classical.choose (Finset.mem_filter.mp a.2).2

theorem remainderAttachmentNeighbor_mem
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (i : ι)
    (a : {a // a ∈ remainderAttachments G A R i}) :
    remainderAttachmentNeighbor G A R i a ∈ R :=
  (Classical.choose_spec (Finset.mem_filter.mp a.2).2).1

theorem remainderAttachment_adj_neighbor
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (i : ι)
    (a : {a // a ∈ remainderAttachments G A R i}) :
    G.Adj a.1 (remainderAttachmentNeighbor G A R i a) :=
  (Classical.choose_spec (Finset.mem_filter.mp a.2).2).2

noncomputable def remainderAttachmentPart
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (P : Finset (StarMove V))
    (i : ι) (a : {a // a ∈ remainderAttachments G A R i}) :
    StarPartIndex P R :=
  Classical.choose
    (exists_starPart_of_mem (P := P)
      (remainderAttachmentNeighbor_mem G A R i a))

theorem remainderAttachmentNeighbor_mem_part
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (P : Finset (StarMove V))
    (i : ι) (a : {a // a ∈ remainderAttachments G A R i}) :
    remainderAttachmentNeighbor G A R i a ∈
      starPart P R (remainderAttachmentPart G A R P i a) :=
  Classical.choose_spec
    (exists_starPart_of_mem (P := P)
      (remainderAttachmentNeighbor_mem G A R i a))

/-- Cleanup makes the attachment-to-part map injective inside every block:
two attachments assigned to one diameter-two part would be a forbidden
augmenting cleanup move. -/
theorem remainderAttachmentPart_injective
    {V ι : Type*} [Fintype V] (G : SimpleGraph V)
    (A : ι → Finset V) (R : Finset V) (P : Finset (StarMove V))
    {m : ℕ} (hP : IsStarPacking G R m P)
    (hclean : ∀ i, ∀ a ∈ A i, ∀ b ∈ A i, a ≠ b →
      ∀ x y : V, ∀ p : G.Walk x y,
        p.IsPath → p.length ≤ 2 →
        (∀ v ∈ p.support, v ∈ R) →
        G.Adj a x → G.Adj y b → False)
    (i : ι) :
    Function.Injective (remainderAttachmentPart G A R P i) := by
  classical
  intro a b habPart
  apply Subtype.ext
  by_contra hab
  let x := remainderAttachmentNeighbor G A R i a
  let y := remainderAttachmentNeighbor G A R i b
  have hxpart := remainderAttachmentNeighbor_mem_part G A R P i a
  have hypart := remainderAttachmentNeighbor_mem_part G A R P i b
  rw [habPart] at hxpart
  obtain ⟨p, hp, hplen, hploc⟩ :=
    exists_short_path_in_starPart hP
      (remainderAttachmentPart G A R P i b) hxpart hypart
  exact hclean i a.1 (Finset.mem_filter.mp a.2).1
    b.1 (Finset.mem_filter.mp b.2).1 hab x y p hp hplen
      (fun v hv => starPart_subset hP _ (hploc v hv))
      (remainderAttachment_adj_neighbor G A R i a)
      (remainderAttachment_adj_neighbor G A R i b).symm

abbrev RemainderAttachmentIndex
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (A : ι → Finset V) (R : Finset V)
    (J : Finset ι) :=
  Σ i : {i // i ∈ J}, {a // a ∈ remainderAttachments G A R i.1}

noncomputable def remainderIncidenceLabel
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (A : ι → Finset V) (R : Finset V)
    (P : Finset (StarMove V)) (J : Finset ι)
    (hinj : ∀ i, Function.Injective
      (remainderAttachmentPart G A R P i)) :
    RemainderAttachmentIndex G A R J ↪
      ({i // i ∈ J} × StarPartIndex P R) where
  toFun d := (d.1, remainderAttachmentPart G A R P d.1.1 d.2)
  inj' := by
    intro d e hde
    rcases d with ⟨i, a⟩
    rcases e with ⟨j, b⟩
    have hij : i = j := congrArg Prod.fst hde
    subst j
    have hab : a = b := hinj i.1 (congrArg Prod.snd hde)
    subst b
    rfl

theorem card_remainderAttachmentIndex
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (A : ι → Finset V) (R : Finset V)
    (J : Finset ι) :
    Fintype.card (RemainderAttachmentIndex G A R J) =
      ∑ i ∈ J, (remainderAttachments G A R i).card := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rw [Finset.univ_eq_attach, ← J.sum_attach]

theorem exists_attachment_of_remainderIncidence_adj
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (A : ι → Finset V) (R : Finset V)
    (P : Finset (StarMove V)) (J : Finset ι)
    (hinj : ∀ i, Function.Injective
      (remainderAttachmentPart G A R P i))
    {i : {i // i ∈ J}} {p : StarPartIndex P R}
    (hadj :
      (SelectedCrossEdgeGraph
        (incidenceSelectedSystem (remainderIncidenceLabel G A R P J hinj))).Adj
          (Sum.inl i) (Sum.inr p)) :
    ∃ a : {a // a ∈ remainderAttachments G A R i.1},
      remainderAttachmentPart G A R P i.1 a = p := by
  classical
  let label := remainderIncidenceLabel G A R P J hinj
  obtain ⟨e, heM, hdir | hrev⟩ :=
    exists_selectedCrossEdge_of_graph_adj hadj
  · rcases Finset.mem_map.mp heM with ⟨d, _hd, rfl⟩
    have hleft : d.1 = i := by
      have hleft' := Sum.inl.inj hdir.1
      change d.1 = i at hleft'
      exact hleft'
    subst i
    refine ⟨d.2, ?_⟩
    have hright := Sum.inr.inj hdir.2
    change remainderAttachmentPart G A R P d.1.1 d.2 = p at hright
    exact hright
  · rcases Finset.mem_map.mp heM with ⟨d, _hd, rfl⟩
    cases hrev.1

/-- Two attachment vertices from different blocks assigned to one
diameter-two part give a simple handle of length between two and four.  Its
only block vertices are its two endpoints and all other vertices lie in the
displayed remainder part. -/
theorem exists_short_handle_through_starPart
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : ι → Finset V) (R : Finset V) (P : Finset (StarMove V))
    {m : ℕ} (hP : IsStarPacking G R m P)
    (hAB : ∀ i, A i ⊆ B i)
    (hBR : ∀ i, Disjoint (B i) R)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    {i j : ι} (hij : i ≠ j)
    (p : StarPartIndex P R)
    (a : {a // a ∈ remainderAttachments G A R i})
    (b : {b // b ∈ remainderAttachments G A R j})
    (hap : remainderAttachmentPart G A R P i a = p)
    (hbp : remainderAttachmentPart G A R P j b = p) :
    ∃ h : G.Walk a.1 b.1,
      h.IsPath ∧ 2 ≤ h.length ∧ h.length ≤ 4 ∧
      (∀ z ∈ h.support,
        z = a.1 ∨ z = b.1 ∨ z ∈ starPart P R p) := by
  classical
  let x := remainderAttachmentNeighbor G A R i a
  let y := remainderAttachmentNeighbor G A R j b
  have hxpart := remainderAttachmentNeighbor_mem_part G A R P i a
  have hypart := remainderAttachmentNeighbor_mem_part G A R P j b
  rw [hap] at hxpart
  rw [hbp] at hypart
  obtain ⟨r, hr, hrlen, hrloc⟩ :=
    exists_short_path_in_starPart hP p hxpart hypart
  have haA : a.1 ∈ A i := remainderAttachments_subset G A R i a.2
  have hbA : b.1 ∈ A j := remainderAttachments_subset G A R j b.2
  have haB : a.1 ∈ B i := hAB i haA
  have hbB : b.1 ∈ B j := hAB j hbA
  have hpartR : starPart P R p ⊆ R := starPart_subset hP p
  have haNotR : a.1 ∉ R := fun haR =>
    Finset.disjoint_left.mp (hBR i) haB haR
  have hbNotR : b.1 ∉ R := fun hbR =>
    Finset.disjoint_left.mp (hBR j) hbB hbR
  have haNotSupp : a.1 ∉ r.support := by
    intro har
    exact haNotR (hpartR (hrloc a.1 har))
  have hbNotSupp : b.1 ∉ r.support := by
    intro hbr
    exact hbNotR (hpartR (hrloc b.1 hbr))
  have hab : a.1 ≠ b.1 := by
    intro hab
    exact Finset.disjoint_left.mp (hBdisj i j hij) haB (hab ▸ hbB)
  let h₀ : G.Walk a.1 y :=
    SimpleGraph.Walk.cons (remainderAttachment_adj_neighbor G A R i a) r
  have hh₀ : h₀.IsPath := hr.cons haNotSupp
  let h : G.Walk a.1 b.1 :=
    h₀.concat (remainderAttachment_adj_neighbor G A R j b).symm
  have hhbNot : b.1 ∉ h₀.support := by
    simp only [h₀, SimpleGraph.Walk.support_cons, List.mem_cons]
    intro hbmem
    rcases hbmem with hba | hbr
    · exact hab hba.symm
    · exact hbNotSupp hbr
  refine ⟨h, hh₀.concat hhbNot _, ?_, ?_, ?_⟩
  · simp [h, h₀]
  · simp [h, h₀]
    omega
  · intro z hz
    simp only [h, SimpleGraph.Walk.support_concat, h₀,
      SimpleGraph.Walk.support_cons, List.mem_append, List.mem_cons,
      List.mem_singleton] at hz
    rcases hz with (rfl | hz) | (rfl | hz)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hrloc z hz))
    · exact Or.inr (Or.inl rfl)
    · simpa using hz

def incidenceSelectedColoring
    {D ι κ : Type*} [Fintype D]
    (label : D ↪ (ι × κ)) :
    (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Coloring Bool :=
  SimpleGraph.Coloring.mk
    (fun x => match x with | Sum.inl _ => false | Sum.inr _ => true) (by
      classical
      intro u v huv
      obtain ⟨e, heM, hdir | hrev⟩ :=
        exists_selectedCrossEdge_of_graph_adj huv
      · rcases Finset.mem_map.mp heM with ⟨d, _hd, rfl⟩
        rw [← hdir.1, ← hdir.2]
        simp [incidenceSelectedRecord]
      · rcases Finset.mem_map.mp heM with ⟨d, _hd, rfl⟩
        rw [← hrev.1, ← hrev.2]
        simp [incidenceSelectedRecord])

@[simp] theorem incidenceSelectedColoring_inl
    {D ι κ : Type*} [Fintype D] (label : D ↪ (ι × κ)) (i : ι) :
    incidenceSelectedColoring label (Sum.inl i) = false := rfl

@[simp] theorem incidenceSelectedColoring_inr
    {D ι κ : Type*} [Fintype D] (label : D ↪ (ι × κ)) (p : κ) :
    incidenceSelectedColoring label (Sum.inr p) = true := rfl

/-- A cycle copied into an injective bipartite incidence graph has even
order.  This is proved directly by applying the explicit two-coloring to
the canonical closed walk around the copied cycle. -/
theorem even_of_cycleGraph_isContained_incidenceSelectedGraph
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) {l : ℕ} (hl : 3 ≤ l)
    (hcopy : cycleGraph l ⊑
      SelectedCrossEdgeGraph (incidenceSelectedSystem label)) :
    Even l := by
  have hn : l - 3 + 3 = l := Nat.sub_add_cancel hl
  have hcopy' : cycleGraph (l - 3 + 3) ⊑
      SelectedCrossEdgeGraph (incidenceSelectedSystem label) := by
    rw [hn]
    exact hcopy
  rcases hcopy' with ⟨c⟩
  let w := cycleGraph.cycle (l - 3)
  let w' := w.map c.toHom
  have heven : Even w'.length :=
    ((incidenceSelectedColoring label).even_length_iff_congr w').2 (by rfl)
  have hwlen : w'.length = l := by
    simp [w', w, cycleGraph.length_cycle, hn]
  simpa [hwlen] using heven

/-- The initial segment `0,1,…,j` is a walk of length `j` in every cycle
graph with at least two vertices. -/
theorem exists_cycleGraph_prefix_walk
    {l j : ℕ} (hl : 2 ≤ l) (hj : j < l) :
    ∃ p : (cycleGraph l).Walk ⟨0, by omega⟩ ⟨j, hj⟩,
      p.length = j := by
  induction j with
  | zero => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ j ih =>
      have hj' : j < l := by omega
      obtain ⟨p, hplen⟩ := ih hj'
      have hadj : (cycleGraph l).Adj ⟨j, hj'⟩ ⟨j + 1, hj⟩ := by
        apply pathGraph_le_cycleGraph
        rw [pathGraph_adj]
        exact Or.inl (by simp)
      refine ⟨p.concat hadj, ?_⟩
      simp [hplen]

/-- Along a copied incidence cycle, positions of even distance from zero
have the same left/right side as zero. -/
theorem incidence_cycle_even_position_same_color
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) {l r : ℕ} (hl : 3 ≤ l)
    (c : (cycleGraph l).Copy
      (SelectedCrossEdgeGraph (incidenceSelectedSystem label)))
    (hr : 2 * r < l) :
    incidenceSelectedColoring label (c ⟨2 * r, hr⟩) =
      incidenceSelectedColoring label (c ⟨0, by omega⟩) := by
  obtain ⟨p, hplen⟩ := exists_cycleGraph_prefix_walk (by omega) hr
  let p' := p.map c.toHom
  have heven : Even p'.length := by
    rw [show p'.length = 2 * r by simp [p', hplen]]
    exact even_two_mul r
  have hiff := ((incidenceSelectedColoring label).even_length_iff_congr p').1 heven
  exact Bool.eq_iff_iff.2 hiff.symm

/-- Positions of odd distance from zero in the same copied incidence cycle
have the opposite left/right color. -/
theorem incidence_cycle_odd_position_ne_color
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) {l r : ℕ} (hl : 3 ≤ l)
    (c : (cycleGraph l).Copy
      (SelectedCrossEdgeGraph (incidenceSelectedSystem label)))
    (hr : 2 * r + 1 < l) :
    incidenceSelectedColoring label (c ⟨2 * r + 1, hr⟩) ≠
      incidenceSelectedColoring label (c ⟨0, by omega⟩) := by
  obtain ⟨p, hplen⟩ := exists_cycleGraph_prefix_walk (by omega) hr
  let p' := p.map c.toHom
  have hodd : Odd p'.length := by
    rw [show p'.length = 2 * r + 1 by simp [p', hplen]]
    exact odd_two_mul_add_one r
  have hiff := ((incidenceSelectedColoring label).odd_length_iff_not_congr p').1 hodd
  intro heq
  have :
      (¬ incidenceSelectedColoring label (c ⟨0, by omega⟩)) ↔
        incidenceSelectedColoring label (c ⟨0, by omega⟩) := by
    simpa [heq] using hiff
  rcases hzero : incidenceSelectedColoring label (c ⟨0, by omega⟩) with _ | _ <;>
    simp [hzero] at this

theorem remainderAttachment_value_ne_of_block_or_part_ne
    {V ι : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : ι → Finset V) (R : Finset V)
    (P : Finset (StarMove V))
    (hAB : ∀ i, A i ⊆ B i)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    {i j : ι}
    (a : {a // a ∈ remainderAttachments G A R i})
    (b : {b // b ∈ remainderAttachments G A R j})
    {p q : StarPartIndex P R}
    (hap : remainderAttachmentPart G A R P i a = p)
    (hbp : remainderAttachmentPart G A R P j b = q)
    (hne : i ≠ j ∨ p ≠ q) : a.1 ≠ b.1 := by
  intro hab
  rcases hne with hij | hpq
  · have haB : a.1 ∈ B i :=
      hAB i (remainderAttachments_subset G A R i a.2)
    have hbB : b.1 ∈ B j :=
      hAB j (remainderAttachments_subset G A R j b.2)
    exact Finset.disjoint_left.mp (hBdisj i j hij) haB (hab ▸ hbB)
  · have hij : i = j := by
      by_contra hij
      have haB : a.1 ∈ B i :=
        hAB i (remainderAttachments_subset G A R i a.2)
      have hbB : b.1 ∈ B j :=
        hAB j (remainderAttachments_subset G A R j b.2)
      exact Finset.disjoint_left.mp (hBdisj i j hij) haB (hab ▸ hbB)
    subst j
    have habSub : a = b := Subtype.ext hab
    subst b
    exact hpq (hap.symm.trans hbp)

structure AlternatingIncidenceCycleData
    (ι κ : Type*) (H : SimpleGraph (ι ⊕ κ)) (q : ℕ) where
  block : Fin q → ι
  part : Fin q → κ
  block_injective : Function.Injective block
  part_injective : Function.Injective part
  left_adj : ∀ i, H.Adj (Sum.inl (block i)) (Sum.inr (part i))
  right_adj : ∀ i, H.Adj
    (Sum.inl (block (finCyclicSucc (Nat.zero_lt_of_lt i.isLt) i)))
    (Sum.inr (part i))

/-- Every copied cycle in an injectively counted incidence graph can be
oriented as alternating block and part vertices. -/
theorem exists_alternatingIncidenceCycleData
    {D ι κ : Type*} [Fintype D] [Fintype ι] [Fintype κ]
    (label : D ↪ (ι × κ)) {l : ℕ} (hl : 4 ≤ l)
    (hcopy : cycleGraph l ⊑
      SelectedCrossEdgeGraph (incidenceSelectedSystem label)) :
    ∃ q : ℕ, l = q + q ∧ 2 ≤ q ∧
      Nonempty (AlternatingIncidenceCycleData ι κ
        (SelectedCrossEdgeGraph (incidenceSelectedSystem label)) q) := by
  classical
  have heven := even_of_cycleGraph_isContained_incidenceSelectedGraph
    label (by omega) hcopy
  rcases heven with ⟨q, hlq⟩
  have hq : 2 ≤ q := by omega
  subst l
  rcases hcopy with ⟨c⟩
  have hzero : 0 < q + q := by omega
  let next : Fin q → Fin q := finCyclicSucc (by omega)
  have evenSide (i : Fin q) :
      incidenceSelectedColoring label
          (c ⟨2 * i.val, by omega⟩) =
        incidenceSelectedColoring label (c ⟨0, hzero⟩) := by
    exact incidence_cycle_even_position_same_color
      (l := q + q) (r := i.val) label (by omega) c (by omega)
  have oddSide (i : Fin q) :
      incidenceSelectedColoring label
          (c ⟨2 * i.val + 1, by omega⟩) ≠
        incidenceSelectedColoring label (c ⟨0, hzero⟩) := by
    exact incidence_cycle_odd_position_ne_color
      (l := q + q) (r := i.val) label (by omega) c (by omega)
  rcases h0 : c ⟨0, hzero⟩ with b₀ | p₀
  · have evenLabel : ∀ i : Fin q, ∃ b : ι,
        c ⟨2 * i.val, by omega⟩ = Sum.inl b := by
      intro i
      rcases heq : c ⟨2 * i.val, by omega⟩ with b | p
      · exact ⟨b, rfl⟩
      · exfalso
        have hs := evenSide i
        simpa [heq, h0] using hs
    have oddLabel : ∀ i : Fin q, ∃ p : κ,
        c ⟨2 * i.val + 1, by omega⟩ = Sum.inr p := by
      intro i
      rcases heq : c ⟨2 * i.val + 1, by omega⟩ with b | p
      · exfalso
        exact (oddSide i) (by
          simp [heq, h0])
      · exact ⟨p, rfl⟩
    choose block hblock using evenLabel
    choose part hpart using oddLabel
    have hblockInj : Function.Injective block := by
      intro i j hij
      have hcpos :
          (⟨2 * i.val, by omega⟩ : Fin (q + q)) = ⟨2 * j.val, by omega⟩ := by
        apply c.injective
        change c ⟨2 * i.val, by omega⟩ = c ⟨2 * j.val, by omega⟩
        rw [hblock i, hblock j, hij]
      have hval := congrArg Fin.val hcpos
      change 2 * i.val = 2 * j.val at hval
      apply Fin.ext
      omega
    have hpartInj : Function.Injective part := by
      intro i j hij
      have hcpos :
          (⟨2 * i.val + 1, by omega⟩ : Fin (q + q)) =
            ⟨2 * j.val + 1, by omega⟩ := by
        apply c.injective
        change c ⟨2 * i.val + 1, by omega⟩ =
          c ⟨2 * j.val + 1, by omega⟩
        rw [hpart i, hpart j, hij]
      have hval := congrArg Fin.val hcpos
      change 2 * i.val + 1 = 2 * j.val + 1 at hval
      apply Fin.ext
      omega
    have hleft : ∀ i,
        (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
          (Sum.inl (block i)) (Sum.inr (part i)) := by
      intro i
      have hs : (cycleGraph (q + q)).Adj
          ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩ := by
        apply pathGraph_le_cycleGraph
        rw [pathGraph_adj]
        exact Or.inl (by simp)
      simpa [hblock i, hpart i] using c.toHom.map_adj hs
    have hright : ∀ i,
        (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
          (Sum.inl (block (next i))) (Sum.inr (part i)) := by
      intro i
      by_cases hi : i.val + 1 < q
      · have hnval : (next i).val = i.val + 1 := by
          simp [next, finCyclicSucc, Nat.mod_eq_of_lt hi]
        have hs : (cycleGraph (q + q)).Adj
            ⟨2 * (next i).val, by omega⟩
            ⟨2 * i.val + 1, by omega⟩ := by
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          right
          change (2 * i.val + 1) + 1 = 2 * (next i).val
          omega
        simpa [hblock (next i), hpart i] using c.toHom.map_adj hs
      · have hilast : i.val + 1 = q := by omega
        have hnval : (next i).val = 0 := by
          simp [next, finCyclicSucc, hilast]
        have hlastzero : (cycleGraph (q + q)).Adj
            (⟨q + q - 1, by omega⟩ : Fin (q + q)) ⟨0, by omega⟩ := by
          rw [cycleGraph_adj']
          right
          rw [Fin.coe_sub_iff_lt.mpr (show 0 < q + q - 1 by omega)]
          change (q + q) + 0 - (q + q - 1) = 1
          omega
        have hs : (cycleGraph (q + q)).Adj
            ⟨2 * (next i).val, by omega⟩
            ⟨2 * i.val + 1, by omega⟩ := by
          convert hlastzero.symm using 1 <;> apply Fin.ext <;> simp [hnval] <;> omega
        simpa [hblock (next i), hpart i] using c.toHom.map_adj hs
    refine ⟨q, by omega, hq, ⟨⟨block, part, hblockInj, hpartInj,
      hleft, by simpa [next] using hright⟩⟩⟩
  · have evenLabel : ∀ i : Fin q, ∃ p : κ,
        c ⟨2 * i.val, by omega⟩ = Sum.inr p := by
      intro i
      rcases heq : c ⟨2 * i.val, by omega⟩ with b | p
      · exfalso
        have hs := evenSide i
        simpa [heq, h0] using hs
      · exact ⟨p, rfl⟩
    have oddLabel : ∀ i : Fin q, ∃ b : ι,
        c ⟨2 * i.val + 1, by omega⟩ = Sum.inl b := by
      intro i
      rcases heq : c ⟨2 * i.val + 1, by omega⟩ with b | p
      · exact ⟨b, rfl⟩
      · exfalso
        exact (oddSide i) (by
          simp [heq, h0])
    choose evenPart hevenPart using evenLabel
    choose block hblock using oddLabel
    have hevenPartInj : Function.Injective evenPart := by
      intro i j hij
      have hcpos :
          (⟨2 * i.val, by omega⟩ : Fin (q + q)) = ⟨2 * j.val, by omega⟩ := by
        apply c.injective
        change c ⟨2 * i.val, by omega⟩ = c ⟨2 * j.val, by omega⟩
        rw [hevenPart i, hevenPart j, hij]
      have hval := congrArg Fin.val hcpos
      change 2 * i.val = 2 * j.val at hval
      apply Fin.ext
      omega
    have hblockInj : Function.Injective block := by
      intro i j hij
      have hcpos :
          (⟨2 * i.val + 1, by omega⟩ : Fin (q + q)) =
            ⟨2 * j.val + 1, by omega⟩ := by
        apply c.injective
        change c ⟨2 * i.val + 1, by omega⟩ =
          c ⟨2 * j.val + 1, by omega⟩
        rw [hblock i, hblock j, hij]
      have hval := congrArg Fin.val hcpos
      change 2 * i.val + 1 = 2 * j.val + 1 at hval
      apply Fin.ext
      omega
    let part : Fin q → κ := fun i => evenPart (next i)
    have hpartInj : Function.Injective part :=
      hevenPartInj.comp (finCyclicSucc_injective551 (by omega))
    have hright : ∀ i,
        (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
          (Sum.inl (block (next i))) (Sum.inr (part i)) := by
      intro i
      have hs : (cycleGraph (q + q)).Adj
          ⟨2 * (next i).val + 1, by omega⟩
          ⟨2 * (next i).val, by omega⟩ := by
        apply pathGraph_le_cycleGraph
        rw [pathGraph_adj]
        exact Or.inr (by simp)
      simpa [part, hblock (next i), hevenPart (next i)] using c.toHom.map_adj hs
    have hleft : ∀ i,
        (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
          (Sum.inl (block i)) (Sum.inr (part i)) := by
      intro i
      by_cases hi : i.val + 1 < q
      · have hnval : (next i).val = i.val + 1 := by
          simp [next, finCyclicSucc, Nat.mod_eq_of_lt hi]
        have hs : (cycleGraph (q + q)).Adj
            ⟨2 * i.val + 1, by omega⟩
            ⟨2 * (next i).val, by omega⟩ := by
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          left
          change (2 * i.val + 1) + 1 = 2 * (next i).val
          omega
        simpa [part, hblock i, hevenPart (next i)] using c.toHom.map_adj hs
      · have hilast : i.val + 1 = q := by omega
        have hnval : (next i).val = 0 := by
          simp [next, finCyclicSucc, hilast]
        have hlastzero : (cycleGraph (q + q)).Adj
            (⟨q + q - 1, by omega⟩ : Fin (q + q)) ⟨0, by omega⟩ := by
          rw [cycleGraph_adj']
          right
          rw [Fin.coe_sub_iff_lt.mpr (show 0 < q + q - 1 by omega)]
          change (q + q) + 0 - (q + q - 1) = 1
          omega
        have hs : (cycleGraph (q + q)).Adj
            ⟨2 * i.val + 1, by omega⟩
            ⟨2 * (next i).val, by omega⟩ := by
          convert hlastzero using 1 <;> apply Fin.ext <;> simp [hnval] <;> omega
        simpa [part, hblock i, hevenPart (next i)] using c.toHom.map_adj hs
    refine ⟨q, by omega, hq, ⟨⟨block, part, hblockInj, hpartInj,
      hleft, by simpa [next] using hright⟩⟩⟩

/-- A sufficiently short cycle in the cleaned attachment incidence graph
lifts to an exact ambient `C_k`. -/
theorem cycleGraph_isContained_of_remainderIncidence_cycle
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : ι → Finset V) (R : Finset V) (P : Finset (StarMove V))
    {m k l : ℕ} (hP : IsStarPacking G R m P)
    (J : Finset ι)
    (hclean : ∀ i, ∀ a ∈ A i, ∀ b ∈ A i, a ≠ b →
      ∀ x y : V, ∀ p : G.Walk x y,
        p.IsPath → p.length ≤ 2 →
        (∀ v ∈ p.support, v ∈ R) →
        G.Adj a x → G.Adj y b → False)
    (hAB : ∀ i, A i ⊆ B i)
    (hBR : ∀ i, Disjoint (B i) R)
    (hBne : ∀ i, (B i).Nonempty)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBdeg : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (hklarge : 1000 ≤ k) (hl : 4 ≤ l) (hroom : 9 * l ≤ k)
    (hcopy : cycleGraph l ⊑
      SelectedCrossEdgeGraph
        (incidenceSelectedSystem
          (remainderIncidenceLabel G A R P J
            (remainderAttachmentPart_injective G A R P hP hclean)))) :
    cycleGraph k ⊑ G := by
  classical
  let pinj : ∀ i, Function.Injective
      (remainderAttachmentPart G A R P i) :=
    remainderAttachmentPart_injective G A R P hP hclean
  let label := remainderIncidenceLabel G A R P J pinj
  obtain ⟨q, hlq, hq, hdata⟩ :=
    exists_alternatingIncidenceCycleData label hl (by simpa [label, pinj] using hcopy)
  let D := Classical.choice hdata
  let next : Fin q → Fin q := finCyclicSucc (by omega)
  let pred : Fin q → Fin q := finCyclicPred (by omega)
  let hub : Fin q → ι := fun i => (D.block i).1
  have hhubInj : Function.Injective hub := by
    intro i j hij
    apply D.block_injective
    exact Subtype.ext hij
  have hnextNe : ∀ i, next i ≠ i := by
    intro i
    exact finCyclicSucc_ne_self551 hq i
  have hleftAdj : ∀ i,
      (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
        (Sum.inl (D.block i)) (Sum.inr (D.part i)) := D.left_adj
  have hrightAdj : ∀ i,
      (SelectedCrossEdgeGraph (incidenceSelectedSystem label)).Adj
        (Sum.inl (D.block (next i))) (Sum.inr (D.part i)) := by
    simpa [next] using D.right_adj
  have hexLeft : ∀ i : Fin q,
      ∃ a : {a // a ∈ remainderAttachments G A R (hub i)},
        remainderAttachmentPart G A R P (hub i) a = D.part i := by
    intro i
    simpa [label, hub, pinj] using
      (exists_attachment_of_remainderIncidence_adj G A R P J pinj
        (hleftAdj i))
  have hexRight : ∀ i : Fin q,
      ∃ b : {b // b ∈ remainderAttachments G A R (hub (next i))},
        remainderAttachmentPart G A R P (hub (next i)) b = D.part i := by
    intro i
    simpa [label, hub, pinj] using
      (exists_attachment_of_remainderIncidence_adj G A R P J pinj
        (hrightAdj i))
  choose a haPart using hexLeft
  choose b hbPart using hexRight
  have hexHandle : ∀ i : Fin q,
      ∃ h : G.Walk (a i).1 (b i).1,
        h.IsPath ∧ 2 ≤ h.length ∧ h.length ≤ 4 ∧
        ∀ z ∈ h.support,
          z = (a i).1 ∨ z = (b i).1 ∨ z ∈ starPart P R (D.part i) := by
    intro i
    exact exists_short_handle_through_starPart G A B R P hP hAB hBR hBdisj
      (i := hub i) (j := hub (next i))
      (fun h => hnextNe i (hhubInj h.symm)) (D.part i) (a i) (b i)
        (haPart i) (hbPart i)
  choose h hhPath hhLower hhUpper hhLoc using hexHandle
  have hleftNeLeft : ∀ i j, i ≠ j → (a i).1 ≠ (a j).1 := by
    intro i j hij
    exact remainderAttachment_value_ne_of_block_or_part_ne G A B R P hAB hBdisj
      (a i) (a j) (haPart i) (haPart j) (Or.inl (fun h => hij (hhubInj h)))
  have hrightNeRight : ∀ i j, i ≠ j → (b i).1 ≠ (b j).1 := by
    intro i j hij
    exact remainderAttachment_value_ne_of_block_or_part_ne G A B R P hAB hBdisj
      (b i) (b j) (hbPart i) (hbPart j)
        (Or.inl (fun h => hij ((finCyclicSucc_injective551 (by omega))
          (hhubInj h))))
  have hleftNeRight : ∀ i j, i ≠ j → (a i).1 ≠ (b j).1 := by
    intro i j hij
    by_cases hblocks : hub i = hub (next j)
    · exact remainderAttachment_value_ne_of_block_or_part_ne
        G A B R P hAB hBdisj (a i) (b j) (haPart i) (hbPart j)
          (Or.inr (fun hp => hij (D.part_injective hp)))
    · exact remainderAttachment_value_ne_of_block_or_part_ne
        G A B R P hAB hBdisj (a i) (b j) (haPart i) (hbPart j)
          (Or.inl hblocks)
  have hrightNeLeft : ∀ i j, i ≠ j → (b i).1 ≠ (a j).1 := by
    intro i j hij
    by_cases hblocks : hub (next i) = hub j
    · exact remainderAttachment_value_ne_of_block_or_part_ne
        G A B R P hAB hBdisj (b i) (a j) (hbPart i) (haPart j)
          (Or.inr (fun hp => hij (D.part_injective hp)))
    · exact remainderAttachment_value_ne_of_block_or_part_ne
        G A B R P hAB hBdisj (b i) (a j) (hbPart i) (haPart j)
          (Or.inl hblocks)
  have hhDisj : ∀ i j, i ≠ j →
      (h i).support.Disjoint (h j).support := by
    intro i j hij z hzi hzj
    rcases hhLoc i z hzi with hziA | hziB | hziP
    · subst z
      rcases hhLoc j (a i).1 hzj with hzjA | hzjB | hzjP
      · exact hleftNeLeft i j hij hzjA
      · exact hleftNeRight i j hij hzjB
      · exact Finset.disjoint_left.mp (hBR (hub i))
          (hAB (hub i) (remainderAttachments_subset G A R _ (a i).2))
          (starPart_subset hP _ hzjP)
    · subst z
      rcases hhLoc j (b i).1 hzj with hzjA | hzjB | hzjP
      · exact hrightNeLeft i j hij hzjA
      · exact hrightNeRight i j hij hzjB
      · exact Finset.disjoint_left.mp (hBR (hub (next i)))
          (hAB (hub (next i))
            (remainderAttachments_subset G A R _ (b i).2))
          (starPart_subset hP _ hzjP)
    · rcases hhLoc j z hzj with hzjA | hzjB | hzjP
      · subst z
        exact Finset.disjoint_left.mp (hBR (hub j))
          (hAB (hub j) (remainderAttachments_subset G A R _ (a j).2))
          (starPart_subset hP _ hziP)
      · subst z
        exact Finset.disjoint_left.mp (hBR (hub (next j)))
          (hAB (hub (next j))
            (remainderAttachments_subset G A R _ (b j).2))
          (starPart_subset hP _ hziP)
      · exact Finset.disjoint_left.mp
          (starPart_pairwise_disjoint hP (D.part i) (D.part j)
            (fun hp => hij (D.part_injective hp))) hziP hzjP
  have hinternalNe : ∀ i, (b (pred i)).1 ≠ (a i).1 := by
    intro i
    have hn : next (pred i) = i := by
      exact finCyclicSucc_finCyclicPred (by omega) i
    have hparts : D.part (pred i) ≠ D.part i := by
      intro hp
      have hpi := D.part_injective hp
      have hinv : next (pred i) = i := by
        simpa [next, pred] using finCyclicSucc_finCyclicPred (by omega) i
      have hnexteq : next (pred i) = next i := congrArg next hpi
      exact hnextNe i (hnexteq.symm.trans hinv)
    have hne := remainderAttachment_value_ne_of_block_or_part_ne
      G A B R P hAB hBdisj (b (pred i)) (a i)
        (hbPart (pred i)) (haPart i) (Or.inr hparts)
    simpa [hub, next, pred, hn] using hne
  have hhBlocks : ∀ i e z, z ∈ (h i).support → z ∈ B (hub e) →
      (e = i ∧ z = (a i).1) ∨
        (e = next i ∧ z = (b i).1) := by
    intro i e z hzh hzB
    rcases hhLoc i z hzh with hza | hzb | hzp
    · left
      refine ⟨?_, hza⟩
      by_contra hei
      exact Finset.disjoint_left.mp (hBdisj (hub e) (hub i)
        (fun h => hei (hhubInj h))) hzB
          (hza ▸ hAB (hub i)
            (remainderAttachments_subset G A R _ (a i).2))
    · right
      refine ⟨?_, hzb⟩
      by_contra hei
      exact Finset.disjoint_left.mp (hBdisj (hub e) (hub (next i))
        (fun h => hei (hhubInj h))) hzB
          (hzb ▸ hAB (hub (next i))
            (remainderAttachments_subset G A R _ (b i).2))
    · exact (Finset.disjoint_left.mp (hBR (hub e)) hzB
        (starPart_subset hP _ hzp)).elim
  apply cycleGraph_isContained_of_dense_blocks_and_short_handles G hq
    (by omega) hklarge (fun i => B (hub i)) (fun i => hBne (hub i))
      (fun i => hBcard (hub i))
      (fun i j hij => hBdisj (hub i) (hub j) (fun h => hij (hhubInj h)))
      (fun i v hv => hBdeg (hub i) v hv)
      (fun i => (a i).1) (fun i => (b i).1) h
      (fun i => hAB (hub i)
        (remainderAttachments_subset G A R _ (a i).2))
      (fun i => by
        simpa [next] using
          hAB (hub (next i))
            (remainderAttachments_subset G A R _ (b i).2))
      (by simpa [pred] using hinternalNe) hhPath hhLower hhUpper hhDisj
      (by simpa [next] using hhBlocks)

/-- KLS remainder-separation lemma with explicit constants.  If at least
half the dense blocks had `k/8` available vertices seeing the cleaned
remainder, the injectively counted block--part incidence graph would have a
short cycle, and the preceding theorem would lift it to `C_k`. -/
theorem fewer_than_half_large_remainderAttachment_blocks
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : ι → Finset V) (L R : Finset V)
    (P : Finset (StarMove V)) {k n : ℕ}
    (hk : 16 ≤ k) (hklarge : 1000 ≤ k) (hn : 3 ≤ n) (hnk : n ≤ k)
    (horder : Fintype.card V = (k - 1) * (n - 1) + 1)
    (hP : IsStarPacking G R (Nat.sqrt k) P)
    (hpartCount : Nat.sqrt k * Fintype.card (StarPartIndex P R) ≤
      R.card + Nat.sqrt k * ((n - 1) * (Nat.sqrt k - 1)))
    (hRL : R ⊆ L)
    (hLsmall : 64 * L.card ≤ Fintype.card V)
    (hBne : ∀ i, (B i).Nonempty)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBcover : L = (Finset.univ : Finset V) \
      (Finset.univ : Finset ι).biUnion B)
    (hBdeg : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (hAB : ∀ i, A i ⊆ B i)
    (hBR : ∀ i, Disjoint (B i) R)
    (hclean : ∀ i, ∀ a ∈ A i, ∀ b ∈ A i, a ≠ b →
      ∀ x y : V, ∀ p : G.Walk x y,
        p.IsPath → p.length ≤ 2 →
        (∀ v ∈ p.support, v ∈ R) →
        G.Adj a x → G.Adj y b → False)
    (hmargin : 2 * ((8 * (8 + 1)) * 2 *
      (Nat.log 2 (2 * Fintype.card V) + 1)) < Nat.sqrt k / 4096)
    (hcycleRoom : 9 * (72 + 2 * Nat.log 2 (2 * Fintype.card V)) ≤ k)
    (hcycle : ¬ cycleGraph k ⊑ G) :
    2 * ((Finset.univ : Finset ι).filter fun i =>
      k / 8 ≤ (remainderAttachments G A R i).card).card <
      Fintype.card ι := by
  classical
  let J : Finset ι := (Finset.univ : Finset ι).filter fun i =>
    k / 8 ≤ (remainderAttachments G A R i).card
  let s := Fintype.card ι
  let j := J.card
  let r := Fintype.card (StarPartIndex P R)
  let N := Fintype.card V
  let rootm := Nat.sqrt k
  let delta := rootm / 4096
  by_contra hnot
  have hsj : s ≤ 2 * j := by
    simpa [J, s, j] using (Nat.le_of_not_gt hnot)
  have hspos : 0 < s := Fintype.card_pos
  have hjpos : 0 < j := by omega
  have hmpos : 0 < rootm := by
    dsimp [rootm]
    exact Nat.sqrt_pos.mpr (by omega)
  let U : Finset V := (Finset.univ : Finset ι).biUnion B
  have hBpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint B := by
    intro i _hi j _hj hij
    exact hBdisj i j hij
  have hUcard : U.card = ∑ i : ι, (B i).card := by
    simpa [U] using Finset.card_biUnion hBpair
  have hsU : s ≤ U.card := by
    rw [hUcard]
    calc
      s = ∑ _i : ι, 1 := by simp [s]
      _ ≤ ∑ i : ι, (B i).card := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Finset.card_pos.mpr (hBne i)
  have hUN : U.card ≤ N := by
    simpa [N] using Finset.card_le_card (Finset.subset_univ U)
  have hsN : s ≤ N := hsU.trans hUN
  have hRcardN : R.card ≤ N := by
    simpa [N] using Finset.card_le_card (Finset.subset_univ R)
  have hrR : r ≤ R.card := by
    let pick : StarPartIndex P R → {v // v ∈ R} := fun i =>
      ⟨Classical.choose (starPart_nonempty (by
          have := Nat.sqrt_pos.mpr (by omega : 0 < k)
          omega) hP i),
        starPart_subset hP i
          (Classical.choose_spec (starPart_nonempty (by
            have := Nat.sqrt_pos.mpr (by omega : 0 < k)
            omega) hP i))⟩
    have hpick : Function.Injective pick := by
      intro i t hit
      by_contra hit'
      have hi := Classical.choose_spec (starPart_nonempty (by
        have := Nat.sqrt_pos.mpr (by omega : 0 < k)
        omega) hP i)
      have ht := Classical.choose_spec (starPart_nonempty (by
        have := Nat.sqrt_pos.mpr (by omega : 0 < k)
        omega) hP t)
      have hval : (pick i).1 = (pick t).1 := congrArg Subtype.val hit
      have hi' : (pick i).1 ∈ starPart P R i := by
        simpa [pick] using hi
      have ht' : (pick t).1 ∈ starPart P R t := by
        simpa [pick] using ht
      rw [← hval] at ht'
      exact Finset.disjoint_left.mp (starPart_pairwise_disjoint hP i t hit')
        hi' ht'
    have := Fintype.card_le_of_injective pick hpick
    simpa [r] using this
  have hrN : r ≤ N := hrR.trans hRcardN
  have hauxN : Fintype.card ({i // i ∈ J} ⊕ StarPartIndex P R) ≤ 2 * N := by
    rw [Fintype.card_sum]
    change Fintype.card {i // i ∈ J} + r ≤ 2 * N
    rw [Fintype.card_coe]
    have hjN : j ≤ N := by
      exact (Finset.card_le_univ J).trans hsN
    have hadd := Nat.add_le_add hjN hrN
    simpa [j, two_mul] using hadd
  have hLdecomp : U.card + L.card = N := by
    rw [hBcover]
    have hUN' : U ⊆ (Finset.univ : Finset V) := Finset.subset_univ U
    rw [Finset.card_sdiff_of_subset hUN']
    have hcardU : U.card ≤ Fintype.card V := Finset.card_le_univ U
    simp only [Finset.card_univ]
    change U.card + (Fintype.card V - U.card) = N
    rw [Nat.add_sub_of_le hcardU]
  have hcoverage : 63 * N ≤ 64 * U.card := by
    have hLs : 64 * L.card ≤ N := by simpa [N] using hLsmall
    omega
  have hUupper : U.card ≤ s * (k - 1) := by
    rw [hUcard]
    calc
      ∑ i : ι, (B i).card ≤ ∑ _i : ι, (k - 1) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hBcard i
      _ = s * (k - 1) := by simp [s]
  have hNj : 63 * N ≤ 128 * j * (k - 1) := by
    calc
      63 * N ≤ 64 * U.card := hcoverage
      _ ≤ 64 * (s * (k - 1)) := Nat.mul_le_mul_left 64 hUupper
      _ ≤ 64 * ((2 * j) * (k - 1)) := by gcongr
      _ = 128 * j * (k - 1) := by ring
  have hnj : 63 * (n - 1) ≤ 128 * j := by
    have horderN : N = (k - 1) * (n - 1) + 1 := by
      simpa [N] using horder
    have hbase : 63 * ((k - 1) * (n - 1)) ≤
        128 * j * (k - 1) := by
      rw [horderN] at hNj
      omega
    have hscaled : (k - 1) * (63 * (n - 1)) ≤
        (k - 1) * (128 * j) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hnjLoose : n ≤ 4 * j := by omega
  have hNk : N ≤ k * n := by
    rw [show N = (k - 1) * (n - 1) + 1 by simpa [N] using horder]
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    nlinarith
  have hNJK : N ≤ 4 * j * k := by
    calc
      N ≤ k * n := hNk
      _ ≤ k * (4 * j) := Nat.mul_le_mul_left k hnjLoose
      _ = 4 * j * k := by ring
  have hRJ : 16 * R.card ≤ j * k := by
    have hRLcard : R.card ≤ L.card := Finset.card_le_card hRL
    have h64R : 64 * R.card ≤ N :=
      (Nat.mul_le_mul_left 64 hRLcard).trans (by simpa [N] using hLsmall)
    have : 64 * R.card ≤ 4 * j * k := h64R.trans hNJK
    apply Nat.le_of_mul_le_mul_left (c := 4)
    · calc
        4 * (16 * R.card) = 64 * R.card := by ring
        _ ≤ 4 * j * k := this
        _ = 4 * (j * k) := by ring
    · omega
  have hrootSq : rootm * rootm ≤ k := by
    simpa [rootm] using Nat.sqrt_le k
  have hkRoot : k ≤ 3 * (rootm * rootm) := by
    have hsqrtAdd := Nat.sqrt_le_add k
    dsimp [rootm]
    nlinarith [Nat.sqrt_pos.mpr (by omega : 0 < k)]
  have hpartTerm : rootm * ((n - 1) * (rootm - 1)) ≤
      4 * j * k := by
    calc
      rootm * ((n - 1) * (rootm - 1)) ≤
          n * (rootm * rootm) := by
            calc
              rootm * ((n - 1) * (rootm - 1)) ≤
                  rootm * (n * rootm) := by gcongr <;> omega
              _ = n * (rootm * rootm) := by ring
      _ ≤ n * k := Nat.mul_le_mul_left n hrootSq
      _ ≤ (4 * j) * k := Nat.mul_le_mul_right k hnjLoose
  have hmr : rootm * r ≤ 5 * j * k := by
    have hp := hpartCount
    change rootm * r ≤ R.card + rootm * ((n - 1) * (rootm - 1)) at hp
    have hRle : R.card ≤ j * k := by omega
    calc
      rootm * r ≤ R.card + rootm * ((n - 1) * (rootm - 1)) := hp
      _ ≤ j * k + 4 * j * k := Nat.add_le_add hRle hpartTerm
      _ = 5 * j * k := by ring
  have hrBound : r ≤ 15 * j * rootm := by
    have : rootm * r ≤ rootm * (15 * j * rootm) := by
      calc
        rootm * r ≤ 5 * j * k := hmr
        _ ≤ 5 * j * (3 * (rootm * rootm)) := by gcongr
        _ = rootm * (15 * j * rootm) := by ring
    exact Nat.le_of_mul_le_mul_left this hmpos
  let pinj : ∀ i, Function.Injective
      (remainderAttachmentPart G A R P i) :=
    remainderAttachmentPart_injective G A R P hP hclean
  let label := remainderIncidenceLabel G A R P J pinj
  let M := incidenceSelectedSystem label
  let H : SimpleGraph ({i // i ∈ J} ⊕ StarPartIndex P R) :=
    SelectedCrossEdgeGraph M
  have hM : IsSelectedCrossEdgeSystem
      (⊤ : SimpleGraph (IncidenceEndpoint (RemainderAttachmentIndex G A R J)))
      (fun _ => (Finset.univ : Finset
        (IncidenceEndpoint (RemainderAttachmentIndex G A R J)))) M := by
    exact incidenceSelectedSystem_valid label
  have hedgeCard : H.edgeFinset.card =
      ∑ i ∈ J, (remainderAttachments G A R i).card := by
    calc
      H.edgeFinset.card = M.card := card_edgeFinset_selectedCrossEdgeGraph hM
      _ = Fintype.card (RemainderAttachmentIndex G A R J) :=
        incidenceSelectedSystem_card label
      _ = ∑ i ∈ J, (remainderAttachments G A R i).card :=
        card_remainderAttachmentIndex G A R J
  have hedgeLower : j * (k / 8) ≤ H.edgeFinset.card := by
    rw [hedgeCard]
    calc
      j * (k / 8) = ∑ _i ∈ J, k / 8 := by simp [j]
      _ ≤ ∑ i ∈ J, (remainderAttachments G A R i).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
  have hedgePos : 0 < H.edgeFinset.card := by
    have htpos : 0 < k / 8 := by omega
    exact (Nat.mul_pos hjpos htpos).trans_le hedgeLower
  have hsupport : H.support.ncard ≤ 16 * j * rootm := by
    calc
      H.support.ncard ≤
          Fintype.card ({i // i ∈ J} ⊕ StarPartIndex P R) :=
        by simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card H.support
      _ = j + r := by
        rw [Fintype.card_sum, Fintype.card_coe]
      _ ≤ j + 15 * j * rootm := Nat.add_le_add_left hrBound j
      _ ≤ 16 * j * rootm := by
        calc
          j + 15 * j * rootm ≤ j * rootm + 15 * j * rootm :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_right j hmpos) _
          _ = 16 * j * rootm := by ring
  have hdelta : 1024 * delta ≤ rootm := by
    have hd := Nat.div_mul_le_self rootm 4096
    dsimp [delta]
    omega
  have hdense : (8 * delta) * H.support.ncard ≤
      2 * H.edgeFinset.card := by
    have hleft8 : 8 * ((8 * delta) * H.support.ncard) ≤ j * k := by
      calc
        8 * ((8 * delta) * H.support.ncard) ≤
            8 * ((8 * delta) * (16 * j * rootm)) := by gcongr
        _ = (1024 * delta) * j * rootm := by ring
        _ ≤ rootm * j * rootm := by gcongr
        _ ≤ j * k := by
          calc
            rootm * j * rootm = j * (rootm * rootm) := by ring
            _ ≤ j * k := Nat.mul_le_mul_left j hrootSq
    have hkdiv : k ≤ 16 * (k / 8) := by omega
    have hright8 : j * k ≤ 8 * (2 * H.edgeFinset.card) := by
      calc
        j * k ≤ j * (16 * (k / 8)) := Nat.mul_le_mul_left j hkdiv
        _ = 8 * (2 * (j * (k / 8))) := by ring
        _ ≤ 8 * (2 * H.edgeFinset.card) := by gcongr
    exact Nat.le_of_mul_le_mul_left (hleft8.trans hright8) (by omega)
  have hlog : Nat.log 2 (Fintype.card
      ({i // i ∈ J} ⊕ StarPartIndex P R)) ≤ Nat.log 2 (2 * N) :=
    Nat.log_mono_right hauxN
  have hmarginH : 2 * ((8 * (8 + 1)) * 2 *
      (Nat.log 2 (Fintype.card
        ({i // i ∈ J} ⊕ StarPartIndex P R)) + 1)) < delta := by
    have hmul := Nat.mul_le_mul_left (2 * ((8 * (8 + 1)) * 2))
      (Nat.add_le_add_right hlog 1)
    have hle : 2 * ((8 * (8 + 1)) * 2 *
        (Nat.log 2 (Fintype.card
          ({i // i ∈ J} ⊕ StarPartIndex P R)) + 1)) ≤
        2 * ((8 * (8 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) := by
      simpa only [Nat.mul_assoc] using hmul
    exact hle.trans_lt (by simpa [delta, rootm, N] using hmargin)
  obtain ⟨ell, hell8, hellUpper, hcopy⟩ :=
    exists_medium_cycle_of_edge_density H 2 8 delta (by omega)
      (Finset.card_pos.mp hedgePos) hdense hmarginH
  have hellRoom : 9 * ell ≤ k := by
    calc
      9 * ell ≤ 9 * (72 + 2 * Nat.log 2
          (Fintype.card ({i // i ∈ J} ⊕ StarPartIndex P R))) := by
        exact Nat.mul_le_mul_left 9 hellUpper
      _ ≤ 9 * (72 + 2 * Nat.log 2 (2 * N)) := by
        exact Nat.mul_le_mul_left 9
          (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hlog) 72)
      _ ≤ k := by
        change 9 * (72 + 2 * Nat.log 2 (2 * Fintype.card V)) ≤ k
        exact hcycleRoom
  apply hcycle
  apply cycleGraph_isContained_of_remainderIncidence_cycle
    G A B R P hP J hclean hAB hBR hBne hBcard hBdisj hBdeg
      hklarge (by omega) hellRoom
  change cycleGraph ell ⊑ H
  exact hcopy

/-! ## Routing from absorbed vertices back to their dense block -/

variable {J : Type*} [Fintype J]

noncomputable def ShortAbsorbableFamily.enlarged
    {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}
    (F : ShortAbsorbableFamily (J := J) G B) : Finset V :=
  B ∪ F.vertices

/-- Every vertex of an enlarged absorbable block reaches an original dense
block vertex by a simple path of length at most three contained in that
enlarged block. -/
theorem ShortAbsorbableFamily.exists_anchor_path
    {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}
    (F : ShortAbsorbableFamily (J := J) G B) {x : V} (hx : x ∈ F.enlarged) :
    ∃ a ∈ B, ∃ p : G.Walk x a,
      p.IsPath ∧ p.length ≤ 3 ∧
        (∀ z ∈ p.support, z ∈ F.enlarged) ∧
        ∀ z ∈ p.support, z ∈ B → z = a := by
  classical
  rcases Finset.mem_union.mp hx with hxB | hxV
  · refine ⟨x, hxB, SimpleGraph.Walk.nil, by simp, by simp, ?_, ?_⟩
    · intro z hz
      have hzx : z = x := by simpa using hz
      exact Finset.mem_union_left _ (hzx ▸ hxB)
    · intro z hz _hzB
      simpa using hz
  · rcases Finset.mem_biUnion.mp hxV with ⟨j, _hj, hxj⟩
    obtain ⟨q, r, hq, hr, hpath⟩ :=
      ((F.isPath j).mem_support_iff_exists_append).mp
        (by simpa using hxj)
    let a : V := F.attach (j, 1)
    have haB : a ∈ B := F.attach_mem (j, 1)
    have haNotPath : a ∉ (F.path j).support := by
      intro ha
      exact Finset.disjoint_left.mp F.disjoint_block_vertices
        haB (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using ha⟩)
    have haNotR : a ∉ r.support := by
      intro har
      apply haNotPath
      rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr har
    let p : G.Walk x a := r.concat (F.finish_adj j)
    have hp : p.IsPath := hr.concat haNotR _
    refine ⟨a, haB, p, hp, ?_, ?_, ?_⟩
    · have hrlen : r.length ≤ (F.path j).length := by
        rw [hpath, SimpleGraph.Walk.length_append]
        omega
      simp only [p, SimpleGraph.Walk.length_concat]
      have hFlen := F.length_le_two j
      omega
    · intro z hz
      simp only [p, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hz
      rcases hz with hzr | rfl
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
          apply List.mem_toFinset.mpr
          rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hzr⟩
      · exact Finset.mem_union_left _ haB
    · intro z hz hzB
      simp only [p, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hz
      rcases hz with hzr | rfl
      · exfalso
        exact Finset.disjoint_left.mp F.disjoint_block_vertices
          hzB (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
            apply List.mem_toFinset.mpr
            rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
            exact Or.inr hzr⟩)
      · rfl

/-- A vertex actually lying on an absorbed path has an anchor arm whose
non-anchor vertices stay on one explicitly displayed absorbed path. -/
theorem ShortAbsorbableFamily.exists_absorbed_arm
    {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}
    (F : ShortAbsorbableFamily (J := J) G B) {x : V} (hx : x ∈ F.vertices) :
    ∃ j : J, ∃ a ∈ B, a = F.attach (j, 1) ∧ ∃ p : G.Walk x a,
      x ∈ (F.path j).support ∧ p.IsPath ∧ p.length ≤ 3 ∧
      (∀ z ∈ p.support, z = a ∨ z ∈ (F.path j).support) ∧
      ∀ z ∈ p.support, z ∈ B → z = a := by
  classical
  rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
  obtain ⟨q, r, hq, hr, hpath⟩ :=
    ((F.isPath j).mem_support_iff_exists_append).mp (by simpa using hxj)
  let a : V := F.attach (j, 1)
  have haB : a ∈ B := F.attach_mem (j, 1)
  have haNotPath : a ∉ (F.path j).support := by
    intro ha
    exact Finset.disjoint_left.mp F.disjoint_block_vertices
      haB (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using ha⟩)
  have haNotR : a ∉ r.support := by
    intro har
    apply haNotPath
    rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr har
  let p : G.Walk x a := r.concat (F.finish_adj j)
  have hp : p.IsPath := hr.concat haNotR _
  refine ⟨j, a, haB, rfl, p, by simpa using hxj, hp, ?_, ?_, ?_⟩
  · have hrlen : r.length ≤ (F.path j).length := by
      rw [hpath, SimpleGraph.Walk.length_append]
      omega
    simp only [p, SimpleGraph.Walk.length_concat]
    have hFlen := F.length_le_two j
    omega
  · intro z hz
    simp only [p, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with hzr | rfl
    · right
      rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hzr
    · exact Or.inl rfl
  · intro z hz hzB
    have hz' : z ∈ r.support ∨ z = a := by
      simpa only [p, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] using hz
    rcases (show z = a ∨ z ∈ (F.path j).support by
      rcases hz' with hzr | rfl
      · right
        rw [hpath, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inr hzr
      · exact Or.inl rfl) with rfl | hzpath
    · rfl
    · exact (Finset.disjoint_left.mp F.disjoint_block_vertices
        hzB (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ _, by simpa using hzpath⟩)).elim

/-- Anchor arms belonging to two different absorbed paths are vertex
disjoint and have distinct dense-block anchors. -/
theorem disjoint_absorbed_arms_of_ne
    {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}
    (F : ShortAbsorbableFamily (J := J) G B)
    {j t : J} (hjt : j ≠ t)
    {x y a b : V} {p : G.Walk x a} {q : G.Walk y b}
    (haB : a ∈ B) (hbB : b ∈ B)
    (hpa : ∀ z ∈ p.support, z = a ∨ z ∈ (F.path j).support)
    (hqb : ∀ z ∈ q.support, z = b ∨ z ∈ (F.path t).support)
    (ha : a = F.attach (j, 1)) (hb : b = F.attach (t, 1)) :
    a ≠ b ∧ p.support.Disjoint q.support := by
  classical
  have hab : a ≠ b := by
    rw [ha, hb]
    exact fun h => hjt (congrArg Prod.fst (F.attach_injective h))
  refine ⟨hab, ?_⟩
  intro z hzp hzq
  rcases hpa z hzp with hza | hzj
  · subst z
    rcases hqb a hzq with hzb | hzt
    · exact hab hzb
    · exact Finset.disjoint_left.mp F.disjoint_block_vertices
        haB (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simpa using hzt⟩)
  · rcases hqb z hzq with hzb | hzt
    · subst z
      exact Finset.disjoint_left.mp F.disjoint_block_vertices
        hbB (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using hzj⟩)
    · exact List.disjoint_left.mp (F.support_disjoint j t hjt) hzj hzt

/-- Two vertex-disjoint edges from one dense block into two different
absorbed paths of another dense block already force an exact `C_k`. -/
theorem cycleGraph_isContained_of_two_edges_to_distinct_absorbed_paths
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1000 ≤ k)
    {B₀ B₁ : Finset V} (F₁ : ShortAbsorbableFamily (J := J) G B₁)
    (hB₀ne : B₀.Nonempty) (hB₁ne : B₁.Nonempty)
    (hB₀card : B₀.card ≤ k - 1) (hB₁card : B₁.card ≤ k - 1)
    (hBdisj : Disjoint B₀ B₁)
    (hB₀W₁ : Disjoint B₀ F₁.enlarged)
    (hdeg₀ : ∀ v ∈ B₀,
      121 * (k - 1) ≤ 128 * degreeIn G B₀ v)
    (hdeg₁ : ∀ v ∈ B₁,
      121 * (k - 1) ≤ 128 * degreeIn G B₁ v)
    {x₀ x₁ y₀ y₁ : V}
    (hx₀ : x₀ ∈ B₀) (hx₁ : x₁ ∈ B₀) (hxx : x₀ ≠ x₁)
    (hy₀ : y₀ ∈ F₁.vertices) (hy₁ : y₁ ∈ F₁.vertices)
    (hdifferent : ∀ j : J,
      ¬ (y₀ ∈ (F₁.path j).support ∧ y₁ ∈ (F₁.path j).support))
    (hxy₀ : G.Adj x₀ y₀) (hxy₁ : G.Adj x₁ y₁) :
    cycleGraph k ⊑ G := by
  classical
  obtain ⟨j, a₀, ha₀B, haform₀, p₀, hy₀j, hp₀, hp₀len, hp₀loc, hp₀B⟩ :=
    F₁.exists_absorbed_arm hy₀
  obtain ⟨t, a₁, ha₁B, haform₁, p₁, hy₁t, hp₁, hp₁len, hp₁loc, hp₁B⟩ :=
    F₁.exists_absorbed_arm hy₁
  have hjt : j ≠ t := by
    intro hjt
    subst t
    exact hdifferent j ⟨hy₀j, hy₁t⟩
  obtain ⟨haNe, hpDisj⟩ :=
    disjoint_absorbed_arms_of_ne F₁ hjt ha₀B ha₁B
      hp₀loc hp₁loc haform₀ haform₁
  have hp₀Enlarged : ∀ z ∈ p₀.support, z ∈ F₁.enlarged := by
    intro z hz
    rcases hp₀loc z hz with rfl | hz
    · exact Finset.mem_union_left _ ha₀B
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using hz⟩)
  have hp₁Enlarged : ∀ z ∈ p₁.support, z ∈ F₁.enlarged := by
    intro z hz
    rcases hp₁loc z hz with rfl | hz
    · exact Finset.mem_union_left _ ha₁B
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simpa using hz⟩)
  have hx₀p₀ : x₀ ∉ p₀.support := fun hz =>
    Finset.disjoint_left.mp hB₀W₁ hx₀ (hp₀Enlarged x₀ hz)
  have hx₁p₁ : x₁ ∉ p₁.support := fun hz =>
    Finset.disjoint_left.mp hB₀W₁ hx₁ (hp₁Enlarged x₁ hz)
  let h₀ : G.Walk x₀ a₀ := SimpleGraph.Walk.cons hxy₀ p₀
  let h₁f : G.Walk x₁ a₁ := SimpleGraph.Walk.cons hxy₁ p₁
  let h₁ : G.Walk a₁ x₁ := h₁f.reverse
  have hh₀ : h₀.IsPath := hp₀.cons hx₀p₀
  have hh₁f : h₁f.IsPath := hp₁.cons hx₁p₁
  have hh₁ : h₁.IsPath := hh₁f.reverse
  have hp₀pos : 1 ≤ p₀.length := by
    by_contra hzero
    have hnil : p₀.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp (by omega)
    have hya : y₀ = a₀ := hnil.eq
    exact Finset.disjoint_left.mp F₁.disjoint_block_vertices (hya ▸ ha₀B) hy₀
  have hp₁pos : 1 ≤ p₁.length := by
    by_contra hzero
    have hnil : p₁.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp (by omega)
    have hya : y₁ = a₁ := hnil.eq
    exact Finset.disjoint_left.mp F₁.disjoint_block_vertices (hya ▸ ha₁B) hy₁
  have hh₀len : 2 ≤ h₀.length ∧ h₀.length ≤ 4 := by
    simp [h₀]
    omega
  have hh₁len : 2 ≤ h₁.length ∧ h₁.length ≤ 4 := by
    simp [h₁, h₁f, SimpleGraph.Walk.length_reverse]
    omega
  have hhDisj : h₀.support.Disjoint h₁.support := by
    change h₀.support.Disjoint h₁f.reverse.support
    intro z hz₀ hz₁
    have hz₁' : z ∈ h₁f.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hz₁
    simp only [h₀, SimpleGraph.Walk.support_cons, List.mem_cons] at hz₀
    simp only [h₁f, SimpleGraph.Walk.support_cons, List.mem_cons] at hz₁'
    rcases hz₀ with hz₀ | hz₀
    · subst z
      rcases hz₁' with hz₁' | hz₁'
      · exact hxx hz₁'
      · exact Finset.disjoint_left.mp hB₀W₁ hx₀
          (hp₁Enlarged x₀ hz₁')
    · rcases hz₁' with hz₁' | hz₁'
      · subst z
        exact Finset.disjoint_left.mp hB₀W₁ hx₁
          (hp₀Enlarged x₁ hz₀)
      · exact hpDisj hz₀ hz₁'
  let BB : Fin 2 → Finset V := ![B₀, B₁]
  let xx : Fin 2 → V := ![x₀, a₁]
  let yy : Fin 2 → V := ![a₀, x₁]
  let hh : ∀ i : Fin 2, G.Walk (xx i) (yy i) :=
    Fin.cons h₀ (Fin.cons h₁ (fun i => Fin.elim0 i))
  have hh_zero : hh 0 = h₀ := by rfl
  have hh_one : hh 1 = h₁ := by rfl
  apply cycleGraph_isContained_of_dense_blocks_and_short_handles
    G (q := 2) (by omega) (by omega) hk BB (x := xx) (y := yy) (h := hh)
  · intro i
    fin_cases i <;> simp [BB, hB₀ne, hB₁ne]
  · intro i
    fin_cases i <;> simp [BB, hB₀card, hB₁card]
  · intro i t hit
    fin_cases i <;> fin_cases t <;> simp_all [BB, hBdisj, hBdisj.symm]
  · intro i v hv
    fin_cases i
    · simpa [BB] using hdeg₀ v hv
    · simpa [BB] using hdeg₁ v hv
  · intro i
    fin_cases i <;> simp [xx, BB, hx₀, ha₁B]
  · intro i
    fin_cases i <;> simp [yy, BB, finCyclicSucc, ha₀B, hx₁]
  · intro i
    fin_cases i
    · simpa [xx, yy, finCyclicPred] using hxx.symm
    · simpa [xx, yy, finCyclicPred] using haNe
  · intro i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [hh_zero]
      exact hh₀
    · simp only [Fin.mk_one]
      rw [hh_one]
      exact hh₁
  · intro i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [hh_zero]
      exact hh₀len.1
    · simp only [Fin.mk_one]
      rw [hh_one]
      exact hh₁len.1
  · intro i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [hh_zero]
      exact hh₀len.2
    · simp only [Fin.mk_one]
      rw [hh_one]
      exact hh₁len.2
  · intro i t hit
    fin_cases i <;> fin_cases t
    · exact (hit rfl).elim
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [hh_zero, hh_one]
      exact hhDisj
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [hh_one, hh_zero]
      exact hhDisj.symm
    · exact (hit rfl).elim
  · intro i e z hzh hzB
    fin_cases i <;> fin_cases e
    · left
      refine ⟨rfl, ?_⟩
      simp only [Fin.zero_eta, xx, yy, BB] at hzh hzB ⊢
      rw [hh_zero] at hzh
      change z ∈ (SimpleGraph.Walk.cons hxy₀ p₀).support at hzh
      rw [SimpleGraph.Walk.support_cons] at hzh
      simp only [List.mem_cons] at hzh
      rcases hzh with hzx | hzp
      · simpa [xx, Fin.zero_eta] using hzx
      · exfalso
        exact Finset.disjoint_left.mp hB₀W₁ hzB
          (hp₀Enlarged z hzp)
    · right
      refine ⟨by simp [finCyclicSucc], ?_⟩
      simp only [Fin.zero_eta, xx, yy, BB] at hzh hzB ⊢
      rw [hh_zero] at hzh
      change z ∈ (SimpleGraph.Walk.cons hxy₀ p₀).support at hzh
      rw [SimpleGraph.Walk.support_cons] at hzh
      simp only [List.mem_cons] at hzh
      rcases hzh with hzx | hzp
      · exact (Finset.disjoint_left.mp hBdisj hx₀ (hzx ▸ hzB)).elim
      · simpa [yy, Fin.zero_eta] using hp₀B z hzp hzB
    · right
      refine ⟨by simp [finCyclicSucc], ?_⟩
      simp only [Fin.mk_one, xx, yy, BB] at hzh hzB ⊢
      rw [hh_one] at hzh
      change z ∈ h₁f.reverse.support at hzh
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzh
      change z ∈ (SimpleGraph.Walk.cons hxy₁ p₁).support at hzh
      rw [SimpleGraph.Walk.support_cons] at hzh
      simp only [List.mem_cons] at hzh
      rcases hzh with hzx | hzp
      · simpa [yy, Fin.mk_one] using hzx
      · exfalso
        exact Finset.disjoint_left.mp hB₀W₁ hzB
          (hp₁Enlarged z hzp)
    · left
      refine ⟨rfl, ?_⟩
      simp only [Fin.mk_one, xx, yy, BB] at hzh hzB ⊢
      rw [hh_one] at hzh
      change z ∈ h₁f.reverse.support at hzh
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzh
      change z ∈ (SimpleGraph.Walk.cons hxy₁ p₁).support at hzh
      rw [SimpleGraph.Walk.support_cons] at hzh
      simp only [List.mem_cons] at hzh
      rcases hzh with hzx | hzp
      · exact (Finset.disjoint_left.mp hBdisj hx₁ (hzx ▸ hzB)).elim
      · simpa [xx, Fin.mk_one] using hp₁B z hzp hzB

def IsOrientedCrossFamily
    {V : Type*} (G : SimpleGraph V) (X Y : Finset V)
    (M : Finset (V × V)) : Prop :=
  DisjointAdjPairFamily G M ∧
    ∀ e ∈ M, e.1 ∈ X ∧ e.2 ∈ Y

def IsExternalMatching
    {V : Type*} (G : SimpleGraph V) (X W : Finset V)
    (M : Finset (V × V)) : Prop :=
  DisjointAdjPairFamily G M ∧
    ∀ e ∈ M, e.1 ∈ X ∧ e.2 ∉ W

def adjPairEndpointFinset
    {V : Type*} [DecidableEq V] (M : Finset (V × V)) : Finset V :=
  M.biUnion fun e => {e.1, e.2}

theorem exists_maximal_externalMatching
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (X W : Finset V) :
    ∃ M : Finset (V × V), IsExternalMatching G X W M ∧
      ∀ N : Finset (V × V), IsExternalMatching G X W N →
        N.card ≤ M.card := by
  classical
  let C : Finset (Finset (V × V)) :=
    Finset.univ.filter fun M => IsExternalMatching G X W M
  have hCne : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C, IsExternalMatching, DisjointAdjPairFamily]
  obtain ⟨M, hMC, hmax⟩ := Finset.exists_max_image C Finset.card hCne
  refine ⟨M, (Finset.mem_filter.mp hMC).2, ?_⟩
  intro N hN
  exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN⟩)

/-- Maximality in cardinality implies the usual endpoint-cover property:
every further external edge meets one of the selected matching endpoints. -/
theorem external_edge_meets_maximalMatching
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {X W : Finset V} {M : Finset (V × V)}
    (hM : IsExternalMatching G X W M)
    (hmax : ∀ N : Finset (V × V), IsExternalMatching G X W N →
      N.card ≤ M.card)
    {x y : V} (hx : x ∈ X) (hy : y ∉ W) (hxy : G.Adj x y) :
    x ∈ adjPairEndpointFinset M ∨ y ∈ adjPairEndpointFinset M := by
  classical
  by_contra hnone
  push_neg at hnone
  let e : V × V := (x, y)
  have heM : e ∉ M := by
    intro he
    exact hnone.1 (Finset.mem_biUnion.mpr ⟨e, he, by simp [e]⟩)
  have hfresh : ∀ f ∈ M,
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
    intro f hf
    have hxnot : x ∉ ({f.1, f.2} : Finset V) := by
      intro h
      exact hnone.1 (Finset.mem_biUnion.mpr ⟨f, hf, h⟩)
    have hynot : y ∉ ({f.1, f.2} : Finset V) := by
      intro h
      exact hnone.2 (Finset.mem_biUnion.mpr ⟨f, hf, h⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot hynot
    exact ⟨hxnot.1, hxnot.2, hynot.1, hynot.2⟩
  let N := insert e M
  have hN : IsExternalMatching G X W N := by
    refine ⟨?_, ?_⟩
    · constructor
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hxy
        · exact hM.1.1 f hf
      · intro f hf g hg hfg
        rcases Finset.mem_insert.mp hf with rfl | hf <;>
          rcases Finset.mem_insert.mp hg with rfl | hg
        · exact (hfg rfl).elim
        · exact hfresh g hg
        · have h := hfresh f hf
          exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩
        · exact hM.1.2 f hf g hg hfg
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨hx, hy⟩
      · exact hM.2 f hf
  have hle := hmax N hN
  simp [N, heM] at hle

/-- In a `C_k`-free graph, an oriented matching from one dense block into
one other enlarged absorbable block has at most three edges.  Four target
vertices cannot all lie on one absorbed path of order at most three, so two
land on different paths and the preceding lift closes an exact cycle. -/
theorem orientedCrossFamily_card_le_three_of_cycleFree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1000 ≤ k)
    {B₀ B₁ : Finset V} (F₁ : ShortAbsorbableFamily (J := J) G B₁)
    (hB₀ne : B₀.Nonempty) (hB₁ne : B₁.Nonempty)
    (hB₀card : B₀.card ≤ k - 1) (hB₁card : B₁.card ≤ k - 1)
    (hBdisj : Disjoint B₀ B₁)
    (hB₀W₁ : Disjoint B₀ F₁.enlarged)
    (hanti : ∀ x ∈ B₀, ∀ y ∈ B₁, ¬ G.Adj x y)
    (hdeg₀ : ∀ v ∈ B₀,
      121 * (k - 1) ≤ 128 * degreeIn G B₀ v)
    (hdeg₁ : ∀ v ∈ B₁,
      121 * (k - 1) ≤ 128 * degreeIn G B₁ v)
    {X : Finset V} (hXB : X ⊆ B₀)
    {M : Finset (V × V)} (hM : IsOrientedCrossFamily G X F₁.enlarged M)
    (hcycle : ¬ cycleGraph k ⊑ G) : M.card ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤ M.card := by omega
  obtain ⟨Q, hQM, hQcard⟩ := Finset.exists_subset_card_eq (s := M) hfour
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have htargetV : ∀ e ∈ Q, e.2 ∈ F₁.vertices := by
    intro e heQ
    have heM := hQM heQ
    have he := hM.2 e heM
    rcases Finset.mem_union.mp he.2 with heB | heV
    · exact (hanti e.1 (hXB he.1) e.2 heB (hM.1.1 e heM)).elim
    · exact heV
  let idx : (e : V × V) → e ∈ Q → J := fun e he =>
    Classical.choose (show ∃ j : J, e.2 ∈ (F₁.path j).support by
      rcases Finset.mem_biUnion.mp (htargetV e he) with ⟨j, _hj, hej⟩
      exact ⟨j, by simpa using hej⟩)
  have hidxSpec : ∀ e, ∀ he : e ∈ Q,
      e.2 ∈ (F₁.path (idx e he)).support := by
    intro e he
    exact Classical.choose_spec
      (show ∃ j : J, e.2 ∈ (F₁.path j).support by
        rcases Finset.mem_biUnion.mp (htargetV e he) with ⟨j, _hj, hej⟩
        exact ⟨j, by simpa using hej⟩)
  have htwo : ∃ e, ∃ he : e ∈ Q, ∃ f, ∃ hf : f ∈ Q,
      e ≠ f ∧ idx e he ≠ idx f hf := by
    by_contra hnone
    push_neg at hnone
    obtain ⟨e₀, he₀Q⟩ := hQne
    have hsame : ∀ e, ∀ heQ : e ∈ Q, idx e heQ = idx e₀ he₀Q := by
      intro e heQ
      by_cases he : e = e₀
      · subst e
        rfl
      · exact hnone e heQ e₀ he₀Q he
    let T : Finset V := Q.image Prod.snd
    have htargetInj : Set.InjOn Prod.snd (Q : Set (V × V)) := by
      intro e he f hf hef
      by_contra hne
      exact (hM.1.2 e (hQM (by simpa using he)) f (hQM (by simpa using hf)) hne).2.2.2 hef
    have hTcard : T.card = 4 := by
      rw [show T.card = Q.card by
        exact Finset.card_image_of_injOn htargetInj, hQcard]
    have hTsub : T ⊆ (F₁.path (idx e₀ he₀Q)).support.toFinset := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨e, heQ, rfl⟩
      apply List.mem_toFinset.mpr
      rw [← hsame e heQ]
      exact hidxSpec e heQ
    have hsmall : T.card ≤ 3 := by
      calc
        T.card ≤ (F₁.path (idx e₀ he₀Q)).support.toFinset.card :=
          Finset.card_le_card hTsub
        _ = (F₁.path (idx e₀ he₀Q)).length + 1 := by
          exact F₁.path_support_card _
        _ ≤ 3 := by
          have := F₁.length_le_two (idx e₀ he₀Q)
          omega
    omega
  obtain ⟨e, heQ, f, hfQ, hef, hidx⟩ := htwo
  have heM := hQM heQ
  have hfM := hQM hfQ
  have hsep := hM.1.2 e heM f hfM hef
  have hdifferent : ∀ u : J,
      ¬ (e.2 ∈ (F₁.path u).support ∧ f.2 ∈ (F₁.path u).support) := by
    intro u hu
    have heu : idx e heQ = u := by
      by_contra hne
      exact List.disjoint_left.mp (F₁.support_disjoint (idx e heQ) u hne)
        (hidxSpec e heQ) hu.1
    have hfu : idx f hfQ = u := by
      by_contra hne
      exact List.disjoint_left.mp (F₁.support_disjoint (idx f hfQ) u hne)
        (hidxSpec f hfQ) hu.2
    exact hidx (heu.trans hfu.symm)
  apply hcycle
  exact cycleGraph_isContained_of_two_edges_to_distinct_absorbed_paths
    G hk F₁ hB₀ne hB₁ne hB₀card hB₁card hBdisj hB₀W₁
      hdeg₀ hdeg₁ (hXB (hM.2 e heM).1) (hXB (hM.2 f hfM).1)
      hsep.1 (htargetV e heQ) (htargetV f hfQ) hdifferent
      (hM.1.1 e heM) (hM.1.1 f hfM)

/-- Two vertices on one simple path are joined by a simple subpath whose
support stays in the original path and whose length does not increase. -/
theorem exists_subpath_between_mem_support
    {V : Type*} {G : SimpleGraph V} {u v x y : V}
    {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : G.Walk x y, q.IsPath ∧ q.length ≤ p.length ∧
      ∀ z ∈ q.support, z ∈ p.support := by
  obtain ⟨a, r, ha, hr, hpar⟩ := hp.mem_support_iff_exists_append.mp hx
  have hy' : y ∈ a.support ∨ y ∈ r.support := by
    rw [hpar, SimpleGraph.Walk.mem_support_append_iff] at hy
    exact hy
  rcases hy' with hya | hyr
  · obtain ⟨s, t, hs, ht, hat⟩ := ha.mem_support_iff_exists_append.mp hya
    refine ⟨t.reverse, ht.reverse, ?_, ?_⟩
    · have htlen : t.length ≤ a.length := by
        rw [hat, SimpleGraph.Walk.length_append]
        omega
      have halen : a.length ≤ p.length := by
        rw [hpar, SimpleGraph.Walk.length_append]
        omega
      simpa using htlen.trans halen
    · intro z hz
      have hzt : z ∈ t.support := by simpa [SimpleGraph.Walk.support_reverse] using hz
      rw [hpar, SimpleGraph.Walk.mem_support_append_iff]
      left
      rw [hat, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hzt
  · obtain ⟨s, t, hs, ht, hrt⟩ := hr.mem_support_iff_exists_append.mp hyr
    refine ⟨s, hs, ?_, ?_⟩
    · have hslen : s.length ≤ r.length := by
        rw [hrt, SimpleGraph.Walk.length_append]
        omega
      have hrlen : r.length ≤ p.length := by
        rw [hpar, SimpleGraph.Walk.length_append]
        omega
      exact hslen.trans hrlen
    · intro z hz
      rw [hpar, SimpleGraph.Walk.mem_support_append_iff]
      right
      rw [hrt, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hz

/-- A dense trimmed block has a five-edge simple route between every two
distinct displayed vertices, with the whole route staying in the block. -/
theorem exists_five_path_in_dense_block
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} {k : ℕ} (hk : 1000 ≤ k) (hBne : B.Nonempty)
    (hBcard : B.card ≤ k - 1)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v)
    {a b : V} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length = 5 ∧
      ∀ z ∈ p.support, z ∈ B := by
  classical
  have hrob := robustPairSet_of_scaled_internal_degree G hBcard hdeg
  obtain ⟨M, hM, hMcard, hMB⟩ :=
    hasThreeDisjointAdjPairFamily_of_scaled_internal_degree G (by omega) hBne hdeg
  let F : Finset V := {a, b}
  have hFcard : F.card < M.card := by
    have hFtwo : F.card ≤ 2 := by
      simpa [F] using (Finset.card_le_two (a := a) (b := b))
    omega
  obtain ⟨e, heM, he₁F, he₂F, heAdj⟩ :=
    exists_adjPair_avoiding_of_disjointAdjPairFamily G M F hM hFcard
  have heB := hMB e heM
  have hane₁ : a ≠ e.1 := by intro h; exact he₁F (by simp [F, h])
  have hane₂ : a ≠ e.2 := by intro h; exact he₂F (by simp [F, h])
  have he₁neb : e.1 ≠ b := by intro h; exact he₁F (by simp [F, h])
  have he₂neb : e.2 ≠ b := by intro h; exact he₂F (by simp [F, h])
  obtain ⟨p, hp, hplen, hploc⟩ :=
    exists_path_between_of_robustPairSet_and_parity_edge G (ℓ := 5) hrob
      ha heB.1 heB.2 hb heAdj hane₁ hane₂ hab he₁neb he₂neb
        (by omega) (by
          have := (dense_block_balanced_routing_capacities G hk hBne hdeg).1
          omega) (by
          have := (dense_block_balanced_routing_capacities G hk hBne hdeg).2
          omega)
  exact ⟨p, hp, hplen, fun z hz => (hploc z hz).elim id id⟩

/-- Any two vertices of a dense block together with its absorbed short paths
are joined inside the enlarged block by a simple path of length at most
eleven.  Concatenating the two three-edge anchor arms with a five-edge
dense-block route may repeat vertices; `Walk.bypass` removes those repeats
without increasing the length or leaving the enlarged block. -/
theorem ShortAbsorbableFamily.exists_path_in_enlarged_le_eleven
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} (F : ShortAbsorbableFamily (J := J) G B)
    {k : ℕ} (hk : 1000 ≤ k) (hBne : B.Nonempty)
    (hBcard : B.card ≤ k - 1)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v)
    {x y : V} (hx : x ∈ F.enlarged) (hy : y ∈ F.enlarged) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 11 ∧
      ∀ z ∈ p.support, z ∈ F.enlarged := by
  classical
  obtain ⟨a, haB, pa, hpa, hpaLen, hpaLoc, _hpaOnly⟩ :=
    F.exists_anchor_path hx
  obtain ⟨b, hbB, pb, hpb, hpbLen, hpbLoc, _hpbOnly⟩ :=
    F.exists_anchor_path hy
  obtain ⟨r, hrLen, hrLoc⟩ : ∃ r : G.Walk a b, r.length ≤ 5 ∧
      ∀ z ∈ r.support, z ∈ B := by
    by_cases hab : a = b
    · subst b
      refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
      intro z hz
      have hza : z = a := by simpa using hz
      simpa [hza] using haB
    · obtain ⟨r, _hr, hrLen, hrLoc⟩ :=
        exists_five_path_in_dense_block G hk hBne hBcard hdeg haB hbB hab
      exact ⟨r, by omega, hrLoc⟩
  let w : G.Walk x y := (pa.append r).append pb.reverse
  let p : G.Walk x y := w.bypass
  refine ⟨p, by simpa [p] using w.bypass_isPath, ?_, ?_⟩
  · calc
      p.length ≤ w.length := by
        simpa [p] using w.length_bypass_le_length
      _ = pa.length + r.length + pb.length := by simp [w]
      _ ≤ 11 := by omega
  · intro z hz
    have hzw : z ∈ w.support := w.support_bypass_subset_support hz
    rw [show w.support = (pa.append r).support ++ pb.reverse.support.tail by
      simp [w, SimpleGraph.Walk.support_append]] at hzw
    rcases List.mem_append.mp hzw with hpar | hpb'
    · rw [SimpleGraph.Walk.support_append] at hpar
      rcases List.mem_append.mp hpar with hpa' | hr'
      · exact hpaLoc z hpa'
      · exact Finset.mem_union_left _ (hrLoc z (List.mem_of_mem_tail hr'))
    · exact hpbLoc z (by
        have hzrev : z ∈ pb.reverse.support := List.mem_of_mem_tail hpb'
        simpa [SimpleGraph.Walk.support_reverse] using hzrev)

/-- KLS's finite pruning algorithm.  Starting with a source set contained
in `W`, repeatedly delete the at most `2t` neighbours of an outside vertex
whose current positive degree is at most `2t`.  One edge from every deletion
round forms an external matching, so the total loss is controlled by the
size of that matching. -/
theorem exists_pruned_source_and_externalMatching
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S W : Finset V) (hSW : S ⊆ W) (t : ℕ) :
    ∃ D M,
      D ⊆ S ∧ IsExternalMatching G S W M ∧
      S.card ≤ D.card + 2 * t * M.card ∧
      ∀ y : V, y ∉ W →
        degreeIn G D y = 0 ∨ 2 * t < degreeIn G D y := by
  classical
  revert hSW
  refine Finset.strongInductionOn S ?_
  intro S ih hSW
  by_cases hbad : ∃ y : V, y ∉ W ∧
      1 ≤ degreeIn G S y ∧ degreeIn G S y ≤ 2 * t
  · obtain ⟨y, hyW, hyPos, hySmall⟩ := hbad
    let N : Finset V := S.filter fun x => G.Adj y x
    let T : Finset V := S \ N
    have hNsub : N ⊆ S := Finset.filter_subset _ _
    have hNne : N.Nonempty := by
      apply Finset.card_pos.mp
      simpa [N, degreeIn, SimpleGraph.adj_comm] using hyPos
    have hTS : T ⊂ S := Finset.sdiff_ssubset hNsub hNne
    have hTW : T ⊆ W := Finset.sdiff_subset.trans hSW
    obtain ⟨D, M, hDT, hM, hcard, hpruned⟩ := ih T hTS hTW
    obtain ⟨x, hxN⟩ := hNne
    have hxS : x ∈ S := hNsub hxN
    have hxW : x ∈ W := hSW hxS
    have hxy : G.Adj x y := by
      exact ((Finset.mem_filter.mp hxN).2).symm
    let e : V × V := (x, y)
    have heNot : e ∉ M := by
      intro he
      exact (Finset.mem_sdiff.mp (hM.2 e he).1).2 hxN
    have hfresh : ∀ f ∈ M,
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
      intro f hf
      have hfT : f.1 ∈ T := hM.2 f hf |>.1
      have hfOut : f.2 ∉ W := hM.2 f hf |>.2
      have hxNotT : x ∉ T := by
        intro hxT
        exact (Finset.mem_sdiff.mp hxT).2 hxN
      have hxy1 : x ≠ f.1 := fun h => hxNotT (h ▸ hfT)
      have hxy2 : x ≠ f.2 := fun h => hfOut (h ▸ hxW)
      have hyy1 : y ≠ f.1 := fun h => hyW (h ▸ hTW hfT)
      have hyy2 : y ≠ f.2 := by
        intro h
        have hfAdj : G.Adj f.1 f.2 := hM.1.1 f hf
        have hyAdj : G.Adj y f.1 := by simpa [h] using hfAdj.symm
        have hfNotN : f.1 ∉ N := (Finset.mem_sdiff.mp hfT).2
        exact hfNotN (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hfT).1, hyAdj⟩)
      exact ⟨hxy1, hxy2, hyy1, hyy2⟩
    let M' : Finset (V × V) := insert e M
    have hM' : IsExternalMatching G S W M' := by
      refine ⟨?_, ?_⟩
      · constructor
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact hxy
          · exact hM.1.1 f hf
        · intro f hf g hg hfg
          rcases Finset.mem_insert.mp hf with rfl | hf <;>
            rcases Finset.mem_insert.mp hg with rfl | hg
          · exact (hfg rfl).elim
          · exact hfresh g hg
          · have h := hfresh f hf
            exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩
          · exact hM.1.2 f hf g hg hfg
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact ⟨hxS, hyW⟩
        · exact ⟨Finset.sdiff_subset (hM.2 f hf).1, (hM.2 f hf).2⟩
    have hNcard : N.card ≤ 2 * t := by
      simpa [N, degreeIn, SimpleGraph.adj_comm] using hySmall
    have hSTcard : S.card = T.card + N.card := by
      have h := Finset.card_sdiff_add_card S N
      rw [Finset.union_eq_left.mpr hNsub] at h
      dsimp [T]
      omega
    have hM'card : M'.card = M.card + 1 := by
      simp [M', heNot]
    refine ⟨D, M', hDT.trans Finset.sdiff_subset, hM', ?_, hpruned⟩
    rw [hSTcard, hM'card]
    calc
      T.card + N.card ≤
          (D.card + 2 * t * M.card) + 2 * t := Nat.add_le_add hcard hNcard
      _ = D.card + 2 * t * (M.card + 1) := by ring
  · refine ⟨S, ∅, Finset.Subset.rfl, ?_, by simp, ?_⟩
    · simp [IsExternalMatching, DisjointAdjPairFamily]
    · intro y hyW
      by_cases hz : degreeIn G S y = 0
      · exact Or.inl hz
      · right
        have hpos : 1 ≤ degreeIn G S y := Nat.one_le_iff_ne_zero.mpr hz
        by_contra hle
        exact hbad ⟨y, hyW, hpos, by omega⟩

/-- Add a finite set of outside singleton paths to an absorbable family.
Every singleton has at least twice as many available neighbours as there
are singletons, so Hall's theorem chooses two globally distinct fresh
attachments for each of them. -/
theorem ShortAbsorbableFamily.cycleGraph_isContained_of_external_singletons
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B D Q : Finset V} (F : ShortAbsorbableFamily (J := J) G B)
    {k : ℕ} (hk : 1000 ≤ k)
    (hDB : D ⊆ F.remaining)
    (hQoutside : ∀ q ∈ Q, q ∉ F.enlarged)
    (hmany : ∀ q ∈ Q, 2 * Q.card ≤ degreeIn G D q)
    (htotal : B.card + F.vertices.card + Q.card = k)
    (hsmall : 10 * (F.vertices.card + Q.card) ≤ B.card)
    (hdeg : ∀ v ∈ B,
      121 * (k - 1) ≤ 128 * degreeIn G B v) :
    cycleGraph k ⊑ G := by
  classical
  let C : Q × Fin 2 → Finset V := fun qt =>
    D.filter fun a => G.Adj a qt.1.1
  have hHall : ∀ s : Finset (Q × Fin 2),
      s.card ≤ (s.biUnion C).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨qt, hqt⟩ := hs
      have hsDomain : s.card ≤ Fintype.card (Q × Fin 2) :=
        Finset.card_le_univ s
      have hdomain : Fintype.card (Q × Fin 2) = 2 * Q.card := by
        simp [Nat.mul_comm]
      have hCcard : (C qt).card = degreeIn G D qt.1.1 := by
        simp [C, degreeIn, SimpleGraph.adj_comm]
      calc
        s.card ≤ 2 * Q.card := by simpa [hdomain] using hsDomain
        _ ≤ (C qt).card := by rw [hCcard]; exact hmany qt.1.1 qt.1.2
        _ ≤ (s.biUnion C).card := by
          apply Finset.card_le_card
          exact Finset.subset_biUnion_of_mem C hqt
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hfInj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' C).mp hHall
  let F' : ShortAbsorbableFamily (J := J ⊕ Q) G B :=
    { start := fun j => match j with
        | Sum.inl i => F.start i
        | Sum.inr q => q.1
      finish := fun j => match j with
        | Sum.inl i => F.finish i
        | Sum.inr q => q.1
      path := fun j => match j with
        | Sum.inl i => F.path i
        | Sum.inr _ => SimpleGraph.Walk.nil
      isPath := by
        intro j
        cases j with
        | inl i => exact F.isPath i
        | inr q => simp
      length_le_two := by
        intro j
        cases j with
        | inl i => exact F.length_le_two i
        | inr q => simp
      attach := fun qt => match qt.1 with
        | Sum.inl i => F.attach (i, qt.2)
        | Sum.inr q => f (q, qt.2)
      attach_mem := by
        intro qt
        rcases qt with ⟨j, t⟩
        cases j with
        | inl i => exact F.attach_mem (i, t)
        | inr q => exact (Finset.mem_sdiff.mp
            (hDB (Finset.mem_filter.mp (hfmem (q, t))).1)).1
      attach_injective := by
        rintro ⟨i, t⟩ ⟨j, u⟩ hij
        cases i with
        | inl i =>
            cases j with
            | inl j =>
                change F.attach (i, t) = F.attach (j, u) at hij
                have hp := F.attach_injective hij
                exact Prod.ext
                  (congrArg (fun z : J × Fin 2 => Sum.inl z.1) hp)
                  (congrArg (fun z : J × Fin 2 => z.2) hp)
            | inr q =>
                exfalso
                change F.attach (i, t) = f (q, u) at hij
                have hOld : F.attach (i, t) ∈ F.attachments :=
                  Finset.mem_image.mpr ⟨(i, t), Finset.mem_univ _, rfl⟩
                have hNew := hDB (Finset.mem_filter.mp (hfmem (q, u))).1
                exact (Finset.mem_sdiff.mp hNew).2 (hij ▸ hOld)
        | inr q =>
            cases j with
            | inl j =>
                exfalso
                change f (q, t) = F.attach (j, u) at hij
                have hOld : F.attach (j, u) ∈ F.attachments :=
                  Finset.mem_image.mpr ⟨(j, u), Finset.mem_univ _, rfl⟩
                have hNew := hDB (Finset.mem_filter.mp (hfmem (q, t))).1
                exact (Finset.mem_sdiff.mp hNew).2 (hij.symm ▸ hOld)
            | inr r =>
                change f (q, t) = f (r, u) at hij
                have hp := hfInj hij
                exact Prod.ext
                  (congrArg (fun z : Q × Fin 2 => Sum.inr z.1) hp)
                  (congrArg (fun z : Q × Fin 2 => z.2) hp)
      start_adj := by
        intro j
        cases j with
        | inl i => exact F.start_adj i
        | inr q =>
            exact (Finset.mem_filter.mp (hfmem (q, 0))).2
      finish_adj := by
        intro j
        cases j with
        | inl i => exact F.finish_adj i
        | inr q =>
            exact (Finset.mem_filter.mp (hfmem (q, 1))).2.symm
      support_outside := by
        intro j v hv hvB
        cases j with
        | inl i => exact F.support_outside i v hv hvB
        | inr q =>
            have hvq : v = q.1 := by simpa using hv
            subst v
            exact hQoutside q.1 q.2 (Finset.mem_union_left _ hvB)
      support_disjoint := by
        intro i j hij
        cases i with
        | inl i =>
            cases j with
            | inl j => exact F.support_disjoint i j (fun h => hij (congrArg Sum.inl h))
            | inr q =>
                rw [List.disjoint_left]
                intro v hvi hvq
                have hvq' : v = q.1 := by simpa using hvq
                subst v
                apply hQoutside q.1 q.2
                exact Finset.mem_union_right _
                  (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hvi⟩)
        | inr q =>
            cases j with
            | inl j =>
                rw [List.disjoint_left]
                intro v hvq hvj
                have hvq' : v = q.1 := by simpa using hvq
                subst v
                apply hQoutside q.1 q.2
                exact Finset.mem_union_right _
                  (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using hvj⟩)
            | inr r =>
                rw [List.disjoint_left]
                intro v hvq hvr
                have hvq' : v = q.1 := by simpa using hvq
                have hvr' : v = r.1 := by simpa using hvr
                subst v
                exact hij (congrArg Sum.inr (Subtype.ext hvr')) }
  have hvertices : F'.vertices = F.vertices ∪ Q := by
    ext v
    simp [ShortAbsorbableFamily.vertices, F']
  have hdisj : Disjoint F.vertices Q := by
    rw [Finset.disjoint_left]
    intro v hvF hvQ
    exact hQoutside v hvQ (Finset.mem_union_right _ hvF)
  have hverticesCard : F'.vertices.card = F.vertices.card + Q.card := by
    rw [hvertices, Finset.card_union_of_disjoint hdisj]
  apply F'.cycleGraph_isContained_of_dense hk
  · rw [hverticesCard]
    omega
  · rw [hverticesCard]
    exact hsmall
  · exact hdeg

/-- In the pruned source set, the outside neighbourhood of any surviving
source vertex is no larger than a maximum external matching.  Otherwise
Hall's theorem matches one more outside neighbour back into the pruned
source, contradicting maximality. -/
theorem outsideNeighbor_card_le_maximalExternalMatching_of_pruned
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X W D : Finset V} {M : Finset (V × V)} {t : ℕ} {v : V}
    (hDX : D ⊆ X) (hXW : X ⊆ W) (hvD : v ∈ D)
    (hM : IsExternalMatching G X W M)
    (hmax : ∀ N, IsExternalMatching G X W N → N.card ≤ M.card)
    (hMt : M.card ≤ t) (ht : 1 ≤ t)
    (hpruned : ∀ y : V, y ∉ W →
      degreeIn G D y = 0 ∨ 2 * t < degreeIn G D y) :
    (((Finset.univ : Finset V) \ W).filter fun y => G.Adj v y).card ≤
      M.card := by
  classical
  let Y : Finset V := ((Finset.univ : Finset V) \ W).filter fun y => G.Adj v y
  change Y.card ≤ M.card
  by_contra hnot
  have hQcardLe : M.card + 1 ≤ Y.card := by omega
  obtain ⟨Q, hQY, hQcard⟩ := Finset.exists_subset_card_eq hQcardLe
  let C : Q → Finset V := fun q => D.filter fun a => G.Adj a q.1
  have hCcard : ∀ q : Q, M.card + 1 ≤ (C q).card := by
    intro q
    have hqY : q.1 ∈ Y := hQY q.2
    have hqOut : q.1 ∉ W := (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hqY).1).2
    have hvq : G.Adj v q.1 := (Finset.mem_filter.mp hqY).2
    have hpos : degreeIn G D q.1 ≠ 0 := by
      intro hz
      have hvFilter : v ∈ D.filter fun a => G.Adj q.1 a :=
        Finset.mem_filter.mpr ⟨hvD, hvq.symm⟩
      have : 0 < degreeIn G D q.1 := by
        rw [degreeIn]
        exact Finset.card_pos.mpr ⟨v, hvFilter⟩
      omega
    have hlarge := (hpruned q.1 hqOut).resolve_left hpos
    have hEq : (C q).card = degreeIn G D q.1 := by
      simp [C, degreeIn, SimpleGraph.adj_comm]
    rw [hEq]
    omega
  have hHall : ∀ s : Finset Q, s.card ≤ (s.biUnion C).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨q, hq⟩ := hs
      calc
        s.card ≤ Fintype.card Q := Finset.card_le_univ s
        _ = Q.card := Fintype.card_coe Q
        _ = M.card + 1 := hQcard
        _ ≤ (C q).card := hCcard q
        _ ≤ (s.biUnion C).card := Finset.card_le_card
          (Finset.subset_biUnion_of_mem C hq)
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hf, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' C).mp hHall
  let edge : Q → V × V := fun q => (f q, q.1)
  let N : Finset (V × V) := (Finset.univ : Finset Q).image edge
  have hedgeInj : Function.Injective edge := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg Prod.snd hqr
  have hNcard : N.card = M.card + 1 := by
    change ((Finset.univ : Finset Q).image edge).card = M.card + 1
    rw [Finset.card_image_of_injective _ hedgeInj]
    simpa using hQcard
  have hN : IsExternalMatching G X W N := by
    refine ⟨?_, ?_⟩
    · constructor
      · intro e he
        rcases Finset.mem_image.mp he with ⟨q, _hq, rfl⟩
        exact (Finset.mem_filter.mp (hfmem q)).2
      · intro e he r hr her
        rcases Finset.mem_image.mp he with ⟨q, _hq, rfl⟩
        rcases Finset.mem_image.mp hr with ⟨s, _hs, rfl⟩
        have hqs : q ≠ s := fun h => her (congrArg edge h)
        have hff : f q ≠ f s := hf.ne hqs
        have hqq : q.1 ≠ s.1 := fun h => hqs (Subtype.ext h)
        have hfW : f q ∈ W := hXW (hDX (Finset.mem_filter.mp (hfmem q)).1)
        have hfsW : f s ∈ W := hXW (hDX (Finset.mem_filter.mp (hfmem s)).1)
        have hqOut : q.1 ∉ W := (Finset.mem_sdiff.mp
          (Finset.mem_filter.mp (hQY q.2)).1).2
        have hsOut : s.1 ∉ W := (Finset.mem_sdiff.mp
          (Finset.mem_filter.mp (hQY s.2)).1).2
        refine ⟨hff, ?_, ?_, hqq⟩
        · change f q ≠ s.1
          intro h
          exact hsOut (h ▸ hfW)
        · change q.1 ≠ f s
          intro h
          exact hqOut (h ▸ hfsW)
    · intro e he
      rcases Finset.mem_image.mp he with ⟨q, _hq, rfl⟩
      exact ⟨hDX (Finset.mem_filter.mp (hfmem q)).1,
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hQY q.2)).1).2⟩
  have := hmax N hN
  rw [hNcard] at this
  omega

/-- Deterministic stability cleanup.  Starting from a sufficiently accurate
anticomplete seed family, discard the few high-deficit blocks and trim the
few low-degree vertices from every remaining block.  The resulting family
is nonempty, anticomplete, bounded by `k-1`, internally Dirac-dense, and
covers all but at most `1/64` of the ambient vertices. -/
theorem exists_dense_stable_family_of_seed_fraction
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k n : ℕ} {Q : Finset (Finset V)}
    (hk : 8388609 ≤ k) (hn : 3 ≤ n)
    (horder : Fintype.card V = (k - 1) * (n - 1) + 1)
    (hfree : G.IndepSetFree n)
    (hQne : ∀ A ∈ Q, A.Nonempty)
    (hQdisj : DisjointFinsetFamily Q)
    (hQanti : PairwiseAnticomplete G Q)
    (hQcard : ∀ A ∈ Q, A.card ≤ k - 1)
    (hQcover : 16777216 *
      ((Finset.univ : Finset V) \ Q.biUnion id).card ≤ Fintype.card V) :
    ∃ R : Finset (Finset V), R.Nonempty ∧
      (∀ B ∈ R, B.Nonempty) ∧ DisjointFinsetFamily R ∧
      PairwiseAnticomplete G R ∧
      (∀ B ∈ R, B.card ≤ k - 1) ∧
      (∀ B ∈ R, ∀ v ∈ B,
        k ≤ 2 * degreeIn G B v ∧
        123 * (k - 1) ≤ 128 * degreeIn G B v) ∧
      64 * ((Finset.univ : Finset V) \ R.biUnion id).card ≤
        Fintype.card V := by
  classical
  let Good : Finset (Finset V) := Q.filter fun A => LowDeficitBlock G k A
  let Bad : Finset (Finset V) := Q.filter fun A => ¬ LowDeficitBlock G k A
  let trim : Finset V → Finset V := fun A => denseTrim G k A
  let R : Finset (Finset V) := Good.image trim
  let U : Finset V := Q.biUnion id
  let L₀ : Finset V := (Finset.univ : Finset V) \ U
  let ZU : Finset V := Good.biUnion fun A => lowInternalDegreeVertices G k A
  let L : Finset V := (Finset.univ : Finset V) \ R.biUnion id
  have hGoodSub : Good ⊆ Q := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ Q := Finset.filter_subset _ _
  have htrimProp : ∀ A ∈ Good,
      (trim A).Nonempty ∧ trim A ⊆ A ∧ (trim A).card ≤ k - 1 ∧
        ∀ v ∈ trim A,
          k ≤ 2 * degreeIn G (trim A) v ∧
          123 * (k - 1) ≤ 128 * degreeIn G (trim A) v := by
    intro A hA
    have hAQ : A ∈ Q := hGoodSub hA
    have hgood : LowDeficitBlock G k A := (Finset.mem_filter.mp hA).2
    simpa [trim] using denseTrim_properties G (by omega)
      (hQne A hAQ) (hQcard A hAQ) hgood
  have hGoodDisj : (Good : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    exact hQdisj A (hGoodSub (by simpa using hA))
      B (hGoodSub (by simpa using hB)) hAB
  have hZDisj : (Good : Set (Finset V)).PairwiseDisjoint
      (fun A => lowInternalDegreeVertices G k A) := by
    intro A hA B hB hAB
    exact (hGoodDisj hA hB hAB).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hmass := blockDeficit_mass_small_of_extremal_fraction_coverage
    G hk hn horder hfree hQdisj hQanti hQcard hQcover
  have hBadSmall : 256 * (Bad.biUnion id).card ≤ U.card := by
    simpa [Bad, U] using highDeficit_seed_union_small G (by omega) hQdisj hmass
  have hZmass : 128 * ZU.card ≤ U.card := by
    calc
      128 * ZU.card =
          ∑ A ∈ Good, 128 * (lowInternalDegreeVertices G k A).card := by
        rw [show ZU.card =
            ∑ A ∈ Good, (lowInternalDegreeVertices G k A).card by
          simpa [ZU] using Finset.card_biUnion hZDisj,
          Finset.mul_sum]
      _ ≤ ∑ A ∈ Good, A.card := by
        apply Finset.sum_le_sum
        intro A hA
        exact oneHundredTwentyEight_mul_lowInternalDegreeVertices_card_le
          G (by omega) (hQcard A (hGoodSub hA))
            (Finset.mem_filter.mp hA).2
      _ = (Good.biUnion id).card := by
        simpa only [id_eq] using (Finset.card_biUnion hGoodDisj).symm
      _ ≤ U.card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_biUnion.mp hv with ⟨A, hA, hvA⟩
        exact Finset.mem_biUnion.mpr ⟨A, hGoodSub hA, hvA⟩
  have hLsub : L ⊆ L₀ ∪ Bad.biUnion id ∪ ZU := by
    intro v hvL
    have hvNotR : v ∉ R.biUnion id := (Finset.mem_sdiff.mp hvL).2
    by_cases hvU : v ∈ U
    · rcases Finset.mem_biUnion.mp hvU with ⟨A, hAQ, hvA⟩
      by_cases hgood : LowDeficitBlock G k A
      · have hAGood : A ∈ Good := Finset.mem_filter.mpr ⟨hAQ, hgood⟩
        by_cases hvZ : v ∈ lowInternalDegreeVertices G k A
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨A, hAGood, hvZ⟩)
        · have hvTrim : v ∈ trim A := by
            exact Finset.mem_sdiff.mpr ⟨hvA, hvZ⟩
          exfalso
          apply hvNotR
          exact Finset.mem_biUnion.mpr
            ⟨trim A, Finset.mem_image.mpr ⟨A, hAGood, rfl⟩, hvTrim⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr
            ⟨A, Finset.mem_filter.mpr ⟨hAQ, hgood⟩, hvA⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvU⟩))
  have hLcard : L.card ≤ L₀.card + (Bad.biUnion id).card + ZU.card := by
    calc
      L.card ≤ (L₀ ∪ Bad.biUnion id ∪ ZU).card := Finset.card_le_card hLsub
      _ ≤ (L₀ ∪ Bad.biUnion id).card + ZU.card := Finset.card_union_le _ _
      _ ≤ L₀.card + (Bad.biUnion id).card + ZU.card := by
        gcongr
        exact Finset.card_union_le _ _
  have hUcard : U.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ U)
  have hL₀scaled : 16777216 * L₀.card ≤ Fintype.card V := by
    simpa [L₀, U] using hQcover
  have hBadScaled : 256 * (Bad.biUnion id).card ≤ Fintype.card V :=
    hBadSmall.trans hUcard
  have hZScaled : 128 * ZU.card ≤ Fintype.card V := hZmass.trans hUcard
  have hLscaled : 64 * L.card ≤ Fintype.card V := by
    nlinarith
  have hRneBlocks : ∀ B ∈ R, B.Nonempty := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    exact (htrimProp A hA).1
  have hRnonempty : R.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    have hLall : L.card = Fintype.card V := by simp [L, hnot]
    have hVpos : 0 < Fintype.card V := by rw [horder]; positivity
    rw [hLall] at hLscaled
    nlinarith
  have hRdisj : DisjointFinsetFamily R := by
    intro B hB C hC hBC
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
    have hAD : A ≠ D := by
      intro h
      subst D
      exact hBC rfl
    exact (hGoodDisj (by simpa using hA) (by simpa using hD) hAD).mono
      (htrimProp A hA).2.1 (htrimProp D hD).2.1
  have hRanti : PairwiseAnticomplete G R := by
    intro B hB C hC hBC b hb c hc hbc
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
    have hAD : A ≠ D := by
      intro h
      subst D
      exact hBC rfl
    exact hQanti A (hGoodSub hA) D (hGoodSub hD) hAD
      b ((htrimProp A hA).2.1 hb) c ((htrimProp D hD).2.1 hc) hbc
  refine ⟨R, hRnonempty, hRneBlocks, hRdisj, hRanti, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    exact (htrimProp A hA).2.2.1
  · intro B hB v hv
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    exact (htrimProp A hA).2.2.2 v hv
  · simpa [L] using hLscaled

/-- Unconditional eventual KLS stability output obtained from the full hub,
separator, deficit-filtering, and dense-trimming development. -/
theorem eventually_exists_dense_stable_family :
    ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, 3 ≤ n → n ≤ k →
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = (k - 1) * (n - 1) + 1 →
        G.IndepSetFree n →
        ¬ _root_.SimpleGraph.cycleGraph k ⊑ G →
        ∃ R : Finset (Finset V), R.Nonempty ∧
          (∀ B ∈ R, B.Nonempty) ∧ DisjointFinsetFamily R ∧
          PairwiseAnticomplete G R ∧
          (∀ B ∈ R, B.card ≤ k - 1) ∧
          (∀ B ∈ R, ∀ v ∈ B,
            k ≤ 2 * degreeIn G B v ∧
            123 * (k - 1) ≤ 128 * degreeIn G B v) ∧
          64 * ((Finset.univ : Finset V) \ R.biUnion id).card ≤
            Fintype.card V := by
  filter_upwards
    [eventually_exists_anticomplete_seed_family_covering_fraction
      16777216 (by norm_num),
     eventually_ge_atTop 8388609]
      with k hseed hk
  intro n hn hnk V instV G instG horder hfree hcycle
  obtain ⟨Q, hQne, hQdisj, hQanti, hQcard, hQcover⟩ :=
    hseed n hn hnk G horder hfree hcycle
  exact exists_dense_stable_family_of_seed_fraction
    G hk hn horder hfree hQne hQdisj hQanti hQcard hQcover

/-! ## Final absorption: directed cuts and enlarged-block routing -/

noncomputable def directedCutLabels
    {ι : Type*} [Fintype ι] (E : Finset (ι × ι)) (S : Finset ι) :
    Finset (ι × ι) :=
  E.filter fun e => e.1 ∈ S ∧ e.2 ∉ S

/-- Every finite loopless directed graph has an oriented cut containing at
least one quarter of its arcs.  We choose a maximum cut.  Complementing the
cut bounds the reverse arcs, while flipping one vertex at a time and summing
the resulting inequalities bounds the two classes of uncut arcs. -/
theorem exists_directedCutLabels_quarter
    {ι : Type*} [Fintype ι] (E : Finset (ι × ι))
    (hloop : ∀ e ∈ E, e.1 ≠ e.2) :
    ∃ S : Finset ι,
      E.card ≤ 4 * (directedCutLabels E S).card := by
  classical
  obtain ⟨S, _hSuniv, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset ι))
      (fun T => (directedCutLabels E T).card) ⟨∅, Finset.mem_univ _⟩
  let C : Finset (ι × ι) := directedCutLabels E S
  let D : Finset (ι × ι) := E.filter fun e => e.1 ∉ S ∧ e.2 ∈ S
  let I : Finset (ι × ι) := E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S
  let O : Finset (ι × ι) := E.filter fun e => e.1 ∉ S ∧ e.2 ∉ S
  have hmax' (T : Finset ι) :
      (directedCutLabels E T).card ≤ C.card := by
    simpa [C] using hmax T (Finset.mem_univ _)
  have hpartition : E.card = C.card + D.card + I.card + O.card := by
    have hsplit₁ := Finset.card_filter_add_card_filter_not
      (s := E) (fun e : ι × ι => e.1 ∈ S)
    have hsplit₂ := Finset.card_filter_add_card_filter_not
      (s := E.filter fun e : ι × ι => e.1 ∈ S) (fun e => e.2 ∉ S)
    have hsplit₃ := Finset.card_filter_add_card_filter_not
      (s := E.filter fun e : ι × ι => e.1 ∉ S) (fun e => e.2 ∈ S)
    simp only [Finset.filter_filter, not_not] at hsplit₁ hsplit₂ hsplit₃
    change E.card = C.card + D.card + I.card + O.card
    dsimp [C, D, I, O, directedCutLabels]
    omega
  have hD : D.card ≤ C.card := by
    have hcompl : directedCutLabels E (Finset.univ \ S) = D := by
      ext e
      simp [directedCutLabels, D]
    rw [← hcompl]
    exact hmax' (Finset.univ \ S)
  have hOlocal : ∀ v ∉ S,
      (O.filter fun e => e.1 = v).card ≤
        (C.filter fun e => e.2 = v).card := by
    intro v hvS
    let gain : Finset (ι × ι) := O.filter fun e => e.1 = v
    let lost : Finset (ι × ι) := C.filter fun e => e.2 = v
    have hlostSub : lost ⊆ C := Finset.filter_subset _ _
    have hgainDisj : Disjoint (C \ lost) gain := by
      rw [Finset.disjoint_left]
      intro e heC heG
      have heG' := Finset.mem_filter.mp heG
      have heO := Finset.mem_filter.mp heG'.1
      exact heO.2.1 (Finset.mem_filter.mp (Finset.mem_sdiff.mp heC).1).2.1
    have hcut : directedCutLabels E (insert v S) = (C \ lost) ∪ gain := by
      ext e
      have hCmem : e ∈ C ↔ e ∈ E ∧ e.1 ∈ S ∧ e.2 ∉ S := by
        simp [C, directedCutLabels]
      have hOmem : e ∈ O ↔ e ∈ E ∧ e.1 ∉ S ∧ e.2 ∉ S := by
        simp [O]
      have hLostmem : e ∈ lost ↔ e ∈ C ∧ e.2 = v := by simp [lost]
      have hGainmem : e ∈ gain ↔ e ∈ O ∧ e.1 = v := by simp [gain]
      rw [Finset.mem_union, Finset.mem_sdiff, hLostmem, hGainmem,
        hCmem, hOmem]
      simp only [directedCutLabels, Finset.mem_filter, Finset.mem_insert, not_or]
      change (e ∈ E ∧ (e.1 = v ∨ e.1 ∈ S) ∧
          (e.2 ≠ v ∧ e.2 ∉ S)) ↔ _
      constructor
      · rintro ⟨heE, heSrc, heDst⟩
        rcases heSrc with heSrcEq | heSrcS
        · right
          have heSrcNot : e.1 ∉ S := by simpa [heSrcEq] using hvS
          exact ⟨⟨heE, heSrcNot, heDst.2⟩, heSrcEq⟩
        · left
          refine ⟨⟨heE, heSrcS, heDst.2⟩, ?_⟩
          exact fun heLost => heDst.1 heLost.2
      · rintro (⟨heC, heNotLost⟩ | ⟨heO, heSrcEq⟩)
        · refine ⟨heC.1, Or.inr heC.2.1, ?_⟩
          exact ⟨fun he => heNotLost ⟨heC, he⟩, heC.2.2⟩
        · refine ⟨heO.1, Or.inl heSrcEq, ?_⟩
          refine ⟨?_, heO.2.2⟩
          intro heDstEq
          exact hloop e heO.1 (heSrcEq.trans heDstEq.symm)
    have hcard : (directedCutLabels E (insert v S)).card =
        C.card - lost.card + gain.card := by
      rw [hcut, Finset.card_union_of_disjoint hgainDisj,
        Finset.card_sdiff_of_subset hlostSub]
    have hle := hmax' (insert v S)
    rw [hcard] at hle
    simpa [gain, lost] using (show gain.card ≤ lost.card by omega)
  have hIlocal : ∀ v ∈ S,
      (I.filter fun e => e.2 = v).card ≤
        (C.filter fun e => e.1 = v).card := by
    intro v hvS
    let gain : Finset (ι × ι) := I.filter fun e => e.2 = v
    let lost : Finset (ι × ι) := C.filter fun e => e.1 = v
    have hlostSub : lost ⊆ C := Finset.filter_subset _ _
    have hgainDisj : Disjoint (C \ lost) gain := by
      rw [Finset.disjoint_left]
      intro e heC heG
      have heG' := Finset.mem_filter.mp heG
      have heI := Finset.mem_filter.mp heG'.1
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp heC).1).2.2 heI.2.2
    have hcut : directedCutLabels E (S.erase v) = (C \ lost) ∪ gain := by
      ext e
      have hCmem : e ∈ C ↔ e ∈ E ∧ e.1 ∈ S ∧ e.2 ∉ S := by
        simp [C, directedCutLabels]
      have hImem : e ∈ I ↔ e ∈ E ∧ e.1 ∈ S ∧ e.2 ∈ S := by
        simp [I]
      have hLostmem : e ∈ lost ↔ e ∈ C ∧ e.1 = v := by simp [lost]
      have hGainmem : e ∈ gain ↔ e ∈ I ∧ e.2 = v := by simp [gain]
      rw [Finset.mem_union, Finset.mem_sdiff, hLostmem, hGainmem,
        hCmem, hImem]
      simp only [directedCutLabels, Finset.mem_filter, Finset.mem_erase]
      change (e ∈ E ∧ (e.1 ≠ v ∧ e.1 ∈ S) ∧
          ¬ (e.2 ≠ v ∧ e.2 ∈ S)) ↔ _
      constructor
      · rintro ⟨heE, ⟨heSrcNe, heSrcS⟩, heDst⟩
        by_cases heDstS : e.2 ∈ S
        · right
          have heDstEq : e.2 = v := by
            by_contra heDstNe
            exact heDst ⟨heDstNe, heDstS⟩
          exact ⟨⟨heE, heSrcS, heDstS⟩, heDstEq⟩
        · left
          refine ⟨⟨heE, heSrcS, heDstS⟩, ?_⟩
          exact fun heLost => heSrcNe heLost.2
      · rintro (⟨heC, heNotLost⟩ | ⟨heI, heDstEq⟩)
        · refine ⟨heC.1, ⟨?_, heC.2.1⟩, ?_⟩
          · exact fun he => heNotLost ⟨heC, he⟩
          · exact fun he => heC.2.2 he.2
        · refine ⟨heI.1, ⟨?_, heI.2.1⟩, ?_⟩
          · intro heSrcEq
            exact hloop e heI.1 (heSrcEq.trans heDstEq.symm)
          · intro heErase
            exact heErase.1 heDstEq
    have hcard : (directedCutLabels E (S.erase v)).card =
        C.card - lost.card + gain.card := by
      rw [hcut, Finset.card_union_of_disjoint hgainDisj,
        Finset.card_sdiff_of_subset hlostSub]
    have hle := hmax' (S.erase v)
    rw [hcard] at hle
    simpa [gain, lost] using (show gain.card ≤ lost.card by omega)
  have hO : O.card ≤ C.card := by
    have hOsum : O.card = ∑ v ∈ (Finset.univ \ S),
        (O.filter fun e => e.1 = v).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := O) (t := Finset.univ \ S) (f := Prod.fst)]
      intro e he
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp he).2.1⟩
    have hCsum : C.card = ∑ v ∈ (Finset.univ \ S),
        (C.filter fun e => e.2 = v).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := C) (t := Finset.univ \ S) (f := Prod.snd)]
      intro e he
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp he).2.2⟩
    rw [hOsum, hCsum]
    exact Finset.sum_le_sum fun v hv => hOlocal v (Finset.mem_sdiff.mp hv).2
  have hI : I.card ≤ C.card := by
    have hIsum : I.card = ∑ v ∈ S,
        (I.filter fun e => e.2 = v).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := I) (t := S) (f := Prod.snd)]
      intro e he
      exact (Finset.mem_filter.mp he).2.2
    have hCsum : C.card = ∑ v ∈ S,
        (C.filter fun e => e.1 = v).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := C) (t := S) (f := Prod.fst)]
      intro e he
      exact (Finset.mem_filter.mp he).2.1
    rw [hIsum, hCsum]
    exact Finset.sum_le_sum fun v hv => hIlocal v hv
  refine ⟨S, ?_⟩
  change E.card ≤ 4 * C.card
  rw [hpartition]
  calc
    C.card + D.card + I.card + O.card ≤
        C.card + C.card + C.card + C.card := by omega
    _ = 4 * C.card := by omega

/-- An edge from an unused, remainder-separated attachment can only end in
another enlarged block.  It cannot end in an original different block by
anticompleteness, nor in the final remainder by the definition of
`remainderAttachments`; hence it ends on a cleanup path. -/
theorem exists_other_enlarged_block_of_external_cleanup_edge
    {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : ι → Finset V) (L : Finset V)
    {M : Finset (CleanupMove ι V)}
    (hM : IsCleanupFamily G B L M)
    (hBL : ∀ i, Disjoint (B i) L)
    (hcover : L = (Finset.univ : Finset V) \
      (Finset.univ : Finset ι).biUnion B)
    (hanti : ∀ i j, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y)
    {i : ι} {x y : V}
    (hx : x ∈ (B i \ cleanupAttachmentsAt M i) \
      remainderAttachments G (fun j => B j \ cleanupAttachmentsAt M j)
        (L \ cleanupAbsorbed M) i)
    (hy : y ∉ (hM.absorbableFamilyAt hBL i).enlarged)
    (hxy : G.Adj x y) :
    ∃ j, j ≠ i ∧ y ∈ (hM.absorbableFamilyAt hBL j).enlarged := by
  classical
  let A : ι → Finset V := fun j => B j \ cleanupAttachmentsAt M j
  let R : Finset V := L \ cleanupAbsorbed M
  have hxA : x ∈ A i := (Finset.mem_sdiff.mp hx).1
  have hxB : x ∈ B i := Finset.sdiff_subset hxA
  have hxNotAttach : x ∉ remainderAttachments G A R i :=
    (Finset.mem_sdiff.mp hx).2
  by_cases hyL : y ∈ L
  · by_cases hyR : y ∈ R
    · exfalso
      apply (Finset.mem_sdiff.mp hx).2
      simp only [remainderAttachments, Finset.mem_filter]
      exact ⟨(Finset.mem_sdiff.mp hx).1, y, hyR, hxy⟩
    · have hyAbs : y ∈ cleanupAbsorbed M := by
        exact by
          by_contra hyNotAbs
          exact hyR (Finset.mem_sdiff.mpr ⟨hyL, hyNotAbs⟩)
      rcases Finset.mem_biUnion.mp hyAbs with ⟨c, hcM, hyc⟩
      let j : ι := c.block
      have hyAt : y ∈ cleanupAbsorbedAt M j :=
        Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_filter.mpr ⟨hcM, rfl⟩, hyc⟩
      have hyVertices : y ∈ (hM.absorbableFamilyAt hBL j).vertices := by
        rw [hM.absorbableFamilyAt_vertices hBL j]
        exact hyAt
      have hji : j ≠ i := by
        intro h
        change c.block = i at h
        dsimp [j] at hyVertices
        apply hy
        change y ∈ B i ∪ (hM.absorbableFamilyAt hBL i).vertices
        rw [← h]
        exact Finset.mem_union.mpr (Or.inr hyVertices)
      exact ⟨j, hji, Finset.mem_union.mpr (Or.inr hyVertices)⟩
  · have hyUnion : y ∈ (Finset.univ : Finset ι).biUnion B := by
      have : y ∉ (Finset.univ : Finset V) \
          (Finset.univ : Finset ι).biUnion B := by simpa [← hcover] using hyL
      exact by
        by_contra hnot
        exact this (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
    rcases Finset.mem_biUnion.mp hyUnion with ⟨j, _hj, hyB⟩
    by_cases hji : j = i
    · subst j
      exact (hy (Finset.mem_union_left _ hyB)).elim
    · exact (hanti i j (Ne.symm hji) x hxB y hyB hxy).elim

/-- KLS Lemma 6.3 in the form used below.  If more than half of a family of
dense blocks carried large external matchings, collapse the matching edges
to ordered block labels.  A label has multiplicity at most three by the
two-block absorption lemma.  A quarter-sized directed cut therefore has
large edge density; a short cycle in its bipartite incidence graph lifts,
through the enlarged target blocks, to an exact `C_k`. -/
theorem exists_small_externalMatching_in_dense_family
    {V ι : Type*} {J : ι → Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    [∀ i : ι, Fintype (J i)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k t δ : ℕ}
    (B X : ι → Finset V)
    (F : ∀ i, ShortAbsorbableFamily (J := J i) G (B i))
    (T : Finset ι) (M : ι → Finset (V × V))
    (hk : 1000 ≤ k)
    (hThalf : Fintype.card ι < 2 * T.card)
    (hBne : ∀ i, (B i).Nonempty)
    (hBcard : ∀ i, (B i).card ≤ k - 1)
    (hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hanti : ∀ i j, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y)
    (hBdeg : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v)
    (hBWdisj : ∀ i j, i ≠ j → Disjoint (B i) (F j).enlarged)
    (hWdisj : ∀ i j, i ≠ j →
      Disjoint (F i).enlarged (F j).enlarged)
    (hXB : ∀ i, X i ⊆ B i)
    (hM : ∀ i ∈ T, IsExternalMatching G (X i) (F i).enlarged (M i))
    (htarget : ∀ i ∈ T, ∀ e ∈ M i,
      ∃ j, j ≠ i ∧ e.2 ∈ (F j).enlarged)
    (hscale : 192 * δ ≤ t)
    (hmargin : 2 * ((8 * (4 + 1)) * 2 *
      (Nat.log 2 (2 * Fintype.card ι) + 1)) < δ)
    (hroom : 9 * (40 + 2 * Nat.log 2 (2 * Fintype.card ι)) ≤ k)
    (hcycle : ¬ cycleGraph k ⊑ G) :
    ∃ i ∈ T, (M i).card ≤ t := by
  classical
  by_contra hnone
  push_neg at hnone
  let R : Finset (Σ _i : ι, V × V) := T.sigma M
  let D := {d // d ∈ R}
  let target : D → ι := fun d =>
    Classical.choose (htarget d.1.1
      (Finset.mem_sigma.mp d.2).1 d.1.2 (Finset.mem_sigma.mp d.2).2)
  have htargetNe : ∀ d : D, target d ≠ d.1.1 := by
    intro d
    exact (Classical.choose_spec (htarget d.1.1
      (Finset.mem_sigma.mp d.2).1 d.1.2
      (Finset.mem_sigma.mp d.2).2)).1
  have htargetMem : ∀ d : D, d.1.2.2 ∈ (F (target d)).enlarged := by
    intro d
    exact (Classical.choose_spec (htarget d.1.1
      (Finset.mem_sigma.mp d.2).1 d.1.2
      (Finset.mem_sigma.mp d.2).2)).2
  let label : D → ι × ι := fun d => (d.1.1, target d)
  let E : Finset (ι × ι) := (Finset.univ : Finset D).image label
  have hloop : ∀ e ∈ E, e.1 ≠ e.2 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨d, _hd, rfl⟩
    simpa [label] using (htargetNe d).symm
  have hfiber : ∀ a ∈ E,
      ((Finset.univ : Finset D).filter fun d => label d = a).card ≤ 3 := by
    intro a haE
    let Z : Finset D := (Finset.univ : Finset D).filter fun d => label d = a
    let Q : Finset (V × V) := Z.image fun d => d.1.2
    have hZsource : ∀ d ∈ Z, d.1.1 = a.1 := by
      intro d hd
      exact congrArg Prod.fst (Finset.mem_filter.mp hd).2
    have hZtarget : ∀ d ∈ Z, target d = a.2 := by
      intro d hd
      exact congrArg Prod.snd (Finset.mem_filter.mp hd).2
    have hQcard : Q.card = Z.card := by
      apply Finset.card_image_of_injOn
      intro d hd e he hde
      apply Subtype.ext
      rw [Sigma.ext_iff, heq_eq_eq]
      exact ⟨(hZsource d (by simpa [Z] using hd)).trans
          (hZsource e (by simpa [Z] using he)).symm, hde⟩
    have haSourceT : a.1 ∈ T := by
      rcases Finset.mem_image.mp haE with ⟨d, _hd, hda⟩
      rw [← hda]
      exact (Finset.mem_sigma.mp d.2).1
    have hQsub : Q ⊆ M a.1 := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨d, hdZ, rfl⟩
      have hdM := (Finset.mem_sigma.mp d.2).2
      simpa [hZsource d hdZ] using hdM
    have hQorient : IsOrientedCrossFamily G (X a.1) (F a.2).enlarged Q := by
      refine ⟨?_, ?_⟩
      · constructor
        · intro e he
          exact (hM a.1 haSourceT).1.1 e (hQsub he)
        · intro e he f hf hef
          exact (hM a.1 haSourceT).1.2 e (hQsub he) f (hQsub hf) hef
      · intro e he
        rcases Finset.mem_image.mp he with ⟨d, hdZ, rfl⟩
        have hdM := (Finset.mem_sigma.mp d.2).2
        have hsrc := (hM d.1.1 (Finset.mem_sigma.mp d.2).1).2 d.1.2 hdM |>.1
        refine ⟨?_, ?_⟩
        · simpa [hZsource d hdZ] using hsrc
        · have ht := hZtarget d hdZ
          rw [← ht]
          exact htargetMem d
    have haNe : a.1 ≠ a.2 := by
      rcases Finset.mem_image.mp haE with ⟨d, _hd, hda⟩
      rw [← hda]
      simpa [label] using (htargetNe d).symm
    have hQthree := orientedCrossFamily_card_le_three_of_cycleFree
      G hk (F a.2) (hBne a.1) (hBne a.2)
      (hBcard a.1) (hBcard a.2) (hBdisj a.1 a.2 haNe)
      (hBWdisj a.1 a.2 haNe) (hanti a.1 a.2 haNe)
      (hBdeg a.1) (hBdeg a.2) (hXB a.1) hQorient hcycle
    simpa [hQcard, Z, Q] using hQthree
  have hRle : R.card ≤ 3 * E.card := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset D)) (t := E) (f := label) (by
        intro d _hd
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
    have hle : (∑ a ∈ E,
        ((Finset.univ : Finset D).filter fun d => label d = a).card) ≤
        ∑ _a ∈ E, 3 := by
      apply Finset.sum_le_sum
      intro a ha
      exact hfiber a ha
    have hDcard : Fintype.card D = R.card := by simp [D]
    rw [← hDcard]
    rw [show Fintype.card D = (Finset.univ : Finset D).card by simp, hsum]
    calc
      (∑ a ∈ E,
          ((Finset.univ : Finset D).filter fun d => label d = a).card) ≤
          ∑ _a ∈ E, 3 := hle
      _ = 3 * E.card := by simp [Nat.mul_comm]
  have hRcard : R.card = ∑ i ∈ T, (M i).card := by
    simpa [R] using Finset.card_sigma T M
  have hTt : T.card * t < R.card := by
    rw [hRcard]
    calc
      T.card * t = ∑ _i ∈ T, t := by simp
      _ < ∑ i ∈ T, (M i).card := by
        apply Finset.sum_lt_sum
        · intro i hi
          exact Nat.le_of_lt (hnone i hi)
        · obtain ⟨i, hi⟩ : T.Nonempty := by
            apply Finset.card_pos.mp
            have : 0 < Fintype.card ι := Fintype.card_pos
            omega
          exact ⟨i, hi, hnone i hi⟩
  obtain ⟨S, hcut⟩ := exists_directedCutLabels_quarter E hloop
  let C : Finset (ι × ι) := directedCutLabels E S
  have hsCut : Fintype.card ι * t < 24 * C.card := by
    have htwice : Fintype.card ι * t < 2 * R.card := by
      have hm := Nat.mul_lt_mul_of_pos_right hThalf (by
        have htpos : 0 < t := by
          have : 0 < δ := by omega
          omega
        exact htpos)
      calc
        Fintype.card ι * t < (2 * T.card) * t := hm
        _ = 2 * (T.card * t) := by ring
        _ < 2 * R.card := by omega
    calc
      Fintype.card ι * t < 2 * R.card := htwice
      _ ≤ 2 * (3 * E.card) := Nat.mul_le_mul_left 2 hRle
      _ ≤ 2 * (3 * (4 * C.card)) := by
        dsimp [C]
        gcongr
      _ = 24 * C.card := by ring
  let K : {a // a ∈ C} ↪ (ι × ι) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let H : SimpleGraph (ι ⊕ ι) :=
    SelectedCrossEdgeGraph (incidenceSelectedSystem K)
  have hHedge : H.edgeFinset.card = C.card := by
    calc
      H.edgeFinset.card = (incidenceSelectedSystem K).card := by
        apply card_edgeFinset_selectedCrossEdgeGraph
        exact incidenceSelectedSystem_valid K
      _ = Fintype.card {a // a ∈ C} := incidenceSelectedSystem_card K
      _ = C.card := Fintype.card_coe C
  have hCpos : C.Nonempty := by
    apply Finset.card_pos.mp
    have hspos : 0 < Fintype.card ι := Fintype.card_pos
    have htpos : 0 < t := by
      have : 0 < δ := by omega
      omega
    have hprod : 0 < Fintype.card ι * t := Nat.mul_pos hspos htpos
    omega
  have hHpos : H.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [hHedge]
    exact Finset.card_pos.mpr hCpos
  have hsupport : H.support.ncard ≤ 2 * Fintype.card ι := by
    calc
      H.support.ncard ≤ Fintype.card (ι ⊕ ι) := by
        simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card H.support
      _ = 2 * Fintype.card ι := by simp [two_mul]
  have hdense : (8 * δ) * H.support.ncard ≤ 2 * H.edgeFinset.card := by
    rw [hHedge]
    have hmain : 192 * δ * Fintype.card ι ≤
        Fintype.card ι * t := by
      calc
        192 * δ * Fintype.card ι = Fintype.card ι * (192 * δ) := by ring
        _ ≤ Fintype.card ι * t := Nat.mul_le_mul_left _ hscale
    have hstrict : 192 * δ * Fintype.card ι < 24 * C.card :=
      hmain.trans_lt hsCut
    calc
      (8 * δ) * H.support.ncard ≤
          (8 * δ) * (2 * Fintype.card ι) := by gcongr
      _ ≤ 2 * C.card := by
        ring_nf at hstrict ⊢
        omega
  have hlog : Nat.log 2 (Fintype.card (ι ⊕ ι)) =
      Nat.log 2 (2 * Fintype.card ι) := by simp [two_mul]
  obtain ⟨l, hl4, hlUpper, hlcopy⟩ :=
    exists_medium_cycle_of_edge_density H 2 4 δ (by omega)
      hHpos hdense
      (by simpa [Fintype.card_sum, two_mul] using hmargin)
  obtain ⟨q, hlq, hq, hdata⟩ :=
    exists_alternatingIncidenceCycleData K hl4 hlcopy
  let AData := Classical.choice hdata
  have hexact : ∀ i j,
      H.Adj (Sum.inl i) (Sum.inr j) →
      ∃ d : D, label d = (i, j) ∧ label d ∈ C := by
    intro i j hij
    obtain ⟨e, he, hdir | hrev⟩ := exists_selectedCrossEdge_of_graph_adj hij
    · rcases Finset.mem_map.mp he with ⟨c, _hc, rfl⟩
      have hcval : c.1 = (i, j) := by
        apply Prod.ext
        · exact Sum.inl.inj hdir.1
        · exact Sum.inr.inj hdir.2
      have hcE : c.1 ∈ E := (Finset.mem_filter.mp c.2).1
      rcases Finset.mem_image.mp hcE with ⟨d, _hd, hdc⟩
      exact ⟨d, hdc.trans hcval, by rw [hdc]; exact c.2⟩
    · rcases Finset.mem_map.mp he with ⟨c, _hc, rfl⟩
      cases hrev.1
  have hexLeft : ∀ i : Fin q, ∃ d : D,
      label d = (AData.block i, AData.part i) ∧ label d ∈ C := by
    intro i
    exact hexact _ _ (AData.left_adj i)
  have hexRight : ∀ i : Fin q, ∃ d : D,
      label d = (AData.block (finCyclicSucc (by omega) i), AData.part i) ∧
        label d ∈ C := by
    intro i
    exact hexact _ _ (AData.right_adj i)
  choose dl hdl hdlC using hexLeft
  choose dr hdr hdrC using hexRight
  have hblockS : ∀ i, AData.block i ∈ S := by
    intro i
    have hcC : label (dl i) ∈ directedCutLabels E S := by
      simpa only [C] using hdlC i
    have hc : (label (dl i)).1 ∈ S :=
      (Finset.mem_filter.mp hcC).2.1
    have heq : (label (dl i)).1 = AData.block i := by
      simpa using congrArg Prod.fst (hdl i)
    rw [heq] at hc
    exact hc
  have hpartNotS : ∀ i, AData.part i ∉ S := by
    intro i
    have hcC : label (dl i) ∈ directedCutLabels E S := by
      simpa only [C] using hdlC i
    have hc : (label (dl i)).2 ∉ S :=
      (Finset.mem_filter.mp hcC).2.2
    have heq : (label (dl i)).2 = AData.part i := by
      simpa using congrArg Prod.snd (hdl i)
    rw [heq] at hc
    exact hc
  have hBlockPartNe : ∀ i j, AData.block i ≠ AData.part j := by
    intro i j heq
    apply hpartNotS j
    rw [← heq]
    exact hblockS i
  have hedgeL : ∀ i, G.Adj (dl i).1.2.1 (dl i).1.2.2 := by
    intro i
    exact (hM _ (Finset.mem_sigma.mp (dl i).2).1).1.1 _
      (Finset.mem_sigma.mp (dl i).2).2
  have hedgeR : ∀ i, G.Adj (dr i).1.2.1 (dr i).1.2.2 := by
    intro i
    exact (hM _ (Finset.mem_sigma.mp (dr i).2).1).1.1 _
      (Finset.mem_sigma.mp (dr i).2).2
  have hsourceL : ∀ i, (dl i).1.2.1 ∈ B (AData.block i) := by
    intro i
    have hs := (hM _ (Finset.mem_sigma.mp (dl i).2).1).2 _
      (Finset.mem_sigma.mp (dl i).2).2 |>.1
    have heq : (dl i).1.1 = AData.block i := by
      simpa [label] using congrArg Prod.fst (hdl i)
    rw [heq] at hs
    exact hXB _ hs
  have hsourceR : ∀ i, (dr i).1.2.1 ∈
      B (AData.block (finCyclicSucc (by omega) i)) := by
    intro i
    have hs := (hM _ (Finset.mem_sigma.mp (dr i).2).1).2 _
      (Finset.mem_sigma.mp (dr i).2).2 |>.1
    have heq : (dr i).1.1 = AData.block (finCyclicSucc (by omega) i) := by
      simpa [label] using congrArg Prod.fst (hdr i)
    rw [heq] at hs
    exact hXB _ hs
  have htargetL : ∀ i, (dl i).1.2.2 ∈ (F (AData.part i)).enlarged := by
    intro i
    have heq : target (dl i) = AData.part i := by
      simpa [label] using congrArg Prod.snd (hdl i)
    rw [← heq]
    exact htargetMem (dl i)
  have htargetR : ∀ i, (dr i).1.2.2 ∈ (F (AData.part i)).enlarged := by
    intro i
    have heq : target (dr i) = AData.part i := by
      simpa [label] using congrArg Prod.snd (hdr i)
    rw [← heq]
    exact htargetMem (dr i)
  have hexPath : ∀ i : Fin q, ∃ p : G.Walk (dl i).1.2.2 (dr i).1.2.2,
      p.IsPath ∧ p.length ≤ 11 ∧
        ∀ z ∈ p.support, z ∈ (F (AData.part i)).enlarged := by
    intro i
    exact (F (AData.part i)).exists_path_in_enlarged_le_eleven
      G hk (hBne _) (hBcard _) (hBdeg _) (htargetL i) (htargetR i)
  choose p hpPath hpLen hpLoc using hexPath
  let x : Fin q → V := fun i => (dl i).1.2.1
  let y : Fin q → V := fun i => (dr i).1.2.1
  have hrecordEq : ∀ d e : D, d.1.1 = e.1.1 → d.1.2 = e.1.2 → d = e := by
    intro d e hs he
    apply Subtype.ext
    rw [Sigma.ext_iff, heq_eq_eq]
    exact ⟨hs, he⟩
  have hfirstNe : ∀ d e : D, d.1.1 = e.1.1 → d ≠ e →
      d.1.2.1 ≠ e.1.2.1 := by
    intro d e hs hde
    have hdM := (Finset.mem_sigma.mp d.2).2
    have heM := (Finset.mem_sigma.mp e.2).2
    have hedge : d.1.2 ≠ e.1.2 := fun h => hde (hrecordEq d e hs h)
    have hsep := (hM d.1.1 (Finset.mem_sigma.mp d.2).1).1.2
      d.1.2 hdM e.1.2 (by simpa [hs] using heM) hedge
    exact hsep.1
  have hsourceEqL : ∀ i, (dl i).1.1 = AData.block i := by
    intro i
    simpa [label] using congrArg Prod.fst (hdl i)
  have hsourceEqR : ∀ i,
      (dr i).1.1 = AData.block (finCyclicSucc (by omega) i) := by
    intro i
    simpa [label] using congrArg Prod.fst (hdr i)
  have htargetEqL : ∀ i, target (dl i) = AData.part i := by
    intro i
    simpa [label] using congrArg Prod.snd (hdl i)
  have htargetEqR : ∀ i, target (dr i) = AData.part i := by
    intro i
    simpa [label] using congrArg Prod.snd (hdr i)
  have hxxNe : ∀ i j, i ≠ j → x i ≠ x j := by
    intro i j hij hxy
    have hj : x i ∈ B (AData.block j) := by
      rw [hxy]
      exact hsourceL j
    exact Finset.disjoint_left.mp (hBdisj _ _
      (fun h => hij (AData.block_injective h))) (hsourceL i) hj
  have hyyNe : ∀ i j, i ≠ j → y i ≠ y j := by
    intro i j hij hxy
    have hj : y i ∈ B (AData.block (finCyclicSucc (by omega) j)) := by
      rw [hxy]
      exact hsourceR j
    exact Finset.disjoint_left.mp (hBdisj _ _
      (fun h => hij (finCyclicSucc_injective551 (by omega)
        (AData.block_injective h)))) (hsourceR i) hj
  have hxyNe : ∀ i j, i ≠ j → x i ≠ y j := by
    intro i j hij
    by_cases hb : AData.block i =
        AData.block (finCyclicSucc (by omega) j)
    · have hpartNe : AData.part i ≠ AData.part j :=
        AData.part_injective.ne hij
      have hdne : dl i ≠ dr j := by
        intro hde
        apply hpartNe
        have ht := congrArg target hde
        simpa [htargetEqL, htargetEqR] using ht
      exact hfirstNe (dl i) (dr j)
        ((hsourceEqL i).trans (hb.trans (hsourceEqR j).symm)) hdne
    · intro h
      have hj : x i ∈ B (AData.block (finCyclicSucc (by omega) j)) := by
        rw [h]
        exact hsourceR j
      exact Finset.disjoint_left.mp (hBdisj _ _ hb) (hsourceL i) hj
  let h₀ : ∀ i : Fin q, G.Walk (x i) (dr i).1.2.2 := fun i =>
    SimpleGraph.Walk.cons (hedgeL i) (p i)
  let h : ∀ i : Fin q, G.Walk (x i) (y i) := fun i =>
    (h₀ i).concat (hedgeR i).symm
  have hhPath : ∀ i, (h i).IsPath := by
    intro i
    have hxNot : x i ∉ (p i).support := by
      intro hx
      exact Finset.disjoint_left.mp
        (hBWdisj (AData.block i) (AData.part i)
          (fun heq => (hpartNotS i) (heq ▸ hblockS i)))
        (hsourceL i) (hpLoc i _ hx)
    have hh₀ : (h₀ i).IsPath := (hpPath i).cons hxNot
    have hyNot : y i ∉ (h₀ i).support := by
      simp only [h₀, SimpleGraph.Walk.support_cons, List.mem_cons]
      rintro (hyx | hyp)
      · have hnextNe : AData.block i ≠
            AData.block (finCyclicSucc (by omega) i) :=
          AData.block_injective.ne (finCyclicSucc_ne_self551 hq i).symm
        change y i = x i at hyx
        have hyB : x i ∈ B (AData.block (finCyclicSucc (by omega) i)) := by
          rw [← hyx]
          exact hsourceR i
        exact Finset.disjoint_left.mp (hBdisj _ _ hnextNe)
          (hsourceL i) hyB
      · exact Finset.disjoint_left.mp
          (hBWdisj (AData.block (finCyclicSucc (by omega) i))
            (AData.part i) (fun heq =>
              (hpartNotS i) (heq ▸ hblockS (finCyclicSucc (by omega) i))))
          (hsourceR i) (hpLoc i _ hyp)
    exact hh₀.concat hyNot _
  have hhLen : ∀ i, 2 ≤ (h i).length ∧ (h i).length ≤ 13 := by
    intro i
    have hpi := hpLen i
    simp only [h, h₀, SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.length_cons]
    constructor <;> omega
  have hhDisj : ∀ i j, i ≠ j → (h i).support.Disjoint (h j).support := by
    intro i j hij z hzi hzj
    have hloc : ∀ r z, z ∈ (h r).support →
        z = x r ∨ z = y r ∨ z ∈ (F (AData.part r)).enlarged := by
      intro r z hzr
      simp only [h, SimpleGraph.Walk.support_concat, h₀,
        SimpleGraph.Walk.support_cons, List.mem_append, List.mem_cons,
        List.mem_singleton] at hzr
      rcases hzr with (rfl | hzp) | (rfl | hz)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hpLoc r _ hzp))
      · exact Or.inr (Or.inl rfl)
      · simpa using hz
    rcases hloc i z hzi with hix | hiy | hiW
    · rcases hloc j z hzj with hjx | hjy | hjW
      · exact hxxNe i j hij (hix.symm.trans hjx)
      · exact hxyNe i j hij (hix.symm.trans hjy)
      · have hix' : z = (dl i).1.2.1 := by simpa [x] using hix
        exact Finset.disjoint_left.mp
          (hBWdisj _ _ (hBlockPartNe i j))
          (hsourceL i) (by rw [← hix']; exact hjW)
    · rcases hloc j z hzj with hjx | hjy | hjW
      · exact hxyNe j i hij.symm (hjx.symm.trans hiy)
      · exact hyyNe i j hij (hiy.symm.trans hjy)
      · have hiy' : z = (dr i).1.2.1 := by simpa [y] using hiy
        exact Finset.disjoint_left.mp
          (hBWdisj _ _ (hBlockPartNe (finCyclicSucc (by omega) i) j))
          (hsourceR i) (by rw [← hiy']; exact hjW)
    · rcases hloc j z hzj with hjx | hjy | hjW
      · exact Finset.disjoint_left.mp
          (hBWdisj _ _ (hBlockPartNe j i)).symm
          hiW (by rw [hjx]; exact hsourceL j)
      · exact Finset.disjoint_left.mp
          (hBWdisj _ _ (hBlockPartNe (finCyclicSucc (by omega) j) i)).symm
          hiW (by rw [hjy]; exact hsourceR j)
      · exact Finset.disjoint_left.mp
          (hWdisj _ _ (fun heq => hij (AData.part_injective heq))) hiW hjW
  have hhBlocks : ∀ i e z, z ∈ (h i).support →
      z ∈ B (AData.block e) →
      (e = i ∧ z = x i) ∨
        (e = finCyclicSucc (by omega) i ∧ z = y i) := by
    intro i e z hzh hzB
    simp only [h, SimpleGraph.Walk.support_concat, h₀,
      SimpleGraph.Walk.support_cons, List.mem_append, List.mem_cons,
      List.mem_singleton] at hzh
    rcases hzh with (hzx | hzp) | (hzy | hz)
    · left
      refine ⟨?_, hzx⟩
      apply AData.block_injective
      by_contra hei
      have hie : AData.block i ≠ AData.block e := by
        intro h
        exact hei h.symm
      have hxB : x i ∈ B (AData.block e) := by
        rw [← hzx]
        exact hzB
      exact Finset.disjoint_left.mp (hBdisj _ _ hie)
        (hsourceL i) hxB
    · exact (Finset.disjoint_left.mp
        (hBWdisj _ _ (hBlockPartNe e i)).symm
        (hpLoc i _ hzp) hzB).elim
    · right
      refine ⟨?_, hzy⟩
      apply AData.block_injective
      by_contra hei
      have hie : AData.block (finCyclicSucc (by omega) i) ≠
          AData.block e := by
        intro h
        exact hei h.symm
      have hyB : y i ∈ B (AData.block e) := by
        rw [← hzy]
        exact hzB
      exact Finset.disjoint_left.mp (hBdisj _ _ hie)
        (hsourceR i) hyB
    · simpa using hz
  have hqroom : (5 + 13) * q ≤ k := by
    have hroom' : 9 * (40 + 2 * Nat.log 2 (Fintype.card (ι ⊕ ι))) ≤ k := by
      simpa [Fintype.card_sum, two_mul] using hroom
    have : 9 * l ≤ k := (Nat.mul_le_mul_left 9 hlUpper).trans hroom'
    rw [hlq] at this
    omega
  have hxy : ∀ i,
      y (finCyclicPred (by omega) i) ≠ x i := by
    intro i
    exact (hxyNe i (finCyclicPred (by omega) i)
      (finCyclicPred_ne_self hq i).symm).symm
  apply hcycle
  apply cycleGraph_isContained_of_dense_blocks_and_bounded_handles
    G hq (by omega) hk hqroom (fun i => B (AData.block i))
      (fun i => hBne _) (fun i => hBcard _)
      (fun i j hij => hBdisj _ _ (fun heq => hij (AData.block_injective heq)))
      (fun i => hBdeg _) x y h
      (fun i => hsourceL i) (fun i => hsourceR i)
      hxy
      hhPath (fun i => (hhLen i).1) (fun i => (hhLen i).2)
      hhDisj hhBlocks

/-- The stable family consumed by the final KLS cleanup and absorption
argument.  Naming the package keeps the final eventual composition small. -/
def DenseStableWitness
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k n : ℕ) : Prop :=
  ∃ RF : Finset (Finset V), RF.Nonempty ∧
    (∀ B ∈ RF, B.Nonempty) ∧ DisjointFinsetFamily RF ∧
    PairwiseAnticomplete G RF ∧
    (∀ B ∈ RF, B.card ≤ k - 1) ∧
    (∀ B ∈ RF, ∀ v ∈ B,
      k ≤ 2 * degreeIn G B v ∧
      123 * (k - 1) ≤ 128 * degreeIn G B v) ∧
    64 * ((Finset.univ : Finset V) \ RF.biUnion id).card ≤
      Fintype.card V

/-- Stable witnesses for every diagonal counterexample at one fixed cycle
length. -/
def DenseStableFinAtCore (k : ℕ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≤ k →
  ∀ (G : SimpleGraph (Fin ((k - 1) * (n - 1) + 1))) [DecidableRel G.Adj],
    G.IndepSetFree n → ¬ cycleGraph k ⊑ G →
    DenseStableWitness G k n

/-- Numerical assumptions used uniformly for every `n ≤ k` by the final
absorption endpoint. -/
def FinalAbsorptionBoundsAt (k t delta : ℕ) : Prop :=
  1000 ≤ k ∧ 2 ≤ Nat.sqrt k ∧ 192 * delta ≤ t ∧ 1 ≤ t ∧
  16 * t * t ≤ 6 * k ∧
  ∀ n : ℕ, 3 ≤ n → n ≤ k →
    let N := (k - 1) * (n - 1) + 1
    2 * ((8 * (8 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) <
        Nat.sqrt k / 4096 ∧
    9 * (72 + 2 * Nat.log 2 (2 * N)) ≤ k ∧
    2 * ((8 * (4 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) < delta

/-- All inputs to the fixed-parameter contradiction bundled behind one
named proposition.  This keeps downstream applications within Lean's
ordinary elaboration budget. -/
def DenseCounterexampleData
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k n t delta : ℕ) : Prop :=
  1000 ≤ k ∧ 3 ≤ n ∧ n ≤ k ∧
  Fintype.card V = (k - 1) * (n - 1) + 1 ∧
  k - 1 ≤ G.minDegree ∧ G.IndepSetFree n ∧
  ¬ cycleGraph k ⊑ G ∧ DenseStableWitness G k n ∧
  2 ≤ Nat.sqrt k ∧
  2 * ((8 * (8 + 1)) * 2 *
    (Nat.log 2 (2 * Fintype.card V) + 1)) < Nat.sqrt k / 4096 ∧
  9 * (72 + 2 * Nat.log 2 (2 * Fintype.card V)) ≤ k ∧
  192 * delta ≤ t ∧
  2 * ((8 * (4 + 1)) * 2 *
    (Nat.log 2 (2 * Fintype.card V) + 1)) < delta ∧
  1 ≤ t ∧ 16 * t * t ≤ 6 * k

/-- The fixed-parameter endpoint of the KLS stability and absorption
argument.  The hypotheses are precisely the elementary inequalities that
will subsequently be discharged eventually. -/
theorem denseCounterexample_false_of_data
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k n t delta : ℕ} (hdata : DenseCounterexampleData G k n t delta) :
    False := by
  classical
  unfold DenseCounterexampleData at hdata
  obtain ⟨hk, hn, hnk, horder, hmin, hfree, hcycle, hwitness, hsqrt,
    hsepMargin, hsepRoom, hscale, hmatchMargin, ht, hprune⟩ := hdata
  unfold DenseStableWitness at hwitness
  obtain ⟨RF, hRFne, hRFblocks, hRFdisj, hRFanti, hRFcard,
    hRFdeg, hRFleft⟩ := hwitness
  let ι := {B // B ∈ RF}
  letI : DecidableEq ι := Classical.decEq ι
  let B : ι → Finset V := fun i => i.1
  let U : Finset V := (Finset.univ : Finset ι).biUnion B
  let L : Finset V := Finset.univ \ U
  letI : Nonempty ι := by
    obtain ⟨C, hC⟩ := hRFne
    exact ⟨⟨C, hC⟩⟩
  have hBne : ∀ i, (B i).Nonempty := by
    intro i
    exact hRFblocks i.1 i.2
  have hBcard : ∀ i, (B i).card ≤ k - 1 := by
    intro i
    exact hRFcard i.1 i.2
  have hBdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply hRFdisj i.1 i.2 j.1 j.2
    intro h
    exact hij (Subtype.ext h)
  have hBanti : ∀ i j, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y := by
    intro i j hij
    apply hRFanti i.1 i.2 j.1 j.2
    intro h
    exact hij (Subtype.ext h)
  have hBdeg123 : ∀ i, ∀ v ∈ B i,
      123 * (k - 1) ≤ 128 * degreeIn G (B i) v := by
    intro i v hv
    exact (hRFdeg i.1 i.2 v hv).2
  have hBdeg121 : ∀ i, ∀ v ∈ B i,
      121 * (k - 1) ≤ 128 * degreeIn G (B i) v := by
    intro i v hv
    have := hBdeg123 i v hv
    omega
  have hBL : ∀ i, Disjoint (B i) L := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvB hvL
    exact (Finset.mem_sdiff.mp hvL).2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvB⟩)
  have hUeq : U = RF.biUnion id := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨i, _hi, hvi⟩
      exact Finset.mem_biUnion.mpr ⟨i.1, i.2, by simpa [B] using hvi⟩
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨C, hC, hvC⟩
      let i : ι := ⟨C, hC⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, by simpa [B, i] using hvC⟩
  have hLsmall : 64 * L.card ≤ Fintype.card V := by
    change 64 * ((Finset.univ : Finset V) \ U).card ≤ Fintype.card V
    rw [hUeq]
    exact hRFleft
  have hcover : L = (Finset.univ : Finset V) \
      (Finset.univ : Finset ι).biUnion B := rfl
  have hBpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint B := by
    intro i _hi j _hj hij
    exact hBdisj i j hij
  have hUcard : U.card = ∑ i : ι, (B i).card := by
    simpa [U] using Finset.card_biUnion hBpair
  have hιV : Fintype.card ι ≤ Fintype.card V := by
    calc
      Fintype.card ι = ∑ _i : ι, 1 := by simp
      _ ≤ ∑ i : ι, (B i).card := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Finset.card_pos.mpr (hBne i)
      _ = U.card := hUcard.symm
      _ ≤ Fintype.card V := Finset.card_le_univ U
  have hlogι : Nat.log 2 (2 * Fintype.card ι) ≤
      Nat.log 2 (2 * Fintype.card V) := by
    apply Nat.log_mono_right
    exact Nat.mul_le_mul_left 2 hιV
  obtain ⟨M, hM, htotal, hAcard, hclean⟩ :=
    exists_KLS_cleanup G B L hk hBne hBL hBcard hBdeg123 hcycle
  let A : ι → Finset V := fun i => B i \ cleanupAttachmentsAt M i
  let R : Finset V := L \ cleanupAbsorbed M
  let AF := fun i => hM.absorbableFamilyAt hBL i
  have hAFvertices : ∀ i, (AF i).vertices = cleanupAbsorbedAt M i := by
    intro i
    exact hM.absorbableFamilyAt_vertices hBL i
  have hAB : ∀ i, A i ⊆ B i := by
    intro i
    exact Finset.sdiff_subset
  have hRL : R ⊆ L := Finset.sdiff_subset
  have hBR : ∀ i, Disjoint (B i) R := by
    intro i
    exact (hBL i).mono_right hRL
  obtain ⟨P, hP, _hpartDisj, _hpartNe, _hpartSub, _hpartCover,
      _hpartPath, hpartCount⟩ :=
    exists_diameterTwo_starPartition G (R := R) (m := Nat.sqrt k)
      hsqrt hfree
  let J : Finset ι := (Finset.univ : Finset ι).filter fun i =>
    k / 8 ≤ (remainderAttachments G A R i).card
  have hJsmall : 2 * J.card < Fintype.card ι := by
    apply fewer_than_half_large_remainderAttachment_blocks
      G A B L R P (by omega) hk hn hnk horder hP hpartCount
      hRL hLsmall hBne hBcard hBdisj hcover hBdeg121 hAB hBR hclean
    · exact hsepMargin
    · exact hsepRoom
    · exact hcycle
  let T : Finset ι := (Finset.univ : Finset ι) \ J
  have hJsub : J ⊆ (Finset.univ : Finset ι) := Finset.subset_univ J
  have hsplitT : T.card + J.card = Fintype.card ι := by
    have hs := Finset.card_sdiff_add_card (Finset.univ : Finset ι) J
    rw [Finset.union_eq_left.mpr hJsub] at hs
    simpa [T] using hs
  have hThalf : Fintype.card ι < 2 * T.card := by omega
  let X : ι → Finset V := fun i => A i \
    remainderAttachments G A R i
  let maxM : ι → Finset (V × V) := fun i =>
    Classical.choose (exists_maximal_externalMatching G (X i) (AF i).enlarged)
  have hmaxM : ∀ i, IsExternalMatching G (X i) (AF i).enlarged (maxM i) ∧
      ∀ N, IsExternalMatching G (X i) (AF i).enlarged N →
        N.card ≤ (maxM i).card := by
    intro i
    exact Classical.choose_spec
      (exists_maximal_externalMatching G (X i) (AF i).enlarged)
  have hXsubB : ∀ i, X i ⊆ B i := by
    intro i
    exact Finset.sdiff_subset.trans (hAB i)
  have hBWdisj : ∀ i j, i ≠ j →
      Disjoint (B i) (AF j).enlarged := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rcases Finset.mem_union.mp hvj with hvjB | hvjV
    · exact Finset.disjoint_left.mp (hBdisj i j hij) hvi hvjB
    · have hvjL : v ∈ L := by
        apply cleanupAbsorbedAt_subset hM j
        rw [← hAFvertices j]
        exact hvjV
      exact Finset.disjoint_left.mp (hBL i) hvi hvjL
  have hWdisj : ∀ i j, i ≠ j →
      Disjoint (AF i).enlarged (AF j).enlarged := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rcases Finset.mem_union.mp hvi with hviB | hviV
    · exact Finset.disjoint_left.mp (hBWdisj i j hij) hviB hvj
    · rcases Finset.mem_union.mp hvj with hvjB | hvjV
      · have hviL : v ∈ L := by
          apply cleanupAbsorbedAt_subset hM i
          rw [← hAFvertices i]
          exact hviV
        exact Finset.disjoint_left.mp (hBL j).symm hviL hvjB
      · have hviAt : v ∈ cleanupAbsorbedAt M i := by
          rw [← hAFvertices i]
          exact hviV
        have hvjAt : v ∈ cleanupAbsorbedAt M j := by
          rw [← hAFvertices j]
          exact hvjV
        exact Finset.disjoint_left.mp
          (cleanupAbsorbedAt_disjoint_of_ne hM hij) hviAt hvjAt
  have htarget : ∀ i ∈ T, ∀ e ∈ maxM i,
      ∃ j, j ≠ i ∧ e.2 ∈ (AF j).enlarged := by
    intro i _hi e he
    have heM := (hmaxM i).1.2 e he
    exact exists_other_enlarged_block_of_external_cleanup_edge
      G B L hM hBL hcover hBanti heM.1 heM.2 ((hmaxM i).1.1.1 e he)
  have hmatchMarginι : 2 * ((8 * (4 + 1)) * 2 *
      (Nat.log 2 (2 * Fintype.card ι) + 1)) < delta := by
    have hle := Nat.mul_le_mul_left (2 * ((8 * (4 + 1)) * 2))
      (Nat.add_le_add_right hlogι 1)
    have hmatchMargin' :
        (2 * ((8 * (4 + 1)) * 2)) *
          (Nat.log 2 (2 * Fintype.card V) + 1) < delta := by
      simpa only [Nat.mul_assoc] using hmatchMargin
    have hh := hle.trans_lt hmatchMargin'
    simpa only [Nat.mul_assoc] using hh
  have hmatchRoomι :
      9 * (40 + 2 * Nat.log 2 (2 * Fintype.card ι)) ≤ k := by
    calc
      9 * (40 + 2 * Nat.log 2 (2 * Fintype.card ι)) ≤
          9 * (72 + 2 * Nat.log 2 (2 * Fintype.card V)) := by
            gcongr <;> omega
      _ ≤ k := hsepRoom
  obtain ⟨i, hiT, hMi⟩ := exists_small_externalMatching_in_dense_family
    G B X AF T maxM hk hThalf hBne hBcard hBdisj hBanti hBdeg121
      hBWdisj hWdisj hXsubB (fun j _hj => (hmaxM j).1) htarget
      hscale hmatchMarginι hmatchRoomι hcycle
  have hiNotJ : i ∉ J := (Finset.mem_sdiff.mp hiT).2
  have hAttlt : (remainderAttachments G A R i).card < k / 8 := by
    by_contra hnot
    apply hiNotJ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hAttSub : remainderAttachments G A R i ⊆ A i :=
    remainderAttachments_subset G A R i
  have hXsplit : (X i).card + (remainderAttachments G A R i).card =
      (A i).card := by
    have hs := Finset.card_sdiff_add_card (A i)
      (remainderAttachments G A R i)
    rw [Finset.union_eq_left.mpr hAttSub] at hs
    simpa [X] using hs
  have hXlarge : 6 * k < 8 * (X i).card := by
    have hAi : 7 * k ≤ 8 * (A i).card := by
      simpa [A] using hAcard i
    have hdiv : 8 * (k / 8) ≤ k := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self k 8
    omega
  have hXW : X i ⊆ (AF i).enlarged := by
    intro v hv
    exact Finset.mem_union_left _ (hXsubB i hv)
  obtain ⟨D, K, hDX, hK, hloss, hprunedD⟩ :=
    exists_pruned_source_and_externalMatching G (X i) (AF i).enlarged
      hXW t
  have hKMi : K.card ≤ (maxM i).card := (hmaxM i).2 K hK
  have hKt : K.card ≤ t := hKMi.trans hMi
  have hLoss' : (X i).card ≤ D.card + 2 * t * t := by
    calc
      (X i).card ≤ D.card + 2 * t * K.card := hloss
      _ ≤ D.card + 2 * t * t := by gcongr
  have hDne : D.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hzero
    have hDz : D.card = 0 := by omega
    have h8 : 8 * (X i).card ≤ 16 * t * t := by
      calc
        8 * (X i).card ≤ 8 * (D.card + 2 * t * t) :=
          Nat.mul_le_mul_left 8 hLoss'
        _ = 16 * t * t := by rw [hDz]; ring
    omega
  obtain ⟨v, hvD⟩ := hDne
  let W : Finset V := (AF i).enlarged
  let Y : Finset V := ((Finset.univ : Finset V) \ W).filter fun y => G.Adj v y
  have hYle : Y.card ≤ (maxM i).card := by
    apply outsideNeighbor_card_le_maximalExternalMatching_of_pruned
      G hDX hXW hvD (hmaxM i).1 (hmaxM i).2 hMi ht
    intro y hyW
    exact hprunedD y (by simpa [W] using hyW)
  have hBVertDisj : Disjoint (B i) (AF i).vertices := by
    rw [hAFvertices i]
    exact cleanupAbsorbedAt_disjoint_block hM hBL i
  have hWcard : W.card = (B i).card + (AF i).vertices.card := by
    simpa [W, ShortAbsorbableFamily.enlarged] using
      Finset.card_union_of_disjoint hBVertDisj
  have hWlt : W.card < k := by
    rw [hWcard, hAFvertices i]
    exact htotal i
  have hvW : v ∈ W := hXW (hDX hvD)
  have hinside : degreeIn G W v ≤ W.card - 1 :=
    degreeIn_le_card_pred_of_mem G W hvW
  have hdegLower : k - 1 ≤ G.degree v :=
    hmin.trans (G.minDegree_le_degree v)
  have hsplitDeg : degreeIn G W v +
      degreeIn G ((Finset.univ : Finset V) \ W) v = G.degree v := by
    have hdisj : Disjoint
        (W.filter fun w => G.Adj v w)
        (((Finset.univ : Finset V) \ W).filter fun w => G.Adj v w) := by
      rw [Finset.disjoint_left]
      intro w hwW hwC
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwC).1).2
        (Finset.mem_filter.mp hwW).1
    calc
      degreeIn G W v + degreeIn G ((Finset.univ : Finset V) \ W) v =
          (W.filter fun w => G.Adj v w).card +
            (((Finset.univ : Finset V) \ W).filter fun w => G.Adj v w).card := rfl
      _ = ((W.filter fun w => G.Adj v w) ∪
            (((Finset.univ : Finset V) \ W).filter fun w => G.Adj v w)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = ((Finset.univ : Finset V).filter fun w => G.Adj v w).card := by
        rw [← Finset.filter_union]
        simp only [Finset.union_sdiff_of_subset (Finset.subset_univ W)]
      _ = G.degree v := by
        rw [← G.card_neighborFinset_eq_degree]
        congr 1
        ext w
        simp [SimpleGraph.mem_neighborFinset]
  have hneed : k - W.card ≤ Y.card := by
    have hYdeg : Y.card = degreeIn G ((Finset.univ : Finset V) \ W) v := rfl
    have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨v, hvW⟩
    have hinsideSucc : degreeIn G W v + 1 ≤ W.card := by omega
    have hkWB : k ≤ W.card +
        degreeIn G ((Finset.univ : Finset V) \ W) v := by
      omega
    rw [hYdeg]
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using hkWB
  obtain ⟨Q, hQY, hQcard⟩ := Finset.exists_subset_card_eq hneed
  have hQleT : Q.card ≤ t := by
    rw [hQcard]
    exact hneed.trans (hYle.trans hMi)
  have hQoutside : ∀ q ∈ Q, q ∉ (AF i).enlarged := by
    intro q hq
    have hqY := hQY hq
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hqY).1).2
  have hmany : ∀ q ∈ Q, 2 * Q.card ≤ degreeIn G D q := by
    intro q hq
    have hqY := hQY hq
    have hqOut : q ∉ W :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hqY).1).2
    have hvq : G.Adj v q := (Finset.mem_filter.mp hqY).2
    have hpos : degreeIn G D q ≠ 0 := by
      intro hz
      have hvFilter : v ∈ D.filter fun a => G.Adj q a :=
        Finset.mem_filter.mpr ⟨hvD, hvq.symm⟩
      have : 0 < degreeIn G D q := by
        rw [degreeIn]
        exact Finset.card_pos.mpr ⟨v, hvFilter⟩
      omega
    have hlarge := (hprunedD q (by simpa [W] using hqOut)).resolve_left hpos
    omega
  have hAremaining : A i = (AF i).remaining := by
    simp [A, AF, ShortAbsorbableFamily.remaining,
      hM.absorbableFamilyAt_attachments hBL i]
  have hDremaining : D ⊆ (AF i).remaining := by
    intro a ha
    rw [← hAremaining]
    exact Finset.sdiff_subset (hDX ha)
  have htargetTotal :
      (B i).card + (AF i).vertices.card + Q.card = k := by
    rw [← hWcard, hQcard]
    exact Nat.add_sub_of_le (Nat.le_of_lt hWlt)
  have hroom : 10 * (k - (B i).card + 2) + 2 ≤ (B i).card := by
    obtain ⟨b, hb⟩ := hBne i
    have hstrong := hBdeg123 i b hb
    have hupper := degreeIn_le_card_pred_of_mem G (B i) hb
    omega
  have hsmall : 10 * ((AF i).vertices.card + Q.card) ≤ (B i).card := by
    omega
  apply hcycle
  exact (AF i).cycleGraph_isContained_of_external_singletons
    G hk hDremaining hQoutside hmany htargetTotal hsmall (hBdeg121 i)

/-- The bundled fixed-counterexample endpoint applied uniformly over the
diagonal counterexample branch. -/
theorem denseCounterexampleExcludedAt_of_stable_family
    {k t delta : ℕ}
    (hstable : DenseStableFinAtCore k)
    (hbounds : FinalAbsorptionBoundsAt k t delta) :
    DenseCounterexampleExcludedAt k := by
  classical
  unfold DenseStableFinAtCore at hstable
  unfold FinalAbsorptionBoundsAt at hbounds
  unfold DenseCounterexampleExcludedAt
  intro n hn hnk G hmin hfree hcycle
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨hk, hsqrt, hscale, ht, hprune, hall⟩ := hbounds
  obtain ⟨hsep, hroom, hmatch⟩ := hall n hn hnk
  have hfamily : DenseStableWitness G k n :=
    hstable n hn hnk G hfree hcycle
  apply denseCounterexample_false_of_data G
  unfold DenseCounterexampleData
  refine ⟨hk, hn, hnk, by simp, hmin, hfree, hcycle, hfamily,
    hsqrt, ?_, ?_, hscale, ?_, ht, hprune⟩
  · simpa using hsep
  · simpa using hroom
  · simpa using hmatch


def finalMatchingScale (k : ℕ) : ℕ := Nat.sqrt k / 65536

def finalCutScale (k : ℕ) : ℕ := finalMatchingScale k / 192

/-- The elementary numerical hypotheses consumed by the fixed-parameter
absorption endpoint. -/
def FinalAbsorptionNumericAt (k : ℕ) : Prop :=
  1000 ≤ k ∧ 2 ≤ Nat.sqrt k ∧
  ∀ n : ℕ, 3 ≤ n → n ≤ k →
    let N := (k - 1) * (n - 1) + 1
    2 * ((8 * (8 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) <
        Nat.sqrt k / 4096 ∧
    9 * (72 + 2 * Nat.log 2 (2 * N)) ≤ k ∧
    192 * finalCutScale k ≤ finalMatchingScale k ∧
    2 * ((8 * (4 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) <
        finalCutScale k ∧
    1 ≤ finalMatchingScale k ∧
    16 * finalMatchingScale k * finalMatchingScale k ≤ 6 * k

/-- Uniform logarithmic bound for every extremal order on the diagonal
range `n ≤ k`. -/
theorem log_two_twice_extremalOrder_le
    {k n : ℕ} (hn : 3 ≤ n) (hnk : n ≤ k) :
    Nat.log 2 (2 * ((k - 1) * (n - 1) + 1)) ≤
      2 * Nat.log 2 k + 3 := by
  let ell := Nat.log 2 k
  have hk : 3 ≤ k := hn.trans hnk
  have hN : (k - 1) * (n - 1) + 1 ≤ k * k := by
    have hsub : n - 1 ≤ k - 1 := Nat.sub_le_sub_right hnk 1
    have hkdecomp : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    calc
      (k - 1) * (n - 1) + 1 ≤ (k - 1) * (k - 1) + 1 := by gcongr
      _ ≤ (k - 1) * k + 1 := by gcongr <;> omega
      _ ≤ (k - 1) * k + k := by omega
      _ = (k - 1) * k + 1 * k := by simp
      _ = (k - 1 + 1) * k := by rw [Nat.add_mul]
      _ = k * k := by rw [hkdecomp]
  have hkpow : k ≤ 2 ^ (ell + 1) := by
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two k).le
  have harg : 2 * ((k - 1) * (n - 1) + 1) ≤
      2 ^ (2 * ell + 3) := by
    calc
      2 * ((k - 1) * (n - 1) + 1) ≤ 2 * (k * k) :=
        Nat.mul_le_mul_left 2 hN
      _ ≤ 2 * (2 ^ (ell + 1) * 2 ^ (ell + 1)) := by gcongr
      _ = 2 ^ (2 * ell + 3) := by
        rw [show 2 * ell + 3 = 1 + (ell + 1) + (ell + 1) by omega,
          Nat.pow_add, Nat.pow_add]
        norm_num [Nat.pow_add]
        ring
  have hpos : 2 * ((k - 1) * (n - 1) + 1) ≠ 0 := by positivity
  have hpowlt : 2 ^ (2 * ell + 3) < 2 ^ (2 * ell + 3 + 1) :=
    Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  have hloglt := Nat.log_lt_of_lt_pow hpos (harg.trans_lt hpowlt)
  dsimp [ell] at hloglt ⊢
  omega

/-- All elementary inequalities needed by the final stability/absorption
endpoint hold uniformly on the diagonal range once `k` is large. -/
theorem eventually_final_absorption_numeric :
    ∀ᶠ k : ℕ in atTop, FinalAbsorptionNumericAt k := by
  have hroot : ∀ᶠ k : ℕ in atTop,
      8192 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt k)) :=
    (tendsto_nat_sqrt_atTop.comp
      (tendsto_nat_sqrt_atTop.comp tendsto_nat_sqrt_atTop)).eventually
      (eventually_ge_atTop 8192)
  filter_upwards [hroot] with k hr
  unfold FinalAbsorptionNumericAt
  let s := Nat.sqrt k
  let q := Nat.sqrt s
  let r := Nat.sqrt q
  have hr' : 8192 ≤ r := by simpa [r, q, s] using hr
  have hr16 : 16 ≤ r := by omega
  have hrq : r * r ≤ q := by
    simpa [r, Nat.pow_two] using Nat.sqrt_le' q
  have hqs : q * q ≤ s := by
    simpa [q, Nat.pow_two] using Nat.sqrt_le' s
  have hrs : r ^ 4 ≤ s := by
    calc
      r ^ 4 = (r * r) * (r * r) := by ring
      _ ≤ q * q := Nat.mul_le_mul hrq hrq
      _ ≤ s := hqs
  have hss : s * s ≤ k := by
    simpa [s, Nat.pow_two] using Nat.sqrt_le k
  have hrCube : 20000000000 ≤ r ^ 3 := by
    calc
      20000000000 ≤ 8192 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr' 3
  have hbig : 20000000000 * r ≤ s := by
    calc
      20000000000 * r ≤ r ^ 3 * r := Nat.mul_le_mul_right r hrCube
      _ = r ^ 4 := by ring
      _ ≤ s := hrs
  have hsLarge : 65536 ≤ s := by
    calc
      65536 ≤ 20000000000 * r := by omega
      _ ≤ s := hbig
  have hsqrt : 2 ≤ Nat.sqrt k := by simpa [s] using (show 2 ≤ s by omega)
  have hk : 1000 ≤ k := by
    have hsk : s ≤ k := by simpa [s] using Nat.sqrt_le_self k
    omega
  refine ⟨hk, hsqrt, ?_⟩
  intro n hn hnk
  let N := (k - 1) * (n - 1) + 1
  have hlogK : Nat.log 2 k ≤ 4 * r := by
    simpa [r, q, s] using log_two_le_four_mul_triple_sqrt hr16
  have hlogN : Nat.log 2 (2 * N) ≤ 8 * r + 3 := by
    have h := log_two_twice_extremalOrder_le hn hnk
    dsimp [N]
    exact h.trans (by omega)
  have hsepLinear :
      (2 * ((8 * (8 + 1)) * 2 * ((8 * r + 3) + 1)) + 1) * 4096 ≤
        20000000000 * r := by
    ring_nf
    omega
  have hsepDiv :
      2 * ((8 * (8 + 1)) * 2 * ((8 * r + 3) + 1)) + 1 ≤ s / 4096 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4096)]
    exact hsepLinear.trans hbig
  have hsep : 2 * ((8 * (8 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) <
      Nat.sqrt k / 4096 := by
    change 2 * ((8 * (8 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) < s / 4096
    have hmul := Nat.mul_le_mul_left (2 * ((8 * (8 + 1)) * 2))
      (Nat.add_le_add_right hlogN 1)
    omega
  have hroom : 9 * (72 + 2 * Nat.log 2 (2 * N)) ≤ k := by
    have hr200 : 200 ≤ r := by omega
    have h200 : 200 * r ≤ r * r := Nat.mul_le_mul_right r hr200
    have hrk : r * r ≤ k := by
      calc
        r * r ≤ q := hrq
        _ ≤ s := by simpa [q] using Nat.sqrt_le_self s
        _ ≤ k := by simpa [s] using Nat.sqrt_le_self k
    calc
      9 * (72 + 2 * Nat.log 2 (2 * N)) ≤ 200 * r := by omega
      _ ≤ r * r := h200
      _ ≤ k := hrk
  let t := finalMatchingScale k
  let delta := finalCutScale k
  have h65536t : 65536 * t ≤ s := by
    simpa [t, finalMatchingScale, s, Nat.mul_comm] using
      Nat.div_mul_le_self s 65536
  have htS : t ≤ s := by omega
  have ht : 1 ≤ t := by
    rw [show t = s / 65536 by rfl, Nat.le_div_iff_mul_le (by norm_num : 0 < 65536)]
    simpa using hsLarge
  have hscale : 192 * delta ≤ t := by
    simpa [delta, finalCutScale, t, Nat.mul_comm] using
      Nat.div_mul_le_self t 192
  have hmatchLinear :
      ((2 * ((8 * (4 + 1)) * 2 * ((8 * r + 3) + 1)) + 1) * 192) *
          65536 ≤ 20000000000 * r := by
    ring_nf
    nlinarith
  have hmatchToS :
      ((2 * ((8 * (4 + 1)) * 2 * ((8 * r + 3) + 1)) + 1) * 192) *
          65536 ≤ s := hmatchLinear.trans hbig
  have hmatchToT :
      (2 * ((8 * (4 + 1)) * 2 * ((8 * r + 3) + 1)) + 1) * 192 ≤ t := by
    rw [show t = s / 65536 by rfl,
      Nat.le_div_iff_mul_le (by norm_num : 0 < 65536)]
    exact hmatchToS
  have hmatchDiv :
      2 * ((8 * (4 + 1)) * 2 * ((8 * r + 3) + 1)) + 1 ≤ delta := by
    change _ ≤ t / 192
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 192)]
    exact hmatchToT
  have hmatch :
      2 * ((8 * (4 + 1)) * 2 * (Nat.log 2 (2 * N) + 1)) < delta := by
    have hmul := Nat.mul_le_mul_left (2 * ((8 * (4 + 1)) * 2))
      (Nat.add_le_add_right hlogN 1)
    omega
  have h16t : 16 * t ≤ s := by omega
  have hprune : 16 * t * t ≤ 6 * k := by
    calc
      16 * t * t ≤ s * s := Nat.mul_le_mul h16t htS
      _ ≤ k := hss
      _ ≤ 6 * k := by omega
  exact ⟨hsep, hroom, hscale, hmatch, ht, hprune⟩


/-- Reorder the elementary eventual package into the form consumed by the
fixed-parameter endpoint. -/
theorem finalAbsorptionBounds_of_numeric {k : ℕ}
    (h : FinalAbsorptionNumericAt k) :
    FinalAbsorptionBoundsAt k (finalMatchingScale k) (finalCutScale k) := by
  unfold FinalAbsorptionNumericAt at h
  unfold FinalAbsorptionBoundsAt
  obtain ⟨hk, hsqrt, hall⟩ := h
  have hbase := hall 3 (by omega) (by
    have := hsqrt
    have hsle : Nat.sqrt k ≤ k := Nat.sqrt_le_self k
    omega)
  obtain ⟨_hsep, _hroom, hscale, _hmatch, ht, hprune⟩ := hbase
  refine ⟨hk, hsqrt, hscale, ht, hprune, ?_⟩
  intro n hn hnk
  obtain ⟨hsep, hroom, _hscale, hmatch, _ht, _hprune⟩ := hall n hn hnk
  exact ⟨hsep, hroom, hmatch⟩

/-- The non-elementary branch in the deletion induction is eventually
impossible. -/
theorem eventually_denseCounterexampleExcludedAt_551 :
    ∀ᶠ k : ℕ in atTop, DenseCounterexampleExcludedAt k := by
  have hstableFin : ∀ᶠ k : ℕ in atTop, DenseStableFinAtCore k := by
    apply eventually_exists_dense_stable_family.mono
    intro k hk
    classical
    unfold DenseStableFinAtCore
    intro n hn hnk G instG hfree hcycle
    unfold DenseStableWitness
    exact hk n hn hnk G (by simp) hfree hcycle
  apply (hstableFin.and
    eventually_final_absorption_numeric).mono
  rintro k ⟨hstable, hnumeric⟩
  exact denseCounterexampleExcludedAt_of_stable_family hstable
    (finalAbsorptionBounds_of_numeric hnumeric)

/-- Erdős Problem 551, in the unconditional form established by
Keevash--Long--Skokan: for every sufficiently large clique parameter `n`,
the exact formula holds simultaneously for all cycle lengths `k ≥ n`. -/
theorem erdos_551 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, n ≤ k →
      cycleCliqueRamseyNumber k n = (k - 1) * (n - 1) + 1 :=
  erdos551_eventually_of_eventually_denseCounterexampleExcluded
    eventually_denseCounterexampleExcludedAt_551

#print axioms erdos_551


end Erdos551

alias _root_.Erdos551.erdos_551_eventually := _root_.Erdos551.erdos_551
