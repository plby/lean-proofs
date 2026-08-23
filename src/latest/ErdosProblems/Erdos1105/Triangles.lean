import ErdosProblems.Erdos1105.Representatives

namespace Erdos1105

open SimpleGraph

/-- A coloring of unordered pairs has no rainbow triangle. Diagonal values are
irrelevant because the three vertices in this predicate are distinct. -/
def NoRainbowTriangle {V C : Type*} (c : Sym2 V → C) : Prop :=
  ∀ a b d, a ≠ b → b ≠ d → a ≠ d →
    c s(a, b) = c s(b, d) ∨ c s(a, b) = c s(a, d) ∨ c s(b, d) = c s(a, d)

/-- In a coloring without rainbow triangles, the closing edge of a rainbow
path has a color already used by that path. -/
lemma closing_color_mem_path {V C : Type*} {G : SimpleGraph V}
    {c : Sym2 V → C} (hc : NoRainbowTriangle c) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hr : (p.edges.map c).Nodup)
    (huv : u ≠ v) : c s(u, v) ∈ p.edges.map c := by
  induction p with
  | nil => exact (huv rfl).elim
  | @cons u w v h p ih =>
    have hp' := hp.of_cons
    have hr' : c s(u, w) ∉ p.edges.map c ∧ (p.edges.map c).Nodup := by
      simpa only [Walk.edges_cons, List.map_cons, List.nodup_cons] using hr
    by_cases hwv : w = v
    · subst w
      have hnil : p = .nil := by simpa using hp'
      subst p
      simp
    · have hm := ih hp' hr'.2 hwv
      simp only [Walk.edges_cons, List.map_cons, List.mem_cons]
      rcases hc u w v h.ne hwv huv with heq | heq | heq
      · exact (hr'.1 (heq ▸ hm)).elim
      · exact Or.inl heq.symm
      · exact Or.inr (heq ▸ hm)

/-- A graph whose edges all have distinct colors is acyclic if the ambient
complete coloring has no rainbow triangle. -/
lemma isAcyclic_of_noRainbowTriangle {V C : Type*} {G : SimpleGraph V}
    {c : Sym2 V → C} (hc : NoRainbowTriangle c) (hinj : Set.InjOn c G.edgeSet) :
    G.IsAcyclic := by
  intro u p hp
  have hr : (p.edges.map c).Nodup :=
    hp.isTrail.edges_nodup.map_on fun x hx y hy hxy ↦
      hinj (p.edges_subset_edgeSet hx) (p.edges_subset_edgeSet hy) hxy
  cases p with
  | nil => exact Walk.not_isCycle_nil hp
  | @cons u v _ h p =>
    have hpath : p.IsPath := (Walk.cons_isCycle_iff p h).mp hp |>.1
    have hr' : c s(u, v) ∉ p.edges.map c ∧ (p.edges.map c).Nodup := by
      simpa only [Walk.edges_cons, List.map_cons, List.nodup_cons] using hr
    have hm := closing_color_mem_path hc p hpath hr'.2 h.ne.symm
    exact hr'.1 (by simpa only [Sym2.eq_swap] using hm)

/-- Three distinct vertices give a non-induced triangle copy. -/
def triangleCopy {V : Type*} (a b d : V) (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    (cycleGraph 3).Copy (⊤ : SimpleGraph V) where
  toHom := {
    toFun := ![a, b, d]
    map_rel' := by
      intro i j hij
      have hne := hij.ne
      fin_cases i <;> fin_cases j <;> simp_all [hab.symm, hbd.symm, had.symm] }
  injective' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm, hbd.symm, had.symm]

lemma noRainbowTriangle_of_no_copy {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hc : ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    NoRainbowTriangle (extendColor c) := by
  intro a b d hab hbd had
  by_contra hn
  have hab' : (⊤ : SimpleGraph V).Adj a b := hab
  have hbd' : (⊤ : SimpleGraph V).Adj b d := hbd
  have had' : (⊤ : SimpleGraph V).Adj a d := had
  have hn' : c ⟨s(a, b), hab'⟩ ≠ c ⟨s(b, d), hbd'⟩ ∧
      c ⟨s(a, b), hab'⟩ ≠ c ⟨s(a, d), had'⟩ ∧
      c ⟨s(b, d), hbd'⟩ ≠ c ⟨s(a, d), had'⟩ := by
    have habc := extendColor_edge c ⟨s(a, b), hab'⟩
    have hbdc := extendColor_edge c ⟨s(b, d), hbd'⟩
    have hadc := extendColor_edge c ⟨s(a, d), had'⟩
    rw [habc, hbdc, hadc] at hn
    simpa only [Option.some.injEq, not_or] using hn
  apply hc (triangleCopy a b d hab hbd had)
  intro x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  apply Subtype.ext
  induction x using Sym2.inductionOn with
  | _ i j =>
    induction y using Sym2.inductionOn with
    | _ l m =>
      have hij := (show (cycleGraph 3).Adj i j from hx).ne
      have hlm := (show (cycleGraph 3).Adj l m from hy).ne
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
        simp_all [triangleCopy, SimpleGraph.Copy.mapEdgeSet,
          SimpleGraph.Hom.mapEdgeSet, Sym2.eq_swap]

private def edge01 : (cycleGraph 3).edgeSet :=
  ⟨s((0 : Fin 3), (1 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

private def edge02 : (cycleGraph 3).edgeSet :=
  ⟨s((0 : Fin 3), (2 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

private def edge12 : (cycleGraph 3).edgeSet :=
  ⟨s((1 : Fin 3), (2 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

lemma no_copy_of_noRainbowTriangle {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hc : NoRainbowTriangle (extendColor c)) :
    ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
  intro f hf
  have h01 : f 0 ≠ f 1 := f.injective.ne (by decide)
  have h12 : f 1 ≠ f 2 := f.injective.ne (by decide)
  have h02 : f 0 ≠ f 2 := f.injective.ne (by decide)
  have ht := hc (f 0) (f 1) (f 2) h01 h12 h02
  have hc01 : extendColor c s(f 0, f 1) = some (c (f.mapEdgeSet edge01)) :=
    extendColor_edge c (f.mapEdgeSet edge01)
  have hc02 : extendColor c s(f 0, f 2) = some (c (f.mapEdgeSet edge02)) :=
    extendColor_edge c (f.mapEdgeSet edge02)
  have hc12 : extendColor c s(f 1, f 2) = some (c (f.mapEdgeSet edge12)) :=
    extendColor_edge c (f.mapEdgeSet edge12)
  rw [hc01, hc02, hc12] at ht
  rcases ht with ht | ht | ht
  · exact (by decide : edge01 ≠ edge12) (hf (Option.some.inj ht))
  · exact (by decide : edge01 ≠ edge02) (hf (Option.some.inj ht))
  · exact (by decide : edge12 ≠ edge02) (hf (Option.some.inj ht))

/-- The elementary upper bound for rainbow-triangle-free colorings. -/
theorem antiRamseyNum_cycleGraph_three_le (n : ℕ) :
    antiRamseyNum (cycleGraph 3) n ≤ n - 1 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    apply antiRamseyNum_le
    intro q c hc hH
    obtain ⟨R, _, hinj, e, _⟩ := exists_representative c hc
    have hR : R.IsAcyclic :=
      isAcyclic_of_noRainbowTriangle (noRainbowTriangle_of_no_copy c hH) hinj
    obtain ⟨T, hRT, _, hT⟩ :=
      (connected_top (V := Fin (n + 1))).exists_isTree_le_of_le_of_isAcyclic
        (show R ≤ ⊤ from le_top) hR
    have hcard : Fintype.card R.edgeSet = q := by
      simpa using Fintype.card_congr e.symm
    have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRT)
    have hTcard := hT.card_edgeFinset
    rw [← SimpleGraph.card_edgeSet, hcard] at hle
    simp only [Fintype.card_fin] at hTcard
    omega

/-- Color an edge by its larger endpoint minus one. -/
def maxColoring (n : ℕ) : (⊤ : SimpleGraph (Fin (n + 1))).edgeSet → Fin n :=
  EdgeLabeling.mk (fun a b h ↦ ⟨max a.val b.val - 1, by
    have hne : a ≠ b := h
    have hmax : 1 ≤ max a.val b.val := by
      by_contra hh
      exact hne (Fin.ext (by omega))
    have ha := a.isLt
    have hb := b.isLt
    omega⟩) (by
      intro a b h
      apply Fin.ext
      simp [max_comm])

lemma maxColoring_surjective (n : ℕ) : Function.Surjective (maxColoring n) := by
  intro i
  let a : Fin (n + 1) := 0
  let b : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  refine ⟨⟨s(a, b), hab⟩, ?_⟩
  apply Fin.ext
  change max a.val b.val - 1 = i.val
  simp [a, b]

lemma maxColoring_noRainbowTriangle (n : ℕ) :
    NoRainbowTriangle (extendColor (maxColoring n)) := by
  intro a b d hab hbd had
  have he (x y : Fin (n + 1)) (hxy : x ≠ y) :
      extendColor (maxColoring n) s(x, y) =
        some (maxColoring n ⟨s(x, y), hxy⟩) :=
    extendColor_edge (maxColoring n) ⟨s(x, y), hxy⟩
  rw [he a b hab, he b d hbd, he a d had]
  simp only [Option.some.injEq, Fin.ext_iff]
  change max a.val b.val - 1 = max b.val d.val - 1 ∨
    max a.val b.val - 1 = max a.val d.val - 1 ∨
    max b.val d.val - 1 = max a.val d.val - 1
  omega

/-- The classical triangle anti-Ramsey number, including the empty host convention. -/
theorem antiRamseyNum_cycleGraph_three (n : ℕ) :
    antiRamseyNum (cycleGraph 3) n = n - 1 := by
  apply le_antisymm (antiRamseyNum_cycleGraph_three_le n)
  cases n with
  | zero => simp
  | succ n =>
    exact le_antiRamseyNum (maxColoring n) (maxColoring_surjective n)
      (no_copy_of_noRainbowTriangle _ (maxColoring_noRainbowTriangle n))

end Erdos1105
