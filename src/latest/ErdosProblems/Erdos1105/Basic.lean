import Mathlib

/-!
# Anti-Ramsey numbers

Colors are assigned only to genuine edges. A rainbow copy is a vertex-injective
graph homomorphism, not necessarily an induced embedding. Surjectivity ensures
that the number of colors counts colors actually used on edges.
-/

namespace Erdos1105

open SimpleGraph

/-- A copy is rainbow if distinct source edges receive distinct colors. -/
def IsRainbow {α V C : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H.Copy G) (c : G.edgeSet → C) : Prop :=
  Function.Injective (c ∘ f.mapEdgeSet)

/-- Every vertex injection into a complete graph is a non-induced copy. -/
def completeCopy {α V : Type*} (H : SimpleGraph α) (f : α ↪ V) : H.Copy (⊤ : SimpleGraph V) where
  toHom := { toFun := f, map_rel' := fun h ↦ f.injective.ne h.ne }
  injective' := f.injective

def pathCopyOfLE {k n : ℕ} (h : k ≤ n) : (pathGraph k).Copy (pathGraph n) where
  toHom :=
    { toFun := Fin.castLE h
      map_rel' := by
        intro a b hab
        simpa only [pathGraph_adj, Fin.val_castLE] using hab }
  injective' := fun _ _ he ↦ Fin.ext (congrArg (Fin.val (n := n)) he)

/-- The maximum number of colors used by an edge-coloring of `K_n` with no
rainbow copy of `H`. The supremum of an empty feasible set is zero. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {q | ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q,
    Function.Surjective c ∧ ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c}

lemma feasible_colors_le_choose_two {α : Type*}
    (H : SimpleGraph α) (n q : ℕ)
    (hq : ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q,
      Function.Surjective c ∧ ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) :
    q ≤ n.choose 2 := by
  classical
  obtain ⟨c, hc, _⟩ := hq
  have h := Fintype.card_le_of_surjective c hc
  rw [Fintype.card_fin, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at h
  exact h

lemma feasible_colors_bddAbove {α : Type*}
    (H : SimpleGraph α) (n : ℕ) :
    BddAbove {q | ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q,
      Function.Surjective c ∧ ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c} :=
  ⟨n.choose 2, fun q hq ↦ feasible_colors_le_choose_two H n q hq⟩

theorem le_antiRamseyNum {α : Type*} [Fintype α]
    {H : SimpleGraph α} {n q : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q)
    (hc : Function.Surjective c)
    (hH : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) :
    q ≤ antiRamseyNum H n :=
  le_csSup (feasible_colors_bddAbove H n) ⟨c, hc, hH⟩

theorem antiRamseyNum_le {α : Type*} [Fintype α]
    {H : SimpleGraph α} {n b : ℕ}
    (h : ∀ q (c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q),
      Function.Surjective c →
      (∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) → q ≤ b) :
    antiRamseyNum H n ≤ b := by
  apply csSup_le'
  rintro q ⟨c, hc, hH⟩
  exact h q c hc hH

theorem antiRamseyNum_le_real {α : Type*} [Fintype α]
    {H : SimpleGraph α} {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ q (c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q),
      Function.Surjective c →
      (∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) → (q : ℝ) ≤ b) :
    (antiRamseyNum H n : ℝ) ≤ b := by
  have hnat : antiRamseyNum H n ≤ ⌊b⌋₊ := by
    apply antiRamseyNum_le
    intro q c hc hH
    exact Nat.le_floor (h q c hc hH)
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le hb)

/-- In particular, diagonal pairs cannot inflate the number of colors. -/
theorem antiRamseyNum_le_choose_two {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) : antiRamseyNum H n ≤ n.choose 2 := by
  apply antiRamseyNum_le
  intro q c hc hH
  exact feasible_colors_le_choose_two H n q ⟨c, hc, hH⟩

@[simp] theorem antiRamseyNum_zero {α : Type*} [Fintype α]
    (H : SimpleGraph α) : antiRamseyNum H 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using antiRamseyNum_le_choose_two H 0)

@[simp] theorem antiRamseyNum_one {α : Type*} [Fintype α]
    (H : SimpleGraph α) : antiRamseyNum H 1 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using antiRamseyNum_le_choose_two H 1)

/-- If the host contains no copy of `H`, every edge can have its own color. -/
theorem antiRamseyNum_eq_choose_two_of_no_copy {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hH : IsEmpty (H.Copy (⊤ : SimpleGraph (Fin n)))) :
    antiRamseyNum H n = n.choose 2 := by
  classical
  apply le_antisymm (antiRamseyNum_le_choose_two H n)
  have hcard : Fintype.card (⊤ : SimpleGraph (Fin n)).edgeSet = n.choose 2 := by
    rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet ≃ Fin (n.choose 2) :=
    (Fintype.equivFin _).trans (finCongr hcard)
  apply le_antiRamseyNum e e.surjective
  intro f
  exact (hH.false f).elim

theorem antiRamseyNum_eq_choose_two_of_card_lt {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hn : n < Fintype.card α) :
    antiRamseyNum H n = n.choose 2 := by
  apply antiRamseyNum_eq_choose_two_of_no_copy
  refine ⟨fun f ↦ ?_⟩
  have h := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at h
  omega

/-- Regression for vertex injectivity: a five-vertex path does not fit in `K₄`. -/
theorem antiRamseyNum_pathGraph_five_four :
    antiRamseyNum (pathGraph 5) 4 = 6 := by
  have h := antiRamseyNum_eq_choose_two_of_card_lt (pathGraph 5) 4 (by decide)
  norm_num [Nat.choose] at h
  exact h

/-- A coloring on an arbitrary finite vertex type can be relabeled to the
canonical `Fin` vertex and color types in the definition. -/
theorem card_le_antiRamseyNum {α V C : Type*} [Fintype α] [Fintype V] [Fintype C]
    {H : SimpleGraph α} (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hc : Function.Surjective c)
    (hH : ∀ f : H.Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    Fintype.card C ≤ antiRamseyNum H (Fintype.card V) := by
  classical
  let eV : (⊤ : SimpleGraph (Fin (Fintype.card V))) ≃g (⊤ : SimpleGraph V) :=
    { (Fintype.equivFin V).symm with
      map_rel_iff' := by simp }
  let eC := Fintype.equivFin C
  let c' := eC ∘ c ∘ eV.mapEdgeSet
  apply le_antiRamseyNum c' (eC.surjective.comp (hc.comp eV.mapEdgeSet.surjective))
  intro f hf
  apply hH (eV.toCopy.comp f)
  intro a b hab
  have hmap (e : H.edgeSet) :
      (eV.toCopy.comp f).mapEdgeSet e = eV.mapEdgeSet (f.mapEdgeSet e) := by
    apply Subtype.ext
    simp [Copy.mapEdgeSet, Hom.mapEdgeSet, Copy.comp, Iso.mapEdgeSet, Sym2.map_map]
  apply hf
  apply congrArg eC
  simpa only [Function.comp_apply, hmap] using hab

end Erdos1105
