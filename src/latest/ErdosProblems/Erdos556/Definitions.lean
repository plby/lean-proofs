import Util.Ramsey

/-!
# Three-color cycle Ramsey numbers

The color classes are ordinary simple graphs, and containment is non-induced
graph containment.  Existence of a successful order is proved from finite
two-color Ramsey theory before defining the least order.

`cycleGraph` has degenerate values below three; the main cycle theorems will
always have thresholds at least four or five.
-/

namespace Erdos556

open SimpleGraph

/-- A coloring of unordered pairs, represented by a symmetric function.
The diagonal values are ignored by `graph`. -/
structure ThreeColoring (V : Type*) where
  color : V → V → Fin 3
  symm : ∀ u v, color u v = color v u

namespace ThreeColoring

variable {V W : Type*}

/-- The simple graph of edges of one color. -/
def graph (c : ThreeColoring V) (i : Fin 3) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c.color u v = i
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, (c.symm v u).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem graph_adj (c : ThreeColoring V) (i : Fin 3) (u v : V) :
    (c.graph i).Adj u v ↔ u ≠ v ∧ c.color u v = i := Iff.rfl

/-- Pull back an edge coloring along any map. -/
def comap (c : ThreeColoring V) (f : W → V) : ThreeColoring W where
  color u v := c.color (f u) (f v)
  symm u v := c.symm (f u) (f v)

/-- An injective pullback gives a non-induced copy of every color graph. -/
def comapCopy (c : ThreeColoring V) (f : W ↪ V) (i : Fin 3) :
    Copy ((c.comap f).graph i) (c.graph i) where
  toHom := {
    toFun := f
    map_rel' := fun h => ⟨f.injective.ne h.1, h.2⟩ }
  injective' := f.injective

end ThreeColoring

/-- A monochromatic copy of the usual cycle graph. -/
def HasMonoCycle {V : Type*} (c : ThreeColoring V) (n : ℕ) : Prop :=
  ∃ i : Fin 3, cycleGraph n ⊑ c.graph i

/-- Every three-coloring of the complete graph of order `N` has `C_n`. -/
def RamseyCycle (n N : ℕ) : Prop :=
  ∀ c : ThreeColoring (Fin N), HasMonoCycle c n

theorem HasMonoCycle.of_comap {V W : Type*} {c : ThreeColoring V} {n : ℕ}
    (f : W ↪ V) (h : HasMonoCycle (c.comap f) n) : HasMonoCycle c n := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.trans (c.comapCopy f i).isContained⟩

theorem RamseyCycle.mono {n N M : ℕ} (h : RamseyCycle n N) (hNM : N ≤ M) :
    RamseyCycle n M := by
  intro c
  exact HasMonoCycle.of_comap (Fin.castLEEmb hNM) (h (c.comap (Fin.castLEEmb hNM)))

/-- Transfer the Ramsey property to any finite vertex type of the stated size. -/
theorem RamseyCycle.of_card {n N : ℕ} {V : Type*} [Fintype V]
    (h : RamseyCycle n N) (hV : Fintype.card V = N) (c : ThreeColoring V) :
    HasMonoCycle c n := by
  let e : Fin N ≃ V := (Fintype.equivFinOfCardEq hV).symm
  exact HasMonoCycle.of_comap e.toEmbedding (h (c.comap e))

/-- The cycle predicate agrees with the standard simple closed-walk predicate
at every nondegenerate length. -/
theorem hasMonoCycle_iff_walk {V : Type*} (c : ThreeColoring V) {n : ℕ}
    (hn : 3 ≤ n) :
    HasMonoCycle c n ↔
      ∃ (i : Fin 3) (v : V) (p : (c.graph i).Walk v v), p.IsCycle ∧ p.length = n := by
  simp only [HasMonoCycle, cycleGraph_isContained_iff (by omega : 2 < n)]

private theorem compl_contains_clique_of_cliqueFree {a b : ℕ}
    (G : SimpleGraph (Fin (Ramsey.ramseyNumber a b))) (h : G.CliqueFree a) :
    completeGraph (Fin b) ⊑ Gᶜ := by
  apply (not_cliqueFree_iff_top_isContained b).mp
  intro hc
  apply Ramsey.ramseyNumber_spec a b G
  exact ⟨h, by simpa only [← cliqueFree_compl] using hc⟩

/-- Finite three-color clique Ramsey existence, using the explicit nested
two-color bound `R(n, R(n,n))`. -/
theorem exists_monochromatic_clique (n : ℕ)
    (c : ThreeColoring
      (Fin (Ramsey.ramseyNumber n (Ramsey.ramseyNumber n n)))) :
    ∃ i : Fin 3, completeGraph (Fin n) ⊑ c.graph i := by
  classical
  by_cases h₀ : (c.graph 0).CliqueFree n
  · obtain ⟨f⟩ := compl_contains_clique_of_cliqueFree (c.graph 0) h₀
    let d := c.comap f
    by_cases h₁ : (d.graph 1).CliqueFree n
    · obtain ⟨g⟩ := compl_contains_clique_of_cliqueFree (d.graph 1) h₁
      refine ⟨2, ⟨⟨⟨fun u => f (g u), ?_⟩, f.injective.comp g.injective⟩⟩⟩
      intro u v huv
      have huv' : u ≠ v := by simpa using huv
      have hgv : g u ≠ g v := g.injective.ne huv'
      have hfv : f (g u) ≠ f (g v) := f.injective.ne hgv
      have hf := f.toHom.map_rel' (show (completeGraph _).Adj (g u) (g v) from hgv)
      have hg := g.toHom.map_rel' huv
      have hc₀ : c.color (f (g u)) (f (g v)) ≠ 0 := by
        intro he
        exact hf.2 ⟨hfv, he⟩
      have hc₁ : c.color (f (g u)) (f (g v)) ≠ 1 := by
        intro he
        exact hg.2 ⟨hgv, he⟩
      refine ⟨hfv, ?_⟩
      have hc := (c.color (f (g u)) (f (g v))).isLt
      apply Fin.ext
      have hzero : (c.color (f (g u)) (f (g v))).val ≠ 0 := by
        exact fun he => hc₀ (Fin.ext he)
      have hone : (c.color (f (g u)) (f (g v))).val ≠ 1 := by
        exact fun he => hc₁ (Fin.ext he)
      change (c.color (f (g u)) (f (g v))).val = 2
      omega
    · exact ⟨1, ((not_cliqueFree_iff_top_isContained n).mp h₁).trans
        (c.comapCopy f.toEmbedding 1).isContained⟩
  · exact ⟨0, (not_cliqueFree_iff_top_isContained n).mp h₀⟩

/-- Qualitative cycle Ramsey existence is proved independently of the sharp bounds. -/
theorem ramseyCycle_exists (n : ℕ) : ∃ N, RamseyCycle n N := by
  refine ⟨Ramsey.ramseyNumber n (Ramsey.ramseyNumber n n), ?_⟩
  intro c
  obtain ⟨i, hi⟩ := exists_monochromatic_clique n c
  exact ⟨i, (IsContained.of_le (show cycleGraph n ≤ completeGraph (Fin n) from
    le_top)).trans hi⟩

/-- The least three-color Ramsey order of the Mathlib cycle graph. -/
noncomputable def cycleRamsey (n : ℕ) : ℕ := by
  classical
  exact Nat.find (ramseyCycle_exists n)

theorem cycleRamsey_spec (n : ℕ) : RamseyCycle n (cycleRamsey n) := by
  classical
  exact Nat.find_spec (ramseyCycle_exists n)

theorem cycleRamsey_le {n N : ℕ} (h : RamseyCycle n N) : cycleRamsey n ≤ N := by
  classical
  exact Nat.find_min' (ramseyCycle_exists n) h

theorem ramseyCycle_iff {n N : ℕ} : RamseyCycle n N ↔ cycleRamsey n ≤ N :=
  ⟨cycleRamsey_le, fun h => (cycleRamsey_spec n).mono h⟩

theorem lt_cycleRamsey_of_counterexample {n N : ℕ} (c : ThreeColoring (Fin N))
    (hc : ¬ HasMonoCycle c n) : N < cycleRamsey n := by
  by_contra h
  exact hc (ramseyCycle_iff.mpr (by omega) c)

theorem lt_cycleRamsey_of_card_counterexample {V : Type*} [Fintype V] {n : ℕ}
    (c : ThreeColoring V) (hc : ¬ HasMonoCycle c n) : Fintype.card V < cycleRamsey n := by
  by_contra h
  exact hc ((ramseyCycle_iff.mpr (by omega)).of_card rfl c)

end Erdos556
