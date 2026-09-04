/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Function Set SimpleGraph
open scoped ENat

namespace Erdos921.KST

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A proper coloring of the vertices in `S`; vertices outside `S` are ignored. -/
def ColorableOn (G : SimpleGraph V) (S : Finset V) (c : ℕ) : Prop :=
  ∃ color : V → Fin c,
    ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S → G.Adj v w → color v ≠ color w

lemma colorableOn_mono {G : SimpleGraph V} {S T : Finset V} {c : ℕ}
    (hST : S ⊆ T) (h : ColorableOn G T c) : ColorableOn G S c := by
  obtain ⟨color, hcolor⟩ := h
  exact ⟨color, fun _ hv _ hw hadj ↦ hcolor (hST hv) (hST hw) hadj⟩

lemma colorableOn_univ_iff {G : SimpleGraph V} {c : ℕ} :
    ColorableOn G Finset.univ c ↔ G.Colorable c := by
  constructor
  · rintro ⟨color, hcolor⟩
    exact ⟨SimpleGraph.Coloring.mk color fun h ↦ hcolor (by simp) (by simp) h⟩
  · rintro ⟨color, hcolor⟩
    exact ⟨color, fun _ _ _ _ h ↦ hcolor h⟩

lemma colorableOn_empty (G : SimpleGraph V) (c : ℕ) [Nonempty (Fin c)] :
    ColorableOn G ∅ c := by
  exact ⟨fun _ ↦ Classical.choice inferInstance, by simp⟩

lemma colorableOn_one_iff {G : SimpleGraph V} {S : Finset V} :
    ColorableOn G S 1 ↔ ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S → ¬G.Adj v w := by
  constructor
  · rintro ⟨color, hcolor⟩ v hv w hw hadj
    exact (hcolor hv hw hadj) (Subsingleton.elim _ _)
  · intro h
    exact ⟨fun _ ↦ 0, fun _ hv _ hw hadj heq ↦ h hv hw hadj⟩

lemma exists_adj_of_not_colorableOn_one {G : SimpleGraph V} {S : Finset V}
    (h : ¬ColorableOn G S 1) :
    ∃ v ∈ S, ∃ w ∈ S, G.Adj v w := by
  rw [colorableOn_one_iff] at h
  push Not at h
  exact h

/-- Color the union with disjoint palettes.  No separation hypothesis is
needed because vertices in the two pieces receive colors in different summands. -/
lemma colorableOn_union {G : SimpleGraph V} {S T : Finset V} {a b : ℕ}
    (hS : ColorableOn G S a) (hT : ColorableOn G T b) :
    ColorableOn G (S ∪ T) (a + b) := by
  obtain ⟨cS, hcS⟩ := hS
  obtain ⟨cT, hcT⟩ := hT
  let color : V → Fin (a + b) := fun v ↦
    if hv : v ∈ S then Fin.castAdd b (cS v) else Fin.natAdd a (cT v)
  refine ⟨color, ?_⟩
  intro v hv w hw hadj heq
  simp only [Finset.mem_union] at hv hw
  by_cases hvS : v ∈ S <;> by_cases hwS : w ∈ S
  · apply hcS hvS hwS hadj
    have := congrArg Fin.val heq
    exact Fin.eq_of_val_eq (by simpa [color, hvS, hwS] using this)
  · have : (Fin.castAdd b (cS v) : Fin (a + b)) ≠ Fin.natAdd a (cT w) :=
      by
        intro h
        have he := congrArg Fin.val h
        have hvlt := (cS v).isLt
        simp only [Fin.coe_castAdd, Fin.coe_natAdd] at he
        omega
    exact this (by simpa [color, hvS, hwS] using heq)
  · have : (Fin.natAdd a (cT v) : Fin (a + b)) ≠ Fin.castAdd b (cS w) :=
      by
        intro h
        have he := congrArg Fin.val h
        have hwlt := (cS w).isLt
        simp only [Fin.coe_castAdd, Fin.coe_natAdd] at he
        omega
    exact this (by simpa [color, hvS, hwS] using heq)
  · have hvT : v ∈ T := hv.resolve_left hvS
    have hwT : w ∈ T := hw.resolve_left hwS
    apply hcT hvT hwT hadj
    have := congrArg Fin.val heq
    exact Fin.eq_of_val_eq (by simpa [color, hvS, hwS] using this)

lemma colorableOn_union_of_le {G : SimpleGraph V} {W S T : Finset V} {a b : ℕ}
    (hW : W ⊆ S ∪ T) (hS : ColorableOn G S a) (hT : ColorableOn G T b) :
    ColorableOn G W (a + b) :=
  colorableOn_mono hW (colorableOn_union hS hT)

lemma colorableOn_of_colorable {G : SimpleGraph V} (S : Finset V) {c : ℕ}
    (h : G.Colorable c) : ColorableOn G S c := by
  exact colorableOn_mono (by simp) (colorableOn_univ_iff.mpr h)

/-- The color class with color `i`. -/
def colorClass (H : Finset V) {c : ℕ} (color : V → Fin c) (i : Fin c) : Finset V :=
  H.filter fun v ↦ color v = i

lemma colorClass_subset (H : Finset V) {c : ℕ} (color : V → Fin c) (i : Fin c) :
    colorClass H color i ⊆ H :=
  Finset.filter_subset _ _

lemma colorClass_independent {G : SimpleGraph V} {H : Finset V} {c : ℕ}
    {color : V → Fin c}
    (hcolor : ∀ ⦃v⦄, v ∈ H → ∀ ⦃w⦄, w ∈ H → G.Adj v w → color v ≠ color w)
    (i : Fin c) : G.IsIndepSet (colorClass H color i : Set V) := by
  intro v hv w hw _hvw hadj
  simp only [colorClass, Finset.mem_coe, Finset.mem_filter] at hv hw
  exact hcolor hv.1 hw.1 hadj (hv.2.trans hw.2.symm)

/-- Delete one color class from a `c`-coloring and compress the remaining
colors to `Fin (c-1)`. -/
lemma colorableOn_sdiff_colorClass {G : SimpleGraph V} {H : Finset V} {c : ℕ}
    (hc : 1 < c) {color : V → Fin c}
    (hcolor : ∀ ⦃v⦄, v ∈ H → ∀ ⦃w⦄, w ∈ H → G.Adj v w → color v ≠ color w)
    (i : Fin c) : ColorableOn G (H \ colorClass H color i) (c - 1) := by
  have hcard : Fintype.card {j : Fin c // j ≠ i} = c - 1 := by
    simp
  let e : {j : Fin c // j ≠ i} ≃ Fin (c - 1) :=
    (Fintype.equivFin {j : Fin c // j ≠ i}).trans
      (Equiv.cast (congrArg Fin hcard))
  let newColor : V → Fin (c - 1) := fun v ↦
    if hv : color v ≠ i then e ⟨color v, hv⟩ else ⟨0, by omega⟩
  refine ⟨newColor, ?_⟩
  intro v hv w hw hadj heq
  simp only [Finset.mem_sdiff, colorClass, Finset.mem_filter] at hv hw
  have hvi : color v ≠ i := fun h ↦ hv.2 ⟨hv.1, h⟩
  have hwi : color w ≠ i := fun h ↦ hw.2 ⟨hw.1, h⟩
  have hsub : (⟨color v, hvi⟩ : {j : Fin c // j ≠ i}) = ⟨color w, hwi⟩ :=
    e.injective (by simpa [newColor, hvi, hwi] using heq)
  exact hcolor hv.1 hw.1 hadj (congrArg Subtype.val hsub)

/-- Two sets with no cross-edge may reuse the same palette. -/
lemma colorableOn_union_of_noEdges {G : SimpleGraph V} {S T : Finset V} {c : ℕ}
    (hS : ColorableOn G S c) (hT : ColorableOn G T c)
    (hsep : ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ T → ¬G.Adj v w) :
    ColorableOn G (S ∪ T) c := by
  obtain ⟨cS, hcS⟩ := hS
  obtain ⟨cT, hcT⟩ := hT
  let color : V → Fin c := fun v ↦ if v ∈ S then cS v else cT v
  refine ⟨color, ?_⟩
  intro v hv w hw hadj heq
  simp only [Finset.mem_union] at hv hw
  by_cases hvS : v ∈ S <;> by_cases hwS : w ∈ S
  · exact hcS hvS hwS hadj (by simpa [color, hvS, hwS] using heq)
  · exact hsep hvS (hw.resolve_left hwS) hadj
  · exact hsep hwS (hv.resolve_left hvS) hadj.symm
  · exact hcT (hv.resolve_left hvS) (hw.resolve_left hwS) hadj
      (by simpa [color, hvS, hwS] using heq)

/-- Ambient-radius witness, measured in the original graph.  The center need
not lie in the displayed vertex set; this is KST's "radius in `G`". -/
def RadiusAtMost (G : SimpleGraph V) (S : Finset V) (R : ℕ) : Prop :=
  ∃ z : V, ∀ v ∈ S, G.edist z v ≤ R

lemma radiusAtMost_mono {G : SimpleGraph V} {S T : Finset V} {R : ℕ}
    (hST : S ⊆ T) (h : RadiusAtMost G T R) : RadiusAtMost G S R := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun v hv ↦ hz v (hST hv)⟩

lemma radiusAtMost_mono_bound {G : SimpleGraph V} {S : Finset V} {R R' : ℕ}
    (hRR' : R ≤ R') (h : RadiusAtMost G S R) : RadiusAtMost G S R' := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun v hv ↦ (hz v hv).trans (by exact_mod_cast hRR')⟩

lemma radiusAtMost_singleton (G : SimpleGraph V) (v : V) :
    RadiusAtMost G {v} 0 := by
  exact ⟨v, by simp⟩

/-- Extended distance from a nonempty finite set. -/
def eDistTo (G : SimpleGraph V) (P : Finset V) (hP : P.Nonempty) (v : V) : ℕ∞ :=
  P.inf' hP fun p ↦ G.edist p v

lemma exists_edist_eq_eDistTo (G : SimpleGraph V) (P : Finset V)
    (hP : P.Nonempty) (v : V) :
    ∃ p ∈ P, G.edist p v = eDistTo G P hP v := by
  obtain ⟨p, hp, hEq⟩ := Finset.exists_mem_eq_inf' hP (fun p ↦ G.edist p v)
  exact ⟨p, hp, hEq.symm⟩

lemma eDistTo_le_edist (G : SimpleGraph V) (P : Finset V) (hP : P.Nonempty)
    {p v : V} (hp : p ∈ P) : eDistTo G P hP v ≤ G.edist p v :=
  Finset.inf'_le _ hp

lemma eDistTo_self (G : SimpleGraph V) (P : Finset V) (hP : P.Nonempty)
    {p : V} (hp : p ∈ P) : eDistTo G P hP p = 0 := by
  apply le_antisymm
  · simpa using eDistTo_le_edist G P hP (v := p) hp
  · exact bot_le

lemma eDistTo_adj_le_add_one (G : SimpleGraph V) (P : Finset V)
    (hP : P.Nonempty) {v w : V} (hvw : G.Adj v w) :
    eDistTo G P hP w ≤ eDistTo G P hP v + 1 := by
  obtain ⟨p, hp, hpv⟩ := exists_edist_eq_eDistTo G P hP v
  calc
    eDistTo G P hP w ≤ G.edist p w := eDistTo_le_edist G P hP hp
    _ ≤ G.edist p v + G.edist v w := SimpleGraph.edist_triangle
    _ = eDistTo G P hP v + 1 := by rw [hpv, G.edist_eq_one_iff_adj.mpr hvw]

lemma eDistTo_adj_le_add_one' (G : SimpleGraph V) (P : Finset V)
    (hP : P.Nonempty) {v w : V} (hvw : G.Adj v w) :
    eDistTo G P hP v ≤ eDistTo G P hP w + 1 :=
  eDistTo_adj_le_add_one G P hP hvw.symm

/-- The vertices of `H` at ambient distance exactly `j` from `P`. -/
def layer (G : SimpleGraph V) (H P : Finset V) (hP : P.Nonempty) (j : ℕ) : Finset V :=
  H.filter fun v ↦ eDistTo G P hP v = j

@[simp]
lemma mem_layer {G : SimpleGraph V} {H P : Finset V} {hP : P.Nonempty}
    {j : ℕ} {v : V} :
    v ∈ layer G H P hP j ↔ v ∈ H ∧ eDistTo G P hP v = j := by
  simp [layer]

lemma layer_subset (G : SimpleGraph V) (H P : Finset V) (hP : P.Nonempty) (j : ℕ) :
    layer G H P hP j ⊆ H :=
  Finset.filter_subset _ _

lemma disjoint_layers {G : SimpleGraph V} {H P : Finset V} (hP : P.Nonempty)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (layer G H P hP i) (layer G H P hP j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  apply hij
  exact_mod_cast (mem_layer.mp hvi).2.symm.trans (mem_layer.mp hvj).2

/-- The KST local hypothesis in its finite-set form. -/
def LocallyColorable (G : SimpleGraph V) (R c : ℕ) : Prop :=
  ∀ S : Finset V, RadiusAtMost G S R → ColorableOn G S c

/-- A large set with small ambient radius. -/
def IsObstruction (G : SimpleGraph V) (Q : Finset V) (s R : ℕ) : Prop :=
  s ≤ Q.card ∧ RadiusAtMost G Q R

lemma exists_maximal_colorableOn (G : SimpleGraph V) (W : Finset V) {c : ℕ}
    (hc : 0 < c) :
    ∃ H : Finset V, H ⊆ W ∧ ColorableOn G H c ∧
      ∀ T : Finset V, T ⊆ W → ColorableOn G T c → T.card ≤ H.card := by
  let candidates : Finset (Finset V) :=
    W.powerset.filter fun H ↦ ColorableOn G H c
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.empty_mem_powerset, true_and]
    have : Nonempty (Fin c) := Fin.pos_iff_nonempty.mp hc
    exact colorableOn_empty G c
  obtain ⟨H, hH, hmax⟩ := candidates.exists_max_image Finset.card hne
  refine ⟨H, ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
  · exact (Finset.mem_filter.mp hH).2
  · intro T hTW hT
    exact hmax T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTW, hT⟩)

lemma card_sdiff_union_gt {P H B : Finset V}
    (hBH : B ⊆ H) (hdisj : Disjoint P H) (hlt : B.card < P.card) :
    H.card < ((H \ B) ∪ P).card := by
  have hsep : Disjoint (H \ B) P :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj.symm
  rw [Finset.card_union_of_disjoint hsep, Finset.card_sdiff_of_subset hBH]
  have hBHcard := Finset.card_le_card hBH
  omega

/-- A set lying in a `j`-neighborhood of `P` inherits the radius of `P`, plus
`j`. -/
lemma radiusAtMost_of_eDistTo_le {G : SimpleGraph V} {P S : Finset V}
    (hP : P.Nonempty) {R j : ℕ} (hPR : RadiusAtMost G P R)
    (hS : ∀ v ∈ S, eDistTo G P hP v ≤ j) :
    RadiusAtMost G S (R + j) := by
  obtain ⟨z, hz⟩ := hPR
  refine ⟨z, ?_⟩
  intro v hv
  obtain ⟨p, hpP, hpv⟩ := exists_edist_eq_eDistTo G P hP v
  calc
    G.edist z v ≤ G.edist z p + G.edist p v := SimpleGraph.edist_triangle
    _ ≤ (R : ℕ∞) + j := add_le_add (hz p hpP) (by simpa [hpv] using hS v hv)
    _ = (R + j : ℕ) := by simp

lemma colorableOn_sdiff_subset_add {G : SimpleGraph V} {W K : Finset V}
    {q r : ℕ} (hK : K ⊆ W) (hWK : ColorableOn G (W \ K) q)
    (hKcol : ColorableOn G K r) : ColorableOn G W (q + r) := by
  apply colorableOn_union_of_le (S := W \ K) (T := K)
  · intro v hv
    by_cases hvK : v ∈ K
    · exact Finset.mem_union_right _ hvK
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hvK⟩)
  · exact hWK
  · exact hKcol

/-- The maximality step in KST: every two consecutive nonzero distance
layers contain many vertices outside an arbitrary independent set. -/
lemma boundary_card_ge
    {G : SimpleGraph V} {W H P I : Finset V} {a c d m j : ℕ}
    (ha : 0 < a) (hc : 1 < c) (hm : m + 1 ≤ d) (hj0 : 0 < j) (hj : j < 2 * a)
    (hHW : H ⊆ W) (hHcol : ColorableOn G H c)
    (hHmax : ∀ T : Finset V, T ⊆ W → ColorableOn G T c → T.card ≤ H.card)
    (hPW : P ⊆ W) (hPH : Disjoint P H) (hP : P.Nonempty)
    (hPrad : RadiusAtMost G P (2 * m * a))
    (hI : G.IsIndepSet (I : Set V))
    (hlocal : LocallyColorable G (2 * d * a) c) :
    P.card ≤ (((layer G H P hP j) ∪ (layer G H P hP (j + 1))) \ I).card := by
  let Lj := layer G H P hP j
  let Lj1 := layer G H P hP (j + 1)
  let B := (Lj ∪ Lj1) \ I
  by_contra hnot
  have hlt : B.card < P.card := Nat.lt_of_not_ge hnot
  have hBH : B ⊆ H := by
    intro v hv
    have hv' := (Finset.mem_sdiff.mp hv).1
    rcases Finset.mem_union.mp hv' with hvj | hvj1
    · exact layer_subset G H P hP j hvj
    · exact layer_subset G H P hP (j + 1) hvj1
  let H' := (H \ B) ∪ P
  have hH'W : H' ⊆ W := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hHW (Finset.mem_sdiff.mp hv).1
    · exact hPW hv
  have hcard : H.card < H'.card := by
    exact card_sdiff_union_gt hBH hPH hlt
  let H0 := H'.filter fun v ↦ eDistTo G P hP v ≤ j
  let H1 := H' \ H0
  have hP0 : P ⊆ H0 := by
    intro p hp
    simp only [H0, Finset.mem_filter]
    refine ⟨Finset.mem_union_right _ hp, ?_⟩
    rw [eDistTo_self G P hP hp]
    simp
  have hH0H' : H0 ⊆ H' := Finset.filter_subset _ _
  have hH1base : H1 ⊆ H \ B := by
    intro v hv
    have hvH' := (Finset.mem_sdiff.mp hv).1
    have hvH0 := (Finset.mem_sdiff.mp hv).2
    rcases Finset.mem_union.mp hvH' with hvHB | hvP
    · exact hvHB
    · exact (hvH0 (hP0 hvP)).elim
  have hH1H : H1 ⊆ H := fun _ hv ↦ (Finset.mem_sdiff.mp (hH1base hv)).1
  have hrad0 : RadiusAtMost G H0 (2 * d * a) := by
    have hnear : RadiusAtMost G H0 (2 * m * a + j) := by
      apply radiusAtMost_of_eDistTo_le hP hPrad
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    apply radiusAtMost_mono_bound (h := hnear)
    have hjle : j ≤ 2 * a := hj.le
    nlinarith
  have hH0col : ColorableOn G H0 c := hlocal H0 hrad0
  have hH1col : ColorableOn G H1 c := colorableOn_mono hH1H hHcol
  have hsep : ∀ ⦃v⦄, v ∈ H0 → ∀ ⦃w⦄, w ∈ H1 → ¬G.Adj v w := by
    intro v hv w hw hvw
    have hvdist : eDistTo G P hP v ≤ j := (Finset.mem_filter.mp hv).2
    have hwH' : w ∈ H' := (Finset.mem_sdiff.mp hw).1
    have hwNot0 : w ∉ H0 := (Finset.mem_sdiff.mp hw).2
    have hwNotLe : ¬eDistTo G P hP w ≤ j := by
      intro hwle
      exact hwNot0 (Finset.mem_filter.mpr ⟨hwH', hwle⟩)
    have hwlt : (j : ℕ∞) < eDistTo G P hP w := lt_of_not_ge hwNotLe
    have hwle : eDistTo G P hP w ≤ (j + 1 : ℕ) := by
      calc
        eDistTo G P hP w ≤ eDistTo G P hP v + 1 :=
          eDistTo_adj_le_add_one G P hP hvw
        _ ≤ (j : ℕ∞) + 1 := by simpa [add_comm] using add_le_add_right hvdist 1
        _ = (j + 1 : ℕ) := by simp
    have hwge : (j + 1 : ℕ∞) ≤ eDistTo G P hP w :=
      ENat.natCast_add_one_le_iff.mpr hwlt
    have hwEq : eDistTo G P hP w = (j + 1 : ℕ) := le_antisymm hwle hwge
    have hwLayer : w ∈ Lj1 := by
      exact mem_layer.mpr ⟨hH1H hw, hwEq⟩
    have hwNotB : w ∉ B := (Finset.mem_sdiff.mp (hH1base hw)).2
    have hwI : w ∈ I := by
      by_contra hwNI
      exact hwNotB <| Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ hwLayer, hwNI⟩
    have hback := eDistTo_adj_le_add_one G P hP hvw
    rw [hwEq] at hback
    have hvge : (j : ℕ∞) ≤ eDistTo G P hP v := by
      have : (j : ℕ∞) + 1 ≤ eDistTo G P hP v + 1 := by simpa using hback
      exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp this
    have hvEq : eDistTo G P hP v = (j : ℕ) := le_antisymm hvdist hvge
    have hvNotP : v ∉ P := by
      intro hvP
      have hvzero := eDistTo_self G P hP hvP
      rw [hvEq] at hvzero
      norm_num at hvzero
      have : j = 0 := by exact_mod_cast hvzero
      exact hj0.ne' this
    have hvH' : v ∈ H' := hH0H' hv
    have hvHB : v ∈ H \ B := by
      rcases Finset.mem_union.mp hvH' with h | h
      · exact h
      · exact (hvNotP h).elim
    have hvLayer : v ∈ Lj := mem_layer.mpr ⟨(Finset.mem_sdiff.mp hvHB).1, hvEq⟩
    have hvI : v ∈ I := by
      by_contra hvNI
      exact (Finset.mem_sdiff.mp hvHB).2 <| Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ hvLayer, hvNI⟩
    exact hI hvI hwI hvw.ne hvw
  have hH'col : ColorableOn G H' c := by
    have hcover : H' = H0 ∪ H1 := by
      exact (Finset.union_sdiff_of_subset hH0H').symm
    rw [hcover]
    exact colorableOn_union_of_noEdges hH0col hH1col hsep
  exact (not_lt_of_ge (hHmax H' hH'W hH'col)) hcard

/-- Union of the first `a` disjoint pairs of nonzero layers. -/
def obstructionBands (G : SimpleGraph V) (H P I : Finset V)
    (hP : P.Nonempty) (a : ℕ) : Finset V :=
  (Finset.range a).biUnion fun t ↦
    ((layer G H P hP (2 * t + 1)) ∪ (layer G H P hP (2 * t + 2))) \ I

lemma obstructionBands_subset {G : SimpleGraph V} {W H P I : Finset V}
    (hP : P.Nonempty) {a : ℕ} (hHW : H ⊆ W) :
    obstructionBands G H P I hP a ⊆ W \ I := by
  intro v hv
  simp only [obstructionBands, Finset.mem_biUnion] at hv
  obtain ⟨t, ht, hv⟩ := hv
  have hvout := Finset.mem_sdiff.mp hv
  refine Finset.mem_sdiff.mpr ⟨?_, hvout.2⟩
  rcases Finset.mem_union.mp hvout.1 with hvL | hvL
  · exact hHW (layer_subset G H P hP (2 * t + 1) hvL)
  · exact hHW (layer_subset G H P hP (2 * t + 2) hvL)

lemma obstructionBands_eDistTo_le {G : SimpleGraph V} {H P I : Finset V}
    (hP : P.Nonempty) {a : ℕ} {v : V}
    (hv : v ∈ obstructionBands G H P I hP a) :
    eDistTo G P hP v ≤ (2 * a : ℕ) := by
  simp only [obstructionBands, Finset.mem_biUnion] at hv
  obtain ⟨t, ht, hv⟩ := hv
  have htlt : t < a := Finset.mem_range.mp ht
  have hv' := (Finset.mem_sdiff.mp hv).1
  rcases Finset.mem_union.mp hv' with hvL | hvL
  · rw [(mem_layer.mp hvL).2]
    exact_mod_cast (by omega : 2 * t + 1 ≤ 2 * a)
  · rw [(mem_layer.mp hvL).2]
    exact_mod_cast (by omega : 2 * t + 2 ≤ 2 * a)

lemma obstructionBands_pairwiseDisjoint {G : SimpleGraph V} {H P I : Finset V}
    (hP : P.Nonempty) {a : ℕ} :
    ((Finset.range a : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun t ↦ ((layer G H P hP (2 * t + 1)) ∪
        (layer G H P hP (2 * t + 2))) \ I) := by
  intro s hs t ht hst
  change Disjoint
    (((layer G H P hP (2 * s + 1)) ∪ (layer G H P hP (2 * s + 2))) \ I)
    (((layer G H P hP (2 * t + 1)) ∪ (layer G H P hP (2 * t + 2))) \ I)
  rw [Finset.disjoint_left]
  intro v hvs hvt
  have hvs' := (Finset.mem_sdiff.mp hvs).1
  have hvt' := (Finset.mem_sdiff.mp hvt).1
  rcases Finset.mem_union.mp hvs' with hvs1 | hvs2 <;>
    rcases Finset.mem_union.mp hvt' with hvt1 | hvt2
  · have hEq : 2 * s + 1 = 2 * t + 1 := by
      exact_mod_cast (mem_layer.mp hvs1).2.symm.trans (mem_layer.mp hvt1).2
    exact hst (by omega)
  · have hEq : 2 * s + 1 = 2 * t + 2 := by
      exact_mod_cast (mem_layer.mp hvs1).2.symm.trans (mem_layer.mp hvt2).2
    omega
  · have hEq : 2 * s + 2 = 2 * t + 1 := by
      exact_mod_cast (mem_layer.mp hvs2).2.symm.trans (mem_layer.mp hvt1).2
    omega
  · have hEq : 2 * s + 2 = 2 * t + 2 := by
      exact_mod_cast (mem_layer.mp hvs2).2.symm.trans (mem_layer.mp hvt2).2
    exact hst (by omega)

lemma card_obstructionBands_ge
    {G : SimpleGraph V} {W H P I : Finset V} {a c d m : ℕ}
    (ha : 0 < a) (hc : 1 < c) (hm : m + 1 ≤ d)
    (hHW : H ⊆ W) (hHcol : ColorableOn G H c)
    (hHmax : ∀ T : Finset V, T ⊆ W → ColorableOn G T c → T.card ≤ H.card)
    (hPW : P ⊆ W) (hPH : Disjoint P H) (hP : P.Nonempty)
    (hPrad : RadiusAtMost G P (2 * m * a))
    (hI : G.IsIndepSet (I : Set V))
    (hlocal : LocallyColorable G (2 * d * a) c) :
    a * P.card ≤ (obstructionBands G H P I hP a).card := by
  let band : ℕ → Finset V := fun t ↦
    ((layer G H P hP (2 * t + 1)) ∪ (layer G H P hP (2 * t + 2))) \ I
  have hpair : ((Finset.range a : Finset ℕ) : Set ℕ).PairwiseDisjoint band :=
    obstructionBands_pairwiseDisjoint hP
  rw [obstructionBands, Finset.card_biUnion hpair]
  calc
    a * P.card = ∑ _t ∈ Finset.range a, P.card := by simp
    _ ≤ ∑ t ∈ Finset.range a, (band t).card := by
      apply Finset.sum_le_sum
      intro t ht
      exact boundary_card_ge (j := 2 * t + 1) ha hc hm (by omega)
        (by have := Finset.mem_range.mp ht; omega) hHW hHcol hHmax hPW hPH
        hP hPrad hI hlocal
    _ = ∑ t ∈ Finset.range a,
        ((((layer G H P hP (2 * t + 1)) ∪
          (layer G H P hP (2 * t + 2))) \ I).card) := rfl

/-- KST's obstruction induction (Lemma 2 in the 1984 paper). -/
theorem obstruction_induction
    {G : SimpleGraph V} {a c d l : ℕ}
    (ha : 0 < a) (hc : 1 < c) (hl : l ≤ d)
    (hlocal : LocallyColorable G (2 * d * a) c)
    (W I : Finset V) (hI : G.IsIndepSet (I : Set V))
    (hnot : ¬ColorableOn G W (l * (c - 1) + 1)) :
    ∃ Q : Finset V, Q ⊆ W \ I ∧ IsObstruction G Q (a ^ l) (2 * l * a) := by
  induction l generalizing W I with
  | zero =>
      have hnot1 : ¬ColorableOn G W 1 := by simpa using hnot
      obtain ⟨v, hvW, w, hwW, hvw⟩ := exists_adj_of_not_colorableOn_one hnot1
      have hout : v ∉ I ∨ w ∉ I := by
        by_contra h
        push_neg at h
        exact hI h.1 h.2 hvw.ne hvw
      rcases hout with hvI | hwI
      · refine ⟨{v}, ?_, ?_⟩
        · simpa using And.intro hvW hvI
        · constructor
          · simp
          · simpa using radiusAtMost_singleton G v
      · refine ⟨{w}, ?_, ?_⟩
        · simpa using And.intro hwW hwI
        · constructor
          · simp
          · simpa using radiusAtMost_singleton G w
  | succ m ih =>
      have hm : m + 1 ≤ d := by simpa using hl
      obtain ⟨H, hHW, hHcol, hHmax⟩ :=
        exists_maximal_colorableOn (c := c) G W (by omega)
      have hHcol_saved := hHcol
      obtain ⟨color, hcolor⟩ := hHcol
      let i : Fin c := ⟨0, by omega⟩
      let J : Finset V := colorClass H color i
      let K : Finset V := H \ J
      let W' : Finset V := W \ K
      have hJind : G.IsIndepSet (J : Set V) :=
        colorClass_independent hcolor i
      have hKcol : ColorableOn G K (c - 1) := by
        exact colorableOn_sdiff_colorClass hc hcolor i
      have hKW : K ⊆ W := fun _ hv ↦ hHW (Finset.mem_sdiff.mp hv).1
      have hW'not : ¬ColorableOn G W' (m * (c - 1) + 1) := by
        intro hW'col
        have hWcol := colorableOn_sdiff_subset_add hKW hW'col hKcol
        apply hnot
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hWcol
      obtain ⟨P, hPsub, hPcard, hPrad⟩ :=
        ih (hl := by omega) (W := W') (I := J) hJind hW'not
      have hP : P.Nonempty := by
        exact Finset.card_pos.mp ((pow_pos ha m).trans_le hPcard)
      have hPW : P ⊆ W := by
        intro p hp
        have hpW' : p ∈ W' := (Finset.mem_sdiff.mp (hPsub hp)).1
        exact (Finset.mem_sdiff.mp hpW').1
      have hPH : Disjoint P H := by
        rw [Finset.disjoint_left]
        intro p hpP hpH
        have hpSub := hPsub hpP
        have hpW' := (Finset.mem_sdiff.mp hpSub).1
        have hpNotJ := (Finset.mem_sdiff.mp hpSub).2
        have hpNotK := (Finset.mem_sdiff.mp hpW').2
        by_cases hpi : color p = i
        · exact hpNotJ (by simp [J, colorClass, hpH, hpi])
        · exact hpNotK (by simp [K, J, colorClass, hpH, hpi])
      let Q := obstructionBands G H P I hP a
      refine ⟨Q, obstructionBands_subset hP hHW, ?_, ?_⟩
      · have hbands := card_obstructionBands_ge ha hc hm hHW
          hHcol_saved hHmax hPW hPH hP hPrad hI hlocal
        calc
          a ^ (m + 1) = a * a ^ m := by rw [pow_succ']
          _ ≤ a * P.card := Nat.mul_le_mul_left a hPcard
          _ ≤ Q.card := hbands
      · have hnear : RadiusAtMost G Q (2 * m * a + 2 * a) := by
          apply radiusAtMost_of_eDistTo_le hP hPrad
          intro v hv
          exact obstructionBands_eDistTo_le hP hv
        convert hnear using 1 <;> ring

/-- Integer form of the Kierstead--Szemerédi--Trotter local-coloring theorem. -/
theorem colorable_of_locallyColorable
    {G : SimpleGraph V} [Nonempty V] {a c d : ℕ}
    (ha : 0 < a) (hc : 1 < c) (hcard : Fintype.card V ≤ a ^ d)
    (hlocal : LocallyColorable G (2 * d * a) c) :
    G.Colorable (d * (c - 1) + 1) := by
  rw [← colorableOn_univ_iff]
  by_contra hnot
  let v : V := Classical.choice inferInstance
  have hind : G.IsIndepSet ((↑({v} : Finset V)) : Set V) := by simp
  obtain ⟨Q, hQsub, hQcard, _hQrad⟩ :=
    obstruction_induction ha hc (le_refl d) hlocal Finset.univ {v} hind hnot
  have hupper : Q.card ≤ Fintype.card V - 1 := by
    calc
      Q.card ≤ (Finset.univ \ {v}).card := Finset.card_le_card hQsub
      _ = Fintype.card V - 1 := by
        rw [Finset.card_sdiff_of_subset (by simp)]
        simp
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  omega

end

end Erdos921.KST
