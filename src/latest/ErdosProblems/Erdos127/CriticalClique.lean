import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped ENat
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- The degree-sum consequence needed for a finite critical graph. -/
lemma card_mul_le_twice_edges_of_degree_ge (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hdeg : ∀ v, d ≤ G.degree v) :
    Fintype.card V * d ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    Fintype.card V * d = ∑ _v : V, d := by simp [mul_comm]
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ ↦ hdeg v
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A finite graph of positive finite chromatic number has an induced subgraph
which is vertex-critical for that chromatic number. -/
lemma exists_induced_vertex_critical (G : SimpleGraph V) [DecidableEq V]
    (q : ℕ) (hq : 0 < q)
    (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      (G.induce (s : Set V)).chromaticNumber = q ∧
      ∀ v : s, ((G.induce (s : Set V)).induce ({v}ᶜ : Set s)).Colorable (q - 1) := by
  classical
  let bad : Finset (Finset V) :=
    Finset.univ.powerset.filter fun s ↦
      ¬(G.induce (s : Set V)).Colorable (q - 1)
  have hGq : G.Colorable q := by
    rw [← chromaticNumber_le_iff_colorable, hχ]
  have hGbad : ¬G.Colorable (q - 1) := by
    intro hc
    have := hc.chromaticNumber_le
    rw [hχ, ENat.natCast_le_natCast] at this
    omega
  have hbad : bad.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [bad, mem_filter, mem_powerset, subset_refl, true_and]
    rw [show (↑(Finset.univ : Finset V) : Set V) = Set.univ by ext; simp]
    exact ((colorable_congr (G.induceUnivIso)).not).mpr hGbad
  obtain ⟨s, hsbad, hsmin⟩ := bad.exists_min_image Finset.card hbad
  have hsnot : ¬(G.induce (s : Set V)).Colorable (q - 1) :=
    (Finset.mem_filter.mp hsbad).2
  have hsq : (G.induce (s : Set V)).Colorable q :=
    hGq.of_hom (Embedding.induce (G := G) (s : Set V)).toHom
  refine ⟨s, ?_, ?_⟩
  · apply le_antisymm hsq.chromaticNumber_le
    rw [le_chromaticNumber_iff_colorable]
    intro m hm
    by_contra! hmq
    exact hsnot (hm.mono (by omega))
  · intro v
    have herase : (G.induce ((s.erase v : Finset V) : Set V)).Colorable (q - 1) := by
      by_contra! hnot
      have herase_bad : s.erase v ∈ bad := by
        simp only [bad, mem_filter, mem_powerset, subset_univ, true_and]
        exact hnot
      have hcard := hsmin (s.erase v) herase_bad
      exact (Nat.not_lt_of_ge hcard) (Finset.card_erase_lt_of_mem v.property)
    obtain ⟨C⟩ := herase
    refine ⟨Coloring.mk (fun w ↦ C ⟨w.1.1, ?_⟩) ?_⟩
    · rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun heq ↦ w.property (Subtype.ext heq), w.1.property⟩
    · intro a b hab
      apply C.valid
      simpa using hab

/-- Extend a coloring over one omitted vertex when fewer than `q` colors occur
among its neighbors. -/
lemma colorable_of_induce_compl_singleton_colorable_of_degree_lt
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (v : V) (q : ℕ)
    (hc : (G.induce ({v}ᶜ : Set V)).Colorable q)
    (hdeg : G.degree v < q) : G.Colorable q := by
  classical
  let C : (G.induce ({v}ᶜ : Set V)).Coloring (Fin q) := hc.some
  let N : Finset (Fin q) := (G.neighborFinset v).attach.image fun
      w : {x // x ∈ G.neighborFinset v} ↦
    C ⟨w.1, by
      have hwadj : G.Adj v w.1 := (G.mem_neighborFinset v w.1).mp w.property
      simpa using (G.ne_of_adj hwadj).symm⟩
  have hNcard : N.card < Fintype.card (Fin q) := by
    calc
      N.card ≤ (G.neighborFinset v).attach.card := Finset.card_image_le
      _ = G.degree v := by simp [SimpleGraph.card_neighborFinset_eq_degree]
      _ < q := hdeg
      _ = Fintype.card (Fin q) := by simp
  obtain ⟨c, -, hcN⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := N) (t := Finset.univ) hNcard
  refine ⟨Coloring.mk (fun w ↦ if hw : w = v then c else C ⟨w, by simpa [hw]⟩) ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := (G.ne_of_adj hab).symm
    simp only [dite_true, hb, dite_false]
    intro hcb
    apply hcN
    simp only [N, Finset.mem_image]
    refine ⟨⟨b, by simpa using hab⟩, ?_⟩
    exact ⟨by simp, hcb.symm⟩
  · by_cases hb : b = v
    · subst b
      have hva : a ≠ v := G.ne_of_adj hab
      simp only [ha, dite_false, dite_true]
      intro hac
      apply hcN
      simp only [N, Finset.mem_image]
      refine ⟨⟨a, by simpa [G.adj_comm] using hab⟩, ?_⟩
      exact ⟨by simp, hac⟩
    · simp only [ha, hb, dite_false]
      apply C.valid
      simpa using hab

/-- Vertex-criticality forces the usual lower bound on minimum degree. -/
lemma le_minDegree_of_delete_vertex_colorable
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (q : ℕ) (hnot : ¬G.Colorable q)
    (hdel : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Colorable q) :
    q ≤ G.minDegree := by
  apply G.le_minDegree_of_forall_le_degree
  intro v
  by_contra! hdeg
  exact hnot (colorable_of_induce_compl_singleton_colorable_of_degree_lt G v q (hdel v) hdeg)

/-- Packaged structural consequence: a finite `q`-chromatic graph has an
induced `q`-critical subgraph of minimum degree at least `q - 1`. -/
lemma exists_induced_critical_minDegree
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      (G.induce (s : Set V)).chromaticNumber = q ∧
      q - 1 ≤ (G.induce (s : Set V)).minDegree := by
  obtain ⟨s, hsχ, hsdel⟩ := exists_induced_vertex_critical G q hq hχ
  have hcard : q ≤ Fintype.card s := by
    have h := (G.induce (s : Set V)).chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hsne : s.Nonempty := Finset.card_pos.mp (by simpa using hq.trans_le hcard)
  let : Nonempty s := hsne.to_subtype
  refine ⟨s, hsχ, ?_⟩
  apply le_minDegree_of_delete_vertex_colorable
  · intro hc
    have := hc.chromaticNumber_le
    rw [hsχ, ENat.natCast_le_natCast] at this
    omega
  · exact hsdel

/-- If a `q`-coloring cannot be improved to `q-1` colors, representatives of
two singleton color classes must be adjacent. -/
lemma adj_of_singleton_color_classes
    (G : SimpleGraph V) [DecidableEq V] (q : ℕ)
    (C : G.Coloring (Fin q)) (hnot : ¬G.Colorable (q - 1))
    {u v : V} (huv : u ≠ v)
    (hu : ∀ w, C w = C u → w = u)
    (hv : ∀ w, C w = C v → w = v) : G.Adj u v := by
  classical
  by_contra hadj
  let col : V → Fin q := fun w ↦ if w = u then C v else C w
  have hcu : C v ≠ C u := by
    intro h
    exact huv (hu v h).symm
  have havoid (w : V) : col w ≠ C u := by
    by_cases hw : w = u
    · simp [col, hw, hcu]
    · simp only [col, hw, if_false]
      intro h
      exact hw (hu w h)
  have hproper {a b : V} (hab : G.Adj a b) : col a ≠ col b := by
    by_cases ha : a = u
    · subst a
      have hb : b ≠ u := (G.ne_of_adj hab).symm
      simp only [col, if_pos, hb, if_false]
      intro heq
      have hbv : b = v := hv b heq.symm
      subst b
      exact hadj hab
    · by_cases hb : b = u
      · subst b
        simp only [col, ha, if_false, if_pos]
        intro heq
        have hav : a = v := hv a heq
        subst a
        exact hadj (G.adj_symm hab)
      · simp only [col, ha, hb, if_false]
        exact C.valid hab
  let D : G.Coloring {i : Fin q // i ≠ C u} :=
    Coloring.mk (fun w ↦ ⟨col w, havoid w⟩) (by
      intro a b hab heq
      exact hproper hab (congrArg Subtype.val heq))
  apply hnot
  simpa using D.colorable

/-- In any surjective map to `q` colors, the number of singleton fibers is
at least `2*q - |V|`, in subtraction-free form. -/
lemma twice_card_le_card_add_singleton_fibers
    (q : ℕ) (C : V → Fin q) (hsurj : Function.Surjective C) :
    2 * q ≤ Fintype.card V +
      (Finset.univ.filter fun i : Fin q ↦
        (Finset.univ.filter fun v : V ↦ C v = i).card = 1).card := by
  classical
  let F : Fin q → Finset V := fun i ↦ Finset.univ.filter fun v ↦ C v = i
  let T : Finset (Fin q) := Finset.univ.filter fun i ↦ (F i).card = 1
  have hFpos (i : Fin q) : 0 < (F i).card := by
    obtain ⟨v, hv⟩ := hsurj i
    exact Finset.card_pos.mpr ⟨v, by simp [F, hv]⟩
  have hpoint (i : Fin q) : 2 ≤ (F i).card + if i ∈ T then 1 else 0 := by
    by_cases hi : i ∈ T
    · have hFi : (F i).card = 1 := (Finset.mem_filter.mp hi).2
      simp [hi, hFi]
    · have hFi : (F i).card ≠ 1 := by
        intro heq
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)
      simp only [hi, if_false, add_zero]
      have hp := hFpos i
      omega
  change 2 * q ≤ Fintype.card V + T.card
  calc
    2 * q = ∑ _i : Fin q, 2 := by simp [mul_comm]
    _ ≤ ∑ i : Fin q, ((F i).card + if i ∈ T then 1 else 0) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = (∑ i : Fin q, (F i).card) + ∑ i : Fin q, (if i ∈ T then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = Fintype.card V + T.card := by
      congr 1
      · symm
        apply Finset.card_eq_sum_card_fiberwise
        intro v _
        simp
      · simp

/-- The singleton classes of an optimal coloring yield the desired large
clique.  The bound `2*q ≤ |V| + |S|` is equivalent to `2*q-|V| ≤ |S|`. -/
lemma exists_clique_twice_chromatic_le_card_add_card
    (G : SimpleGraph V) [DecidableEq V] (q : ℕ) (hq : 0 < q)
    (C : G.Coloring (Fin q)) (hχ : G.chromaticNumber = q) :
    ∃ S : Finset V, G.IsClique (S : Set V) ∧
      2 * q ≤ Fintype.card V + S.card := by
  classical
  have hqχ : Fintype.card (Fin q) ≤ G.chromaticNumber := by simp [hχ]
  have hsurj : Function.Surjective C :=
    card_le_chromaticNumber_iff_forall_surjective.mp hqχ C
  have hnot : ¬G.Colorable (q - 1) := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hχ, ENat.natCast_le_natCast] at hle
    omega
  let F : Fin q → Finset V := fun i ↦ Finset.univ.filter fun v ↦ C v = i
  let T : Finset (Fin q) := Finset.univ.filter fun i ↦ (F i).card = 1
  let rep : Fin q → V := fun i ↦ (hsurj i).choose
  have hrep (i : Fin q) : C (rep i) = i := (hsurj i).choose_spec
  have hsingle (i : T) : ∀ w, C w = C (rep i) → w = rep i := by
    intro w hw
    have hiCard : (F i).card = 1 := (Finset.mem_filter.mp i.property).2
    exact (Finset.card_le_one_iff.mp hiCard.le)
      (by simp [F, hw, hrep]) (by simp [F, hrep])
  have hrep_inj : Function.Injective (fun i : T ↦ rep i) := by
    intro i j hij
    apply Subtype.ext
    have hcij := congrArg C hij
    simpa [hrep] using hcij
  let S : Finset V := T.attach.image fun i : T ↦ rep i
  have hScard : S.card = T.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hrep_inj]
    simp
  have hSclique : G.IsClique (S : Set V) := by
    rintro a ha b hb hab
    change a ∈ S at ha
    change b ∈ S at hb
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, _, rfl⟩
    exact adj_of_singleton_color_classes G q C hnot hab (hsingle i) (hsingle j)
  refine ⟨S, hSclique, ?_⟩
  rw [hScard]
  simpa [F, T] using twice_card_le_card_add_singleton_fibers q C hsurj

/-- One-stop finite structural lemma collecting criticality, the handshake
bound, and the singleton-class clique bound. -/
lemma exists_induced_critical_with_handshake_and_clique
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      let H := G.induce (s : Set V)
      H.chromaticNumber = q ∧
      (∀ v : s, (H.induce ({v}ᶜ : Set s)).Colorable (q - 1)) ∧
      q - 1 ≤ H.minDegree ∧
      Fintype.card s * (q - 1) ≤ 2 * H.edgeFinset.card ∧
      ∃ K : Finset s, H.IsClique (K : Set s) ∧
        2 * q ≤ Fintype.card s + K.card := by
  classical
  obtain ⟨s, hsχ, hsdel⟩ := exists_induced_vertex_critical G q hq hχ
  let H := G.induce (s : Set V)
  have hcard : q ≤ Fintype.card s := by
    have h := H.chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hsne : s.Nonempty := Finset.card_pos.mp (by simpa using hq.trans_le hcard)
  let : Nonempty s := hsne.to_subtype
  have hnot : ¬H.Colorable (q - 1) := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hsχ, ENat.natCast_le_natCast] at hle
    omega
  have hmin : q - 1 ≤ H.minDegree :=
    le_minDegree_of_delete_vertex_colorable H (q - 1) hnot hsdel
  have hhand : Fintype.card s * (q - 1) ≤ 2 * H.edgeFinset.card :=
    card_mul_le_twice_edges_of_degree_ge H (q - 1) fun v ↦
      hmin.trans (H.minDegree_le_degree v)
  have hcol : H.Colorable q := by
    rw [← chromaticNumber_le_iff_colorable, hsχ]
  obtain ⟨K, hK, hKcard⟩ :=
    exists_clique_twice_chromatic_le_card_add_card H q hq hcol.some hsχ
  exact ⟨s, hsχ, hsdel, hmin, hhand, K, hK, hKcard⟩

end SimpleGraph
