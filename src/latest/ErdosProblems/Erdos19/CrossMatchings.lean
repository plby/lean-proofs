import ErdosProblems.Erdos19.OutlierPartners
import ErdosProblems.Erdos19.PairingSubgraph
import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Matchings between exceptional vertices and their assigned partners -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V J : Type*} (X : Set V) (active : X → Finset J)

def requestSource (e : ActiveRequest active) : V := e.1.1.1

def partnerVertices (partner : ActiveRequest active → V) (i : J) : Set V :=
  {v | ∃ e : ActiveRequest active, e.1.2 = i ∧ partner e = v}

def crossMatching (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (i : J) : G.Subgraph :=
  pairingSubgraph G (fun e : {e : ActiveRequest active // e.1.2 = i} ↦ requestSource X active e.1)
    (fun e ↦ partner e.1) (fun e ↦ hadj e.1)

theorem crossMatching_verts (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (i : J) (v : V) :
    v ∈ (crossMatching X active G partner hadj i).verts ↔
      ∃ e : ActiveRequest active, e.1.2 = i ∧ (requestSource X active e = v ∨ partner e = v) := by
  rw [crossMatching, pairingSubgraph_verts]
  constructor
  · rintro (⟨e, he⟩ | ⟨e, he⟩)
    · exact ⟨e.1, e.2, Or.inl he⟩
    · exact ⟨e.1, e.2, Or.inr he⟩
  · rintro ⟨e, hi, h | h⟩
    · exact Or.inl ⟨⟨e, hi⟩, h⟩
    · exact Or.inr ⟨⟨e, hi⟩, h⟩

theorem crossMatching_adj (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (i : J) (x y : V) :
    (crossMatching X active G partner hadj i).Adj x y ↔
      ∃ e : ActiveRequest active, e.1.2 = i ∧
        ((requestSource X active e = x ∧ partner e = y) ∨
          (requestSource X active e = y ∧ partner e = x)) := by
  rw [crossMatching, pairingSubgraph_adj]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.1, e.2, he⟩
  · rintro ⟨e, hi, he⟩
    exact ⟨⟨e, hi⟩, he⟩

theorem crossMatching_isMatching (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e))
    (hout : ∀ e, partner e ∉ X)
    (hproper : ∀ e f, e ≠ f → e.1.2 = f.1.2 → partner e ≠ partner f) (i : J) :
    (crossMatching X active G partner hadj i).IsMatching := by
  apply pairingSubgraph_isMatching
  · intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Subtype.ext h) (e.2.trans f.2.symm)
  · intro e f h
    apply Subtype.ext
    by_contra hef
    exact hproper e.1 f.1 hef (e.2.trans f.2.symm) h
  · apply Set.disjoint_left.mpr
    rintro v ⟨e, he⟩ ⟨f, hf⟩
    have hv : v ∈ X := he ▸ e.1.1.1.2
    have hf' : partner f.1 = v := hf
    apply hout f.1
    rw [hf']
    exact hv

theorem crossMatching_mem_of_outlier (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (hout : ∀ e, partner e ∉ X)
    (i : J) (u : X) :
    u.1 ∈ (crossMatching X active G partner hadj i).verts ↔ i ∈ active u := by
  rw [crossMatching_verts]
  constructor
  · rintro ⟨e, hi, hs | hp⟩
    · have heu : e.1.1 = u := Subtype.ext hs
      have h := e.2
      rwa [hi, heu] at h
    · exact (hout e (hp ▸ u.2)).elim
  · intro hi
    exact ⟨⟨(u, i), hi⟩, rfl, Or.inl rfl⟩

theorem crossMatching_mem_of_not_outlier (G : _root_.SimpleGraph V)
    (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e))
    (i : J) {v : V} (hv : v ∉ X) :
    v ∈ (crossMatching X active G partner hadj i).verts ↔ v ∈ partnerVertices X active partner i := by
  rw [crossMatching_verts]
  constructor
  · rintro ⟨e, hi, hs | hp⟩
    · exact (hv (hs ▸ e.1.1.2)).elim
    · exact ⟨e, hi, hp⟩
  · rintro ⟨e, hi, hp⟩
    exact ⟨e, hi, Or.inr hp⟩

#print axioms crossMatching_isMatching

theorem crossMatching_pairwise_disjoint (G : _root_.SimpleGraph V)
    (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (hout : ∀ e, partner e ∉ X)
    (hproper : ∀ e f, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.2 = f.1.2) → partner e ≠ partner f) :
    Pairwise (fun i j ↦ Disjoint (crossMatching X active G partner hadj i).spanningCoe
      (crossMatching X active G partner hadj j).spanningCoe) := by
  have hne : ∀ e f, requestSource X active e ≠ partner f := by
    intro e f h
    apply hout f
    rw [← h]
    exact e.1.1.2
  have hsame : ∀ e f, requestSource X active e = requestSource X active f →
      partner e = partner f → e = f := by
    intro e f hs hp
    by_contra hef
    exact hproper e f hef (Or.inl (Subtype.ext hs)) hp
  intro i j hij
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hixy hjxy
  obtain ⟨e, he, hexy⟩ := (crossMatching_adj X active G partner hadj i x y).mp hixy
  obtain ⟨f, hf, hfxy⟩ := (crossMatching_adj X active G partner hadj j x y).mp hjxy
  have hcolors (hef : e = f) : False := hij (he.symm.trans ((congrArg (fun e ↦ e.1.2) hef).trans hf))
  rcases hexy with hexy | hexy <;> rcases hfxy with hfxy | hfxy
  · exact hcolors (hsame e f (hexy.1.trans hfxy.1.symm) (hexy.2.trans hfxy.2.symm))
  · exact hne e f (hexy.1.trans hfxy.2.symm)
  · exact hne e f (hexy.1.trans hfxy.2.symm)
  · exact hcolors (hsame e f (hexy.1.trans hfxy.1.symm) (hexy.2.trans hfxy.2.symm))

theorem partnerVertices_subset_compl (partner : ActiveRequest active → V)
    (hout : ∀ e, partner e ∉ X) (i : J) : partnerVertices X active partner i ⊆ Xᶜ := by
  rintro v ⟨e, _, rfl⟩
  exact hout e

theorem partnerVertices_ncard_le [Fintype V] [Fintype J]
    (partner : ActiveRequest active → V) (i : J) :
    (partnerVertices X active partner i).ncard ≤ X.ncard := by
  classical
  let D : Set (ActiveRequest active) := {e | e.1.2 = i}
  let code : D → X := fun e ↦ e.1.1.1
  have hinj : Function.Injective code := by
    intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext h (e.2.trans f.2.symm)
  have hcard : D.ncard ≤ X.ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_injective code hinj
  have himage : partnerVertices X active partner i = partner '' D := by
    ext v
    simp only [partnerVertices, Set.mem_setOf_eq, Set.mem_image, D]
  rw [himage]
  exact (Set.ncard_image_le).trans hcard

theorem partnerVertices_color_count_le [Fintype V] [Fintype J]
    (partner : ActiveRequest active → V) (q : ℕ)
    (hquota : ∀ v, ({e : ActiveRequest active | partner e = v} : Set (ActiveRequest active)).ncard ≤ q)
    (v : V) : (∑ i : J, if v ∈ partnerVertices X active partner i then 1 else 0) ≤ q := by
  classical
  have hcount := ncard_eq_sum_indicator
    ({i : J | v ∈ partnerVertices X active partner i} : Set J)
  simp only [Set.mem_setOf_eq] at hcount
  rw [← hcount]
  have himage : ({i : J | v ∈ partnerVertices X active partner i} : Set J) =
      (fun e : ActiveRequest active ↦ e.1.2) '' {e | partner e = v} := by
    ext i
    simp only [partnerVertices, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨e, he, hp⟩
      exact ⟨e, hp, he⟩
    · rintro ⟨e, hp, he⟩
      exact ⟨e, he, hp⟩
  rw [himage]
  exact (Set.ncard_image_le).trans (hquota v)

theorem crossMatching_avoids (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (C : J → Set V)
    (hactive : ∀ u i, i ∈ active u → u.1 ∉ C i)
    (hpartner : ∀ e, partner e ∉ C e.1.2) (i : J) :
    (crossMatching X active G partner hadj i).verts ⊆ (C i)ᶜ := by
  intro v hv
  obtain ⟨e, he, hs | hp⟩ := (crossMatching_verts X active G partner hadj i v).mp hv
  · have hnot : requestSource X active e ∉ C i := by
      rw [← he]
      exact hactive e.1.1 e.1.2 e.2
    exact hs ▸ hnot
  · have hnot : partner e ∉ C i := by rw [← he]; exact hpartner e
    exact hp ▸ hnot

#print axioms crossMatching_pairwise_disjoint
#print axioms partnerVertices_color_count_le

end Erdos19
