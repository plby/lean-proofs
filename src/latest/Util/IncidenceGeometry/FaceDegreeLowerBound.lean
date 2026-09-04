import Util.IncidenceGeometry.DartSuccessorPreservesFace
import Util.IncidenceGeometry.EveryFaceIncidentDart
import Util.IncidenceGeometry.PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma FaceDegreeLowerBound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, 3 ≤ A.faceDegree F := by
  classical
  intro hconn hn hedge F
  rcases EveryFaceIncidentDart G D hD A hconn hn hedge F with ⟨d0, hd0F⟩
  have hsuccFace := (DartSuccessorPreservesFace G D hD A).1
  have no_fixed : ∀ d : G.Dart, A.successor d ≠ d := by
    intro d hfix
    have htail : d.toProd.1 = d.toProd.2 := by
      simpa [hfix] using A.successor_tail d
    exact d.fst_ne_snd htail
  have no_two_cycle : ∀ d : G.Dart, A.successor (A.successor d) ≠ d := by
    intro d hcycle
    let d' : G.Dart := A.successor d
    have htail1 : d'.toProd.1 = d.toProd.2 := by
      simpa [d'] using A.successor_tail d
    have htail2 : d'.toProd.2 = d.toProd.1 := by
      have h := A.successor_tail d'
      simpa [d', hcycle] using h.symm
    have hsucc_symm : A.successor d = d.symm := by
      apply SimpleGraph.Dart.ext
      ext <;> simp [d', htail1, htail2, SimpleGraph.Dart.symm]
    have hsucc_symm' : A.successor d.symm = d := by
      simpa [hsucc_symm] using hcycle
    let incomingAtHead : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hcw_head : A.clockwiseNext d.toProd.2 incomingAtHead = incomingAtHead := by
      apply Subtype.ext
      have h := A.successor_eq_clockwiseNext d
      change (A.clockwiseNext d.toProd.2 incomingAtHead).1 = d.symm
      simpa [incomingAtHead, hsucc_symm] using h.symm
    have hunique_head :
        ∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e = incomingAtHead :=
      (A.clockwiseNext_eq_self_iff_isolated d.toProd.2 incomingAtHead).mp hcw_head
    let incomingAtTail : {e : G.Dart // e.toProd.1 = d.symm.toProd.2} :=
      ⟨d.symm.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hcw_tail :
        A.clockwiseNext d.symm.toProd.2 incomingAtTail = incomingAtTail := by
      apply Subtype.ext
      have h := A.successor_eq_clockwiseNext d.symm
      change (A.clockwiseNext d.symm.toProd.2 incomingAtTail).1 = incomingAtTail.1
      simpa [incomingAtTail, hsucc_symm'] using h.symm
    have hunique_tail :
        ∀ e : {e : G.Dart // e.toProd.1 = d.symm.toProd.2}, e = incomingAtTail :=
      (A.clockwiseNext_eq_self_iff_isolated d.symm.toProd.2 incomingAtTail).mp hcw_tail
    have neigh_tail :
        ∀ {w : V}, G.Adj d.toProd.1 w → w = d.toProd.2 := by
      intro w hadj
      let e : {e : G.Dart // e.toProd.1 = d.symm.toProd.2} :=
        ⟨⟨(d.toProd.1, w), hadj⟩, by simp [SimpleGraph.Dart.symm]⟩
      have heq := hunique_tail e
      have hprod : e.1.toProd = incomingAtTail.1.toProd :=
        congrArg SimpleGraph.Dart.toProd (congrArg Subtype.val heq)
      simpa [e, incomingAtTail] using congrArg Prod.snd hprod
    have neigh_head :
        ∀ {w : V}, G.Adj d.toProd.2 w → w = d.toProd.1 := by
      intro w hadj
      let e : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
        ⟨⟨(d.toProd.2, w), hadj⟩, rfl⟩
      have heq := hunique_head e
      have hprod : e.1.toProd = incomingAtHead.1.toProd :=
        congrArg SimpleGraph.Dart.toProd (congrArg Subtype.val heq)
      simpa [e, incomingAtHead, SimpleGraph.Dart.symm] using congrArg Prod.snd hprod
    have walk_stays :
        ∀ {a b : V}, (a = d.toProd.1 ∨ a = d.toProd.2) →
          G.Walk a b → b = d.toProd.1 ∨ b = d.toProd.2 := by
      intro a b ha p
      induction p with
      | nil =>
          exact ha
      | @cons a c b hadj q ih =>
          have hc : c = d.toProd.1 ∨ c = d.toProd.2 := by
            cases ha with
            | inl ha_tail =>
                right
                exact neigh_tail (ha_tail ▸ hadj)
            | inr ha_head =>
                left
                exact neigh_head (ha_head ▸ hadj)
          exact ih hc
    have all_vertices :
        ∀ w : V, w = d.toProd.1 ∨ w = d.toProd.2 := by
      intro w
      exact (hconn d.toProd.1 w).elim fun p => walk_stays (Or.inl rfl) p
    have hcard_le_two : Fintype.card V ≤ 2 := by
      have hsubset :
          (Finset.univ : Finset V) ⊆ ({d.toProd.1, d.toProd.2} : Finset V) := by
        intro w _hw
        simpa using all_vertices w
      calc
        Fintype.card V = (Finset.univ : Finset V).card := by simp
        _ ≤ ({d.toProd.1, d.toProd.2} : Finset V).card := Finset.card_le_card hsubset
        _ ≤ 2 := Finset.card_le_two
    omega
  let d1 : G.Dart := A.successor d0
  let d2 : G.Dart := A.successor d1
  have hd1F : A.leftFace d1 = F := by
    simpa [d1, hd0F] using hsuccFace d0
  have hd2F : A.leftFace d2 = F := by
    simpa [d2, hd1F] using hsuccFace d1
  let f : Fin 3 → {d : G.Dart // A.leftFace d = F} := fun i =>
    match i with
    | ⟨0, _⟩ => ⟨d0, hd0F⟩
    | ⟨1, _⟩ => ⟨d1, hd1F⟩
    | ⟨2, _⟩ => ⟨d2, hd2F⟩
    | ⟨n + 3, h⟩ => False.elim (by omega)
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.mk_one, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, Fin.zero_eta, one_ne_zero, zero_ne_one] at hij ⊢
    · exact False.elim (no_fixed d0 (by
        have := congrArg Subtype.val hij.symm
        simpa [f, d1] using this))
    · exact False.elim (no_two_cycle d0 (by
        have := congrArg Subtype.val hij.symm
        simpa [f, d1, d2] using this))
    · exact False.elim (no_fixed d0 (by
        have := congrArg Subtype.val hij
        simpa [f, d1] using this))
    · exact False.elim (no_fixed d1 (by
        have := congrArg Subtype.val hij.symm
        simpa [f, d2] using this))
    · exact False.elim (no_two_cycle d0 (by
        have := congrArg Subtype.val hij
        simpa [f, d1, d2] using this))
    · exact False.elim (no_fixed d1 (by
        have := congrArg Subtype.val hij
        simpa [f, d2] using this))
  have hcard :
      3 ≤ Fintype.card {d : G.Dart // A.leftFace d = F} := by
    simpa using (Fintype.card_le_of_injective f hf_inj)
  simpa [A.faceDegree_eq F] using hcard
