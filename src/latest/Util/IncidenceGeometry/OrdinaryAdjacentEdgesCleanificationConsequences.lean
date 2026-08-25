import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskFamilyExists
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskFillingFamilyExists
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskCleanification

open Classical
noncomputable section


lemma OrdinaryAdjacentEdgesCleanificationConsequences
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ D.crossingSet)
    (hab : alpha ≠ beta)
    (hxAlpha : x ∈ (D.edgeArc alpha).relativeInterior)
    (hxBeta : x ∈ (D.edgeArc beta).relativeInterior) :
    ∃ Dclean : OrdinaryPolygonalDrawing G,
      Dclean.vertexPlacement = D.vertexPlacement ∧
        Dclean.crossingSet.card ≤ D.crossingSet.card ∧
        (∀ (e f : G.edgeFinset) (p : EuclideanSpace ℝ (Fin 2)), e ≠ f →
          p ∈ (Dclean.edgeArc e).relativeInterior →
          p ∈ (Dclean.edgeArc f).relativeInterior →
          ∃ i j : ℕ,
            ∃ (hi : i + 1 < (Dclean.edgeArc e).vertices.length)
              (hj : j + 1 < (Dclean.edgeArc f).vertices.length),
              p ∈ openSegment ℝ (Dclean.edgeArc e).vertices[i]
                  (Dclean.edgeArc e).vertices[i + 1] ∧
              p ∈ openSegment ℝ (Dclean.edgeArc f).vertices[j]
                  (Dclean.edgeArc f).vertices[j + 1] ∧
              ¬ ∃ c : ℝ,
                (Dclean.edgeArc f).vertices[j + 1] -
                    (Dclean.edgeArc f).vertices[j] =
                  c • ((Dclean.edgeArc e).vertices[i + 1] -
                    (Dclean.edgeArc e).vertices[i])) ∧
        (Dclean.crossingSet.card = D.crossingSet.card →
          ∃ p : EuclideanSpace ℝ (Fin 2),
            p ∈ Dclean.crossingSet ∧
              p ∈ (Dclean.edgeArc alpha).relativeInterior ∧
              p ∈ (Dclean.edgeArc beta).relativeInterior) := by
  rcases OrdinaryLabeledCrossingDiskFamilyExists G D with ⟨F⟩
  rcases OrdinaryLabeledCrossingDiskFillingFamilyExists G D F with ⟨L⟩
  rcases OrdinaryLabeledCrossingDiskCleanification G D F L with
    ⟨Dclean, hvertex, hcard, provenance, _hinj, hlocal, hsurvive⟩
  refine ⟨Dclean, hvertex, hcard, ?_, ?_⟩
  · have crossing_owner_pair :
        ∀ (e f a b : G.edgeFinset) (p : EuclideanSpace ℝ (Fin 2)),
          e ≠ f → a ≠ b →
          p ∈ (Dclean.edgeArc e).relativeInterior →
          p ∈ (Dclean.edgeArc f).relativeInterior →
          p ∈ (Dclean.edgeArc a).relativeInterior →
          p ∈ (Dclean.edgeArc b).relativeInterior →
          (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
      intro e f a b p hef hab' he hf ha hb
      have hea : e = a ∨ e = b := by
        by_contra h
        push Not at h
        exact Dclean.no_three_edge_interiors_meet h.1 h.2 hab' he ha hb
      have hfa : f = a ∨ f = b := by
        by_contra h
        push Not at h
        exact Dclean.no_three_edge_interiors_meet h.1 h.2 hab' hf ha hb
      rcases hea with rfl | rfl <;> rcases hfa with rfl | rfl
      · exact (hef rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hef rfl).elim
    have nonparallel_symm :
        ∀ {v w : EuclideanSpace ℝ (Fin 2)}, v ≠ 0 →
          (¬ ∃ c : ℝ, w = c • v) → ¬ ∃ c : ℝ, v = c • w := by
      intro v w hv h
      rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        intro hc0
        subst c
        simp at hc
        exact hv hc
      apply h
      refine ⟨c⁻¹, ?_⟩
      rw [hc, smul_smul]
      simp [hc0]
    intro e f p hef hpe hpf
    have hpCross : p ∈ Dclean.crossingSet :=
      (Dclean.crossingSet_spec p).2 ⟨e, f, hef, hpe, hpf⟩
    let pp : {q // q ∈ Dclean.crossingSet} := ⟨p, hpCross⟩
    have hloc := (hlocal pp).1
    rcases hloc with
      ⟨_hpBall, _hpFill0, _hpFill1, hpFirst, hpSecond,
        i, j, hi, hj, hpOpenFirst, hpOpenSecond, hnp⟩
    let oldx := provenance pp
    let first := (F.disk oldx).firstEdge
    let second := (F.disk oldx).secondEdge
    have howners := crossing_owner_pair e f first second p hef
      (F.disk oldx).edges_ne hpe hpf hpFirst hpSecond
    rcases howners with howners | howners
    · rcases howners with ⟨rfl, rfl⟩
      exact ⟨i, j, hi, hj, hpOpenFirst, hpOpenSecond, hnp⟩
    · rcases howners with ⟨rfl, rfl⟩
      refine ⟨j, i, hj, hi, hpOpenSecond, hpOpenFirst, ?_⟩
      change i + 1 < (Dclean.edgeArc first).vertices.length at hi
      change p ∈ openSegment ℝ (Dclean.edgeArc first).vertices[i]
        (Dclean.edgeArc first).vertices[i + 1] at hpOpenFirst
      change j + 1 < (Dclean.edgeArc second).vertices.length at hj
      change p ∈ openSegment ℝ (Dclean.edgeArc second).vertices[j]
        (Dclean.edgeArc second).vertices[j + 1] at hpOpenSecond
      change ¬ ∃ c : ℝ,
        (Dclean.edgeArc second).vertices[j + 1] -
            (Dclean.edgeArc second).vertices[j] =
          c • ((Dclean.edgeArc first).vertices[i + 1] -
            (Dclean.edgeArc first).vertices[i]) at hnp
      have hdir :
          (Dclean.edgeArc first).vertices[i + 1] -
              (Dclean.edgeArc first).vertices[i] ≠ 0 := by
        intro hzero
        have hii : i < (Dclean.edgeArc first).vertices.length := by omega
        have heq : (Dclean.edgeArc first).vertices[i]'hii =
            (Dclean.edgeArc first).vertices[i + 1]'hi := by
          simpa using (sub_eq_zero.mp hzero).symm
        have hidx := ((Dclean.edgeArc first).simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := hii) (hj := hi)).1 heq
        omega
      exact nonparallel_symm hdir hnp
  · intro hcardEq
    let oldx : {q // q ∈ D.crossingSet} := ⟨x, hx⟩
    rcases hsurvive hcardEq oldx with ⟨p, _hprov, hloc⟩
    have hAlphaOwner := (F.disk oldx).owner_labels alpha hxAlpha
    have hBetaOwner := (F.disk oldx).owner_labels beta hxBeta
    rcases hloc with
      ⟨_hpBall, _hpFill0, _hpFill1, hpFirst, hpSecond, _hpOpen⟩
    refine ⟨p.1, p.2, ?_⟩
    rcases hAlphaOwner with ha | ha <;> rcases hBetaOwner with hb | hb
    · exact (hab (ha.trans hb.symm)).elim
    · exact ⟨ha ▸ hpFirst, hb ▸ hpSecond⟩
    · exact ⟨ha ▸ hpSecond, hb ▸ hpFirst⟩
    · exact (hab (ha.trans hb.symm)).elim
