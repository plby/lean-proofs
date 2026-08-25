import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.ComponentSegmentInOpenBall
import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.PolygonalPathConstant
import Util.IncidenceGeometry.PolygonalPathExtendSegment
import Util.IncidenceGeometry.PolygonalPathSegment
import Util.IncidenceGeometry.PolygonallyPathConnected

lemma OpenConnectedComponentPolygonallyConnected
    (U C : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen U → ComplementComponent Uᶜ C → PolygonallyPathConnected C := by
  intro hU hcomp
  classical
  let Reach :=
    fun a b : EuclideanSpace ℝ (Fin 2) =>
      ∃ γ : PolygonalPath, γ.source = a ∧ γ.target = b ∧ γ.carrier ⊆ C
  have start_reach :
      ∀ ⦃a : EuclideanSpace ℝ (Fin 2)⦄, a ∈ C → Reach a a := by
    intro a ha
    rcases PolygonalPathConstant a with ⟨γ, hsrc, htgt, hcarrier⟩
    refine ⟨γ, hsrc, htgt, ?_⟩
    intro x hx
    rw [hcarrier] at hx
    exact hx ▸ ha
  have extend_reach :
      ∀ ⦃a y z : EuclideanSpace ℝ (Fin 2)⦄,
        Reach a y → segment ℝ y z ⊆ C → Reach a z := by
    intro a y z hreach hseg
    rcases hreach with ⟨γ, hsrc, htgt, hcarrier⟩
    rcases PolygonalPathExtendSegment C γ z hcarrier (by
      intro x hx
      exact hseg (by simpa [htgt] using hx)) with ⟨η, hηsrc, hηtgt, hηcarrier⟩
    exact ⟨η, hsrc ▸ hηsrc, hηtgt, hηcarrier⟩
  have local_extend :
      ∀ ⦃a y : EuclideanSpace ℝ (Fin 2)⦄, y ∈ C → Reach a y →
        ∃ r : ℝ, 0 < r ∧
          ∀ z : EuclideanSpace ℝ (Fin 2), z ∈ Metric.ball y r →
            z ∈ C ∧ Reach a z := by
    intro a y hy hreach
    have hCU : C ⊆ (Uᶜ)ᶜ := hcomp.2.1
    have hyU : y ∈ U := by
      simpa using hCU hy
    rcases Metric.isOpen_iff.mp hU y hyU with ⟨r, hrpos, hball⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have hsegC : segment ℝ y z ⊆ C :=
      ComponentSegmentInOpenBall U C y z r hcomp hy hz hball
    exact ⟨hsegC (right_mem_segment ℝ y z), extend_reach hreach hsegC⟩
  intro p q hp hq
  let Rset : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | y ∈ C ∧ Reach p y}
  let Nset : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | y ∈ C ∧ ¬ Reach p y}
  have hRopen : IsOpen Rset := by
    rw [Metric.isOpen_iff]
    intro y hy
    rcases hy with ⟨hyC, hyReach⟩
    rcases local_extend (a := p) hyC hyReach with ⟨r, hrpos, hball⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    exact hball z hz
  have hNopen : IsOpen Nset := by
    rw [Metric.isOpen_iff]
    intro y hy
    rcases hy with ⟨hyC, hyNotReach⟩
    have hCU : C ⊆ (Uᶜ)ᶜ := hcomp.2.1
    have hyU : y ∈ U := by
      simpa using hCU hyC
    rcases Metric.isOpen_iff.mp hU y hyU with ⟨r, hrpos, hball⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have hsegC : segment ℝ y z ⊆ C :=
      ComponentSegmentInOpenBall U C y z r hcomp hyC hz hball
    have hzC : z ∈ C := hsegC (right_mem_segment ℝ y z)
    have hzNotReach : ¬ Reach p z := by
      intro hzReach
      have hsegSymm : segment ℝ z y ⊆ C := by
        intro x hx
        exact hsegC (by simpa [segment_symm ℝ y z] using hx)
      exact hyNotReach (extend_reach hzReach hsegSymm)
    exact ⟨hzC, hzNotReach⟩
  have hcover : C ⊆ Rset ∪ Nset := by
    intro y hyC
    by_cases hyReach : Reach p y
    · exact Or.inl ⟨hyC, hyReach⟩
    · exact Or.inr ⟨hyC, hyReach⟩
  have hRnonempty : (C ∩ Rset).Nonempty := by
    exact ⟨p, hp, hp, start_reach hp⟩
  have hNempty : ¬ (C ∩ Nset).Nonempty := by
    intro hNnonempty
    have hCconn : IsConnected C := hcomp.2.2.1
    have hinter :
        (C ∩ (Rset ∩ Nset)).Nonempty :=
      hCconn.isPreconnected Rset Nset hRopen hNopen hcover hRnonempty hNnonempty
    rcases hinter with ⟨x, _hxC, hxR, hxN⟩
    exact hxN.2 hxR.2
  have hqReach : Reach p q := by
    by_contra hqNotReach
    exact hNempty ⟨q, hq, hq, hqNotReach⟩
  exact hqReach
