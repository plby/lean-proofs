import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps
import Mathlib.Topology.Homotopy.Basic

/-! # Gluing actual homotopies across two closed embedded pieces -/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.ClosedPieceHomotopy

open Wikipedia.SmoothSixDPoincare

variable {R P X Y : Type*} [TopologicalSpace R] [TopologicalSpace P]
  [TopologicalSpace X] [TopologicalSpace Y]
  (r : R → X) (p : P → X) (hr : IsClosedEmbedding r) (hp : IsClosedEmbedding p)
  (hcover : range r ∪ range p = univ)

include hcover in
theorem product_cover :
    range (Prod.map (id : unitInterval → unitInterval) r) ∪
      range (Prod.map (id : unitInterval → unitInterval) p) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  rintro ⟨t, x⟩
  have hx : x ∈ range r ∪ range p := by rw [hcover]; trivial
  rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, b), rfl⟩

variable (F : C(unitInterval × R, Y)) (G : C(unitInterval × P, Y))
  (hagree : ∀ t a b, r a = p b → F (t, a) = G (t, b))

include hagree in
theorem product_agreement (a : unitInterval × R) (b : unitInterval × P)
    (h : Prod.map id r a = Prod.map id p b) : F a = G b := by
  have ht : a.1 = b.1 := congrArg Prod.fst h
  have hx : r a.2 = p b.2 := congrArg Prod.snd h
  change F (a.1, a.2) = G (b.1, b.2)
  rw [ht]
  exact hagree b.1 a.2 b.2 hx

def glueMap : C(unitInterval × X, Y) :=
  ClosedCover.mapOfClosedPieces (Prod.map id r) (Prod.map id p)
    (IsClosedEmbedding.id.prodMap hr) (IsClosedEmbedding.id.prodMap hp)
    (product_cover r p hcover) F G (product_agreement r p F G hagree)

theorem glueMap_left (t : unitInterval) (a : R) :
    glueMap r p hr hp hcover F G hagree (t, r a) = F (t, a) :=
  ClosedCover.mapOfClosedPieces_left _ _ _ _ _ _ _ _ (t, a)

theorem glueMap_right (t : unitInterval) (b : P) :
    glueMap r p hr hp hcover F G hagree (t, p b) = G (t, b) :=
  ClosedCover.mapOfClosedPieces_right _ _ _ _ _ _ _ _ (t, b)

variable (f₀ f₁ : C(X, Y))
  (H : (f₀.comp ⟨r, hr.continuous⟩).Homotopy (f₁.comp ⟨r, hr.continuous⟩))
  (K : (f₀.comp ⟨p, hp.continuous⟩).Homotopy (f₁.comp ⟨p, hp.continuous⟩))
  (hHK : ∀ t a b, r a = p b → H (t, a) = K (t, b))

def glue : f₀.Homotopy f₁ where
  toContinuousMap := glueMap r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK
  map_zero_left x := by
    have hx : x ∈ range r ∪ range p := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (glueMap_left r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK 0 a).trans
        (H.apply_zero a)
    · exact (glueMap_right r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK 0 b).trans
        (K.apply_zero b)
  map_one_left x := by
    have hx : x ∈ range r ∪ range p := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (glueMap_left r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK 1 a).trans
        (H.apply_one a)
    · exact (glueMap_right r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK 1 b).trans
        (K.apply_one b)

theorem glue_left (t : unitInterval) (a : R) :
    glue r p hr hp hcover f₀ f₁ H K hHK (t, r a) = H (t, a) :=
  glueMap_left r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK t a

theorem glue_right (t : unitInterval) (b : P) :
    glue r p hr hp hcover f₀ f₁ H K hHK (t, p b) = K (t, b) :=
  glueMap_right r p hr hp hcover H.toContinuousMap K.toContinuousMap hHK t b

end Wikipedia.HopfProblem.DegreeCollapse.ClosedPieceHomotopy
