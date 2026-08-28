import Wikipedia.HopfProblem.DegreeCollapseCylinderBall

/-!
# Compatible bottom, top and side data on the entire cylinder boundary

The full prescribed boundary is glued by a compact quotient. Every boundary
value is retained exactly, so filling the resulting sphere is a homotopy
with the original endpoints and side family.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.CylinderBoundary

open DiskCylinder CylinderBall

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def lower : C(bottomOrSide (E := V), boundary (V := V)) :=
  ⟨fun p => ⟨p.val, p.property.elim Or.inl (fun h => Or.inr (Or.inr h))⟩,
    continuous_subtype_val.subtype_mk _⟩

def top : C(Disk (E := V), boundary (V := V)) :=
  ⟨fun z => ⟨(1, z), Or.inr (Or.inl rfl)⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

def quotient : C(bottomOrSide (E := V) ⊕ Disk (E := V), boundary (V := V)) :=
  ⟨Sum.elim lower top, lower.continuous.sumElim top.continuous⟩

omit [NormedSpace ℝ V] in
theorem quotient_surjective : Function.Surjective (quotient (V := V)) := by
  rintro ⟨⟨t, z⟩, ht | ht | hz⟩
  · exact ⟨.inl ⟨(t, z), Or.inl ht⟩, rfl⟩
  · change t = 1 at ht
    subst t
    exact ⟨.inr z, rfl⟩
  · exact ⟨.inl ⟨(t, z), Or.inr hz⟩, rfl⟩

variable [FiniteDimensional ℝ V]

theorem quotient_isQuotientMap : IsQuotientMap (quotient (V := V)) := by
  have hclosed : IsClosed (bottomOrSide (E := V)) :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq (continuous_subtype_val.comp continuous_snd).norm continuous_const)
  let : CompactSpace (bottomOrSide (E := V)) := isCompact_iff_compactSpace.mp hclosed.isCompact
  exact .of_surjective_continuous quotient_surjective quotient.continuous

variable {X : Type*} [TopologicalSpace X]
  (f g : C(Disk (E := V), X)) (H : C(I × Sphere (E := V), X))
  (h0 : ∀ s, H (0, s) = f (boundaryToDisk s))
  (h1 : ∀ s, H (1, s) = g (boundaryToDisk s))

include h1 in
theorem lower_top_compat (a : bottomOrSide (E := V)) (b : Disk (E := V))
    (he : lower a = top b) : gluedBottomSide f H h0 a = g b := by
  have ht : a.val.1 = (1 : I) := congrArg (fun p : boundary (V := V) => p.val.1) he
  have hz : a.val.2 = b := congrArg (fun p : boundary (V := V) => p.val.2) he
  have hs : ‖(a.val.2 : V)‖ = 1 := by
    rcases a.property with h | h
    · exact False.elim (zero_ne_one (h.symm.trans ht))
    · exact h
  let s : Sphere (E := V) := ⟨a.val.2.val, mem_sphere_zero_iff_norm.mpr hs⟩
  have ha : a = sideMap (1, s) := Subtype.ext (Prod.ext ht rfl)
  rw [ha, gluedBottomSide_side]
  exact (h1 s).trans (congrArg g hz)

def data : C(bottomOrSide (E := V) ⊕ Disk (E := V), X) :=
  ⟨Sum.elim (gluedBottomSide f H h0) g, (gluedBottomSide f H h0).continuous.sumElim g.continuous⟩

include h1 in
theorem data_constant_on_fibres (a b : bottomOrSide (E := V) ⊕ Disk (E := V))
    (he : quotient a = quotient b) : data f g H h0 a = data f g H h0 b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hv : a.val = b.val := congrArg (fun p : boundary (V := V) => p.val) he
      exact congrArg (gluedBottomSide f H h0) (Subtype.ext hv)
    | inr b => exact lower_top_compat f g H h0 h1 a b he
  | inr a =>
    cases b with
    | inl b => exact (lower_top_compat f g H h0 h1 b a he.symm).symm
    | inr b => exact congrArg g (congrArg (fun p : boundary (V := V) => p.val.2) he)

/-- The original three compatible pieces form a continuous map on the full boundary. -/
def glued : C(boundary (V := V), X) :=
  quotient_isQuotientMap.lift (data f g H h0) (data_constant_on_fibres f g H h0 h1)

theorem glued_lower (a : bottomOrSide (E := V)) :
    glued f g H h0 h1 (lower a) = gluedBottomSide f H h0 a :=
  ContinuousMap.congr_fun (quotient_isQuotientMap.lift_comp (data f g H h0)
    (data_constant_on_fibres f g H h0 h1)) (.inl a)

theorem glued_top (z : Disk (E := V)) : glued f g H h0 h1 (top z) = g z :=
  ContinuousMap.congr_fun (quotient_isQuotientMap.lift_comp (data f g H h0)
    (data_constant_on_fibres f g H h0 h1)) (.inr z)

theorem glued_bottom (z : Disk (E := V)) :
    glued f g H h0 h1 (lower (bottomMap z)) = f z := by
  rw [glued_lower, gluedBottomSide_bottom]

theorem glued_side (t : I) (s : Sphere (E := V)) :
    glued f g H h0 h1 (lower (sideMap (t, s))) = H (t, s) := by
  rw [glued_lower, gluedBottomSide_side]

end Wikipedia.HopfProblem.DegreeCollapse.CylinderBoundary
