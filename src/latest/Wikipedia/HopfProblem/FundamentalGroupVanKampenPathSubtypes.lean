import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# Paths and homotopies in a subspace

A path or endpoint-preserving homotopy whose image lies in a set determines
the corresponding object in the subspace topology.  The actual subpath
concatenation homotopy stays in the image of the ordered outer interval.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {S : Set X}
variable {x y z : X}

/-- Regard a path lying in a set as a path in that subspace. -/
def pathIn (p : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem pathIn_apply (p : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) (t : I) : (pathIn p hx hy hp t : X) = p t := rfl

@[simp] theorem pathIn_map (p : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

@[simp] theorem pathIn_map_subtype_val {a b : S} (p : Path a b) :
    pathIn (p.map continuous_subtype_val) a.property b.property
      (fun t => (p t).property) = p := by
  ext t
  rfl

@[simp] theorem pathIn_refl (hx : x ∈ S) (hp : ∀ t, Path.refl x t ∈ S) :
    pathIn (Path.refl x) hx hx hp = Path.refl (⟨x, hx⟩ : S) := by
  ext t
  rfl

@[simp] theorem pathIn_trans (p : Path x y) (q : Path y z)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (hpq : ∀ t, p.trans q t ∈ S) :
    pathIn (p.trans q) hx hz hpq = (pathIn p hx hy hp).trans (pathIn q hy hz hq) := by
  ext t
  simp only [pathIn_apply, Path.trans_apply]
  split_ifs <;> rfl

@[simp] theorem pathIn_symm (p : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) (hps : ∀ t, p.symm t ∈ S) :
    pathIn p.symm hy hx hps = (pathIn p hx hy hp).symm := by
  ext t
  rfl

/-- Restrict an actual endpoint-preserving homotopy to a subspace. -/
def homotopyIn (p q : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ S) :
    Path.Homotopy (pathIn p hx hy hp) (pathIn q hx hy hq) where
  toFun s := ⟨H s, hH s⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' s _t ht := Subtype.ext (H.eq_fst s ht)

@[simp] theorem homotopyIn_apply (p q : Path x y) (hx : x ∈ S) (hy : y ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ S) (s : I × I) :
    (homotopyIn p q hx hy hp hq H hH s : X) = H s := rfl

/-- Vertical composition preserves containment of homotopy squares. -/
theorem homotopy_trans_mem {p q r : Path x y}
    (H : Path.Homotopy p q) (K : Path.Homotopy q r)
    (hH : ∀ s, H s ∈ S) (hK : ∀ s, K s ∈ S) :
    ∀ s, H.trans K s ∈ S := by
  intro s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

/-- Removing a terminal constant path does not leave the original path image. -/
theorem homotopy_transRefl_mem (p : Path x y) (hp : ∀ t, p t ∈ S) :
    ∀ s, Path.Homotopy.transRefl p s ∈ S := by
  intro s
  exact hp _

/-- The moving split point in the subpath homotopy stays in the outer interval. -/
theorem homotopy_subpathTransSubpathRefl_mem (p : Path x y) (a b c : I)
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpathRefl p a b c s ∈ S := by
  intro s
  let m := Icc.convexComb b c s.1
  have ham : a ≤ m := hab.trans (Icc.le_convexComb hbc s.1)
  have hmc : m ≤ c := Icc.convexComb_le hbc s.1
  change ((p.subpath a m).trans (p.subpath m c)) s.2 ∈ S
  apply SimplyConnectedCover.trans_mem
  · exact subpath_mem_of_mem_Icc p ham (fun t ht => hp t ⟨ht.1, ht.2.trans hmc⟩)
  · exact subpath_mem_of_mem_Icc p hmc (fun t ht => hp t ⟨ham.trans ht.1, ht.2⟩)

/-- The standard subpath-concatenation homotopy lies in the ordered outer interval. -/
theorem homotopy_subpathTransSubpath_mem (p : Path x y) (a b c : I)
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpath p a b c s ∈ S :=
  homotopy_trans_mem _ _ (homotopy_subpathTransSubpathRefl_mem p a b c hab hbc hp)
    (homotopy_transRefl_mem _ (subpath_mem_of_mem_Icc p (hab.trans hbc) hp))

/-- Containment of an ordered subpath implies containment of the original
path on the corresponding closed interval. -/
theorem mem_Icc_of_subpath_mem (p : Path x y) {a b : I} (hab : a ≤ b)
    (hp : ∀ t, p.subpath a b t ∈ S) : ∀ t ∈ Icc a b, p t ∈ S := by
  have hr := range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hr
  intro t ht
  exact hr ⟨t, ht, rfl⟩

/-- Concatenation of adjacent ordered subpaths is homotopic to the outer
subpath in the subspace itself, with no ambient homotopy assumption. -/
def subpathTransSubpathIn (p : Path x y) (a b c : I) (hab : a ≤ b) (hbc : b ≤ c)
    (ha : p a ∈ S) (hb : p b ∈ S) (hc : p c ∈ S)
    (hpab : ∀ t, p.subpath a b t ∈ S)
    (hpbc : ∀ t, p.subpath b c t ∈ S)
    (hpac : ∀ t, p.subpath a c t ∈ S) :
    Path.Homotopy
      ((pathIn (p.subpath a b) ha hb hpab).trans (pathIn (p.subpath b c) hb hc hpbc))
      (pathIn (p.subpath a c) ha hc hpac) :=
  (homotopyIn _ _ ha hc
    (SimplyConnectedCover.trans_mem _ _ hpab hpbc) hpac
    (Path.Homotopy.subpathTransSubpath p a b c)
    (homotopy_subpathTransSubpath_mem p a b c hab hbc
      (mem_Icc_of_subpath_mem p (hab.trans hbc) hpac))).cast
        (pathIn_trans _ _ ha hb hc hpab hpbc _) rfl

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
