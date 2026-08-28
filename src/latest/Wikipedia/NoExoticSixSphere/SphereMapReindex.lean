import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!
# Dimension equalities for the actual sphere suspension maps

Only equality of the natural-number dimensions is transported here. The maps
and their homotopies are not replaced by arbitrary sphere identifications.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

variable {m n m' n' : ℕ}

def reindex (hm : m = m') (hn : n = n') (f : C(Sphere m, Sphere n)) :
    C(Sphere m', Sphere n') := hm ▸ hn ▸ f

theorem reindex_heq (hm : m = m') (hn : n = n') (f : C(Sphere m, Sphere n)) :
    HEq (reindex hm hn f) f := by
  subst m'
  subst n'
  rfl

theorem map_heq (hm : m = m') (hn : n = n')
    {f : C(Sphere m, Sphere n)} {g : C(Sphere m', Sphere n')} (h : HEq f g) :
    HEq (map f) (map g) := by
  subst m'
  subst n'
  cases eq_of_heq h
  rfl

theorem iterate_heq (hm : m = m') (hn : n = n')
    {f : C(Sphere m, Sphere n)} {g : C(Sphere m', Sphere n')} (h : HEq f g) (r : ℕ) :
    HEq (iterate f r) (iterate g r) := by
  subst m'
  subst n'
  cases eq_of_heq h
  rfl

theorem nullhomotopic_iff_of_heq (hm : m = m') (hn : n = n')
    {f : C(Sphere m, Sphere n)} {g : C(Sphere m', Sphere n')} (h : HEq f g) :
    f.Nullhomotopic ↔ g.Nullhomotopic := by
  subst m'
  subst n'
  cases eq_of_heq h
  rfl

theorem iterate_reindex_nullhomotopic_iff (hm : m = m') (hn : n = n')
    (f : C(Sphere m, Sphere n)) (r : ℕ) :
    (iterate (reindex hm hn f) r).Nullhomotopic ↔ (iterate f r).Nullhomotopic :=
  nullhomotopic_iff_of_heq (congrArg (· + r) hm.symm) (congrArg (· + r) hn.symm)
    (iterate_heq hm.symm hn.symm (reindex_heq hm hn f) r)

end NoExoticSixSphere.SphereMapSuspension
