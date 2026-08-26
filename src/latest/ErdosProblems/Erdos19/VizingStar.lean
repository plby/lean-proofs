import ErdosProblems.Erdos19.VizingCore

/-! # Proper recoloring of the spokes of a fan -/

namespace Erdos19.Vizing

open Finset

variable {V K : Type*} [Fintype V]

/-- A change restricted to one star is proper if it is proper at the center,
and each changed color was missing at the other endpoint. -/
theorem proper_of_star_recoloring (G : SimpleGraph V) (C D : PartialColoring V K)
    (hC : IsProper G C) (x : V)
    (houtside : ∀ u v, u ≠ x → v ≠ x → D s(u, v) = C s(u, v))
    (hcenter : ∀ v w a, G.Adj x v → G.Adj x w →
      D s(x, v) = some a → D s(x, w) = some a → v = w)
    (hlocal : ∀ v a, D s(x, v) = some a → C s(x, v) = some a ∨ Missing G C v a) :
    IsProper G D := by
  intro u v w a huv huw hvc hwc
  by_cases hux : u = x
  · subst u
    exact hcenter v w a huv huw hvc hwc
  · by_cases hvx : v = x
    · subst v
      by_cases hwx : w = x
      · exact hwx.symm
      · rw [houtside u w hux hwx] at hwc
        have hxc : D s(x, u) = some a := by simpa only [Sym2.eq_swap] using hvc
        rcases hlocal u a hxc with hold | hmiss
        · apply hC huv huw _ hwc
          simpa only [Sym2.eq_swap] using hold
        · exact (hmiss w huw hwc).elim
    · by_cases hwx : w = x
      · subst w
        rw [houtside u v hux hvx] at hvc
        have hxc : D s(x, u) = some a := by simpa only [Sym2.eq_swap] using hwc
        rcases hlocal u a hxc with hold | hmiss
        · apply hC huv huw hvc
          simpa only [Sym2.eq_swap] using hold
        · exact (hmiss v huv hvc).elim
      · rw [houtside u v hux hvx] at hvc
        rw [houtside u w hux hwx] at hwc
        exact hC huv huw hvc hwc

namespace Fan

variable {G : SimpleGraph V} {C : PartialColoring V K} {x y : V} {n : ℕ}

noncomputable def recolorWith (F : Fan G C x y n) (values : Fin (n + 1) → Option K) :
    PartialColoring V K := Function.extend (fun i ↦ s(x, F.vert i)) values C

theorem recolorWith_spoke (F : Fan G C x y n) (values : Fin (n + 1) → Option K)
    (i : Fin (n + 1)) : F.recolorWith values s(x, F.vert i) = values i :=
  F.edge_injective.extend_apply values C i

theorem recolorWith_outside (F : Fan G C x y n) (values : Fin (n + 1) → Option K)
    (u v : V) (hux : u ≠ x) (hvx : v ≠ x) :
    F.recolorWith values s(u, v) = C s(u, v) := by
  apply Function.extend_apply'
  rintro ⟨i, hi⟩
  rcases Sym2.eq_iff.mp hi with hi | hi
  · exact hux hi.1.symm
  · exact hvx hi.1.symm

theorem recolorWith_nonspoke (F : Fan G C x y n) (values : Fin (n + 1) → Option K)
    (v : V) (hv : v ∉ Set.range F.vert) : F.recolorWith values s(x, v) = C s(x, v) := by
  apply Function.extend_apply'
  rintro ⟨i, hi⟩
  rcases Sym2.eq_iff.mp hi with hi | hi
  · exact hv ⟨i, hi.2⟩
  · exact F.center_ne i hi.2.symm

/-- Three local checks suffice for simultaneously replacing every fan spoke:
distinct new colors at the center, missing colors at the outer endpoints,
and avoidance of the unchanged center edges. -/
theorem recolorWith_proper (F : Fan G C x y n) (values : Fin (n + 1) → Option K)
    (hC : IsProper G C)
    (hinj : ∀ i j a, values i = some a → values j = some a → i = j)
    (hmissing : ∀ i a, values i = some a → Missing G C (F.vert i) a)
    (havoid : ∀ i v a, v ∉ Set.range F.vert → G.Adj x v →
      values i = some a → C s(x, v) ≠ some a) : IsProper G (F.recolorWith values) := by
  classical
  apply proper_of_star_recoloring G C (F.recolorWith values) hC x
  · exact F.recolorWith_outside values
  · intro v w a hxv hxw hvc hwc
    by_cases hv : v ∈ Set.range F.vert
    · obtain ⟨i, rfl⟩ := hv
      rw [F.recolorWith_spoke] at hvc
      by_cases hw : w ∈ Set.range F.vert
      · obtain ⟨j, rfl⟩ := hw
        rw [F.recolorWith_spoke] at hwc
        exact congrArg F.vert (hinj i j a hvc hwc)
      · rw [F.recolorWith_nonspoke values w hw] at hwc
        exact (havoid i w a hw hxw hvc hwc).elim
    · rw [F.recolorWith_nonspoke values v hv] at hvc
      by_cases hw : w ∈ Set.range F.vert
      · obtain ⟨j, rfl⟩ := hw
        rw [F.recolorWith_spoke] at hwc
        exact (havoid j v a hv hxv hwc hvc).elim
      · rw [F.recolorWith_nonspoke values w hw] at hwc
        exact hC hxv hxw hvc hwc
  · intro v a hvc
    by_cases hv : v ∈ Set.range F.vert
    · obtain ⟨i, rfl⟩ := hv
      rw [F.recolorWith_spoke] at hvc
      exact Or.inr (hmissing i a hvc)
    · exact Or.inl ((F.recolorWith_nonspoke values v hv).symm.trans hvc)

end Fan

#print axioms proper_of_star_recoloring
#print axioms Fan.recolorWith_proper

end Erdos19.Vizing
