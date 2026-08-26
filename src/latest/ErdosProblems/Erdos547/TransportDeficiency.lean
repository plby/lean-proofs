import ErdosProblems.Erdos547.TransportRedistribution

/-!
# A maximum transport with as many deficient rows as possible
-/

noncomputable section

namespace Erdos547.DPRS.Transport

open Finset

variable {V : Type*} [Fintype V] {P : V → V → Prop} {a b : V → ℝ}

def deficientRows (f : Transport P a b) : Finset V :=
  Finset.univ.filter (fun u ↦ f.row u < a u)

theorem exists_maximum_with_deficiency (P : V → V → Prop) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) :
    ∃ f : Transport P a b, (∀ g : Transport P a b, g.total ≤ f.total) ∧
      ∀ g : Transport P a b, (∀ h : Transport P a b, h.total ≤ g.total) →
        g.deficientRows.card ≤ f.deficientRows.card := by
  classical
  obtain ⟨f₀, h₀⟩ := exists_maximum P a b ha hb
  let candidates := (Finset.univ : Finset V).powerset.filter fun S ↦
    ∃ f : Transport P a b, (∀ g : Transport P a b, g.total ≤ f.total) ∧ f.deficientRows = S
  have hn : candidates.Nonempty := ⟨f₀.deficientRows, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), f₀, h₀, rfl⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hn
  obtain ⟨f, hf, hdef⟩ := (Finset.mem_filter.mp hS).2
  refine ⟨f, hf, ?_⟩
  intro g hg
  rw [hdef]
  exact hmax g.deficientRows (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), g, hg, rfl⟩)

theorem maximum_deficiency_closed {f : Transport P a b}
    (hmax : ∀ g : Transport P a b, g.total ≤ f.total)
    (hdef : ∀ g : Transport P a b, (∀ h : Transport P a b, h.total ≤ g.total) →
      g.deficientRows.card ≤ f.deficientRows.card)
    {x y z : V} (hx : x ∈ f.deficientRows) (hxy : P x y) (hp : 0 < f.weight z y) :
    z ∈ f.deficientRows := by
  classical
  by_contra hz
  have hxrow := (Finset.mem_filter.mp hx).2
  have hxz : x ≠ z := fun he ↦ hz (he ▸ hx)
  let t := min ((a x - f.row x) / 2) (f.weight z y / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htx : t ≤ (a x - f.row x) / 2 := min_le_left _ _
  have htz : t ≤ f.weight z y / 2 := min_le_right _ _
  have hr : f.row x + t < a x := by linarith
  have hw : t ≤ f.weight z y := by linarith
  let g := f.redistribute hxz hxy t ht.le hr.le hw
  have hgt : g.total = f.total := f.redistribute_total hxz hxy t ht.le hr.le hw
  have hgmax : ∀ h : Transport P a b, h.total ≤ g.total := fun h ↦ hgt.symm ▸ hmax h
  have hrow (u : V) : g.row u =
      f.row u + (if u = x then t else 0) - (if u = z then t else 0) :=
    f.redistributeWeight_row x z y t u
  have hsub : f.deficientRows ⊆ g.deficientRows := by
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hurow := (Finset.mem_filter.mp hu).2
    rw [hrow]
    by_cases hux : u = x
    · subst u
      simpa only [if_pos rfl, if_neg hxz, if_true, sub_zero] using hr
    · rw [if_neg hux, add_zero]
      split_ifs <;> linarith
  have hzg : z ∈ g.deficientRows := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hrow, if_neg (Ne.symm hxz), if_pos rfl, add_zero]
    have hzrow : f.row z ≤ a z := f.row_bound z
    linarith
  have hcard := Finset.card_le_card (Finset.insert_subset hzg hsub)
  rw [Finset.card_insert_of_notMem hz] at hcard
  have hh := hdef g hgmax
  omega

end Erdos547.DPRS.Transport

#print axioms Erdos547.DPRS.Transport.maximum_deficiency_closed
