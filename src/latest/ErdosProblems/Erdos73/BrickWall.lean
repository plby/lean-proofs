/- The elementary brick wall, before and after removal of degree-one corners. -/
import ErdosProblems.Erdos73.GridSeparation

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph SimpleGraph

def rawBrickWall (c r : ℕ) : SimpleGraph (Fin r × Fin (2 * c)) where
  Adj x y :=
    (x.1 = y.1 ∧ (pathGraph (2 * c)).Adj x.2 y.2) ∨
    (x.2 = y.2 ∧ ((x.1.val + 1 = y.1.val ∧ (x.2.val + x.1.val) % 2 = 1) ∨
      (y.1.val + 1 = x.1.val ∧ (y.2.val + y.1.val) % 2 = 1)))
  symm := ⟨by
    rintro x y (⟨hr, hi⟩ | ⟨hi, hv⟩)
    · exact Or.inl ⟨hr.symm, hi.symm⟩
    · exact Or.inr ⟨hi.symm, hv.symm⟩⟩
  loopless := ⟨by
    rintro x (⟨_, hx⟩ | ⟨_, hx⟩)
    · exact (pathGraph (2 * c)).irrefl hx
    · omega⟩

theorem rawBrickWall_le_grid (c r : ℕ) : rawBrickWall c r ≤ pathGraph r □ pathGraph (2 * c) := by
  intro x y hxy
  rcases hxy with ⟨hr, hi⟩ | ⟨hi, hv⟩
  · exact Or.inr ⟨hi, hr⟩
  · exact Or.inl ⟨pathGraph_adj.mpr (hv.imp And.left And.left), hi⟩

def brickWallPort {c r : ℕ} (x y : Fin r × Fin (2 * c)) : Fin 3 :=
  if x.1 = y.1 then (if y.2.val < x.2.val then 0 else 1) else 2

theorem brickWallPort_injective_on_neighbors {c r : ℕ} (x : Fin r × Fin (2 * c))
    {y z : Fin r × Fin (2 * c)} (hxy : (rawBrickWall c r).Adj x y)
    (hxz : (rawBrickWall c r).Adj x z) (hport : brickWallPort x y = brickWallPort x z) : y = z := by
  have hxys : (x.1.val = y.1.val ∧
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.2.val = y.2.val ∧ ((x.1.val + 1 = y.1.val ∧ (x.2.val + x.1.val) % 2 = 1) ∨
        (y.1.val + 1 = x.1.val ∧ (y.2.val + y.1.val) % 2 = 1))) := by
    rcases hxy with ⟨hr, hi⟩ | ⟨hi, hv⟩
    · exact Or.inl ⟨congrArg Fin.val hr, pathGraph_adj.mp hi⟩
    · exact Or.inr ⟨congrArg Fin.val hi, hv⟩
  have hxzs : (x.1.val = z.1.val ∧
      (x.2.val + 1 = z.2.val ∨ z.2.val + 1 = x.2.val)) ∨
      (x.2.val = z.2.val ∧ ((x.1.val + 1 = z.1.val ∧ (x.2.val + x.1.val) % 2 = 1) ∨
        (z.1.val + 1 = x.1.val ∧ (z.2.val + z.1.val) % 2 = 1))) := by
    rcases hxz with ⟨hr, hi⟩ | ⟨hi, hv⟩
    · exact Or.inl ⟨congrArg Fin.val hr, pathGraph_adj.mp hi⟩
    · exact Or.inr ⟨congrArg Fin.val hi, hv⟩
  have hcode := congrArg Fin.val hport
  simp only [brickWallPort, apply_ite, Fin.val_zero, Fin.val_one, Fin.isValue] at hcode
  split_ifs at hcode <;> apply Prod.ext <;> apply Fin.ext <;> omega

theorem rawBrickWall_degree_le_three (c r : ℕ) (x : Fin r × Fin (2 * c)) :
    (rawBrickWall c r).degree x ≤ 3 := by
  let f : (rawBrickWall c r).neighborSet x → Fin 3 := fun y => brickWallPort x y.val
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext (brickWallPort_injective_on_neighbors x y.property z.property h)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [card_neighborSet_eq_degree, Fintype.card_fin] using hcard

theorem rawBrickWall_degree_ge_two_of_interior {c r : ℕ}
    (x : Fin r × Fin (2 * c)) (hleft : 0 < x.2.val) (hright : x.2.val + 1 < 2 * c) :
    2 ≤ (rawBrickWall c r).degree x := by
  let a : Fin r × Fin (2 * c) := (x.1, ⟨x.2.val - 1, by omega⟩)
  let b : Fin r × Fin (2 * c) := (x.1, ⟨x.2.val + 1, hright⟩)
  have ha : (rawBrickWall c r).Adj x a :=
    Or.inl ⟨rfl, pathGraph_adj.mpr (Or.inr (by change x.2.val - 1 + 1 = x.2.val; omega))⟩
  have hb : (rawBrickWall c r).Adj x b :=
    Or.inl ⟨rfl, pathGraph_adj.mpr (Or.inl rfl)⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg (fun y : Fin r × Fin (2 * c) => y.2.val) h
    change x.2.val - 1 = x.2.val + 1 at hv
    omega
  exact Finset.one_lt_card.mpr ⟨a, ((rawBrickWall c r).mem_neighborFinset x a).mpr ha,
    b, ((rawBrickWall c r).mem_neighborFinset x b).mpr hb, hab⟩

def ElementaryWallVertex (c r : ℕ) :=
  {x : Fin r × Fin (2 * c) // 2 ≤ (rawBrickWall c r).degree x}

instance (c r : ℕ) : Fintype (ElementaryWallVertex c r) :=
  inferInstanceAs (Fintype {x : Fin r × Fin (2 * c) // 2 ≤ (rawBrickWall c r).degree x})

instance (c r : ℕ) : LinearOrder (ElementaryWallVertex c r) := finiteLinearOrder _

def elementaryWallInteriorNail {g : ℕ} (hg : 2 ≤ g) (r c : Fin g) :
    ElementaryWallVertex g g := by
  let x : Fin g × Fin (2 * g) := (r, ⟨c.val + 1, by omega⟩)
  refine ⟨x, rawBrickWall_degree_ge_two_of_interior x ?_ ?_⟩
  · change 0 < c.val + 1
    omega
  · change c.val + 1 + 1 < 2 * g
    omega

def elementaryWall (c r : ℕ) : SimpleGraph (ElementaryWallVertex c r) :=
  (rawBrickWall c r).induce {x | 2 ≤ (rawBrickWall c r).degree x}

theorem elementaryWall_degree_le_three (c r : ℕ) (x : ElementaryWallVertex c r) :
    (elementaryWall c r).degree x ≤ 3 := by
  let f : (elementaryWall c r).Copy (rawBrickWall c r) := {
    toHom := { toFun := Subtype.val, map_rel' := fun h => h }
    injective' := Subtype.val_injective }
  exact (f.degree_le x).trans (rawBrickWall_degree_le_three c r x.val)

def elementaryWallGridCopy {c r n : ℕ} (hr : r ≤ n) (hc : 2 * c ≤ n) :
    (elementaryWall c r).Copy (squareGrid n) where
  toHom := {
    toFun := fun x => (Fin.castLE hr x.val.1, Fin.castLE hc x.val.2)
    map_rel' := by
      intro x y hxy
      exact (boxProdCopy (pathGraphCopyOfLE hr) (pathGraphCopyOfLE hc)).toHom.map_adj
        (rawBrickWall_le_grid c r hxy) }
  injective' := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext (Fin.castLE_injective hr (congrArg Prod.fst hxy))
      (Fin.castLE_injective hc (congrArg Prod.snd hxy))

theorem elementaryWall_isMinor_of_grid {V : Type*} {G : SimpleGraph V}
    {c r n : ℕ} (hr : r ≤ n) (hc : 2 * c ≤ n) (hgrid : IsMinor (squareGrid n) G) :
    IsMinor (elementaryWall c r) G :=
  (show IsMinor (elementaryWall c r) (squareGrid n) from
    ⟨MinorModel.of_copy (elementaryWallGridCopy hr hc)⟩).trans hgrid

end
end Erdos73
