import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The index-V lattice extension for a cyclic interval
-/

namespace Erdos336

abbrev IntPair := ℤ × ℤ

/-- The integer label homomorphism associated to two elements. -/
def intPairLabelHom {G : Type*} [AddCommGroup G] (a d : G) : IntPair →+ G where
  toFun p := p.1 • a + p.2 • d
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

/-- The determinant-`V` change of coordinates
`(j,k) ↦ (Vj-k,k)`. -/
def intervalStretchHom (V : ℕ) : IntPair →+ IntPair where
  toFun p := ((V : ℤ) * p.1 - p.2, p.2)
  map_zero' := by simp
  map_add' p q := by
    apply Prod.ext <;> simp <;> ring

/-- Sum of transformed coordinates modulo `V`. -/
def coordinateSumModHom (V : ℕ) : IntPair →+ ZMod V where
  toFun p := (p.1 + p.2 : ℤ)
  map_zero' := by simp
  map_add' p q := by
    change (((p.1 + q.1) + (p.2 + q.2) : ℤ) : ZMod V) =
      ((p.1 + p.2 : ℤ) : ZMod V) + ((q.1 + q.2 : ℤ) : ZMod V)
    push_cast
    ring

/-- The stretched lattice consists exactly of integer pairs whose coordinate
sum is divisible by `V`. -/
theorem range_intervalStretchHom_eq_ker (V : ℕ) :
    (intervalStretchHom V).range = (coordinateSumModHom V).ker := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change (((V : ℤ) * q.1 - q.2 + q.2 : ℤ) : ZMod V) = 0
    simp
  · intro hp
    change (((p.1 + p.2 : ℤ) : ZMod V) = 0) at hp
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hp
    obtain ⟨j, hj⟩ := hp
    refine ⟨(j, p.2), ?_⟩
    apply Prod.ext
    · dsimp [intervalStretchHom]
      nlinarith
    · rfl

/-- The stretch is injective when `V>0`. -/
theorem intervalStretchHom_injective {V : ℕ} (hV : 0 < V) :
    Function.Injective (intervalStretchHom V) := by
  intro p q hpq
  have h₁ := congrArg (fun z : IntPair => z.1) hpq
  have h₂ := congrArg (fun z : IntPair => z.2) hpq
  dsimp [intervalStretchHom] at h₁ h₂
  apply Prod.ext
  · nlinarith
  · exact h₂

/-- The subgroup obtained by stretching the kernel of a label map. -/
def stretchedKernel {G : Type*} [AddCommGroup G]
    (f : IntPair →+ G) (V : ℕ) : AddSubgroup IntPair :=
  f.ker.map (intervalStretchHom V)

/-- The corresponding finite lattice quotient. -/
abbrev IntervalLatticeExtension {G : Type*} [AddCommGroup G]
    (f : IntPair →+ G) (V : ℕ) :=
  IntPair ⧸ stretchedKernel f V

private theorem coordinateSumModHom_surjective (V : ℕ) :
    Function.Surjective (coordinateSumModHom V) := by
  intro z
  obtain ⟨i, hi⟩ := ZMod.intCast_surjective z
  refine ⟨(i, 0), ?_⟩
  simpa [coordinateSumModHom] using hi

/-- If the original label map is onto a finite group `G`, the stretched
quotient has exactly `V |G|` elements. -/
theorem card_intervalLatticeExtension
    {G : Type*} [AddCommGroup G] [Finite G]
    (f : IntPair →+ G) {V : ℕ} (hV : 0 < V)
    (hf : Function.Surjective f) :
    Nat.card (IntervalLatticeExtension f V) = V * Nat.card G := by
  let M := intervalStretchHom V
  let L := f.ker
  let K := M.range
  let L' := stretchedKernel f V
  have hMinj : Function.Injective M := intervalStretchHom_injective hV
  have hL' : L' = L.map M := rfl
  have hK : K = (coordinateSumModHom V).ker := by
    exact range_intervalStretchHom_eq_ker V
  have hmaptop : (⊤ : AddSubgroup IntPair).map M = K := by
    ext x
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Set.mem_univ z, hz⟩
  have hrel : L'.relIndex K = L.index := by
    rw [hL', ← hmaptop]
    simpa using AddSubgroup.relIndex_map_map_of_injective L ⊤ hMinj
  have hKindex : K.index = V := by
    rw [hK, AddSubgroup.index_ker]
    have hrange : (coordinateSumModHom V).range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr (coordinateSumModHom_surjective V)
    rw [hrange]
    simp [Nat.card_zmod]
  have hLindex : L.index = Nat.card G := by
    dsimp [L]
    rw [AddSubgroup.index_ker]
    have hrange : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hf
    rw [hrange]
    simp
  have hle : L' ≤ K := by
    rw [hL', ← hmaptop]
    exact AddSubgroup.map_mono le_top
  have hchain := AddSubgroup.relIndex_mul_index hle
  rw [hrel, hKindex, hLindex] at hchain
  calc
    Nat.card (IntervalLatticeExtension f V) = L'.index :=
      (AddSubgroup.index_eq_card L').symm
    _ = V * Nat.card G := by simpa [mul_comm] using hchain.symm

end Erdos336
