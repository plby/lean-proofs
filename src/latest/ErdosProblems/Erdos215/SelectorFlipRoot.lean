/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorModular

/-!
Flipping one primary coordinate of a global root of `-1`.

For a primary factorization `d = c.q * c.D`, the Chinese remainder
equivalence writes a root modulo `d` as a root modulo `c.q` together with a
root modulo `c.D`.  Negating just the first coordinate again gives a root.
The lemmas below record both the changed primary reduction and the unchanged
complementary reduction, including the useful consequence for every other
primary component whose modulus divides `c.D`.
-/

namespace Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace PrimaryComponent

/-- Reduction to the complementary CRT factor. -/
def reduceComplement {d : ℕ} (c : PrimaryComponent d) : ZMod d →+* ZMod c.D :=
  ZMod.castHom c.D_dvd (ZMod c.D)

/-- The first CRT coordinate is the primary-component reduction. -/
lemma split_fst_eq_reduce {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    (c.split x).1 = c.reduce x := by
  have hhom :
      (RingHom.fst (ZMod c.q) (ZMod c.D)).comp c.split.toRingHom = c.reduce :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun hhom x

/-- The second CRT coordinate is reduction to the complementary factor. -/
lemma split_snd_eq_reduceComplement {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    (c.split x).2 = c.reduceComplement x := by
  have hhom :
      (RingHom.snd (ZMod c.q) (ZMod c.D)).comp c.split.toRingHom =
        c.reduceComplement :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun hhom x

/-- Negate the `c.q` CRT coordinate of a root while preserving its `c.D`
coordinate. -/
def flipRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) : Root d :=
  ⟨c.combine (-c.reduce lam.1) (c.split lam.1).2, by
    apply c.split.injective
    simp only [map_pow, split_combine, map_neg, map_one]
    apply Prod.ext
    · change (-c.reduce lam.1) ^ 2 = (-1 : ZMod c.q)
      rw [neg_sq, ← map_pow, lam.property]
      simp
    · change (c.split lam.1).2 ^ 2 = (-1 : ZMod c.D)
      have hroot : c.split (lam.1 ^ 2) = c.split (-1) :=
        congrArg c.split lam.property
      rw [map_pow, map_neg, map_one] at hroot
      have hcoord := congrArg Prod.snd hroot
      change (c.split lam.1).2 ^ 2 = (-1 : ZMod c.D) at hcoord
      exact hcoord⟩

@[simp] theorem reduce_flipRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) :
    c.reduce (c.flipRoot lam).1 = -c.reduce lam.1 := by
  rw [← c.split_fst_eq_reduce]
  exact c.split_combine_fst _ _

@[simp] theorem reduceComplement_flipRoot {d : ℕ}
    (c : PrimaryComponent d) (lam : Root d) :
    c.reduceComplement (c.flipRoot lam).1 = c.reduceComplement lam.1 := by
  rw [← c.split_snd_eq_reduceComplement, ← c.split_snd_eq_reduceComplement]
  exact c.split_combine_snd _ _

/-- Flipping `c` is invisible to any primary component whose whole modulus
lies in the complementary factor `c.D`. -/
theorem reduce_flipRoot_eq_of_q_dvd_D {d : ℕ}
    (c c' : PrimaryComponent d) (hdiv : c'.q ∣ c.D) (lam : Root d) :
    c'.reduce (c.flipRoot lam).1 = c'.reduce lam.1 := by
  let fromComplement : ZMod c.D →+* ZMod c'.q :=
    ZMod.castHom hdiv (ZMod c'.q)
  have hfactor : fromComplement.comp c.reduceComplement = c'.reduce :=
    RingHom.ext_zmod _ _
  calc
    c'.reduce (c.flipRoot lam).1 =
        fromComplement (c.reduceComplement (c.flipRoot lam).1) := by
      exact (DFunLike.congr_fun hfactor (c.flipRoot lam).1).symm
    _ = fromComplement (c.reduceComplement lam.1) := by
      rw [c.reduceComplement_flipRoot]
    _ = c'.reduce lam.1 := by
      exact DFunLike.congr_fun hfactor lam.1

end PrimaryComponent

end

end Erdos215.Selector.Modular
