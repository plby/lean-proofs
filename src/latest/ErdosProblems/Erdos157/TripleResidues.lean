import ErdosProblems.Erdos157.PrimeTriples
import ErdosProblems.Erdos157.MonicProgressions

/-! Triple-product residue fibers: their exact ambient ceiling and disjoint supports. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem PrimeTriple.residue_fiber_card_le {n : ℕ} (g : K[X]) (hg : g.Monic)
    (hd : g.natDegree ≤ 3 * n) (a : AdjoinRoot g) :
    Nat.card {T : PrimeTriple K n // AdjoinRoot.mk g T.product = a} ≤
      Fintype.card K ^ (3 * n - g.natDegree) := by
  let f : {T : PrimeTriple K n // AdjoinRoot.mk g T.product = a} →
      {P : MonicDegreeEq K (3 * n) // AdjoinRoot.mk g P.1 = a} := fun T =>
    ⟨MonicDegreeEq.mk T.1.product T.1.product_monic T.1.product_natDegree, T.2⟩
  have hinj : Function.Injective f := by
    intro U V h
    apply Subtype.ext
    apply PrimeTriple.product_injective n
    exact congrArg (fun P => P.1.1) h
  calc
    _ ≤ Nat.card {P : MonicDegreeEq K (3 * n) // AdjoinRoot.mk g P.1 = a} :=
      Nat.card_le_card_of_injective f hinj
    _ = _ := card_monicResidueFiber g hg _ hd a

noncomputable def PrimeTriple.residueUnit {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (T : PrimeTriple K n) : (AdjoinRoot g)ˣ :=
  (isUnit_mk_of_isCoprime g T.product (by
    apply IsCoprime.prod_right
    intro f _
    exact hc f)).unit

theorem PrimeTriple.residueUnit_val {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (T : PrimeTriple K n) :
    ↑(T.residueUnit g hc) = AdjoinRoot.mk g T.product := IsUnit.unit_spec _

theorem PrimeTriple.residueUnit_fiber_card_le {n : ℕ} (g : K[X]) (hg : g.Monic)
    (hd : g.natDegree ≤ 3 * n) (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1)
    (a : (AdjoinRoot g)ˣ) :
    Nat.card {T : PrimeTriple K n // T.residueUnit g hc = a} ≤
      Fintype.card K ^ (3 * n - g.natDegree) := by
  have hiff (T : PrimeTriple K n) : T.residueUnit g hc = a ↔ AdjoinRoot.mk g T.product = ↑a := by
    rw [← Units.val_inj, PrimeTriple.residueUnit_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact PrimeTriple.residue_fiber_card_le g hg hd ↑a

theorem PrimeTriple.residueUnit_fiber_pairwise_disjoint {n : ℕ} (g : K[X])
    (hd : 2 * n < g.natDegree) (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1)
    (a : (AdjoinRoot g)ˣ) :
    Set.Pairwise {T : PrimeTriple K n | T.residueUnit g hc = a}
      (fun U V => Disjoint U.1 V.1) := by
  intro U hU V hV hne
  have hU' : AdjoinRoot.mk g U.product = ↑a := by rw [← U.residueUnit_val g hc, hU]
  have hV' : AdjoinRoot.mk g V.product = ↑a := by rw [← V.residueUnit_val g hc, hV]
  exact PrimeTriple.residue_fiber_pairwise_disjoint g hd hc ↑a hU' hV' hne

end Erdos157.Elementary.PolynomialCharacters
