import ErdosProblems.Erdos157.TripleResidues
import ErdosProblems.Erdos157.GroupTripleCounts

/-! Unordered prime-triple supply from the elementary prime-distribution estimate. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open FiniteFiberCounts GroupTripleCounts

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def primeResidueUnit {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (f : PrimeDegree K n) : (AdjoinRoot g)ˣ :=
  (isUnit_mk_of_isCoprime g f.1.1 (hc f)).unit

theorem primeResidueUnit_val {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (f : PrimeDegree K n) :
    ↑(primeResidueUnit g hc f) = AdjoinRoot.mk g f.1.1 := IsUnit.unit_spec _

theorem primeResidueUnit_fiberCard {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (a : (AdjoinRoot g)ˣ) :
    fiberCard (primeResidueUnit g hc) a = primeProgressionCount g n ↑a := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  rw [← Units.val_inj, primeResidueUnit_val]

theorem PrimeTriple.residueUnit_eq_prod {n : ℕ} (g : K[X])
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (T : PrimeTriple K n) :
    T.residueUnit g hc = ∏ f ∈ T.1, primeResidueUnit g hc f := by
  apply Units.ext
  rw [PrimeTriple.residueUnit_val]
  simp only [PrimeTriple.product, primeSetProduct, map_prod, Units.coe_prod, primeResidueUnit_val]

/-- A coarse factor `27` for forgetting the order is sufficient here. -/
theorem PrimeTriple.residueUnit_fiber_card_lower {n : ℕ} (g : K[X]) (hg : g.Monic)
    (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1) (L : ℝ) (hL : 6 ≤ L)
    (hlower : ∀ a : (AdjoinRoot g)ˣ, L ≤ primeProgressionCount g n ↑a)
    (u : (AdjoinRoot g)ˣ) :
    (Nat.card (AdjoinRoot g)ˣ : ℝ) ^ 2 * L ^ 3 / 54 ≤
      Nat.card {T : PrimeTriple K n // T.residueUnit g hc = u} := by
  classical
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  let : Fintype (AdjoinRoot g)ˣ := Fintype.ofFinite _
  let x : PrimeDegree K n → (AdjoinRoot g)ˣ := primeResidueUnit g hc
  let S := (distinctTriples x u).image Parabola.support
  have hs (s : ↥S) : s.1.card = 3 ∧ (∏ f ∈ s.1, x f) = u := by
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp s.2
    have hd : Distinct t := ((mem_distinctTriples x u t).mp ht).2
    have hp : tripleProduct x t = u := ((mem_distinctTriples x u t).mp ht).1
    rw [← heq]
    exact ⟨support_card_of_distinct hd, (support_prod_of_distinct x hd).trans hp⟩
  let f : ↥S → {T : PrimeTriple K n // T.residueUnit g hc = u} := fun s =>
    ⟨⟨s.1, (hs s).1⟩, by rw [PrimeTriple.residueUnit_eq_prod]; exact (hs s).2⟩
  have hinj : Function.Injective f := by
    intro s t h
    exact Subtype.ext (congrArg (fun T => T.1.1) h)
  have hcount := support_image_card_lower x u L hL (fun a => by
    rw [primeResidueUnit_fiberCard]
    exact hlower a)
  rw [← Nat.card_eq_fintype_card] at hcount
  calc
    _ ≤ (S.card : ℝ) := hcount
    _ ≤ _ := by
      have hcard := Nat.card_le_card_of_injective f hinj
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        (show (Nat.card ↥S : ℝ) ≤ Nat.card {T : PrimeTriple K n // T.residueUnit g hc = u} by
          exact_mod_cast hcard)

end Erdos157.Elementary.PolynomialCharacters
