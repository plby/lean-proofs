import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCapMayerVietoris
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportMayerVietorisZero
import Mathlib.Algebra.FiveLemma

/-!
# Binary open-cover gluing for the original integral cap maps

Scale the fourth and fifth vertical maps of the actual five-term
diagram by -(-1)^p. That integer acts bijectively and the four squares
then commute with the original exact rows. The homological degree-zero
endpoint uses the original sum surjection and overlap cohomology
vanishing. No coefficient reduction is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open SingularMayerVietoris IntegralCompactSupportCohomology

section Sign

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]

omit [Module ℤ B] in
/-- The connecting sign acts as an involution on the original integer module. -/
theorem connectingSign_involutive (p : ℕ) :
    Function.Involutive (fun b : B => -((-1 : ℤ) ^ p) • b) := by
  intro b
  change -((-1 : ℤ) ^ p) • (-((-1 : ℤ) ^ p) • b) = b
  rw [← mul_smul, neg_mul_neg, IntegralCap.sign_mul_self, one_smul]

theorem signedMap_bijective (p : ℕ) (f : A →ₗ[ℤ] B) (hf : Function.Bijective f) :
    Function.Bijective (-((-1 : ℤ) ^ p) • f) :=
  (connectingSign_involutive (B := B) p).bijective.comp hf

end Sign

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d) (hc : Compatible X d c)
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)

/-- Scaling both actual vertical maps preserves the original first square. -/
theorem first_square_smul (r : ℤ) {p q : ℕ} (h : p + q = d) :
    (leftHomologyMap U V q).comp (r • capOnOpen (U ∩ V) (hU.inter hV) c hc h) =
      (r • productMap c hc U V hU hV h).comp
        (IntegralCompactSupportMayerVietoris.firstMap U V hU hV p) := by
  apply LinearMap.ext
  intro a
  exact (map_zsmul (leftHomologyMap U V q) r
    (capOnOpen (U ∩ V) (hU.inter hV) c hc h a)).trans
      (congrArg (fun b => r • b) (LinearMap.congr_fun (first_square c hc U V hU hV h) a))

variable (hcover : U ∪ V = Set.univ)

include hU hV hcover in
/-- The signed actual five-term diagram glues bijectivity in positive homological degree. -/
theorem bijective_of_cover_positive (p q : ℕ) (h : p + q + 1 = d)
    (hDU : ∀ a b (hab : a + b = d), Function.Bijective (capOnOpen U hU c hc hab))
    (hDV : ∀ a b (hab : a + b = d), Function.Bijective (capOnOpen V hV c hc hab))
    (hDI : ∀ a b (hab : a + b = d),
      Function.Bijective (capOnOpen (U ∩ V) (hU.inter hV) c hc hab)) :
    Function.Bijective
      (IntegralCompactSupportCap.withClasses (p := p) (q := q + 1) (by omega) c hc) := by
  let h₁ : p + (q + 1) = d := by omega
  let h₂ : (p + 1) + q = d := by omega
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (IntegralCompactSupportMayerVietoris.firstMap U V hU hV p)
    (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p)
    (IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover)
    (IntegralCompactSupportMayerVietoris.firstMap U V hU hV (p + 1))
    (leftHomologyMap U V (q + 1))
    (rightHomologyMap U V (q + 1))
    (connectingHomomorphism U V hU hV hcover q)
    (leftHomologyMap U V q)
    (capOnOpen (U ∩ V) (hU.inter hV) c hc h₁)
    (productMap c hc U V hU hV h₁)
    (IntegralCompactSupportCap.withClasses h₁ c hc)
    (-((-1 : ℤ) ^ p) • capOnOpen (U ∩ V) (hU.inter hV) c hc h₂)
    (-((-1 : ℤ) ^ p) • productMap c hc U V hU hV h₂)
    (first_square c hc U V hU hV h₁)
    (second_square c hc U V hU hV h₁)
    (connecting_square c hc U V hU hV hcover h)
    (first_square_smul c hc U V hU hV (-((-1 : ℤ) ^ p)) h₂)
    (LinearMap.exact_iff.mpr
      (IntegralCompactSupportMayerVietoris.exact_middle U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr
      (IntegralCompactSupportMayerVietoris.exact_right U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr
      (IntegralCompactSupportMayerVietoris.exact_left U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (exact_at_pair U V hU hV hcover (q + 1)).symm)
    (LinearMap.exact_iff.mpr (exact_at_ambient U V hU hV hcover q).symm)
    (LinearMap.exact_iff.mpr (exact_at_intersection U V hU hV hcover q).symm)
    (hDI p (q + 1) h₁).2
    (productMap_bijective c hc U V hU hV h₁ (hDU _ _ _) (hDV _ _ _))
    (signedMap_bijective p _ (hDI (p + 1) q h₂))
    (signedMap_bijective p _
      (productMap_bijective c hc U V hU hV h₂ (hDU _ _ _) (hDV _ _ _))).1

include hU hV hcover in
/-- Original right-exact sequences handle the homological degree-zero endpoint. -/
theorem bijective_of_cover_zero (p : ℕ) (h : p + 0 = d)
    (hDU : Function.Bijective (capOnOpen U hU c hc h))
    (hDV : Function.Bijective (capOnOpen V hV c hc h))
    (hDI : Function.Surjective (capOnOpen (U ∩ V) (hU.inter hV) c hc h))
    [Subsingleton (Cohomology (U ∩ V : Set X) (p + 1))] :
    Function.Bijective (IntegralCompactSupportCap.withClasses h c hc) := by
  have hs : Function.Surjective
      (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p) := by
    intro a
    exact (IntegralCompactSupportMayerVietoris.exact_right U V hU hV hcover p).ge
      (show IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover a = 0 from
        Subsingleton.elim _ _)
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (IntegralCompactSupportMayerVietoris.firstMap U V hU hV p)
    (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p)
    (leftHomologyMap U V 0) (rightHomologyMap U V 0)
    (capOnOpen (U ∩ V) (hU.inter hV) c hc h)
    (productMap c hc U V hU hV h) (IntegralCompactSupportCap.withClasses h c hc)
    (first_square c hc U V hU hV h)
    (second_square c hc U V hU hV h)
    (LinearMap.exact_iff.mpr
      (IntegralCompactSupportMayerVietoris.exact_middle U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (exact_at_pair U V hU hV hcover 0).symm)
    hDI (productMap_bijective c hc U V hU hV h hDU hDV) hs
    (rightHomologyMap_zero_surjective U V hU hV hcover)

include hU hV hcover in
/-- Bijectivity of the actual caps glues in every complementary degree. -/
theorem bijective_of_cover
    (hDU : ∀ a b (hab : a + b = d), Function.Bijective (capOnOpen U hU c hc hab))
    (hDV : ∀ a b (hab : a + b = d), Function.Bijective (capOnOpen V hV c hc hab))
    (hDI : ∀ a b (hab : a + b = d),
      Function.Bijective (capOnOpen (U ∩ V) (hU.inter hV) c hc hab))
    (hI : Subsingleton (Cohomology (U ∩ V : Set X) (d + 1)))
    (p q : ℕ) (h : p + q = d) :
    Function.Bijective (IntegralCompactSupportCap.withClasses h c hc) := by
  cases q with
  | zero =>
    have hp : p + 1 = d + 1 := by omega
    let : Subsingleton (Cohomology (U ∩ V : Set X) (p + 1)) := hp ▸ hI
    exact bijective_of_cover_zero c hc U V hU hV hcover p h
      (hDU p 0 h) (hDV p 0 h) (hDI p 0 h).2
  | succ q =>
    exact bijective_of_cover_positive c hc U V hU hV hcover p q (by omega) hDU hDV hDI

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
