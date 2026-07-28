import Mathlib.Data.Finite.Defs
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

theorem Erdos303.erdos_303 :
    ∀ (𝓒 : Int → Int),
      @Set.Finite.{0} Int (@Set.range.{0, 1} Int Int 𝓒) →
        @Exists.{1} Int fun (a : Int) ↦
          @Exists.{1} Int fun (b : Int) ↦
            @Exists.{1} Int fun (c : Int) ↦
              And
                (@List.Nodup.{0} Int
                  (@List.cons.{0} Int a
                    (@List.cons.{0} Int b
                      (@List.cons.{0} Int c
                        (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.nil.{0} Int))))))
                (And
                  (@Eq.{1} Real
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Int.cast.{0} Real Real.instIntCast a))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Int.cast.{0} Real Real.instIntCast b))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Int.cast.{0} Real Real.instIntCast c))))
                  (@Set.Subsingleton.{0} Int
                    (@Set.image.{0, 0} Int Int 𝓒
                      (@Insert.insert.{0, 0} Int (Set.{0} Int) (@Set.instInsert.{0} Int) a
                        (@Insert.insert.{0, 0} Int (Set.{0} Int) (@Set.instInsert.{0} Int) b
                          (@Singleton.singleton.{0, 0} Int (Set.{0} Int) (@Set.instSingletonSet.{0} Int)
                            c))))))
  := by
  sorry
