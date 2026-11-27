import MackeyDiagrams.ScopedCup
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! A linear label inside a curl is pushed forward along its actual outer strand. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H G : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace AlgebraUpDot

noncomputable def whisker (outer : ConjEmbedding H G) {a b : ConjEmbedding K H}
    (label : AlgebraUpDot R a b) : AlgebraUpDot R (outer.comp a) (outer.comp b) where
  label := MonoidAlgebra.mapDomainAlgHom R R outer.toHom label.label
  intertwines := by
    intro k
    let map := MonoidAlgebra.mapDomainAlgHom R R outer.toHom
    have mapSingle (h : H) : map (MonoidAlgebra.single h 1) =
        MonoidAlgebra.single (outer.toHom h) 1 := MonoidAlgebra.mapDomain_single
    change MonoidAlgebra.single (outer.toHom (a.toHom k)) 1 * map label.label =
      map label.label * MonoidAlgebra.single (outer.toHom (b.toHom k)) 1
    rw [← mapSingle, ← mapSingle, ← map_mul, label.intertwines, map_mul]

theorem whisker_coeff_outside (outer : ConjEmbedding H G)
    {a b : ConjEmbedding K H} (label : AlgebraUpDot R a b) (g : G)
    (outside : g ∉ outer.toHom.range) :
    (label.whisker outer).label.coeff g = 0 := by
  change Finsupp.mapDomain outer.toHom label.label.coeff g = 0
  exact Finsupp.mapDomain_of_notMem_range _ g outside

end AlgebraUpDot

inductive RightCurlLabel (R : Type v) [CommSemiring R] (inner : ConjEmbedding K H) :
    ConjEmbedding H G → ConjEmbedding H G → Type (max u v)
  | groupDot {a b : ConjEmbedding H G} (d : Dot (a.comp inner) (b.comp inner)) :
      RightCurlLabel R inner a b
  | algebraDot (a : ConjEmbedding H G) (d : AlgebraUpDot R inner inner) :
      RightCurlLabel R inner a a

namespace RightCurlLabel

noncomputable def interpret {inner : ConjEmbedding K H} :
    {a b : ConjEmbedding H G} →
    RightCurlLabel R inner a b → ScopedDiagram R (.up (a.comp inner)) (.up (b.comp inner))
  | _, _, .groupDot d => .ordinary (.upDot d)
  | _, _, .algebraDot a d => .algebraUpDot (d.whisker a)

end RightCurlLabel

namespace ScopedDiagram

/-- The cup and cap attach to the through strand by merging and splitting it. -/
noncomputable def rightCurlUp {inner : ConjEmbedding K H} {a b : ConjEmbedding H G}
    (label : RightCurlLabel R inner a b) (finite : inner.toHom.range.FiniteIndex) :
    ScopedDiagram R (.up a) (.up b) :=
  let ga := Word.up a
  let gb := Word.up b
  let hk := Word.up inner
  let kh := Word.down inner
  .vertical (.ordinary (.insertRightUnit ga))
    (.vertical (.ordinary (.horizontal (.id ga) (.reverseCup inner finite)))
      (.vertical (.ordinary (.unassociate ga hk kh))
        (.vertical (.ordinary (.horizontal (.mergeUp a inner) (.id kh)))
          (.vertical (.horizontal label.interpret (.ordinary (.id kh)))
            (.vertical (.ordinary (.horizontal (.splitUp b inner) (.id kh)))
              (.vertical (.ordinary (.associate gb hk kh))
                (.vertical (.ordinary (.horizontal (.id gb) (.multiplicationCap inner)))
                  (.ordinary (.rightUnit gb)))))))))

end ScopedDiagram
end MackeyDiagrams
