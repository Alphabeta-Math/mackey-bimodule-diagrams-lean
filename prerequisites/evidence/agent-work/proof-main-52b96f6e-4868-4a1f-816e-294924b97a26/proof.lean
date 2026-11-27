by
  intro k _ G _
  -- Theorem 7.4 in the lecture notes asks for inverse functors preserving the
  -- underlying groups. Alphabeta Math steps 1.1–3.1 extend the action by the
  -- monoid-algebra lift, and step 4.1 restricts along the scalar and basis
  -- maps. The pinned functors implement these constructions over a
  -- commutative ring and monoid. A field and group supply those instances.
  -- They use the canonical MonoidAlgebra whose convolution and scalar laws
  -- are recorded in GroupAlgebraRingLaws. Only algebra elements have finite
  -- support, so G and the representation carrier can be arbitrary.
  let equivalence := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  refine ⟨equivalence.functor, equivalence.inverse, ?_, ?_, ?_, ?_⟩
  -- Step 6.1 supplies equality of actions. The coordinator's retained check
  -- turns this into literal functor equalities by checking that the natural
  -- isomorphisms have precisely the maps induced by the object equalities.
  · refine CategoryTheory.Functor.ext_of_iso equivalence.unitIso.symm
      representationModule_roundTripRep ?_
    intro X
    have coeEqToHom (Y Z : Rep.{w} k G) (h : Y = Z) :
        ⇑(CategoryTheory.eqToHom h : Y ⟶ Z) =
          cast (congrArg Rep.V h) := by
      cases h
      rfl
    -- Both the unit inverse and the cast act as the identity on elements.
    ext x
    exact congrFun (coeEqToHom _ _ (representationModule_roundTripRep X)).symm x
  · refine CategoryTheory.Functor.ext_of_iso equivalence.counitIso
      representationModule_roundTripModule ?_
    intro M
    have coeEqToHom (N P : ModuleCat.{w} (MonoidAlgebra k G)) (h : N = P) :
        ⇑(CategoryTheory.eqToHom h : N ⟶ P) =
          cast (congrArg ModuleCat.carrier h) := by
      cases h
      rfl
    -- The counit also acts as the identity on elements.
    ext x
    exact congrFun (coeEqToHom _ _ (representationModule_roundTripModule M)).symm x
  -- Step 5.1 is implemented by the functor maps. Extension checks linearity
  -- by induction on group-algebra elements using the intertwining equation.
  -- Restriction checks linearity and equivariance at scalars and basis
  -- elements. Both maps retain the given additive map, and the underlying
  -- additive group objects are definitionally equal.
  · exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
  · exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
