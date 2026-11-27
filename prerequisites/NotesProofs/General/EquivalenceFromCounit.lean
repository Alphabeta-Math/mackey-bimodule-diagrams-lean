import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering

/-! A fully faithful functor and a specified counit isomorphism determine
an equivalence with exactly that counit. -/

namespace NotesProofs.General

open CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

/-- Construct an equivalence while retaining the specified counit. -/
noncomputable def equivalenceFromFullyFaithfulCounit (F : C ⥤ D) (G : D ⥤ C)
    [F.Full] [F.Faithful] (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D := by
  let ff := Functor.FullyFaithful.ofFullyFaithful F
  let η : 𝟭 C ≅ F ⋙ G := NatIso.ofComponents
    (fun X => ff.preimageIso ((ε.app (F.obj X)).symm)) (by
      intro X Y f
      apply F.map_injective
      simpa [Functor.FullyFaithful.preimageIso, ff] using ε.inv.naturality (F.map f))
  exact
    { functor := F
      inverse := G
      unitIso := η
      counitIso := ε
      functor_unitIso_comp := by
        intro X
        change F.map (ff.preimage ((ε.app (F.obj X)).symm.hom)) ≫ ε.hom.app (F.obj X) = _
        rw [ff.map_preimage]
        exact (ε.app (F.obj X)).inv_hom_id }

#print axioms equivalenceFromFullyFaithfulCounit

end NotesProofs.General
