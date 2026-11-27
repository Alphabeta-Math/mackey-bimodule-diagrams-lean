import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Congruence.Hom

universe u v
variable {P : Type u} {T : Type v} [AddCommGroup T]
variable (r : FreeAddGroup P → FreeAddGroup P → Prop)

private def descend (b : P → T)
    (hb : ∀ x y, r x y → (FreeAddGroup.lift b) x = (FreeAddGroup.lift b) y) :
    (addConGen r).Quotient →+ T :=
  AddCon.lift (addConGen r) (FreeAddGroup.lift b) (AddCon.addConGen_le.mpr hb)

private theorem descend_on_generator (b : P → T)
    (hb : ∀ x y, r x y → (FreeAddGroup.lift b) x = (FreeAddGroup.lift b) y) (p : P) :
    descend r b hb (Quotient.mk (addConGen r).toSetoid (FreeAddGroup.of p)) = b p :=
  FreeAddGroup.lift_apply_of

private theorem hom_ext (f g : (addConGen r).Quotient →+ T)
    (h : ∀ p : P, f (Quotient.mk (addConGen r).toSetoid (FreeAddGroup.of p)) =
      g (Quotient.mk (addConGen r).toSetoid (FreeAddGroup.of p))) : f = g := by
  let mk := AddCon.mk' (addConGen r)
  have hfg : f.comp mk = g.comp mk :=
    FreeAddGroup.lift.symm.injective (funext h)
  apply AddMonoidHom.ext
  intro q
  refine Quotient.inductionOn q (fun x => ?_)
  exact DFunLike.congr_fun hfg x

#print axioms descend
#print axioms descend_on_generator
#print axioms hom_ext
