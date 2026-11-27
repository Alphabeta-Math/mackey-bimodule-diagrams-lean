import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Rep.Iso

universe u v w

def endpoint : Prop :=
∀ (k : Type u) [Field k] (G : Type v) [Group G] (H : Subgroup G),
  let R := MonoidAlgebra k (↥H)
  let S := MonoidAlgebra k G
  let i : RingHom R S := MonoidAlgebra.mapDomainRingHom k (Subgroup.subtype H)
  letI : Module (MulOpposite R) S := Module.compHom S (RingHom.op i)
  let Res := ModuleCat.restrictScalars.{max u v w} i
  let ToRepH : CategoryTheory.Functor (ModuleCat.{max u v w} R) (Rep.{max u v w} k (↥H)) :=
    Rep.ofModuleMonoidAlgebra
  let ToRepG : CategoryTheory.Functor (ModuleCat.{max u v w} S) (Rep.{max u v w} k G) :=
    Rep.ofModuleMonoidAlgebra
  let Balanced := fun (V : ModuleCat.{max u v w} R)
      (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)) =>
    ∀ (a : R) (x : S) (z : V), p (x * i a) z = p x (a • z)
  Function.Injective i ∧
  (∀ (a : R) (h : ↥H), MonoidAlgebra.coeff (i a) (h : G) = MonoidAlgebra.coeff a h) ∧
  (∀ (a : R) (g : G), g ∉ H → MonoidAlgebra.coeff (i a) g = 0) ∧
  (∀ (a : R) (x : S), MulOpposite.op a • x = x * i a) ∧
  SMulCommClass (MulOpposite R) S S ∧
  (∀ (W : ModuleCat.{max u v w} S) (a : k) (z : W),
    (show W from a • (show ToRepH.obj (Res.obj W) from z)) =
      (show W from a • (show ToRepG.obj W from z))) ∧
  (∀ (W : ModuleCat.{max u v w} S) (h : ↥H) (z : W),
    (show W from Rep.ρ (ToRepH.obj (Res.obj W)) h z) =
      (show W from Rep.ρ (ToRepG.obj W) (h : G) z)) ∧
  ∃ (Ind : CategoryTheory.Functor (ModuleCat.{max u v w} R) (ModuleCat.{max u v w} S))
    (pure : ∀ V : ModuleCat.{max u v w} R, AddMonoidHom S (AddMonoidHom V (Ind.obj V))),
    (∀ V : ModuleCat.{max u v w} R,
      Balanced V (Ind.obj V) (pure V) ∧
      (∀ (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)),
        Balanced V A p → ∃! f : AddMonoidHom (Ind.obj V) A, ∀ x z, f (pure V x z) = p x z) ∧
      (∀ (s x : S) (z : V), s • pure V x z = pure V (s * x) z) ∧
      (∀ (g : G) (x : S) (z : V),
        (show Ind.obj V from Rep.ρ (ToRepG.obj (Ind.obj V)) g (pure V x z)) =
          pure V (MonoidAlgebra.single g (1 : k) * x) z)) ∧
    (∀ {V V' : ModuleCat.{max u v w} R} (f : Quiver.Hom V V') (x : S) (z : V),
      ModuleCat.Hom.hom (Ind.map f) (pure V x z) = pure V' x (ModuleCat.Hom.hom f z)) ∧
    Nonempty (CategoryTheory.Adjunction Ind Res)
