import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import MackeyDiagrams
import Proofs.BalancedTensorAssociativity

set_option maxHeartbeats 2000000
universe u

#check FreeAbelianGroup
#check FreeAbelianGroup.of
#check FreeAbelianGroup.lift
#print axioms BalancedTensorAssociativity
#print axioms ModuleTensorUniversalProperty
#print axioms Bimodule
#print axioms CategoryTheory.Iso.ext
#check QuotientAddGroup.mk'
#check Exists.elim
#check Classical.choose
#print axioms Classical.choose

def ReviewedCoherence : Prop := (
  let Bimod := fun (B A : RingCat.{u}) =>
    Sigma (fun M : AddCommGrpCat.{u} => Bimodule.{u,u,u}.1 B A M)
  let left := fun {B A : RingCat.{u}} (M : Bimod B A) => M.2.1.smul
  let right := fun {B A : RingCat.{u}} (M : Bimod B A) (a : A) =>
    M.2.2.val.smul (MulOpposite.op a)
  let Equivariant := fun {B A : RingCat.{u}} (M N : Bimod B A) (f : M.1 → N.1) =>
    (∀ (b : B) (m : M.1), f (left M b m) = left N b (f m)) ∧
    (∀ (a : A) (m : M.1), f (right M a m) = right N a (f m))
  let Hom := fun {B A : RingCat.{u}} (M N : Bimod B A) =>
    { f : AddMonoidHom M.1 N.1 // Equivariant M N f }
  let Iso := fun {B A : RingCat.{u}} (M N : Bimod B A) =>
    { e : AddEquiv M.1 N.1 // Equivariant M N e }
  let isoHom := fun {B A : RingCat.{u}} {M N : Bimod B A} (e : Iso M N) =>
    (⟨e.val.toAddMonoidHom, e.property⟩ : Hom M N)
  let idMap := fun {B A : RingCat.{u}} (M : Bimod B A) =>
    (⟨AddMonoidHom.id M.1, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩ : Hom M M)
  let comp := fun {B A : RingCat.{u}} {M N P : Bimod B A}
      (g : Hom N P) (f : Hom M N) =>
    (⟨g.val.comp f.val,
      ⟨fun b m => (congrArg g.val (f.property.1 b m)).trans (g.property.1 b (f.val m)),
       fun a m => (congrArg g.val (f.property.2 a m)).trans (g.property.2 a (f.val m))⟩⟩ :
      Hom M P)
  let regular := fun (A : RingCat.{u}) =>
    (⟨AddCommGrpCat.of A, (Bimodule.{u,u,u}.2.1 A).val⟩ : Bimod A A)
  let IsBalanced := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A)
      (T : AddCommGrpCat.{u}) (t : G.1 → F.1 → T) =>
    (∀ (g g' : G.1) (f : F.1), t (g + g') f = t g f + t g' f) ∧
    (∀ (g : G.1) (f f' : F.1), t g (f + f') = t g f + t g f') ∧
    (∀ (b : B) (g : G.1) (f : F.1), t (right G b g) f = t g (left F b f))
  ∀ (tensor : ∀ {C B A : RingCat.{u}}, Bimod C B → Bimod B A → Bimod C A)
    (tmul : ∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
      G.1 → F.1 → (tensor G F).1),
    (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
      IsBalanced G F (tensor G F).1 (tmul G F) ∧
      ∀ (T : AddCommGrpCat.{u}) (b : G.1 → F.1 → T), IsBalanced G F T b →
        ∃! lift : AddMonoidHom (tensor G F).1 T, ∀ g f, lift (tmul G F g f) = b g f) →
    (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) (g : G.1) (f : F.1),
      (∀ c : C, left (tensor G F) c (tmul G F g f) = tmul G F (left G c g) f) ∧
      (∀ a : A, right (tensor G F) a (tmul G F g f) = tmul G F g (right F a f))) →
    ∃ (tensorMap : ∀ {C B A : RingCat.{u}} {G G' : Bimod C B} {F F' : Bimod B A},
        Hom G G' → Hom F F' → Hom (tensor G F) (tensor G' F'))
      (assoc : ∀ {D C B A : RingCat.{u}} (H : Bimod D C) (G : Bimod C B) (F : Bimod B A),
          Iso (tensor (tensor H G) F) (tensor H (tensor G F)))
      (leftUnitor : ∀ {B A : RingCat.{u}} (F : Bimod B A), Iso (tensor (regular B) F) F)
      (rightUnitor : ∀ {B A : RingCat.{u}} (F : Bimod B A), Iso (tensor F (regular A)) F),
      (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) (x : (tensor G F).1),
        ∃ terms : List (Prod G.1 F.1),
          x = List.sum (List.map (fun p => tmul G F p.1 p.2) terms)) ∧
      (∀ {C B A : RingCat.{u}} {G G' : Bimod C B} {F F' : Bimod B A}
          (g : Hom G G') (f : Hom F F') (y : G.1) (x : F.1),
        (tensorMap g f).val (tmul G F y x) = tmul G' F' (g.val y) (f.val x)) ∧
      (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
        tensorMap (idMap G) (idMap F) = idMap (tensor G F)) ∧
      (∀ {C B A : RingCat.{u}} {G G' G'' : Bimod C B} {F F' F'' : Bimod B A}
          (g : Hom G G') (g' : Hom G' G'') (f : Hom F F') (f' : Hom F' F''),
        tensorMap (comp g' g) (comp f' f) = comp (tensorMap g' f') (tensorMap g f)) ∧
      (∀ {D C B A : RingCat.{u}} (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
          (h : H.1) (g : G.1) (f : F.1),
        (assoc H G F).val (tmul (tensor H G) F (tmul H G h g) f) =
          tmul H (tensor G F) h (tmul G F g f)) ∧
      (∀ {B A : RingCat.{u}} (F : Bimod B A) (b : B) (a : A) (f : F.1),
        (leftUnitor F).val (tmul (regular B) F b f) = left F b f ∧
        (rightUnitor F).val (tmul F (regular A) f a) = right F a f) ∧
      (∀ {D C B A : RingCat.{u}} {H H' : Bimod D C} {G G' : Bimod C B} {F F' : Bimod B A}
          (h : Hom H H') (g : Hom G G') (f : Hom F F'),
        comp (isoHom (assoc H' G' F')) (tensorMap (tensorMap h g) f) =
          comp (tensorMap h (tensorMap g f)) (isoHom (assoc H G F))) ∧
      (∀ {B A : RingCat.{u}} {F F' : Bimod B A} (f : Hom F F'),
        comp (isoHom (leftUnitor F')) (tensorMap (idMap (regular B)) f) =
          comp f (isoHom (leftUnitor F)) ∧
        comp (isoHom (rightUnitor F')) (tensorMap f (idMap (regular A))) =
          comp f (isoHom (rightUnitor F))) ∧
      (∀ {E D C B A : RingCat.{u}}
          (K : Bimod E D) (H : Bimod D C) (G : Bimod C B) (F : Bimod B A),
        comp (isoHom (assoc K H (tensor G F))) (isoHom (assoc (tensor K H) G F)) =
          comp (tensorMap (idMap K) (isoHom (assoc H G F)))
            (comp (isoHom (assoc K (tensor H G) F))
              (tensorMap (isoHom (assoc K H G)) (idMap F)))) ∧
      (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
        comp (tensorMap (idMap G) (isoHom (leftUnitor F))) (isoHom (assoc G (regular B) F)) =
          tensorMap (isoHom (rightUnitor G)) (idMap F))
)
#print axioms ReviewedCoherence
#print axioms FreeAbelianGroup
#print axioms FreeAbelianGroup.of
#print axioms FreeAbelianGroup.lift
#print axioms FreeAbelianGroup.lift_apply_of
#print axioms FreeAbelianGroup.induction_on
#print axioms AddSubgroup.closure
#print axioms QuotientAddGroup.mk'
#print axioms QuotientAddGroup.lift
#print axioms QuotientAddGroup.induction_on
#print axioms Finsupp.single
