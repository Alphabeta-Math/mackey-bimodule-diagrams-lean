import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Category.Ring.Basic
import MackeyDiagrams
import Proofs.BalancedTensorAssociativity
import Proofs.Bimodule
set_option maxHeartbeats 2000000
universe u

namespace MoritaCoherence

abbrev Structure (B A : RingCat.{u}) (M : AddCommGrpCat.{u}) := Bimodule.{u,u,u}.1 B A M
abbrev Bimod (B A : RingCat.{u}) := Sigma (Structure B A)

variable {A B C D E : RingCat.{u}}

abbrev left (M : Bimod B A) := M.2.1.smul
abbrev right (M : Bimod B A) (a : A) := M.2.2.val.smul (MulOpposite.op a)

private theorem act_comm (M : Bimod B A) (b : B) (a : A) (m : M.1) :
    right M a (left M b m) = left M b (right M a m) :=
  M.2.2.property.smul_comm (MulOpposite.op a) b m

private def leftHom (M : Bimod B A) (b : B) : AddMonoidHom M.1 M.1 :=
  letI : Module B M.1 := M.2.1
  DistribSMul.toAddMonoidHom M.1 b

private def rightHom (M : Bimod B A) (a : A) : AddMonoidHom M.1 M.1 :=
  letI : Module (MulOpposite A) M.1 := M.2.2.val
  DistribSMul.toAddMonoidHom M.1 (MulOpposite.op a)

abbrev Equivariant (M N : Bimod B A) (f : M.1 → N.1) :=
  (∀ (b : B) (m : M.1), f (left M b m) = left N b (f m)) ∧
  (∀ (a : A) (m : M.1), f (right M a m) = right N a (f m))

abbrev Hom (M N : Bimod B A) := { f : AddMonoidHom M.1 N.1 // Equivariant M N f }
abbrev Iso (M N : Bimod B A) := { e : AddEquiv M.1 N.1 // Equivariant M N e }

private def isoHom {M N : Bimod B A} (e : Iso M N) : Hom M N :=
  ⟨e.val.toAddMonoidHom, e.property⟩

private def idMap (M : Bimod B A) : Hom M M :=
  ⟨AddMonoidHom.id M.1, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩

private def comp {M N P : Bimod B A} (g : Hom N P) (f : Hom M N) : Hom M P :=
  ⟨g.val.comp f.val,
    ⟨fun b m => (congrArg g.val (f.property.1 b m)).trans (g.property.1 b (f.val m)),
     fun a m => (congrArg g.val (f.property.2 a m)).trans (g.property.2 a (f.val m))⟩⟩

private theorem comp_apply {M N P : Bimod B A} (g : Hom N P) (f : Hom M N) (x : M.1) :
    (comp g f).val x = g.val (f.val x) := rfl

private noncomputable abbrev regular (A : RingCat.{u}) : Bimod A A :=
  ⟨AddCommGrpCat.of A, (Bimodule.{u,u,u}.2.1 A).val⟩

private theorem regular_left (b x : A) : left (regular A) b x = b * x :=
  (Bimodule.{u,u,u}.2.1 A).property.1 b x

private theorem regular_right (a x : A) : right (regular A) a x = x * a :=
  (Bimodule.{u,u,u}.2.1 A).property.2 x a

private def IsBalanced (G : Bimod C B) (F : Bimod B A)
    (T : AddCommGrpCat.{u}) (t : G.1 → F.1 → T) :=
  (∀ (g g' : G.1) (f : F.1), t (g + g') f = t g f + t g' f) ∧
  (∀ (g : G.1) (f f' : F.1), t g (f + f') = t g f + t g f') ∧
  (∀ (b : B) (g : G.1) (f : F.1), t (right G b g) f = t g (left F b f))

/- F5 and the route's explicit quotient. Commutativity is imposed alongside
   the two additivity relations and balance, so the free group supplies an
   actual lift without choosing a lift from an existence proposition. -/
private def relation (G : Bimod C B) (F : Bimod B A)
    (x y : FreeAddGroup (Prod G.1 F.1)) :=
  let gen := fun (g : G.1) (f : F.1) => FreeAddGroup.of (g, f)
  (∃ p q : FreeAddGroup (Prod G.1 F.1), x = p + q ∧ y = q + p) ∨
  (∃ (g g' : G.1) (f : F.1), x = gen (g + g') f ∧ y = gen g f + gen g' f) ∨
  (∃ (g : G.1) (f f' : F.1), x = gen g (f + f') ∧ y = gen g f + gen g f') ∨
  (∃ (b : B) (g : G.1) (f : F.1), x = gen (right G b g) f ∧ y = gen g (left F b f))

private def congruence (G : Bimod C B) (F : Bimod B A) := addConGen (relation G F)

private def underlying (G : Bimod C B) (F : Bimod B A) : AddCommGrpCat.{u} :=
  let c := congruence G F
  letI : AddCommGroup c.Quotient :=
    { AddCon.addGroup c with
      add_comm := fun x y => Quotient.inductionOn₂ x y fun p q =>
        Quotient.sound (s := c.toSetoid) (AddConGen.Rel.of _ _ (Or.inl ⟨p, q, rfl, rfl⟩)) }
  AddCommGrpCat.of c.Quotient

private def pure (G : Bimod C B) (F : Bimod B A) (g : G.1) (f : F.1) : underlying G F :=
  Quotient.mk (congruence G F).toSetoid (FreeAddGroup.of (g, f))

private theorem pure_add_left (G : Bimod C B) (F : Bimod B A) (g g' : G.1) (f : F.1) :
    pure G F (g + g') f = pure G F g f + pure G F g' f :=
  Quotient.sound (s := (congruence G F).toSetoid)
    (AddConGen.Rel.of _ _ (Or.inr (Or.inl ⟨g, g', f, rfl, rfl⟩)))

private theorem pure_add_right (G : Bimod C B) (F : Bimod B A) (g : G.1) (f f' : F.1) :
    pure G F g (f + f') = pure G F g f + pure G F g f' :=
  Quotient.sound (s := (congruence G F).toSetoid)
    (AddConGen.Rel.of _ _ (Or.inr (Or.inr (Or.inl ⟨g, f, f', rfl, rfl⟩))))

private theorem pure_balance (G : Bimod C B) (F : Bimod B A) (b : B) (g : G.1) (f : F.1) :
    pure G F (right G b g) f = pure G F g (left F b f) :=
  Quotient.sound (s := (congruence G F).toSetoid)
    (AddConGen.Rel.of _ _ (Or.inr (Or.inr (Or.inr ⟨b, g, f, rfl, rfl⟩))))

private def pureLeft (G : Bimod C B) (F : Bimod B A) (f : F.1) :
    AddMonoidHom G.1 (underlying G F) :=
  AddMonoidHom.mk' (fun g => pure G F g f) (fun g g' => pure_add_left G F g g' f)

private def pureRight (G : Bimod C B) (F : Bimod B A) (g : G.1) :
    AddMonoidHom F.1 (underlying G F) :=
  AddMonoidHom.mk' (pure G F g) (pure_add_right G F g)

private theorem pure_balanced (G : Bimod C B) (F : Bimod B A) :
    IsBalanced G F (underlying G F) (pure G F) :=
  ⟨pure_add_left G F, pure_add_right G F, pure_balance G F⟩

private def lift (G : Bimod C B) (F : Bimod B A) (T : AddCommGrpCat.{u})
    (t : G.1 → F.1 → T) (ht : IsBalanced G F T t) :
    AddMonoidHom (underlying G F) T := by
  let l : AddMonoidHom (FreeAddGroup (Prod G.1 F.1)) T :=
    FreeAddGroup.lift (fun p => t p.1 p.2)
  have he (g : G.1) (f : F.1) : l (FreeAddGroup.of (g, f)) = t g f :=
    FreeAddGroup.lift_apply_of
  refine AddCon.lift (congruence G F) l (AddCon.addConGen_le.2 ?_)
  intro x y h
  change l x = l y
  rcases h with ⟨p, q, rfl, rfl⟩ | ⟨g, g', f, rfl, rfl⟩ |
    ⟨g, f, f', rfl, rfl⟩ | ⟨b, g, f, rfl, rfl⟩
  · rw [map_add, map_add, add_comm]
  · simpa only [map_add, he] using ht.1 g g' f
  · simpa only [map_add, he] using ht.2.1 g f f'
  · simpa only [he] using ht.2.2 b g f

private theorem lift_pure (G : Bimod C B) (F : Bimod B A) (T : AddCommGrpCat.{u})
    (t : G.1 → F.1 → T) (ht : IsBalanced G F T t) (g : G.1) (f : F.1) :
    lift G F T t ht (pure G F g f) = t g f := by
  change FreeAddGroup.lift (fun p : Prod G.1 F.1 => t p.1 p.2)
    (FreeAddGroup.of (g, f)) = t g f
  exact FreeAddGroup.lift_apply_of

private theorem tensor_ext {T : Type*} [AddMonoid T] {G : Bimod C B} {F : Bimod B A}
    (s t : AddMonoidHom (underlying G F) T)
    (h : ∀ g f, s (pure G F g f) = t (pure G F g f)) : s = t := by
  let q : AddMonoidHom (FreeAddGroup (Prod G.1 F.1)) (underlying G F) :=
    (congruence G F).mk'
  have eq : s.comp q = t.comp q :=
    FreeAddGroup.ext_hom _ _ (fun p => h p.1 p.2)
  apply AddMonoidHom.ext
  intro x
  exact Quotient.inductionOn x (fun w => DFunLike.congr_fun eq w)

private theorem lift_unique (G : Bimod C B) (F : Bimod B A) (T : AddCommGrpCat.{u})
    (t : G.1 → F.1 → T) (ht : IsBalanced G F T t) :
    ∃! l : AddMonoidHom (underlying G F) T, ∀ g f, l (pure G F g f) = t g f :=
  ⟨lift G F T t ht, lift_pure G F T t ht,
    fun _ hl => tensor_ext _ _ (fun g f => (hl g f).trans (lift_pure G F T t ht g f).symm)⟩

private theorem finite_sum (G : Bimod C B) (F : Bimod B A) (x : underlying G F) :
    ∃ terms : List (Prod G.1 F.1), x = (terms.map (fun p => pure G F p.1 p.2)).sum := by
  let q : AddMonoidHom (FreeAddGroup (Prod G.1 F.1)) (underlying G F) :=
    (congruence G F).mk'
  refine Quotient.inductionOn x (fun w => ?_)
  change ∃ terms : List (Prod G.1 F.1), q w = (terms.map (fun p => pure G F p.1 p.2)).sum
  induction w using FreeAddGroup.induction_on with
  | zero => exact ⟨[], map_zero q⟩
  | of p => exact ⟨[p], (add_zero _).symm⟩
  | neg_of p _ =>
    refine ⟨[(-p.1, p.2)], ?_⟩
    change q (-FreeAddGroup.of p) = pure G F (-p.1) p.2 + 0
    rw [map_neg, add_zero]
    exact (map_neg (pureLeft G F p.2) p.1).symm
  | add x y hx hy =>
    obtain ⟨xs, hxs⟩ := hx
    obtain ⟨ys, hys⟩ := hy
    exact ⟨xs ++ ys, by rw [map_add, hxs, hys, List.map_append, List.sum_append]⟩

/- F1. The outer actions descend because each commutes with the appropriate
   middle action. Their module laws are equalities of additive maps. -/
private def outerLeft (G : Bimod C B) (F : Bimod B A) (c : C) :
    AddMonoidHom (underlying G F) (underlying G F) :=
  lift G F (underlying G F) (fun g f => pure G F (left G c g) f) (by
    refine ⟨?_, fun g f f' => pure_add_right G F (left G c g) f f', ?_⟩
    · intro g g' f
      change pure G F (leftHom G c (g + g')) f = _
      rw [map_add, pure_add_left]
      rfl
    · intro b g f
      dsimp only
      rw [← act_comm, pure_balance])

private theorem outerLeft_pure (G : Bimod C B) (F : Bimod B A) (c : C) (g : G.1)
    (f : F.1) : outerLeft G F c (pure G F g f) = pure G F (left G c g) f :=
  lift_pure G F _ _ _ g f

private def outerRight (G : Bimod C B) (F : Bimod B A) (a : A) :
    AddMonoidHom (underlying G F) (underlying G F) :=
  lift G F (underlying G F) (fun g f => pure G F g (right F a f)) (by
    refine ⟨fun g g' f => pure_add_left G F g g' (right F a f), ?_, ?_⟩
    · intro g f f'
      change pure G F g (rightHom F a (f + f')) = _
      rw [map_add, pure_add_right]
      rfl
    · intro b g f
      dsimp only
      rw [pure_balance, act_comm])

private theorem outerRight_pure (G : Bimod C B) (F : Bimod B A) (a : A) (g : G.1)
    (f : F.1) : outerRight G F a (pure G F g f) = pure G F g (right F a f) :=
  lift_pure G F _ _ _ g f

@[instance_reducible] private def moduleFromMaps {R X : Type*} [Semiring R] [AddCommMonoid X]
    (act : R → AddMonoidHom X X) (one : act 1 = AddMonoidHom.id X)
    (mul : ∀ r s, act (r * s) = (act r).comp (act s))
    (add : ∀ r s, act (r + s) = act r + act s)
    (zero : act 0 = 0) : Module R X where
  smul r x := act r x
  one_smul x := DFunLike.congr_fun one x
  mul_smul r s x := DFunLike.congr_fun (mul r s) x
  smul_zero r := map_zero (act r)
  smul_add r x y := map_add (act r) x y
  add_smul r s x := DFunLike.congr_fun (add r s) x
  zero_smul x := DFunLike.congr_fun zero x

@[instance_reducible] private def leftModule (G : Bimod C B) (F : Bimod B A) : Module C (underlying G F) := by
  letI : Module C G.1 := G.2.1
  refine moduleFromMaps (outerLeft G F) ?_ ?_ ?_ ?_
  · apply tensor_ext
    intro g f
    rw [outerLeft_pure]
    change pure G F ((1 : C) • g) f = pure G F g f
    rw [one_smul]
  · intro r s
    apply tensor_ext
    intro g f
    simp only [AddMonoidHom.comp_apply, outerLeft_pure]
    change pure G F ((r * s) • g) f = pure G F (r • (s • g)) f
    rw [mul_smul]
  · intro r s
    apply tensor_ext
    intro g f
    simp only [AddMonoidHom.add_apply, outerLeft_pure]
    change pure G F ((r + s) • g) f = pure G F (r • g) f + pure G F (s • g) f
    rw [add_smul, pure_add_left]
  · apply tensor_ext
    intro g f
    rw [outerLeft_pure]
    change pureLeft G F f ((0 : C) • g) = 0
    rw [zero_smul, map_zero]

@[instance_reducible] private def rightModule (G : Bimod C B) (F : Bimod B A) :
    Module (MulOpposite A) (underlying G F) := by
  letI : Module (MulOpposite A) F.1 := F.2.2.val
  refine moduleFromMaps (fun r => outerRight G F (MulOpposite.unop r)) ?_ ?_ ?_ ?_
  · apply tensor_ext
    intro g f
    rw [outerRight_pure]
    change pure G F g ((1 : MulOpposite A) • f) = pure G F g f
    rw [one_smul]
  · intro r s
    apply tensor_ext
    intro g f
    simp only [AddMonoidHom.comp_apply, outerRight_pure]
    change pure G F g ((r * s) • f) = pure G F g (r • (s • f))
    rw [mul_smul]
  · intro r s
    apply tensor_ext
    intro g f
    simp only [AddMonoidHom.add_apply, outerRight_pure]
    change pure G F g ((r + s) • f) = pure G F g (r • f) + pure G F g (s • f)
    rw [add_smul, pure_add_right]
  · apply tensor_ext
    intro g f
    rw [outerRight_pure]
    change pureRight G F g ((0 : MulOpposite A) • f) = 0
    rw [zero_smul, map_zero]

private def actions (G : Bimod C B) (F : Bimod B A) : Structure C A (underlying G F) := by
  letI : Module C (underlying G F) := leftModule G F
  letI : Module (MulOpposite A) (underlying G F) := rightModule G F
  refine ⟨leftModule G F, ⟨rightModule G F, ?_⟩⟩
  show SMulCommClass (MulOpposite A) C (underlying G F)
  constructor
  intro a c x
  have commute : (outerRight G F (MulOpposite.unop a)).comp (outerLeft G F c) =
      (outerLeft G F c).comp (outerRight G F (MulOpposite.unop a)) := by
    apply tensor_ext
    intro g f
    simp only [AddMonoidHom.comp_apply, outerLeft_pure, outerRight_pure]
  exact DFunLike.congr_fun commute x

private abbrev tensor (G : Bimod C B) (F : Bimod B A) : Bimod C A :=
  ⟨underlying G F, actions G F⟩

private theorem left_pure (G : Bimod C B) (F : Bimod B A) (c : C) (g : G.1) (f : F.1) :
    left (tensor G F) c (pure G F g f) = pure G F (left G c g) f :=
  outerLeft_pure G F c g f

private theorem right_pure (G : Bimod C B) (F : Bimod B A) (a : A) (g : G.1) (f : F.1) :
    right (tensor G F) a (pure G F g f) = pure G F g (right F a f) :=
  outerRight_pure G F a g f

private theorem hom_ext {G : Bimod C B} {F : Bimod B A} {T : Bimod C A}
    (s t : Hom (tensor G F) T)
    (h : ∀ g f, s.val (pure G F g f) = t.val (pure G F g f)) : s = t :=
  Subtype.ext (tensor_ext s.val t.val h)

private theorem equivariant_of_pure {G : Bimod C B} {F : Bimod B A} {T : Bimod C A}
    (l : AddMonoidHom (tensor G F).1 T.1)
    (hl : ∀ c g f, l (pure G F (left G c g) f) = left T c (l (pure G F g f)))
    (hr : ∀ a g f, l (pure G F g (right F a f)) = right T a (l (pure G F g f))) :
    Equivariant (tensor G F) T l := by
  constructor
  · intro c x
    have eq : l.comp (outerLeft G F c) = (leftHom T c).comp l := by
      apply tensor_ext
      intro g f
      change l (outerLeft G F c (pure G F g f)) = left T c (l (pure G F g f))
      rw [outerLeft_pure]
      exact hl c g f
    exact DFunLike.congr_fun eq x
  · intro a x
    have eq : l.comp (outerRight G F a) = (rightHom T a).comp l := by
      apply tensor_ext
      intro g f
      change l (outerRight G F a (pure G F g f)) = right T a (l (pure G F g f))
      rw [outerRight_pure]
      exact hr a g f
    exact DFunLike.congr_fun eq x

/-- Comparing on pure pairs suffices, including when the target is a group of maps. -/
private theorem tensor_ext_left {X : Type*} [AddCommGroup X]
    {H : Bimod D C} {G : Bimod C B} {F : Bimod B A}
    (s t : AddMonoidHom (tensor (tensor H G) F).1 X)
    (he : ∀ h g f, s (pure (tensor H G) F (pure H G h g) f) =
      t (pure (tensor H G) F (pure H G h g) f)) : s = t := by
  apply tensor_ext
  intro x f
  have eq : s.comp (pureLeft (tensor H G) F f) =
      t.comp (pureLeft (tensor H G) F f) := tensor_ext _ _ (fun h g => he h g f)
  exact DFunLike.congr_fun eq x

private theorem tensor_ext_right {X : Type*} [AddCommGroup X]
    {H : Bimod D C} {G : Bimod C B} {F : Bimod B A}
    (s t : AddMonoidHom (tensor H (tensor G F)).1 X)
    (he : ∀ h g f, s (pure H (tensor G F) h (pure G F g f)) =
      t (pure H (tensor G F) h (pure G F g f))) : s = t := by
  apply tensor_ext
  intro h x
  have eq : s.comp (pureRight H (tensor G F) h) =
      t.comp (pureRight H (tensor G F) h) := tensor_ext _ _ (he h)
  exact DFunLike.congr_fun eq x

/- Portal step 1.3 (F1, F4). Construct the map from the balanced pairing
   and check both functor laws by evaluating on elementary tensors. -/
private def mapAdd {G G' : Bimod C B} {F F' : Bimod B A}
    (g : Hom G G') (f : Hom F F') : AddMonoidHom (tensor G F).1 (tensor G' F').1 :=
  lift G F (underlying G' F') (fun x y => pure G' F' (g.val x) (f.val y)) (by
    refine ⟨?_, ?_, ?_⟩
    · intro x x' y
      dsimp only
      rw [map_add, pure_add_left]
    · intro x y y'
      dsimp only
      rw [map_add, pure_add_right]
    · intro b x y
      dsimp only
      rw [g.property.2, f.property.1, pure_balance])

private theorem mapAdd_pure {G G' : Bimod C B} {F F' : Bimod B A}
    (g : Hom G G') (f : Hom F F') (x : G.1) (y : F.1) :
    mapAdd g f (pure G F x y) = pure G' F' (g.val x) (f.val y) :=
  lift_pure G F _ _ _ x y

private def tensorMap {G G' : Bimod C B} {F F' : Bimod B A}
    (g : Hom G G') (f : Hom F F') : Hom (tensor G F) (tensor G' F') :=
  ⟨mapAdd g f, equivariant_of_pure (mapAdd g f)
    (fun c x y => by rw [mapAdd_pure, mapAdd_pure, left_pure, g.property.1])
    (fun a x y => by rw [mapAdd_pure, mapAdd_pure, right_pure, f.property.2])⟩

private theorem tensorMap_pure {G G' : Bimod C B} {F F' : Bimod B A}
    (g : Hom G G') (f : Hom F F') (x : G.1) (y : F.1) :
    (tensorMap g f).val (pure G F x y) = pure G' F' (g.val x) (f.val y) :=
  mapAdd_pure g f x y

private theorem tensorMap_id (G : Bimod C B) (F : Bimod B A) :
    tensorMap (idMap G) (idMap F) = idMap (tensor G F) := by
  apply hom_ext
  intro g f
  rw [tensorMap_pure]
  rfl

private theorem tensorMap_comp {G G' G'' : Bimod C B} {F F' F'' : Bimod B A}
    (g : Hom G G') (g' : Hom G' G'') (f : Hom F F') (f' : Hom F' F'') :
    tensorMap (comp g' g) (comp f' f) = comp (tensorMap g' f') (tensorMap g f) := by
  apply hom_ext
  intro x y
  rw [comp_apply (tensorMap g' f') (tensorMap g f), tensorMap_pure (comp g' g),
    tensorMap_pure g f x y, tensorMap_pure g' f']
  rfl

/- Portal step 1.1 (F1, F2). BalancedTensorAssociativity guides the
   successive lifts. Its Finsupp quotient differs from the reviewed
   quotient, and its axiom audit includes Classical.choice. Each inverse
   is constructed here by lifting in the opposite order. -/
private def assocInner (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) (f : F.1) :
    AddMonoidHom (tensor H G).1 (tensor H (tensor G F)).1 :=
  lift H G (underlying H (tensor G F))
    (fun h g => pure H (tensor G F) h (pure G F g f)) (by
      refine ⟨?_, ?_, ?_⟩
      · intro h h' g
        dsimp only
        rw [pure_add_left]
      · intro h g g'
        dsimp only
        rw [pure_add_left, pure_add_right]
      · intro c h g
        dsimp only
        rw [pure_balance, left_pure])

private theorem assocInner_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    assocInner H G F f (pure H G h g) = pure H (tensor G F) h (pure G F g f) :=
  lift_pure H G _ _ _ h g

private def assocForward (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) :
    AddMonoidHom (tensor (tensor H G) F).1 (tensor H (tensor G F)).1 :=
  lift (tensor H G) F (underlying H (tensor G F))
    (fun x f => assocInner H G F f x) (by
      refine ⟨fun x y f => map_add (assocInner H G F f) x y, ?_, ?_⟩
      · intro x f f'
        have eq : assocInner H G F (f + f') = assocInner H G F f + assocInner H G F f' := by
          apply tensor_ext
          intro h g
          simp only [AddMonoidHom.add_apply]
          rw [assocInner_pure H G F, assocInner_pure H G F, assocInner_pure H G F,
            pure_add_right, pure_add_right]
        exact DFunLike.congr_fun eq x
      · intro b x f
        have eq : (assocInner H G F f).comp (outerRight H G b) =
            assocInner H G F (left F b f) := by
          apply tensor_ext
          intro h g
          rw [AddMonoidHom.comp_apply, outerRight_pure, assocInner_pure H G F,
            assocInner_pure H G F, pure_balance]
        exact DFunLike.congr_fun eq x)

private theorem assocForward_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    assocForward H G F (pure (tensor H G) F (pure H G h g) f) =
      pure H (tensor G F) h (pure G F g f) :=
  (lift_pure (tensor H G) F _ _ _ (pure H G h g) f).trans (assocInner_pure H G F h g f)

private def assocInvInner (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) (h : H.1) :
    AddMonoidHom (tensor G F).1 (tensor (tensor H G) F).1 :=
  lift G F (underlying (tensor H G) F)
    (fun g f => pure (tensor H G) F (pure H G h g) f) (by
      refine ⟨?_, ?_, ?_⟩
      · intro g g' f
        dsimp only
        rw [pure_add_right, pure_add_left]
      · intro g f f'
        dsimp only
        rw [pure_add_right]
      · intro b g f
        dsimp only
        rw [← right_pure H G b, pure_balance])

private theorem assocInvInner_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    assocInvInner H G F h (pure G F g f) = pure (tensor H G) F (pure H G h g) f :=
  lift_pure G F _ _ _ g f

private def assocInverse (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) :
    AddMonoidHom (tensor H (tensor G F)).1 (tensor (tensor H G) F).1 :=
  lift H (tensor G F) (underlying (tensor H G) F)
    (fun h x => assocInvInner H G F h x) (by
      refine ⟨?_, fun h x y => map_add (assocInvInner H G F h) x y, ?_⟩
      · intro h h' x
        have eq : assocInvInner H G F (h + h') = assocInvInner H G F h + assocInvInner H G F h' := by
          apply tensor_ext
          intro g f
          simp only [AddMonoidHom.add_apply]
          rw [assocInvInner_pure H G F, assocInvInner_pure H G F, assocInvInner_pure H G F,
            pure_add_left, pure_add_left]
        exact DFunLike.congr_fun eq x
      · intro c h x
        have eq : assocInvInner H G F (right H c h) =
            (assocInvInner H G F h).comp (outerLeft G F c) := by
          apply tensor_ext
          intro g f
          rw [AddMonoidHom.comp_apply, outerLeft_pure, assocInvInner_pure H G F,
            assocInvInner_pure H G F, pure_balance]
        exact DFunLike.congr_fun eq x)

private theorem assocInverse_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    assocInverse H G F (pure H (tensor G F) h (pure G F g f)) =
      pure (tensor H G) F (pure H G h g) f :=
  (lift_pure H (tensor G F) _ _ _ h (pure G F g f)).trans (assocInvInner_pure H G F h g f)

private def assoc (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) :
    Iso (tensor (tensor H G) F) (tensor H (tensor G F)) := by
  let fw := assocForward H G F
  let bw := assocInverse H G F
  have bwfw : bw.comp fw = AddMonoidHom.id _ :=
    tensor_ext_left _ _ (fun h g f => by
      simp only [bw, fw, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      rw [assocForward_pure H G F, assocInverse_pure H G F])
  have fwbw : fw.comp bw = AddMonoidHom.id _ :=
    tensor_ext_right _ _ (fun h g f => by
      simp only [bw, fw, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      rw [assocInverse_pure H G F, assocForward_pure H G F])
  let e : AddEquiv (tensor (tensor H G) F).1 (tensor H (tensor G F)).1 :=
    { fw with
      invFun := bw
      left_inv := DFunLike.congr_fun bwfw
      right_inv := DFunLike.congr_fun fwbw }
  refine ⟨e, ⟨?_, ?_⟩⟩
  · intro d x
    have eq : fw.comp (outerLeft (tensor H G) F d) =
        (outerLeft H (tensor G F) d).comp fw := by
      apply tensor_ext_left
      intro h g f
      simp only [fw, AddMonoidHom.comp_apply, outerLeft_pure, left_pure]
      rw [assocForward_pure H G F, assocForward_pure H G F, outerLeft_pure]
    exact DFunLike.congr_fun eq x
  · intro a x
    have eq : fw.comp (outerRight (tensor H G) F a) =
        (outerRight H (tensor G F) a).comp fw := by
      apply tensor_ext_left
      intro h g f
      simp only [fw, AddMonoidHom.comp_apply, outerRight_pure]
      rw [assocForward_pure H G F, assocForward_pure H G F, outerRight_pure, right_pure]
    exact DFunLike.congr_fun eq x

private theorem assoc_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    (assoc H G F).val (pure (tensor H G) F (pure H G h g) f) =
      pure H (tensor G F) h (pure G F g f) :=
  assocForward_pure H G F h g f

/- Portal step 1.2 (F1, F3). The regular actions from Bimodule verify the
   balancing equations. The inverses are the additive maps inserting 1. -/
private noncomputable def leftUnitAdd (F : Bimod B A) : AddMonoidHom (tensor (regular B) F).1 F.1 := by
  letI : Module B F.1 := F.2.1
  refine lift (regular B) F F.1 (fun b f => left F b f) ?_
  refine ⟨fun b b' f => add_smul b b' f, fun b f f' => smul_add b f f', ?_⟩
  intro r b f
  dsimp only
  rw [regular_right]
  exact mul_smul b r f

private theorem leftUnitAdd_pure (F : Bimod B A) (b : B) (f : F.1) :
    leftUnitAdd F (pure (regular B) F b f) = left F b f :=
  lift_pure (regular B) F _ _ _ b f

private noncomputable def leftUnitor (F : Bimod B A) : Iso (tensor (regular B) F) F := by
  letI : Module B F.1 := F.2.1
  let fw := leftUnitAdd F
  let bw := pureRight (regular B) F 1
  have bwfw : bw.comp fw = AddMonoidHom.id _ := by
    apply tensor_ext (G := regular B) (F := F)
    intro b f
    change pure (regular B) F 1 (leftUnitAdd F (pure (regular B) F b f)) =
      pure (regular B) F b f
    rw [leftUnitAdd_pure F, ← pure_balance (regular B) F b, regular_right, one_mul]
  let e : AddEquiv (tensor (regular B) F).1 F.1 :=
    { fw with
      invFun := bw
      left_inv := DFunLike.congr_fun bwfw
      right_inv := fun f =>
        (leftUnitAdd_pure F 1 f).trans (one_smul B f) }
  refine ⟨e, equivariant_of_pure (G := regular B) (F := F) (T := F) fw ?_ ?_⟩
  · intro r b f
    change leftUnitAdd F (pure (regular B) F (left (regular B) r b) f) =
      left F r (leftUnitAdd F (pure (regular B) F b f))
    rw [leftUnitAdd_pure F, leftUnitAdd_pure F, regular_left]
    exact mul_smul r b f
  · intro a b f
    change leftUnitAdd F (pure (regular B) F b (right F a f)) =
      right F a (leftUnitAdd F (pure (regular B) F b f))
    rw [leftUnitAdd_pure F, leftUnitAdd_pure F]
    exact (act_comm F b a f).symm

private theorem leftUnitor_pure (F : Bimod B A) (b : B) (f : F.1) :
    (leftUnitor F).val (pure (regular B) F b f) = left F b f :=
  leftUnitAdd_pure F b f

private noncomputable def rightUnitAdd (F : Bimod B A) : AddMonoidHom (tensor F (regular A)).1 F.1 := by
  letI : Module (MulOpposite A) F.1 := F.2.2.val
  refine lift F (regular A) F.1 (fun f a => right F a f) ?_
  refine ⟨fun f f' a => smul_add (MulOpposite.op a) f f',
    fun f a a' => add_smul (MulOpposite.op a) (MulOpposite.op a') f, ?_⟩
  intro r f a
  dsimp only
  rw [regular_left]
  exact (mul_smul (MulOpposite.op a) (MulOpposite.op r) f).symm

private theorem rightUnitAdd_pure (F : Bimod B A) (f : F.1) (a : A) :
    rightUnitAdd F (pure F (regular A) f a) = right F a f :=
  lift_pure F (regular A) _ _ _ f a

private noncomputable def rightUnitor (F : Bimod B A) : Iso (tensor F (regular A)) F := by
  letI : Module (MulOpposite A) F.1 := F.2.2.val
  let fw := rightUnitAdd F
  let bw := pureLeft F (regular A) 1
  have bwfw : bw.comp fw = AddMonoidHom.id _ := by
    apply tensor_ext (G := F) (F := regular A)
    intro f a
    change pure F (regular A) (rightUnitAdd F (pure F (regular A) f a)) 1 =
      pure F (regular A) f a
    rw [rightUnitAdd_pure F, pure_balance F (regular A) a, regular_left, mul_one]
  let e : AddEquiv (tensor F (regular A)).1 F.1 :=
    { fw with
      invFun := bw
      left_inv := DFunLike.congr_fun bwfw
      right_inv := fun f =>
        (rightUnitAdd_pure F f 1).trans (one_smul (MulOpposite A) f) }
  refine ⟨e, equivariant_of_pure (G := F) (F := regular A) (T := F) fw ?_ ?_⟩
  · intro b f a
    change rightUnitAdd F (pure F (regular A) (left F b f) a) =
      left F b (rightUnitAdd F (pure F (regular A) f a))
    rw [rightUnitAdd_pure F, rightUnitAdd_pure F]
    exact act_comm F b a f
  · intro r f a
    change rightUnitAdd F (pure F (regular A) f (right (regular A) r a)) =
      right F r (rightUnitAdd F (pure F (regular A) f a))
    rw [rightUnitAdd_pure F, rightUnitAdd_pure F, regular_right]
    exact mul_smul (MulOpposite.op r) (MulOpposite.op a) f

private theorem rightUnitor_pure (F : Bimod B A) (f : F.1) (a : A) :
    (rightUnitor F).val (pure F (regular A) f a) = right F a f :=
  rightUnitAdd_pure F f a

private theorem assocHom_pure (H : Bimod D C) (G : Bimod C B) (F : Bimod B A)
    (h : H.1) (g : G.1) (f : F.1) :
    (isoHom (assoc H G F)).val (pure (tensor H G) F (pure H G h g) f) =
      pure H (tensor G F) h (pure G F g f) :=
  assoc_pure H G F h g f

private theorem leftUnitorHom_pure (F : Bimod B A) (b : B) (f : F.1) :
    (isoHom (leftUnitor F)).val (pure (regular B) F b f) = left F b f :=
  leftUnitor_pure F b f

private theorem rightUnitorHom_pure (F : Bimod B A) (f : F.1) (a : A) :
    (isoHom (rightUnitor F)).val (pure F (regular A) f a) = right F a f :=
  rightUnitor_pure F f a

/- The naturality parts of steps 1.1 and 1.2 follow by comparing the
   composites on pure tensors. -/
private theorem assoc_natural {H H' : Bimod D C} {G G' : Bimod C B} {F F' : Bimod B A}
    (h : Hom H H') (g : Hom G G') (f : Hom F F') :
    comp (isoHom (assoc H' G' F')) (tensorMap (tensorMap h g) f) =
      comp (tensorMap h (tensorMap g f)) (isoHom (assoc H G F)) := by
  apply Subtype.ext
  apply tensor_ext_left
  intro x y z
  rw [comp_apply (isoHom (assoc H' G' F')), comp_apply (tensorMap h (tensorMap g f)),
    tensorMap_pure (tensorMap h g) f, tensorMap_pure h g,
    assocHom_pure H' G' F', assocHom_pure H G F,
    tensorMap_pure h (tensorMap g f), tensorMap_pure g f]

private theorem leftUnitor_natural {F F' : Bimod B A} (f : Hom F F') :
    comp (isoHom (leftUnitor F')) (tensorMap (idMap (regular B)) f) =
      comp f (isoHom (leftUnitor F)) := by
  apply hom_ext (G := regular B) (F := F)
  intro b x
  rw [comp_apply (isoHom (leftUnitor F')), comp_apply f,
    tensorMap_pure (idMap (regular B)) f, leftUnitorHom_pure F', leftUnitorHom_pure F,
    f.property.1]
  rfl

private theorem rightUnitor_natural {F F' : Bimod B A} (f : Hom F F') :
    comp (isoHom (rightUnitor F')) (tensorMap f (idMap (regular A))) =
      comp f (isoHom (rightUnitor F)) := by
  apply hom_ext (G := F) (F := regular A)
  intro x a
  rw [comp_apply (isoHom (rightUnitor F')), comp_apply f,
    tensorMap_pure f (idMap (regular A)), rightUnitorHom_pure F', rightUnitorHom_pure F,
    f.property.2]
  rfl

/- Portal step 2.1. Extend equality from the four-fold pure tensors,
   first through the two outer tensor factors, then through K tensor H. -/
private theorem pentagon (K : Bimod E D) (H : Bimod D C) (G : Bimod C B) (F : Bimod B A) :
    comp (isoHom (assoc K H (tensor G F))) (isoHom (assoc (tensor K H) G F)) =
      comp (tensorMap (idMap K) (isoHom (assoc H G F)))
        (comp (isoHom (assoc K (tensor H G) F))
          (tensorMap (isoHom (assoc K H G)) (idMap F))) := by
  let lhs := comp (isoHom (assoc K H (tensor G F))) (isoHom (assoc (tensor K H) G F))
  let rhs := comp (tensorMap (idMap K) (isoHom (assoc H G F)))
    (comp (isoHom (assoc K (tensor H G) F))
      (tensorMap (isoHom (assoc K H G)) (idMap F)))
  change lhs = rhs
  apply Subtype.ext
  apply tensor_ext_left (H := tensor K H) (G := G) (F := F)
  intro t g f
  let ins := (pureLeft (tensor (tensor K H) G) F f).comp (pureLeft (tensor K H) G g)
  have he : lhs.val.comp ins = rhs.val.comp ins := by
    apply tensor_ext (G := K) (F := H)
    intro k h
    let x := pure (tensor (tensor K H) G) F (pure (tensor K H) G (pure K H k h) g) f
    change lhs.val x = rhs.val x
    dsimp only [lhs, rhs, x]
    rw [comp_apply (isoHom (assoc K H (tensor G F))),
      comp_apply (tensorMap (idMap K) (isoHom (assoc H G F))),
      comp_apply (isoHom (assoc K (tensor H G) F)),
      assocHom_pure (tensor K H) G F, assocHom_pure K H (tensor G F),
      tensorMap_pure (isoHom (assoc K H G)) (idMap F), assocHom_pure K H G]
    change pure K (tensor H (tensor G F)) k (pure H (tensor G F) h (pure G F g f)) =
      (tensorMap (idMap K) (isoHom (assoc H G F))).val
        ((isoHom (assoc K (tensor H G) F)).val
          (pure (tensor K (tensor H G)) F (pure K (tensor H G) k (pure H G h g)) f))
    rw [assocHom_pure K (tensor H G) F,
      tensorMap_pure (idMap K) (isoHom (assoc H G F)), assocHom_pure H G F]
    rfl
  exact DFunLike.congr_fun he t

/- Portal step 2.2. The pure-triple images coincide by the middle-ring
   balancing relation. -/
private theorem triangle (G : Bimod C B) (F : Bimod B A) :
    comp (tensorMap (idMap G) (isoHom (leftUnitor F))) (isoHom (assoc G (regular B) F)) =
      tensorMap (isoHom (rightUnitor G)) (idMap F) := by
  apply Subtype.ext
  apply tensor_ext_left (H := G) (G := regular B) (F := F)
  intro g b f
  rw [comp_apply (tensorMap (idMap G) (isoHom (leftUnitor F))),
    assocHom_pure G (regular B) F,
    tensorMap_pure (idMap G) (isoHom (leftUnitor F)),
    tensorMap_pure (isoHom (rightUnitor G)) (idMap F),
    leftUnitorHom_pure F, rightUnitorHom_pure G]
  exact (pure_balance G F b g f).symm

end MoritaCoherence
theorem BimoduleTensorBicategoryCoherence : (
  let BimodStructure := fun (B A : RingCat.{u}) (M : AddCommGrpCat.{u}) =>
    Bimodule.{u,u,u}.1 B A M
  let Bimod := fun (B A : RingCat.{u}) => Sigma (BimodStructure B A)
  let sum := fun (T : AddCommGrpCat.{u}) (xs : List T) => List.sum xs
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
  let relation := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A)
      (x y : FreeAddGroup (Prod G.1 F.1)) =>
    let gen := fun (g : G.1) (f : F.1) => FreeAddGroup.of (g, f)
    (∃ p q : FreeAddGroup (Prod G.1 F.1), x = p + q ∧ y = q + p) ∨
    (∃ (g g' : G.1) (f : F.1), x = gen (g + g') f ∧ y = gen g f + gen g' f) ∨
    (∃ (g : G.1) (f f' : F.1), x = gen g (f + f') ∧ y = gen g f + gen g f') ∨
    (∃ (b : B) (g : G.1) (f : F.1), x = gen (right G b g) f ∧ y = gen g (left F b f))
  let congruence := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) =>
    addConGen (relation G F)
  let underlying := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) =>
    let c := congruence G F
    letI : AddCommGroup c.Quotient :=
      { AddCon.addGroup c with
        add_comm := fun x y => Quotient.inductionOn₂ x y fun p q =>
          Quotient.sound (s := c.toSetoid) (AddConGen.Rel.of _ _ (Or.inl ⟨p, q, rfl, rfl⟩)) }
    AddCommGrpCat.of c.Quotient
  let pure := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) (g : G.1) (f : F.1) =>
    (Quotient.mk (congruence G F).toSetoid (FreeAddGroup.of (g, f)) : underlying G F)
  ∃ (actions : ∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
        BimodStructure C A (underlying G F)),
    let tensor := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) =>
      (⟨underlying G F, actions G F⟩ : Bimod C A)
    let tmul := fun {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) =>
      (pure G F : G.1 → F.1 → (tensor G F).1)
    (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A),
      IsBalanced G F (tensor G F).1 (tmul G F) ∧
      ∀ (T : AddCommGrpCat.{u}) (b : G.1 → F.1 → T), IsBalanced G F T b →
        ∃! lift : AddMonoidHom (tensor G F).1 T, ∀ g f, lift (tmul G F g f) = b g f) ∧
    (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) (g : G.1) (f : F.1),
      (∀ c : C, left (tensor G F) c (tmul G F g f) = tmul G F (left G c g) f) ∧
      (∀ a : A, right (tensor G F) a (tmul G F g f) = tmul G F g (right F a f))) ∧
    ∃ (tensorMap : ∀ {C B A : RingCat.{u}} {G G' : Bimod C B} {F F' : Bimod B A},
        Hom G G' → Hom F F' → Hom (tensor G F) (tensor G' F'))
      (assoc : ∀ {D C B A : RingCat.{u}} (H : Bimod D C) (G : Bimod C B) (F : Bimod B A),
          Iso (tensor (tensor H G) F) (tensor H (tensor G F)))
      (leftUnitor : ∀ {B A : RingCat.{u}} (F : Bimod B A), Iso (tensor (regular B) F) F)
      (rightUnitor : ∀ {B A : RingCat.{u}} (F : Bimod B A), Iso (tensor F (regular A)) F),
      (∀ {C B A : RingCat.{u}} (G : Bimod C B) (F : Bimod B A) (x : (tensor G F).1),
        ∃ terms : List (Prod G.1 F.1),
          x = sum (tensor G F).1 (List.map (fun p => tmul G F p.1 p.2) terms)) ∧
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
) := (
by
  -- Portal step 3.1. The witnesses use the reviewed quotient and the given
  -- bimodule structure. Each equality uses the maps constructed above.
  refine ⟨(fun {_ _ _} G F => MoritaCoherence.actions G F), ?_, ?_,
    (fun {_ _ _ _ _ _ _} g f => MoritaCoherence.tensorMap g f),
    (fun {_ _ _ _} H G F => MoritaCoherence.assoc H G F),
    (fun {_ _} F => MoritaCoherence.leftUnitor F),
    (fun {_ _} F => MoritaCoherence.rightUnitor F),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C B A G F
    exact ⟨MoritaCoherence.pure_balanced G F, MoritaCoherence.lift_unique G F⟩
  · intro C B A G F g f
    exact ⟨fun c => MoritaCoherence.left_pure G F c g f,
      fun a => MoritaCoherence.right_pure G F a g f⟩
  · intro C B A G F x
    exact MoritaCoherence.finite_sum G F x
  · intro C B A G G' F F' g f x y
    exact MoritaCoherence.tensorMap_pure g f x y
  · intro C B A G F
    exact MoritaCoherence.tensorMap_id G F
  · intro C B A G G' G'' F F' F'' g g' f f'
    exact MoritaCoherence.tensorMap_comp g g' f f'
  · intro D C B A H G F h g f
    exact MoritaCoherence.assoc_pure H G F h g f
  · intro B A F b a f
    exact ⟨MoritaCoherence.leftUnitor_pure F b f, MoritaCoherence.rightUnitor_pure F f a⟩
  · intro D C B A H H' G G' F F' h g f
    exact MoritaCoherence.assoc_natural h g f
  · intro B A F F' f
    exact ⟨MoritaCoherence.leftUnitor_natural f, MoritaCoherence.rightUnitor_natural f⟩
  · intro E D C B A K H G F
    exact MoritaCoherence.pentagon K H G F
  · intro C B A G F
    exact MoritaCoherence.triangle G F

)
#print axioms BimoduleTensorBicategoryCoherence
#print axioms MoritaCoherence.actions
#print axioms MoritaCoherence.lift
#print axioms MoritaCoherence.tensorMap
#print axioms MoritaCoherence.assoc
#print axioms MoritaCoherence.leftUnitor
#print axioms MoritaCoherence.rightUnitor
#print axioms MoritaCoherence.pentagon
#print axioms MoritaCoherence.triangle
