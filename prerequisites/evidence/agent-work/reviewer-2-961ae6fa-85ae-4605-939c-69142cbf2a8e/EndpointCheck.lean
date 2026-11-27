import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.Algebra.Module.Opposite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finsupp.Basic

universe t s r c b m

def ReviewedEndpoint : Prop :=
  ∀ (T : Type t) (S : Type s) (R : Type r) [Ring T] [Ring S] [Ring R],
    let TS := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite S)) (ModuleCat.{c} T)
    let SR := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
    let starS := CategoryTheory.SingleObj.star (MulOpposite S)
    let starR := CategoryTheory.SingleObj.star (MulOpposite R)
    let carrierC := fun (C : TS) => C.obj.obj starS
    let carrierB := fun (B : SR) => B.obj.obj starR
    let rightC := fun (C : TS) (s : S) (c : carrierC C) =>
      (C.obj.map (show Quiver.Hom starS starS from MulOpposite.op s)) c
    let rightB := fun (B : SR) (r : R) (b : carrierB B) =>
      (B.obj.map (show Quiver.Hom starR starR from MulOpposite.op r)) b
    let CB := fun (C : TS) (B : SR) =>
      let X := carrierC C
      let Y := carrierB B
      let F := Finsupp (Prod X Y) Int
      let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
      let K : AddSubgroup F := AddSubgroup.closure
        { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
              (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
              (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
      (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
        Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
    let BM := fun (B : SR) (M : ModuleCat.{m} R) =>
      let X := carrierB B
      let Y := M
      let F := Finsupp (Prod X Y) Int
      let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
      let K : AddSubgroup F := AddSubgroup.closure
        { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
              (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
              (∃ (a : R) (x : X) (y : Y), z = gen (rightB B a x) y - gen x (a • y)) }
      (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
        Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
    let CBType := fun (C : TS) (B : SR) =>
      HasQuotient.Quotient (Finsupp (Prod (carrierC C) (carrierB B)) Int) (CB C B).1
    let BMType := fun (B : SR) (M : ModuleCat.{m} R) =>
      HasQuotient.Quotient (Finsupp (Prod (carrierB B) M) Int) (BM B M).1
    let Left := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
        (rightCB : Module (MulOpposite R) (CBType C B)) =>
      let X := CBType C B
      let Y := M
      let F := Finsupp (Prod X Y) Int
      let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
      let K : AddSubgroup F := AddSubgroup.closure
        { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
              (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
              (∃ (a : R) (x : X) (y : Y), z = gen (rightCB.smul (MulOpposite.op a) x) y - gen x (a • y)) }
      (⟨K, fun c b m => QuotientAddGroup.mk' K (gen ((CB C B).2 c b) m)⟩ :
        Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
    let Right := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
        (leftBM : Module S (BMType B M)) =>
      letI := leftBM
      let X := carrierC C
      let Y := BMType B M
      let F := Finsupp (Prod X Y) Int
      let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
      let K : AddSubgroup F := AddSubgroup.closure
        { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
              (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
              (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
      (⟨K, fun c b m => QuotientAddGroup.mk' K (gen c ((BM B M).2 b m))⟩ :
        Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
    ∃ (leftCB : ∀ C B, Module T (CBType C B))
      (rightCB : ∀ C B, Module (MulOpposite R) (CBType C B))
      (leftBM : ∀ B (M : ModuleCat.{m} R), Module S (BMType B M)),
      (∀ (C : TS) (B : SR),
        (letI := leftCB C B
         letI := rightCB C B
         SMulCommClass (MulOpposite R) T (CBType C B)) ∧
        (∀ (t : T) (c : carrierC C) (b : carrierB B),
          (leftCB C B).smul t ((CB C B).2 c b) = (CB C B).2 (t • c) b) ∧
        (∀ (r : R) (c : carrierC C) (b : carrierB B),
          (rightCB C B).smul (MulOpposite.op r) ((CB C B).2 c b) = (CB C B).2 c (rightB B r b))) ∧
      (∀ (B : SR) (M : ModuleCat.{m} R) (s : S) (b : carrierB B) (m : M),
        (leftBM B M).smul s ((BM B M).2 b m) = (BM B M).2 (s • b) m) ∧
      (let L := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
         HasQuotient.Quotient (Finsupp (Prod (CBType C B) M) Int) (Left C B M (rightCB C B)).1
       let U := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
         HasQuotient.Quotient (Finsupp (Prod (carrierC C) (BMType B M)) Int) (Right C B M (leftBM B M)).1
       let pureL := fun C B M => (Left C B M (rightCB C B)).2
       let pureU := fun C B M => (Right C B M (leftBM B M)).2
       ∃ (actL : ∀ C B M, Module T (L C B M))
         (actU : ∀ C B M, Module T (U C B M))
         (α : ∀ C B M,
           letI := actL C B M
           letI := actU C B M
           LinearEquiv (RingHom.id T) (L C B M) (U C B M)),
         (∀ (C : TS) (B : SR) (M : ModuleCat.{m} R)
             (c : carrierC C) (b : carrierB B) (m : M),
           α C B M (pureL C B M c b m) = pureU C B M c b m ∧
           ∀ t : T,
             (actL C B M).smul t (pureL C B M c b m) = pureL C B M (t • c) b m ∧
             (actU C B M).smul t (pureU C B M c b m) = pureU C B M (t • c) b m) ∧
         (∀ {C C' : TS} {B B' : SR} {M M' : ModuleCat.{m} R}
             (f : Quiver.Hom C C') (g : Quiver.Hom B B') (h : Quiver.Hom M M'),
           letI := actL C B M
           letI := actL C' B' M'
           letI := actU C B M
           letI := actU C' B' M'
           ∃ (l : LinearMap (RingHom.id T) (L C B M) (L C' B' M'))
             (u : LinearMap (RingHom.id T) (U C B M) (U C' B' M')),
             (∀ (c : carrierC C) (b : carrierB B) (m : M),
               l (pureL C B M c b m) =
                 pureL C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m) ∧
               u (pureU C B M c b m) =
                 pureU C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m)) ∧
             (∀ q : L C B M, α C' B' M' (l q) = u (α C B M q))))

#check ReviewedEndpoint
