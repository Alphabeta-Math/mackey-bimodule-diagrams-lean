import MackeyDiagrams.Linear

/-! Reparenthesizing a word preserves its basis with its actions. -/

namespace MackeyDiagrams.Biset

universe u v
noncomputable section
variable {K H J F : Type u} [Group K] [Group H] [Group J] [Group F]
variable (X : Biset K H) (Y : Biset H J) (Z : Biset J F)

@[simp] theorem act_pair (g : K × J) (x : X.carrier) (y : Y.carrier) :
    (X.tensor Y).act g (X.pair Y x y) =
      X.pair Y (X.act (g.1,1) x) (Y.act (1,g.2) y) := rfl

theorem pair_orbit (h : H) (x : X.carrier) (y : Y.carrier) :
    X.pair Y (X.act (1,h) x) (Y.act (h,1) y) = X.pair Y x y :=
  (Quotient.sound (s := X.balance Y) (a := (x,y))
    (b := (X.act (1,h) x, Y.act (h,1) y)) ⟨h, rfl, rfl⟩).symm

private def associateOnLeft (w : (X.tensor Y).carrier) (z : Z.carrier) :
    (X.tensor (Y.tensor Z)).carrier :=
  Quotient.liftOn w (fun xy => X.pair (Y.tensor Z) xy.1 (Y.pair Z xy.2 z)) (by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hxy
    rw [← hx, ← hy]
    have hZ : Z.act (1,1) z = z := Z.one_act z
    have heq := pair_orbit X (Y.tensor Z) h x.1 (Y.pair Z x.2 z)
    rw [act_pair, hZ] at heq
    exact heq.symm)

def associateBasis : ((X.tensor Y).tensor Z).carrier → (X.tensor (Y.tensor Z)).carrier :=
  Quotient.lift (fun z => associateOnLeft X Y Z z.1 z.2) (by
    intro a b hab
    obtain ⟨j, ha, hb⟩ := hab
    rw [← ha, ← hb]
    rcases a with ⟨w,z⟩
    refine Quotient.inductionOn w (fun xy => ?_)
    change X.pair (Y.tensor Z) xy.1 (Y.pair Z xy.2 z) =
      X.pair (Y.tensor Z) (X.act (1,1) xy.1) (Y.pair Z (Y.act (1,j) xy.2) (Z.act (j,1) z))
    have hX : X.act (1,1) xy.1 = xy.1 := X.one_act xy.1
    rw [hX, pair_orbit Y Z])

private def unassociateOnRight (x : X.carrier) (w : (Y.tensor Z).carrier) :
    ((X.tensor Y).tensor Z).carrier :=
  Quotient.liftOn w (fun yz => (X.tensor Y).pair Z (X.pair Y x yz.1) yz.2) (by
    intro a b hab
    obtain ⟨j, ha, hb⟩ := hab
    rw [← ha, ← hb]
    have hX : X.act (1,1) x = x := X.one_act x
    have heq := pair_orbit (X.tensor Y) Z j (X.pair Y x a.1) a.2
    rw [act_pair, hX] at heq
    exact heq.symm)

def unassociateBasis : (X.tensor (Y.tensor Z)).carrier → ((X.tensor Y).tensor Z).carrier :=
  Quotient.lift (fun w => unassociateOnRight X Y Z w.1 w.2) (by
    intro a b hab
    obtain ⟨h, ha, hb⟩ := hab
    rw [← ha, ← hb]
    rcases a with ⟨x,w⟩
    refine Quotient.inductionOn w (fun yz => ?_)
    change (X.tensor Y).pair Z (X.pair Y x yz.1) yz.2 =
      (X.tensor Y).pair Z (X.pair Y (X.act (1,h) x) (Y.act (h,1) yz.1)) (Z.act (1,1) yz.2)
    have hZ : Z.act (1,1) yz.2 = yz.2 := Z.one_act yz.2
    rw [hZ, pair_orbit X Y])

def associateBasisEquiv : ((X.tensor Y).tensor Z).carrier ≃ (X.tensor (Y.tensor Z)).carrier where
  toFun := associateBasis X Y Z
  invFun := unassociateBasis X Y Z
  left_inv w := by
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl)
  right_inv w := by
    refine Quotient.inductionOn w (fun ⟨x,yz⟩ => ?_)
    exact Quotient.inductionOn yz (fun _ => rfl)

variable (R : Type v) [CommSemiring R]

def associate : Hom R ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z)) :=
  Hom.ofFunction (associateBasis X Y Z) (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl))

def unassociate : Hom R (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z) :=
  Hom.ofFunction (unassociateBasis X Y Z) (by
    intro g w
    refine Quotient.inductionOn w (fun ⟨x,yz⟩ => ?_)
    exact Quotient.inductionOn yz (fun _ => rfl))

end
end MackeyDiagrams.Biset

