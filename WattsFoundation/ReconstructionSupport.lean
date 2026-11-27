import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.RingTheory.Finiteness.Basic

universe u v
open CategoryTheory
open scoped BigOperators

namespace ReconstructionCheck

variable {C : Type u} [Category.{v} C] [Preadditive C]

def IsKernel {X Y K : C} (f : X ⟶ Y) (ι : K ⟶ X) : Prop :=
  ι ≫ f = 0 ∧ ∀ (T : C) (g : T ⟶ X), g ≫ f = 0 →
    ∃! h : T ⟶ K, h ≫ ι = g

def IsCokernel {X Y Q : C} (f : X ⟶ Y) (π : Y ⟶ Q) : Prop :=
  f ≫ π = 0 ∧ ∀ (T : C) (g : Y ⟶ T), f ≫ g = 0 →
    ∃! h : Q ⟶ T, π ≫ h = g

abbrev HGroup (P X : C) : AddCommGrpCat.{v} := AddCommGrpCat.of (P ⟶ X)

def HGroupMap (P : C) {X Y : C} (f : X ⟶ Y) : HGroup P X ⟶ HGroup P Y :=
  AddCommGrpCat.ofHom ((preadditiveCoyonedaObj P).map f).hom.toAddMonoidHom

theorem epi_of_cokernel {X Y Q : C} {f : X ⟶ Y} {π : Y ⟶ Q}
    (h : IsCokernel f π) : Epi π := by
  constructor
  intro T a b hab
  obtain ⟨k, _, uniq⟩ := h.2 T (π ≫ a) (by
    rw [← Category.assoc, h.1, Limits.zero_comp])
  exact (uniq a rfl).trans (uniq b hab.symm).symm

theorem cokernel_of_equiv {X Y Q : C} {f : X ⟶ Y} {π : Y ⟶ Q}
    (hf : f ≫ π = 0)
    (e : ∀ T : C,
      { e : (Q ⟶ T) ≃ {g : Y ⟶ T // f ≫ g = 0} //
          ∀ h : Q ⟶ T, (e h).val = π ≫ h }) : IsCokernel f π := by
  refine ⟨hf, ?_⟩
  intro T g hg
  let t : {g : Y ⟶ T // f ≫ g = 0} := ⟨g, hg⟩
  let a := (e T).val.symm t
  refine ⟨a, ?_, ?_⟩
  · exact ((e T).prop a).symm.trans (congrArg Subtype.val ((e T).val.apply_symm_apply t))
  · intro b hb
    apply (e T).val.injective
    apply Subtype.ext
    exact ((e T).prop b).trans (hb.trans
      (congrArg Subtype.val ((e T).val.apply_symm_apply t)).symm)

-- Alphabeta Math 1.1 and the surjectivity half of 2.1. For this half it
-- suffices to test the abelian-group copower on the quotient by the
-- subgroup of arrows whose composite is in the image of the unit.
theorem unit_surjective {P G Q : C} {I : Type v} (ι : I → (P ⟶ G))
    (π : G ⟶ Q) [Epi π] [Projective P]
    (hAb : ∀ (T : AddCommGrpCat.{v}) (g : I → (HGroup P P ⟶ T)),
      ∃! h : HGroup P G ⟶ T, ∀ i, HGroupMap P (ι i) ≫ h = g i)
    {V : ModuleCat.{v} (End P)ᵐᵒᵖ} (gen : I → V)
    (η : V ⟶ (preadditiveCoyonedaObj P).obj Q)
    (hη : ∀ i, η (gen i) = ι i ≫ π) : Function.Surjective η := by
  let K : AddSubgroup (P ⟶ G) :=
    { carrier := { a | ∃ x : V, η x = a ≫ π }
      zero_mem' := ⟨0, by simp only [map_zero, Limits.zero_comp]; rfl⟩
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, by simp only [map_add, hx, hy, Preadditive.add_comp]; rfl⟩
      neg_mem' := by
        rintro a ⟨x, hx⟩
        exact ⟨-x, by simp only [map_neg, hx, Preadditive.neg_comp]; rfl⟩ }
  have hK (i : I) (a : P ⟶ P) : a ≫ ι i ∈ K := by
    refine ⟨MulOpposite.op ((⟨a⟩ : End P)) • gen i, ?_⟩
    rw [map_smul, hη]
    exact (Category.assoc a (ι i) π).symm
  let rel : AddCon (P ⟶ G) :=
    { r := fun a b => ∃ k ∈ K, b = a + k
      iseqv :=
        { refl := fun a => ⟨0, K.zero_mem, (add_zero a).symm⟩
          symm := by
            rintro a b ⟨k, hk, rfl⟩
            exact ⟨-k, K.neg_mem hk, by rw [add_assoc, add_neg_cancel, add_zero]⟩
          trans := by
            rintro a b c ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
            exact ⟨k + l, K.add_mem hk hl, add_assoc _ _ _⟩ }
      add' := by
        rintro a b c d ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
        exact ⟨k + l, K.add_mem hk hl, add_add_add_comm _ _ _ _⟩ }
  have eq_zero (a : P ⟶ G) : rel.mk' a = 0 ↔ a ∈ K := by
    change ((a : rel.Quotient) = ((0 : P ⟶ G) : rel.Quotient)) ↔ a ∈ K
    rw [rel.eq]
    constructor
    · rintro ⟨k, hk, heq⟩
      have hae : a = -k := (eq_neg_iff_add_eq_zero).mpr heq.symm
      exact hae ▸ K.neg_mem hk
    · intro ha
      exact ⟨-a, K.neg_mem ha, (add_neg_cancel a).symm⟩
  let T := AddCommGrpCat.of rel.Quotient
  let q : HGroup P G ⟶ T := AddCommGrpCat.ofHom rel.mk'
  have hq (i : I) : HGroupMap P (ι i) ≫ q = 0 := by
    apply AddCommGrpCat.ext
    intro a
    exact (eq_zero _).mpr (hK i a)
  obtain ⟨h, _, uniq⟩ := hAb T (fun _ => 0)
  have heq : q = 0 :=
    (uniq q hq).trans (uniq 0 (fun _ => Limits.comp_zero)).symm
  intro b
  obtain ⟨a, ha⟩ := Projective.factors b π
  have hqa : rel.mk' a = 0 :=
    congrArg (fun g : HGroup P G ⟶ T => g a) heq
  obtain ⟨x, hx⟩ := (eq_zero _).mp hqa
  exact ⟨x, hx.trans ha⟩

theorem mono_of_kernel {X Y K : C} {f : X ⟶ Y} {ι : K ⟶ X}
    (h : IsKernel f ι) : Mono ι := by
  constructor
  intro T a b hab
  obtain ⟨k, _, uniq⟩ := h.2 T (a ≫ ι) (by
    rw [Category.assoc, h.1, Limits.comp_zero])
  exact (uniq a rfl).trans (uniq b hab.symm).symm

theorem exact_on_hom {P R G Q : C} [Projective P] {τ : R ⟶ G} {π : G ⟶ Q}
    (hπ : IsCokernel τ π)
    (kernels : ∀ (X Y : C) (f : X ⟶ Y), ∃ (K : C) (ι : K ⟶ X), IsKernel f ι)
    (cokernels : ∀ (X Y : C) (f : X ⟶ Y), ∃ (Q : C) (π : Y ⟶ Q), IsCokernel f π)
    (normalMonos : ∀ (X Y : C) (f : X ⟶ Y), Mono f →
      ∃ (Z : C) (g : Y ⟶ Z), IsKernel g f)
    (a : P ⟶ G) (ha : a ≫ π = 0) : ∃ b : P ⟶ R, b ≫ τ = a := by
  obtain ⟨K, k, hk⟩ := kernels G Q π
  obtain ⟨t, ht, _⟩ := hk.2 R τ hπ.1
  obtain ⟨T, q, hq⟩ := cokernels R K t
  obtain ⟨S, i, hi⟩ := kernels K T q
  obtain ⟨r, hr, _⟩ := hi.2 R t hq.1
  have : Mono k := mono_of_kernel hk
  have : Mono i := mono_of_kernel hi
  obtain ⟨U, g, hg⟩ := normalMonos S G (i ≫ k) inferInstance
  have hτg : τ ≫ g = 0 := by
    rw [← ht, ← hr, Category.assoc r i k, Category.assoc r (i ≫ k) g,
      hg.1, Limits.comp_zero]
  obtain ⟨d, hd, _⟩ := hπ.2 U g hτg
  have hkg : k ≫ g = 0 := by
    rw [← hd, ← Category.assoc, hk.1, Limits.zero_comp]
  obtain ⟨s, hs, _⟩ := hg.2 K k hkg
  have hsi : s ≫ i = 𝟙 K :=
    Mono.right_cancellation (f := k) _ _ (by rw [Category.assoc, hs, Category.id_comp])
  have hq0 : q = 0 := by
    calc
      q = (s ≫ i) ≫ q := by rw [hsi, Category.id_comp]
      _ = 0 := by rw [Category.assoc, hi.1, Limits.comp_zero]
  have : Epi t := by
    constructor
    intro W b c hbc
    have hz : t ≫ (b - c) = 0 := by rw [sub_eq_add_neg, Preadditive.comp_add, Preadditive.comp_neg, hbc, add_neg_cancel]
    obtain ⟨d', hd', _⟩ := hq.2 W (b - c) hz
    rw [hq0, Limits.zero_comp] at hd'
    exact sub_eq_zero.mp hd'.symm
  obtain ⟨a', ha', _⟩ := hk.2 P a ha
  obtain ⟨b, hb⟩ := Projective.factors a' t
  exact ⟨b, by rw [← ht, ← Category.assoc, hb, ha']⟩

-- Alphabeta Math 2.1. The two uses of the abelian-group copower
-- property are pointwise. The additive map on generators evaluates
-- the stated relations, and exactness makes it kill the kernel of π.
theorem unit_injective {P R G Q : C} [Projective P] {I J : Type v}
    (ι : I → (P ⟶ G)) (j : J → (P ⟶ R))
    {τ : R ⟶ G} {π : G ⟶ Q}
    (hπ : IsCokernel τ π)
    (kernels : ∀ (X Y : C) (f : X ⟶ Y), ∃ (K : C) (ι : K ⟶ X), IsKernel f ι)
    (cokernels : ∀ (X Y : C) (f : X ⟶ Y), ∃ (Q : C) (π : Y ⟶ Q), IsCokernel f π)
    (normalMonos : ∀ (X Y : C) (f : X ⟶ Y), Mono f →
      ∃ (Z : C) (g : Y ⟶ Z), IsKernel g f)
    (hAbG : ∀ (T : AddCommGrpCat.{v}) (g : I → (HGroup P P ⟶ T)),
      ∃! h : HGroup P G ⟶ T, ∀ i, HGroupMap P (ι i) ≫ h = g i)
    (hAbR : ∀ (T : AddCommGrpCat.{v}) (g : J → (HGroup P P ⟶ T)),
      ∃! h : HGroup P R ⟶ T, ∀ i, HGroupMap P (j i) ≫ h = g i)
    {V : ModuleCat.{v} (End P)ᵐᵒᵖ} (gen : V → I)
    (points : I → V) (hpoints : ∀ x, points (gen x) = x)
    (s : J → Finset I) (c : J → I → (End P)ᵐᵒᵖ)
    (hr : ∀ r, ∑ i ∈ s r, c r i • points i = 0)
    (hτ : ∀ r, j r ≫ τ = ∑ i ∈ s r, (c r i).unop.asHom ≫ ι i)
    (η : V ⟶ (preadditiveCoyonedaObj P).obj Q)
    (hη : ∀ x, η x = ι (gen x) ≫ π) : Function.Injective η := by
  let T := AddCommGrpCat.of V
  let legs (i : I) : HGroup P P ⟶ T :=
    AddCommGrpCat.ofHom
      { toFun := fun a => MulOpposite.op (⟨a⟩ : End P) • points i
        map_zero' := zero_smul _ _
        map_add' := fun a b =>
          add_smul (MulOpposite.op (⟨a⟩ : End P)) (MulOpposite.op (⟨b⟩ : End P)) _ }
  obtain ⟨q, hq, _⟩ := hAbG T legs
  let q' : (P ⟶ G) →+ V := q.hom
  have hqEval (i : I) (a : P ⟶ P) :
      q (a ≫ ι i) = MulOpposite.op (⟨a⟩ : End P) • points i :=
    congrArg (fun k : HGroup P P ⟶ T => k a) (hq i)
  have hqLeg (r : J) : HGroupMap P (j r) ≫ (HGroupMap P τ ≫ q) = 0 := by
    apply AddCommGrpCat.ext
    intro a
    change P ⟶ P at a
    change q ((a ≫ j r) ≫ τ) = (0 : V)
    have step (i : I) : q (a ≫ (c r i).unop.asHom ≫ ι i) =
        MulOpposite.op (⟨a⟩ : End P) • (c r i • points i) := by
      rw [← Category.assoc, hqEval, ← mul_smul]
      rfl
    rw [Category.assoc, hτ, Preadditive.comp_sum]
    change q' (∑ i ∈ s r, a ≫ (c r i).unop.asHom ≫ ι i) = (0 : V)
    rw [map_sum]
    calc
      (∑ i ∈ s r, q' (a ≫ (c r i).unop.asHom ≫ ι i)) =
          ∑ i ∈ s r, MulOpposite.op (⟨a⟩ : End P) • (c r i • points i) :=
        congrArg (s r).sum (funext step)
      _ = 0 := by rw [← Finset.smul_sum, hr, smul_zero]
  obtain ⟨w, _, uniq⟩ := hAbR T (fun _ => 0)
  have hz : HGroupMap P τ ≫ q = 0 :=
    (uniq _ hqLeg).trans (uniq 0 (fun _ => Limits.comp_zero)).symm
  intro x y hxy
  have hxy' : ι (gen x) ≫ π = ι (gen y) ≫ π := (hη x).symm.trans (hxy.trans (hη y))
  have hsub : (ι (gen x) - ι (gen y)) ≫ π = 0 := by
    rw [sub_eq_add_neg, Preadditive.add_comp, Preadditive.neg_comp, hxy', add_neg_cancel]
  obtain ⟨b, hb⟩ := exact_on_hom hπ kernels cokernels normalMonos _ hsub
  have hqb : q (b ≫ τ) = (0 : V) :=
    congrArg (fun k : HGroup P R ⟶ T => k b) hz
  have eval (i : I) : q (ι i) = points i := by
    have h := hqEval i (𝟙 P)
    rw [Category.id_comp] at h
    exact h.trans (one_smul _ _)
  have hs' : q' (ι (gen x) - ι (gen y)) = (0 : V) := hb ▸ hqb
  have hs₁ : q' (ι (gen x)) - q' (ι (gen y)) = 0 := by
    simpa only [sub_eq_add_neg, map_add, map_neg] using hs'
  exact (hpoints x).symm.trans (((eval _).symm.trans (sub_eq_zero.mp hs₁)).trans
    ((eval _).trans (hpoints y)))

-- Alphabeta Math 3.1. Apply faithfulness to cancel an epi, and use
-- normality of the epi to construct its pointwise inverse.
theorem reflect_bijective {P X Y : C} (hP : IsSeparator P) {f : X ⟶ Y}
    (normalEpis : ∀ (X Y : C) (f : X ⟶ Y), Epi f →
      ∃ (Z : C) (g : Z ⟶ X), IsCokernel g f)
    (hf : Function.Bijective (fun g : P ⟶ X => g ≫ f)) :
    ∃! inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y := by
  have epi : Epi f := by
    constructor
    intro T a b hab
    apply hP.def
    intro z
    obtain ⟨w, hw⟩ := hf.2 z
    change w ≫ f = z at hw
    exact calc
      z ≫ a = w ≫ f ≫ a := by rw [← Category.assoc, hw]
      _ = w ≫ f ≫ b := congrArg (w ≫ ·) hab
      _ = z ≫ b := by rw [← Category.assoc, hw]
  have zero_of_comp (Z : C) (g : Z ⟶ X) (hg : g ≫ f = 0) : g = 0 := by
    apply hP.def
    intro a
    apply hf.1
    change (a ≫ g) ≫ f = (a ≫ 0) ≫ f
    simp only [Category.assoc, hg, Limits.comp_zero, Limits.zero_comp]
  obtain ⟨Z, g, hg⟩ := normalEpis X Y f epi
  have hg0 := zero_of_comp Z g hg.1
  obtain ⟨k, hk, _⟩ := hg.2 X (𝟙 X) (by rw [hg0, Limits.zero_comp])
  refine ⟨k, ⟨hk, epi.left_cancellation _ _ ?_⟩, ?_⟩
  · rw [← Category.assoc, hk, Category.id_comp, Category.comp_id]
  · intro l hl
    exact epi.left_cancellation l k (hl.1.trans hk.symm)

#print axioms cokernel_of_equiv
#print axioms unit_surjective
#print axioms exact_on_hom
#print axioms unit_injective
#print axioms reflect_bijective


/- Alphabeta Math 1.1–3.1. The already supplied unit formula lets us
   work with the two taken copowers and the relation sums. We use the
   pointwise coproduct property in abelian groups and exactness on
   Hom(P, −) to prove bijectivity. Normal epimorphisms and faithfulness
   then give a pointwise inverse of the counit in Prop.

   Step 4.1 asks for global inverse natural transformations. The
   available pointwise existences and the proofs above remain in
   Prop. The supplied copower and cokernel Equivs are in C and do
   not supply simultaneous inverse components in the two categories.
   The corresponding elimination failure is isolated in Packaging.lean. -/
set_option maxHeartbeats 800000 in
theorem PointwiseReconstruction :
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C] (P : C),
  let isKernel := fun {X Y K : C} (f : Quiver.Hom X Y) (ι : Quiver.Hom K X) =>
    CategoryTheory.CategoryStruct.comp ι f = 0 ∧
      ∀ (T : C) (g : Quiver.Hom T X),
        CategoryTheory.CategoryStruct.comp g f = 0 →
        ExistsUnique (fun h : Quiver.Hom T K => CategoryTheory.CategoryStruct.comp h ι = g)
  let isCokernel := fun {X Y Q : C} (f : Quiver.Hom X Y) (π : Quiver.Hom Y Q) =>
    CategoryTheory.CategoryStruct.comp f π = 0 ∧
      ∀ (T : C) (g : Quiver.Hom Y T),
        CategoryTheory.CategoryStruct.comp f g = 0 →
        ExistsUnique (fun h : Quiver.Hom Q T => CategoryTheory.CategoryStruct.comp π h = g)
  let isCoproduct := fun {I : Type v} (X : I → C) (Q : C)
      (ι : ∀ i, Quiver.Hom (X i) Q) =>
    ∀ (T : C) (g : ∀ i, Quiver.Hom (X i) T),
      ExistsUnique (fun h : Quiver.Hom Q T =>
        ∀ i, CategoryTheory.CategoryStruct.comp (ι i) h = g i)
  let A := MulOpposite (CategoryTheory.End P)
  let M := ModuleCat.{v} A
  let H : CategoryTheory.Functor C M := CategoryTheory.preadditiveCoyonedaObj P
  let homGroup := fun X : C => AddCommGrpCat.of (Quiver.Hom P X)
  let homGroupMap := fun {X Y : C} (f : Quiver.Hom X Y) =>
    (AddCommGrpCat.ofHom
      (LinearMap.toAddMonoidHom (ModuleCat.Hom.hom (H.map f))) :
      Quiver.Hom (homGroup X) (homGroup Y))
  (∀ (J : Type v) [CategoryTheory.Category.{v} J] (F : CategoryTheory.Functor J C),
    ∃ (Q : C) (ι : ∀ j, Quiver.Hom (F.obj j) Q),
      (∀ (i j : J) (f : Quiver.Hom i j),
        CategoryTheory.CategoryStruct.comp (F.map f) (ι j) = ι i) ∧
      ∀ (T : C) (g : ∀ j, Quiver.Hom (F.obj j) T),
        (∀ (i j : J) (f : Quiver.Hom i j),
          CategoryTheory.CategoryStruct.comp (F.map f) (g j) = g i) →
        ExistsUnique (fun h : Quiver.Hom Q T =>
          ∀ j, CategoryTheory.CategoryStruct.comp (ι j) h = g j)) →
  (∀ (n : Nat) (X : Fin n → C),
    ∃ (Q : C) (π : ∀ i, Quiver.Hom Q (X i)),
      ∀ (T : C) (g : ∀ i, Quiver.Hom T (X i)),
        ExistsUnique (fun h : Quiver.Hom T Q =>
          ∀ i, CategoryTheory.CategoryStruct.comp h (π i) = g i)) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), ∃ (K : C) (ι : Quiver.Hom K X), isKernel f ι) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), ∃ (Q : C) (π : Quiver.Hom Y Q), isCokernel f π) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), CategoryTheory.Mono f →
    ∃ (Z : C) (g : Quiver.Hom Y Z), isKernel g f) →
  (∀ (X Y : C) (f : Quiver.Hom X Y), CategoryTheory.Epi f →
    ∃ (Z : C) (g : Quiver.Hom Z X), isCokernel g f) →
  CategoryTheory.Projective P →
  CategoryTheory.IsSeparator P →
  (∀ (I : Type v) (X : I → C) (Q : C) (ι : ∀ i, Quiver.Hom (X i) Q),
    isCoproduct X Q ι →
    ∀ (T : AddCommGrpCat.{v}) (g : ∀ i, Quiver.Hom (homGroup (X i)) T),
      ExistsUnique (fun h : Quiver.Hom (homGroup Q) T =>
        ∀ i, CategoryTheory.CategoryStruct.comp (homGroupMap (ι i)) h = g i)) →
  ∀ (copower : ∀ I : Type v,
      Σ Q : C, Σ ι : I → Quiver.Hom P Q,
        ∀ T : C,
          { e : Equiv (Quiver.Hom Q T) (I → Quiver.Hom P T) //
            ∀ (h : Quiver.Hom Q T) (i : I),
              e h i = CategoryTheory.CategoryStruct.comp (ι i) h })
    (cokernel : ∀ {X Y : C} (f : Quiver.Hom X Y),
      Σ Q : C, Σ π : { p : Quiver.Hom Y Q //
        CategoryTheory.CategoryStruct.comp f p = 0 },
        ∀ T : C,
          { e : Equiv (Quiver.Hom Q T)
              { g : Quiver.Hom Y T // CategoryTheory.CategoryStruct.comp f g = 0 } //
            ∀ h : Quiver.Hom Q T,
              (e h).val = CategoryTheory.CategoryStruct.comp π.val h }),
  let coefficients := fun I : Type v =>
    Σ s : Finset I, { a : I → A // ∀ i, Multiset.Mem s.val i ↔ a i ≠ 0 }
  let relations := fun V : M =>
    { r : coefficients (↥V) //
      Finset.sum r.1 (fun x => r.2.val x • x) = (0 : ↥V) }
  let transpose := fun V : M =>
    let generators := copower (↥V)
    let relationCopower := copower (relations V)
    ((relationCopower.2.2 generators.1).val.symm) (fun r : relations V =>
      Finset.sum r.val.1 (fun x =>
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.End.asHom (MulOpposite.unop (r.val.2.val x)))
          (generators.2.1 x)))
  let presentationCokernel := fun V : M => cokernel (transpose V)
  ∀ (L : CategoryTheory.Functor M C),
  let HL : CategoryTheory.Functor M M :=
    { obj := fun V => H.obj (L.obj V)
      map := fun f => H.map (L.map f)
      map_id := fun V => (congrArg H.map (L.map_id V)).trans (H.map_id (L.obj V))
      map_comp := fun f g => (congrArg H.map (L.map_comp f g)).trans (H.map_comp _ _) }
  let LH : CategoryTheory.Functor C C :=
    { obj := fun X => L.obj (H.obj X)
      map := fun f => L.map (H.map f)
      map_id := fun X => (congrArg L.map (H.map_id X)).trans (L.map_id (H.obj X))
      map_comp := fun f g => (congrArg L.map (H.map_comp f g)).trans (L.map_comp _ _) }
  ∀ (adj :
      Σ η : CategoryTheory.NatTrans (CategoryTheory.Functor.id M) HL,
        { ε : CategoryTheory.NatTrans LH (CategoryTheory.Functor.id C) //
          (∀ V : M,
            CategoryTheory.CategoryStruct.comp (L.map (η.app V)) (ε.app (L.obj V)) =
              CategoryTheory.CategoryStruct.id (L.obj V)) ∧
          (∀ X : C,
            CategoryTheory.CategoryStruct.comp (η.app (H.obj X)) (H.map (ε.app X)) =
              CategoryTheory.CategoryStruct.id (H.obj X)) })
    (presentationIso : ∀ V : M, CategoryTheory.Iso (presentationCokernel V).1 (L.obj V)),
    let η := adj.1
    let ε := adj.2.val
    (∀ (V : M) (x : ↥V),
      (η.app V) x =
        CategoryTheory.CategoryStruct.comp ((copower (↥V)).2.1 x)
          (CategoryTheory.CategoryStruct.comp
            (presentationCokernel V).2.1.val (presentationIso V).hom)) →
    (∀ V : M, Function.Bijective (fun x : V => (η.app V) x)) ∧
    (∀ X : C, ∃! inv : X ⟶ LH.obj X,
      ε.app X ≫ inv = 𝟙 (LH.obj X) ∧ inv ≫ ε.app X = 𝟙 X) := by
  intro C cat pre P isKernel isCokernel isCoproduct A M H homGroup homGroupMap
    _ _ kernels cokernels normalMonos normalEpis projective separator hAb copower cokernel
    coefficients relations transpose presentationCokernel L HL LH adj presentationIso η ε hη
  have : Projective P := projective
  have copower_Ab (I : Type v) :
      ∀ (T : AddCommGrpCat.{v}) (g : I → (HGroup P P ⟶ T)),
        ∃! h : HGroup P (copower I).1 ⟶ T,
          ∀ i, HGroupMap P ((copower I).2.1 i) ≫ h = g i := by
    apply hAb I (fun _ => P) (copower I).1 (copower I).2.1
    intro T g
    let e := ((copower I).2.2 T).val
    let h := e.symm g
    have he : e h = g := e.apply_symm_apply g
    refine ⟨h, fun i => (((copower I).2.2 T).prop h i).symm.trans (congrFun he i), ?_⟩
    intro k hk
    apply e.injective
    exact (funext fun i => (((copower I).2.2 T).prop k i).trans (hk i)).trans he.symm
  have unit (V : M) : Function.Bijective (fun x : V => (η.app V) x) := by
    let G := (copower (↥V)).1
    let R := (copower (relations V)).1
    let ι : (↥V) → (P ⟶ G) := (copower (↥V)).2.1
    let j : relations V → (P ⟶ R) := (copower (relations V)).2.1
    let τ : R ⟶ G := transpose V
    let Q := (presentationCokernel V).1
    let π : G ⟶ Q := (presentationCokernel V).2.1.val
    let k : Q ≅ L.obj V := presentationIso V
    let a : V ⟶ H.obj Q := η.app V ≫ H.map k.inv
    have hπ : IsCokernel τ π :=
      cokernel_of_equiv (presentationCokernel V).2.1.prop (presentationCokernel V).2.2
    have : Epi π := epi_of_cokernel hπ
    have ha (x : V) : a x = ι x ≫ π := by
      change ((η.app V) x) ≫ k.inv = ι x ≫ π
      have hηx : (η.app V) x = ι x ≫ π ≫ k.hom := hη V x
      rw [hηx]
      simp only [Category.assoc, k.hom_inv_id, Category.comp_id]
    have hτ (r : relations V) :
        j r ≫ τ = ∑ x ∈ r.val.1, (r.val.2.val x).unop.asHom ≫ ι x := by
      let g : relations V → (P ⟶ G) :=
        fun r => ∑ x ∈ r.val.1, (r.val.2.val x).unop.asHom ≫ ι x
      let e := ((copower (relations V)).2.2 G).val
      have he : e τ = g := e.apply_symm_apply g
      exact (((copower (relations V)).2.2 G).prop τ r).symm.trans (congrFun he r)
    have ha_inj := unit_injective ι j hπ kernels cokernels normalMonos
      (copower_Ab (↥V)) (copower_Ab (relations V)) (fun x => x) (fun x => x) (fun _ => rfl)
      (fun r => r.val.1) (fun r => r.val.2.val) (fun r => r.prop) hτ a ha
    have ha_surj := unit_surjective ι π (copower_Ab (↥V)) (fun x => x) a ha
    constructor
    · intro x y hxy
      apply ha_inj
      exact congrArg (fun z : P ⟶ L.obj V => z ≫ k.inv) hxy
    · intro y
      obtain ⟨x, hx⟩ := ha_surj (y ≫ k.inv)
      change ((η.app V) x) ≫ k.inv = y ≫ k.inv at hx
      refine ⟨x, ?_⟩
      change (η.app V) x = (y : P ⟶ L.obj V)
      let z : P ⟶ L.obj V := (η.app V) x
      let w : P ⟶ L.obj V := y
      calc
        z = (z ≫ k.inv) ≫ k.hom :=
          ((Category.assoc z k.inv k.hom).trans
            ((congrArg (fun t => z ≫ t) k.inv_hom_id).trans (Category.comp_id z))).symm
        _ = (w ≫ k.inv) ≫ k.hom := congrArg (fun t => t ≫ k.hom) hx
        _ = w := (Category.assoc w k.inv k.hom).trans
          ((congrArg (fun t => w ≫ t) k.inv_hom_id).trans (Category.comp_id w))
  refine ⟨unit, ?_⟩
  intro X
  have tri (x : P ⟶ X) : ((η.app (H.obj X)) x) ≫ ε.app X = x :=
    congrArg (fun f : H.obj X ⟶ H.obj X => f x) (adj.2.prop.2 X)
  have hb : Function.Bijective (fun g : P ⟶ L.obj (H.obj X) => g ≫ ε.app X) := by
    constructor
    · intro a b hab
      obtain ⟨x, hx⟩ := (unit (H.obj X)).2 a
      obtain ⟨y, hy⟩ := (unit (H.obj X)).2 b
      have ht : x = y := (tri x).symm.trans
        ((congrArg (fun z => z ≫ ε.app X) hx).trans
          (hab.trans ((congrArg (fun z => z ≫ ε.app X) hy).symm.trans (tri y))))
      exact hx.symm.trans ((congrArg (fun z => (η.app (H.obj X)) z) ht).trans hy)
    · exact fun a => ⟨(η.app (H.obj X)) a, tri a⟩
  exact reflect_bijective separator normalEpis hb

#print axioms PointwiseReconstruction
end ReconstructionCheck
