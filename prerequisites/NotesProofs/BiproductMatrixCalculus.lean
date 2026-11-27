import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.FiniteBiproductUniversalProperties

set_option maxHeartbeats 2000000

open CategoryTheory
open scoped BigOperators

theorem BiproductMatrixCalculus : (
∀ {C : Type*} [CategoryTheory.Category.{_} C] [CategoryTheory.Preadditive C]
  {J K : Type*} [Finite J] [Finite K]
  {X : J → C} {Y : K → C}
  (BX : CategoryTheory.Limits.Bicone X) (BY : CategoryTheory.Limits.Bicone Y),
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype K := Fintype.ofFinite K
  let entry {U A B V : C} (i : Quiver.Hom U A) (f : Quiver.Hom A B)
      (p : Quiver.Hom B V) : Quiver.Hom U V :=
    CategoryTheory.CategoryStruct.comp i (CategoryTheory.CategoryStruct.comp f p)
  (Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (BX.π j) (BX.ι j)) =
    CategoryTheory.CategoryStruct.id BX.pt) →
  (Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp (BY.π k) (BY.ι k)) =
    CategoryTheory.CategoryStruct.id BY.pt) →
  Function.Injective (fun (f : Quiver.Hom BX.pt BY.pt) (k : K) (j : J) =>
    entry (BX.ι j) f (BY.π k)) ∧
  (∀ f : Quiver.Hom BX.pt BY.pt,
    f = Finset.sum Finset.univ (fun k => Finset.sum Finset.univ (fun j =>
      entry (BX.π j) (entry (BX.ι j) f (BY.π k)) (BY.ι k)))) ∧
  (∀ {L : Type*} [Finite L] {Z : L → C} (BZ : CategoryTheory.Limits.Bicone Z),
    letI : Fintype L := Fintype.ofFinite L
    (Finset.sum Finset.univ (fun l => CategoryTheory.CategoryStruct.comp (BZ.π l) (BZ.ι l)) =
      CategoryTheory.CategoryStruct.id BZ.pt) →
    ∀ (f : Quiver.Hom BX.pt BY.pt) (g : Quiver.Hom BY.pt BZ.pt) (l : L) (j : J),
      entry (BX.ι j) (CategoryTheory.CategoryStruct.comp f g) (BZ.π l) =
        Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp
          (entry (BX.ι j) f (BY.π k)) (entry (BY.ι k) g (BZ.π l)))) ∧
  (∀ (f f' : Quiver.Hom BX.pt BY.pt) (k : K) (j : J),
    entry (BX.ι j) (f + f') (BY.π k) =
      entry (BX.ι j) f (BY.π k) + entry (BX.ι j) f' (BY.π k))
) :=
(by
  intros C _ _ J K _ _ X Y BX BY
  let : Fintype J := Fintype.ofFinite J
  let : Fintype K := Fintype.ofFinite K
  dsimp only
  intro hX hY
  -- Proposition 3.7 and Alphabeta Math's matrix correspondence step 2.2
  -- reconstruct a morphism by expanding the two identity sums. Definition 3.4
  -- supplies these sums as hX and hY on the actual bicones. The planned
  -- FiniteBiproductUniversalProperties converts these into bilimit witnesses
  -- or derives totality for bicones of chosen limits or colimits.
  -- Mathlib's biproduct.total concerns the selected HasBiproduct bicone.
  -- Here the reviewed hypotheses give the identities for BX and BY directly.
  have reconstruct (f : BX.pt ⟶ BY.pt) :
      f = ∑ k, ∑ j, BX.π j ≫ (BX.ι j ≫ f ≫ BY.π k) ≫ BY.ι k := by
    calc
      f = 𝟙 BX.pt ≫ f ≫ 𝟙 BY.pt := by simp
      _ = _ := by
        rw [← hX, ← hY]
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  refine ⟨?_, reconstruct, ?_, ?_⟩
  · -- The reconstruction is a left inverse to the entry map, so equal
    -- entries give equal summands for both finite indices.
    intro f f' h
    calc
      f = _ := reconstruct f
      _ = f' := by
        rw [reconstruct f']
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
        exact congrArg (fun e : X j ⟶ Y k => BX.π j ≫ e ≫ BY.ι k)
          (congrFun (congrFun h k) j)
  · -- Alphabeta Math composition steps 1.1, 2.1 and 3.1 expand both arrows
    -- and use the middle orthogonality equations. Proposition 3.7 inserts
    -- hY directly into the fixed (l,j) entry and distributes. The target
    -- contributes its projection, and the finite sum ranges over K.
    intro L _ Z BZ _hZ f g l j
    have compose (a : X j ⟶ BY.pt) (b : BY.pt ⟶ Z l) :
        a ≫ b = ∑ k, (a ≫ BY.π k) ≫ BY.ι k ≫ b := by
      calc
        a ≫ b = a ≫ 𝟙 BY.pt ≫ b := by simp
        _ = _ := by
          simp only [← hY, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    simpa only [Category.assoc] using compose (BX.ι j ≫ f) (g ≫ BZ.π l)
  · -- Matrix correspondence step 1.1 applies bilinearity at both ends.
    intro f f' k j
    simp only [Preadditive.add_comp, Preadditive.comp_add])
