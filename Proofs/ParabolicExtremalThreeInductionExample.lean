import MackeyDiagrams
import Proofs.ParabolicExtremalThreeInductionRegions

set_option maxHeartbeats 2000000

namespace ExtremalThreeInductionExample

private abbrev Perm := Equiv.Perm Nat
private abbrev finitary := Subgroup.closure {σ : Perm | Equiv.Perm.IsSwap σ}
private abbrev U := ↥finitary
private abbrev blockSym (S : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
private abbrev onBlock (S : Finset Nat) := (blockSym S).comap finitary.subtype
private abbrev transposition (i j : Nat) (h : i ≠ j) : U :=
  ⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, h, rfl⟩⟩

-- Factor permutations on the finite subtype before extending by the identity.
private theorem block_le_of_swaps (S : Finset Nat) (H : Subgroup Perm)
    (hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Equiv.swap i j ∈ H) :
    blockSym S ≤ H := by
  rintro _ ⟨σ, rfl⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [map_one]; exact H.one_mem
  | swap_mul f i j hij ih =>
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    exact H.mul_mem (hs i i.property j j.property (fun h => hij (Subtype.ext h))) ih

private theorem onBlock_le_of_swaps (S : Finset Nat) (H : Subgroup U)
    (hs : ∀ i ∈ S, ∀ j ∈ S, ∀ h : i ≠ j, transposition i j h ∈ H) :
    onBlock S ≤ H := by
  have hle : blockSym S ≤ H.map finitary.subtype :=
    block_le_of_swaps S _ fun i hi j hj h => ⟨transposition i j h, hs i hi j hj h, rfl⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hle (show (x : Perm) ∈ blockSym S from hx)
  exact (finitary.subtype_injective hxy) ▸ hy

private theorem transposition_mem_block {S : Finset Nat} {i j : Nat} (h : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) : transposition i j h ∈ onBlock S :=
  ⟨Equiv.swap (⟨i, hi⟩ : ↥S) ⟨j, hj⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

private theorem pair_block {i j : Nat} (h : i ≠ j) :
    Subgroup.closure ({transposition i j h} : Set U) = onBlock {i, j} := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (transposition_mem_block h (by simp) (by simp)))
  · apply onBlock_le_of_swaps
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y
    · exact (hxy rfl).elim
    · exact Subgroup.subset_closure (Set.mem_singleton _)
    · have hs : transposition j i hxy = transposition i j h := Subtype.ext (Equiv.swap_comm j i)
      rw [hs]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    · exact (hxy rfl).elim

private abbrev aSwap := transposition 1 2 (by decide)
private abbrev cSwap := transposition 2 3 (by decide)
private abbrev aGroup := Subgroup.closure ({aSwap} : Set U)
private abbrev cGroup := Subgroup.closure ({cSwap} : Set U)

private theorem join_blocks : aGroup ⊔ cGroup = onBlock (Finset.Icc 1 3) := by
  have h12 : aSwap ∈ aGroup ⊔ cGroup :=
    (show aGroup ≤ aGroup ⊔ cGroup from le_sup_left) (Subgroup.subset_closure (Set.mem_singleton _))
  have h23 : cSwap ∈ aGroup ⊔ cGroup :=
    (show cGroup ≤ aGroup ⊔ cGroup from le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
  have h13eq : transposition 1 3 (by decide) = cSwap * aSwap * cSwap := by
    apply Subtype.ext
    change Equiv.swap 1 3 = Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 2 3
    rw [Equiv.swap_mul_swap_mul_swap (by decide : (1 : Nat) ≠ 2) (by decide : (1 : Nat) ≠ 3),
      Equiv.swap_comm]
  have h13 : transposition 1 3 (by decide) ∈ aGroup ⊔ cGroup :=
    h13eq ▸ (aGroup ⊔ cGroup).mul_mem ((aGroup ⊔ cGroup).mul_mem h23 h12) h23
  have increasing (i j : Nat) (hi : i ∈ Finset.Icc 1 3) (hj : j ∈ Finset.Icc 1 3)
      (hij : i < j) : transposition i j hij.ne ∈ aGroup ⊔ cGroup := by
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    have hcases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact h13
    · exact h23
  have h1 : 1 ∈ Finset.Icc (1 : Nat) 3 := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
  have h2 : 2 ∈ Finset.Icc (1 : Nat) 3 := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
  have h3 : 3 ∈ Finset.Icc (1 : Nat) 3 := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
  apply le_antisymm
  · exact sup_le
      ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (transposition_mem_block (by decide) h1 h2)))
      ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (transposition_mem_block (by decide) h2 h3)))
  · apply onBlock_le_of_swaps
    intro i hi j hj hij
    rcases hij.lt_or_gt with h | h
    · exact increasing i j hi hj h
    · have heq : transposition i j hij = transposition j i h.ne := Subtype.ext (Equiv.swap_comm i j)
      rw [heq]
      exact increasing j i hj hi h

private theorem block_fixes {S : Finset Nat} {x : U} (hx : x ∈ onBlock S)
    {n : Nat} (hn : n ∉ S) : (x : Perm) n = n := by
  obtain ⟨σ, hσ⟩ := (show (x : Perm) ∈ blockSym S from hx)
  rw [← hσ]
  exact Equiv.Perm.ofSubtype_apply_of_not_mem σ hn

private theorem meet_blocks : aGroup ⊓ cGroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxA : x ∈ onBlock {1, 2} := pair_block (by decide : (1 : Nat) ≠ 2) ▸ hx.1
  have hxC : x ∈ onBlock {2, 3} := pair_block (by decide : (2 : Nat) ≠ 3) ▸ hx.2
  -- Only 2 is in both blocks. Injectivity then forces that point to be fixed.
  have fixed (n : Nat) (hn : n ≠ 2) : (x : Perm) n = n := by
    by_cases h : n = 1
    · exact block_fixes hxC (by simp [h])
    · exact block_fixes hxA (by simp [h, hn])
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro n
  change (x : Perm) n = n
  by_cases h : n = 2
  · subst n
    by_contra hn
    exact hn ((x : Perm).injective (fixed ((x : Perm) 2) hn))
  · exact fixed n h

private abbrev Parabolic (H : Subgroup U) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, (blocks i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    H.map finitary.subtype = ⨆ i, blockSym (blocks i)

private theorem block_parabolic (S : Finset Nat) (hs : S.Nonempty) : Parabolic (onBlock S) := by
  refine ⟨1, fun _ => S, fun _ => hs, fun i j hij => (hij (Subsingleton.elim i j)).elim, ?_⟩
  rw [iSup_unique]
  apply Subgroup.map_comap_eq_self
  rw [Subgroup.range_subtype]
  exact block_le_of_swaps S _ fun i _ j _ hij => Subgroup.subset_closure ⟨i, j, hij, rfl⟩

private theorem bot_parabolic : Parabolic (⊥ : Subgroup U) := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  simp only [Subgroup.map_bot, iSup_of_empty]

end ExtremalThreeInductionExample

namespace ExtremalThreeInductionExample
open MackeyDiagrams

private theorem singleton_eval {V : Type*} [Group V] {P Q : Subgroup V}
    {i j : ConjEmbedding Q P} (x : Dot i j) :
    (DotLabel.upDrawing (R := Complex) (Finsupp.single x 1)).interpret.eval =
      (Diagram.upDot (R := Complex) x).eval := by
  rw [DotLabel.eval_upDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  rw [Diagram.eval_linearUpDot_apply, freeLift_single, one_smul]

end ExtremalThreeInductionExample

open MackeyDiagrams

theorem ParabolicExtremalThreeInductionExample : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (X : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
let conjugate := fun (r : U) (H : Subgroup U) =>
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj r)) H
let embed := fun {H K : Subgroup U} (r : U) (h : conjugate r H ≤ K) =>
  MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := K) r
    (fun x => h ⟨(x : U), Subtype.property x, rfl⟩)
let onBlock : Finset Nat → Subgroup U := fun S =>
  Subgroup.comap (Subgroup.subtype finitary) (blockSym S)
let four := Finset.Icc (1 : Nat) 4
let G := onBlock four
let liftSwap := fun (i j : Nat) (hij : i ≠ j) =>
  (⟨Equiv.swap i j, Subgroup.subset_closure
      (show Equiv.Perm.IsSwap (Equiv.swap i j) from ⟨i, j, hij, rfl⟩)⟩ : U)
let s₁₂ := liftSwap 1 2 (by decide)
let s₂₃ := liftSwap 2 3 (by decide)
let A := Subgroup.closure ({s₁₂} : Set U)
let D := A
let C := Subgroup.closure ({s₂₃} : Set U)
let E := C
let F : Subgroup U := ⊥
let p : G := 1
let swapInFour : ∀ (i j : Nat) (hij : i ≠ j), i ∈ four → j ∈ four →
    liftSwap i j hij ∈ G := by
  intro i j hij hi hj
  change Equiv.swap i j ∈ blockSym four
  exact ⟨Equiv.swap (⟨i, hi⟩ : ↥four) ⟨j, hj⟩,
    Equiv.Perm.ofSubtype_swap_eq (⟨i, hi⟩ : ↥four) ⟨j, hj⟩⟩
let oneMem : 1 ∈ four := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
let twoMem : 2 ∈ four := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
let threeMem : 3 ∈ four := Finset.mem_Icc.mpr ⟨by decide, by decide⟩
let aLe : A ≤ G := (Subgroup.closure_le G).mpr
  (Set.singleton_subset_iff.mpr (swapInFour 1 2 (by decide) oneMem twoMem))
let cLe : C ≤ G := (Subgroup.closure_le G).mpr
  (Set.singleton_subset_iff.mpr (swapInFour 2 3 (by decide) twoMem threeMem))
let inclusion : ∀ {H K : Subgroup U}, H ≤ K → MackeyDiagrams.ConjEmbedding H K :=
  fun {H K} h => embed 1 (show conjugate 1 H ≤ K from by
    rintro _ ⟨x, hx, rfl⟩
    change (1 : U) * x * (1 : U)⁻¹ ∈ K
    simpa only [one_mul, inv_one, mul_one] using h hx)
let ga := inclusion aLe
let ad : MackeyDiagrams.ConjEmbedding D A := inclusion le_rfl
let dfEmbedding : MackeyDiagrams.ConjEmbedding F D := inclusion bot_le
let gc := inclusion cLe
let ce : MackeyDiagrams.ConjEmbedding E C := inclusion le_rfl
let efEmbedding : MackeyDiagrams.ConjEmbedding F E := inclusion bot_le
let bottomPair := MackeyDiagrams.ConjEmbedding.comp ga ad
let topPair := MackeyDiagrams.ConjEmbedding.comp gc ce
let word := fun {P Q S T : Subgroup U}
    (i : MackeyDiagrams.ConjEmbedding Q P) (j : MackeyDiagrams.ConjEmbedding S Q)
    (k : MackeyDiagrams.ConjEmbedding T S) =>
  MackeyDiagrams.Word.tensor
    (MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up i) (MackeyDiagrams.Word.up j))
    (MackeyDiagrams.Word.up k)
let bottom := word ga ad dfEmbedding
let top := word gc ce efEmbedding
let straight := fun {P Q : Subgroup U} (a : MackeyDiagrams.ConjEmbedding Q P) =>
  MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
let merge := fun {P Q S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
  MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.mergeUp a b)
let split := fun {P Q S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q) =>
  MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.splitUp a b)
let splitBottom :=
  MackeyDiagrams.LabelledDrawing.vertical (split bottomPair dfEmbedding)
    (MackeyDiagrams.LabelledDrawing.horizontal (split ga ad) (straight dfEmbedding))
let mergeTop :=
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.horizontal (merge gc ce) (straight efEmbedding))
    (merge topPair efEmbedding)
let BoundaryDrawing := MackeyDiagrams.LabelledDrawing Complex bottom top
let realizes := fun (drawing : BoundaryDrawing) =>
  ∀ z : MonoidAlgebra Complex G,
    MonoidAlgebra.ofCoeff
      (MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (MackeyDiagrams.LabelledDrawing.vertical splitBottom
              (MackeyDiagrams.LabelledDrawing.vertical drawing mergeTop))))
        (MonoidAlgebra.coeff z)) = z * MonoidAlgebra.single p (1 : Complex)
let crossing := fun {P Q Q' S : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
    (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
    (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
      (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
  MackeyDiagrams.LabelledDrawing.vertical (merge a b)
    (MackeyDiagrams.LabelledDrawing.vertical (MackeyDiagrams.DotLabel.upDrawing weights)
      (split a' b'))
let crossLeft := fun {P Q Q' S T : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
    (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q')
    (c : MackeyDiagrams.ConjEmbedding T S)
    (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp a b)
      (MackeyDiagrams.ConjEmbedding.comp a' b')) =>
  MackeyDiagrams.LabelledDrawing.horizontal (crossing a b a' b' weights)
    (straight c)
let crossRight := fun {P Q S S' T : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding Q P)
    (b : MackeyDiagrams.ConjEmbedding S Q) (c : MackeyDiagrams.ConjEmbedding T S)
    (b' : MackeyDiagrams.ConjEmbedding S' Q) (c' : MackeyDiagrams.ConjEmbedding T S')
    (weights : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp b c)
      (MackeyDiagrams.ConjEmbedding.comp b' c')) =>
  MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.associate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b)
        (MackeyDiagrams.Word.up c)))
    (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (straight a)
        (crossing b c b' c' weights))
      (MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.unassociate (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b')
          (MackeyDiagrams.Word.up c'))))
let leftDrawing := fun {B : Subgroup U} (gb : MackeyDiagrams.ConjEmbedding B G)
    (bd : MackeyDiagrams.ConjEmbedding D B) (be : MackeyDiagrams.ConjEmbedding E B)
    (x₁ : MackeyDiagrams.DotLabel Complex bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
    (x₂ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp bd dfEmbedding)
      (MackeyDiagrams.ConjEmbedding.comp be efEmbedding))
    (x₃ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp gb be) topPair) =>
  MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ad gb bd dfEmbedding x₁)
    (MackeyDiagrams.LabelledDrawing.vertical (crossRight gb bd dfEmbedding be efEmbedding x₂)
      (crossLeft gb be gc ce efEmbedding x₃))
let rightDrawing := fun {B' : Subgroup U} (ab' : MackeyDiagrams.ConjEmbedding B' A)
    (cb' : MackeyDiagrams.ConjEmbedding B' C) (b'f : MackeyDiagrams.ConjEmbedding F B')
    (y₁ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ad dfEmbedding)
      (MackeyDiagrams.ConjEmbedding.comp ab' b'f))
    (y₂ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp ga ab')
      (MackeyDiagrams.ConjEmbedding.comp gc cb'))
    (y₃ : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp cb' b'f)
      (MackeyDiagrams.ConjEmbedding.comp ce efEmbedding)) =>
  MackeyDiagrams.LabelledDrawing.vertical (crossRight ga ad dfEmbedding ab' b'f y₁)
    (MackeyDiagrams.LabelledDrawing.vertical (crossLeft ga ab' gc cb' b'f y₂)
      (crossRight gc cb' b'f ce efEmbedding y₃))
let shapeOf := fun (drawing : BoundaryDrawing) =>
  (⟨MackeyDiagrams.LabelledDrawing.planarShape drawing, G, F, bottom, top, drawing, rfl, rfl⟩ :
    MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex
      ([true, true, true], [true, true, true]))
let leftShape := shapeOf
  (leftDrawing (MackeyDiagrams.ConjEmbedding.id G) ga gc 0 0 0)
let rightShape := shapeOf
  (rightDrawing (inclusion bot_le) (inclusion bot_le) (MackeyDiagrams.ConjEmbedding.id F) 0 0 0)
let singleton := fun {H K : Subgroup U} {a b : MackeyDiagrams.ConjEmbedding H K}
    (dot : MackeyDiagrams.Dot a b) => (Finsupp.single dot (1 : Complex) : MackeyDiagrams.DotLabel Complex a b)
let leftRegions : Set (Subgroup U) := {H |
  ∃ (B : Subgroup U) (rGB rBD rBE : U), parabolic B ∧
  ∃ (hGB : conjugate rGB B ≤ G) (hBD : conjugate rBD D ≤ B) (hBE : conjugate rBE E ≤ B),
    let gb := embed rGB hGB
    let bd := embed rBD hBD
    let be := embed rBE hBE
    ∃ (x₁ : MackeyDiagrams.Dot bottomPair (MackeyDiagrams.ConjEmbedding.comp gb bd))
      (x₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp bd dfEmbedding)
        (MackeyDiagrams.ConjEmbedding.comp be efEmbedding))
      (x₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp gb be) topPair),
      let drawing := leftDrawing gb bd be (singleton x₁) (singleton x₂) (singleton x₃)
      MackeyDiagrams.LabelledDrawing.planarShape drawing = Subtype.val leftShape ∧
      H = conjugate ((↑(MackeyDiagrams.Dot.element x₁ : G) : U) * rGB) B ∧ realizes drawing}
let rightRegions : Set (Subgroup U) := {H |
  ∃ (B' : Subgroup U) (rAB' rCB' rB'F : U), parabolic B' ∧
  ∃ (hAB' : conjugate rAB' B' ≤ A) (hCB' : conjugate rCB' B' ≤ C)
    (hB'F : conjugate rB'F F ≤ B'),
    let ab' := embed rAB' hAB'
    let cb' := embed rCB' hCB'
    let b'f := embed rB'F hB'F
    ∃ (y₁ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ad dfEmbedding)
        (MackeyDiagrams.ConjEmbedding.comp ab' b'f))
      (y₂ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp ga ab')
        (MackeyDiagrams.ConjEmbedding.comp gc cb'))
      (y₃ : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp cb' b'f)
        (MackeyDiagrams.ConjEmbedding.comp ce efEmbedding)),
      let drawing := rightDrawing ab' cb' b'f (singleton y₁) (singleton y₂) (singleton y₃)
      MackeyDiagrams.LabelledDrawing.planarShape drawing = Subtype.val rightShape ∧
      H = conjugate ((1 : U) * (↑(MackeyDiagrams.Dot.element y₁ : A) : U) * rAB') B' ∧ realizes drawing}
IsLeast leftRegions (onBlock (Finset.Icc (1 : Nat) 3)) ∧
  IsGreatest rightRegions (⊥ : Subgroup U)
) :=
(by
  classical
  -- Xiao, Example 8.3, archived original PDF p. 38 and published 28 November
  -- revision p. 40 (https://getcurious.cc/downloads/mackey-bimodules.pdf#page=40).
  -- Specialize Proposition 8.5 to inclusions and p = 1. The article states the
  -- resulting subgroups directly. The group lemmas below check generation by
  -- the three transpositions and triviality of the intersection.
  -- No numbered Alphabeta Math proof is supplied for this example.
  intro finitary U blockSym parabolic conjugate embed onBlock four G liftSwap
    s₁₂ s₂₃ A D C E F p swapInFour oneMem twoMem threeMem aLe cLe inclusion
    ga ad dfEmbedding gc ce efEmbedding bottomPair topPair word bottom top
    straight merge split splitBottom mergeTop BoundaryDrawing realizes crossing crossLeft crossRight
    leftDrawing rightDrawing shapeOf leftShape rightShape singleton leftRegions rightRegions
  have hG : parabolic G :=
    ExtremalThreeInductionExample.block_parabolic four ⟨1, oneMem⟩
  have hA : parabolic A := by
    have hPair : A = onBlock {1, 2} :=
      ExtremalThreeInductionExample.pair_block (by decide : (1 : Nat) ≠ 2)
    rw [hPair]
    exact ExtremalThreeInductionExample.block_parabolic _ ⟨1, by simp⟩
  have hC : parabolic C := by
    have hPair : C = onBlock {2, 3} :=
      ExtremalThreeInductionExample.pair_block (by decide : (2 : Nat) ≠ 3)
    rw [hPair]
    exact ExtremalThreeInductionExample.block_parabolic _ ⟨2, by simp⟩
  have hF : parabolic F := ExtremalThreeInductionExample.bot_parabolic
  have atOne {H K : Subgroup U} (h : H ≤ K) : conjugate 1 H ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    change (1 : U) * x * (1 : U)⁻¹ ∈ K
    simpa only [one_mul, inv_one, mul_one] using h hx
  have conjOne (H : Subgroup U) : conjugate 1 H = H := by
    apply le_antisymm (atOne le_rfl)
    intro x hx
    exact ⟨x, hx, by simp⟩
  have hMin : conjugate ((1 : U) * 1) D ⊔ conjugate ((p : U) * 1 * 1) E =
      onBlock (Finset.Icc (1 : Nat) 3) := by
    simpa only [p, Subgroup.coe_one, one_mul, conjOne] using
      (show A ⊔ C = onBlock (Finset.Icc (1 : Nat) 3) from ExtremalThreeInductionExample.join_blocks)
  have hMax : conjugate (1 : U) A ⊓ conjugate ((p : U) * 1) C = (⊥ : Subgroup U) := by
    simpa only [p, Subgroup.coe_one, one_mul, conjOne] using
      (show A ⊓ C = (⊥ : Subgroup U) from ExtremalThreeInductionExample.meet_blocks)
  have central : (((1 : U) * 1 * 1)⁻¹ * (p : U) * (1 * 1 * 1)) ∈
      Subgroup.centralizer (F : Set U) := by
    simpa only [p, Subgroup.coe_one, one_mul, inv_one] using
      (Subgroup.centralizer (F : Set U)).one_mem
  obtain ⟨hLeft, hRight, _⟩ :=
    ParabolicExtremalThreeInductionRegions G A D F C E hG hA hA hF hC hC
      1 1 1 1 1 1 (atOne aLe) (atOne le_rfl) (atOne bot_le)
      (atOne cLe) (atOne le_rfl) (atOne bot_le) p central
  rw [← hMin, ← hMax]
  -- The supplier uses typed group-element dots. Converting each to a
  -- coefficient-one up label preserves its evaluation. On both sides the
  -- planar shape checks by reduction because erasure keeps the marked wiring
  -- and forgets the coefficients and the subgroup embeddings.
  constructor
  · constructor
    · obtain ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, hRegion, hEval⟩ := hLeft.1
      refine ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, rfl, hRegion, ?_⟩
      intro w
      have h := hEval w
      dsimp only [realizes, splitBottom, mergeTop, bottomPair, topPair, leftDrawing,
        crossLeft, crossRight, crossing, merge, split, straight, singleton]
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, TrivalentVertex.expand,
        Diagram.eval, ExtremalThreeInductionExample.singleton_eval] at h ⊢
      exact h
    · intro H hH
      apply hLeft.2
      obtain ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, _, hRegion, hEval⟩ := hH
      refine ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, hRegion, ?_⟩
      intro w
      have h := hEval w
      dsimp only [realizes, splitBottom, mergeTop, bottomPair, topPair, leftDrawing,
        crossLeft, crossRight, crossing, merge, split, straight, singleton] at h
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, TrivalentVertex.expand,
        Diagram.eval, ExtremalThreeInductionExample.singleton_eval] at h ⊢
      exact h
  · constructor
    · obtain ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, hRegion, hEval⟩ := hRight.1
      refine ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, rfl, hRegion, ?_⟩
      intro w
      have h := hEval w
      dsimp only [realizes, splitBottom, mergeTop, bottomPair, topPair, rightDrawing,
        crossLeft, crossRight, crossing, merge, split, straight, singleton]
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, TrivalentVertex.expand,
        Diagram.eval, ExtremalThreeInductionExample.singleton_eval] at h ⊢
      exact h
    · intro H hH
      apply hRight.2
      obtain ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, _, hRegion, hEval⟩ := hH
      refine ⟨B, r, s, t, hB, hr, hs, ht, x, y, z, hRegion, ?_⟩
      intro w
      have h := hEval w
      dsimp only [realizes, splitBottom, mergeTop, bottomPair, topPair, rightDrawing,
        crossLeft, crossRight, crossing, merge, split, straight, singleton] at h
      simp only [LabelledDrawing.interpret, ScopedDiagram.eval, TrivalentVertex.expand,
        Diagram.eval, ExtremalThreeInductionExample.singleton_eval] at h ⊢
      exact h)
