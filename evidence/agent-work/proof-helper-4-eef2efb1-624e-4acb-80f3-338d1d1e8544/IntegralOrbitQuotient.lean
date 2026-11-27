import MackeyDiagrams.DotLabels
import MackeyDiagrams.IndexedDrawing
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Ideal.Span

namespace IntegralOrbitQuotient

universe u v w

private theorem lift_smul_eq_zsmul {M : Type v} [AddCommGroup M] [Module (ULift.{u} ℤ) M]
    (r : ULift.{u} ℤ) (x : M) : r • x = r.down • x :=
  Int.cast_smul_eq_zsmul (ULift.{u} ℤ) r.down x

private theorem closure_eq_span {M : Type v} [AddCommGroup M] [Module (ULift.{u} ℤ) M] (s : Set M) :
    AddSubgroup.closure s = (Submodule.span (ULift.{u} ℤ) s).toAddSubgroup := by
  let C := AddSubgroup.closure s
  let P : Submodule (ULift.{u} ℤ) M :=
    { C.toAddSubmonoid with
      smul_mem' := fun r x hx => by
        rw [lift_smul_eq_zsmul]
        exact C.zsmul_mem hx r.down }
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).mpr (Submodule.subset_span (R := ULift.{u} ℤ))
  · have hP : Submodule.span (ULift.{u} ℤ) s ≤ P :=
      Submodule.span_le.mpr AddSubgroup.subset_closure
    exact hP

private theorem intCast_zero_iff_mem_span (n : ℕ) (a : ULift.{u} ℤ) :
    (a.down : ZMod n) = 0 ↔ a ∈ Ideal.span ({(n : ULift.{u} ℤ)} : Set (ULift.{u} ℤ)) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨ULift.up k, congrArg ULift.up hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.down, congrArg ULift.down hk⟩

variable {ι : Type w} {M : Type v} [AddCommGroup M] [Module (ULift.{u} ℤ) M]

private def reduce (n : ι → ℕ) : (ι → ULift.{u} ℤ) →+ ((i : ι) → ZMod (n i)) where
  toFun a i := ((a i).down : ZMod (n i))
  map_zero' := funext fun _ => Int.cast_zero
  map_add' a b := funext fun i => Int.cast_add (a i).down (b i).down

private theorem reduce_surjective (n : ι → ℕ) : Function.Surjective (reduce n : (ι → ULift.{u} ℤ) →+ ((i : ι) → ZMod (n i))) := by
  intro z
  choose a ha using fun i => ZMod.intCast_surjective (n := n i) (z i)
  exact ⟨fun i => ULift.up (a i), funext ha⟩

private noncomputable def coord [Finite ι] (T : Module.Basis ι (ULift.{u} ℤ) M) : M ≃ₗ[ULift.{u} ℤ] (ι → ULift.{u} ℤ) :=
  T.repr.trans (Finsupp.linearEquivFunOnFinite (ULift.{u} ℤ) (ULift.{u} ℤ) ι)

private noncomputable def reduceCoords [Finite ι] (T : Module.Basis ι (ULift.{u} ℤ) M) (n : ι → ℕ) :
    M →+ ((i : ι) → ZMod (n i)) :=
  (reduce n).comp (coord T).toLinearMap.toAddMonoidHom

private theorem reduceCoords_surjective [Finite ι] (T : Module.Basis ι (ULift.{u} ℤ) M) (n : ι → ℕ) :
    Function.Surjective (reduceCoords T n) :=
  (reduce_surjective n).comp (coord T).surjective

private theorem ker_reduceCoords [Finite ι] (T : Module.Basis ι (ULift.{u} ℤ) M) (n : ι → ℕ) (s : Set M)
    (hspan : ∀ x : M, x ∈ Submodule.span (ULift.{u} ℤ) s ↔
      ∀ i : ι, T.repr x i ∈ Ideal.span ({(n i : ULift.{u} ℤ)} : Set (ULift.{u} ℤ))) :
    (reduceCoords T n).ker = AddSubgroup.closure s := by
  have hclosure : AddSubgroup.closure s =
      (Submodule.span (ULift.{u} ℤ) s).toAddSubgroup := closure_eq_span s
  rw [hclosure]
  ext x
  change reduceCoords T n x = 0 ↔ x ∈ Submodule.span (ULift.{u} ℤ) s
  rw [hspan]
  constructor
  · intro hx i
    apply (intCast_zero_iff_mem_span (n i) (T.repr x i)).mp
    exact congrFun hx i
  · intro hx
    funext i
    exact (intCast_zero_iff_mem_span (n i) (T.repr x i)).mpr (hx i)

private noncomputable def quotientEquiv [Finite ι] (T : Module.Basis ι (ULift.{u} ℤ) M) (n : ι → ℕ)
    (s : Set M) (hspan : ∀ x : M, x ∈ Submodule.span (ULift.{u} ℤ) s ↔
      ∀ i : ι, T.repr x i ∈ Ideal.span ({(n i : ULift.{u} ℤ)} : Set (ULift.{u} ℤ))) :
    (M ⧸ AddSubgroup.closure s) ≃+ DirectSum ι (fun i => ZMod (n i)) := by
  classical
  letI := Fintype.ofFinite ι
  rw [← ker_reduceCoords T n s hspan]
  exact (QuotientAddGroup.quotientKerEquivOfSurjective (reduceCoords T n)
    (reduceCoords_surjective T n)).trans (DirectSum.addEquivProd _).symm

private abbrev Sinf := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
private abbrev blockSym (X : Finset Nat) :=
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
private abbrev ParabolicPerm (H : Subgroup (Equiv.Perm Nat)) :=
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, (blocks l).Nonempty) ∧ Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    H = ⨆ l, blockSym (blocks l)
private abbrev Parabolic (H : Subgroup Sinf) := ParabolicPerm (H.map Sinf.subtype)
private theorem parabolic_finite {H : Subgroup Sinf} (hH : Parabolic H) : Finite H := by
  classical
  obtain ⟨n, blocks, _, _, hblocks⟩ := hH
  let X := Finset.univ.biUnion blocks
  have hsub : H.map Sinf.subtype ≤ blockSym X := by
    rw [hblocks]
    refine iSup_le fun i σ hs => ?_
    obtain ⟨τ, rfl⟩ := hs
    let σ : Equiv.Perm Nat := Equiv.Perm.ofSubtype τ
    have moved_mem (x : Nat) (hx : σ x ≠ x) : x ∈ X := by
      by_contra hn
      have hi : x ∉ blocks i := fun hx' => hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx'⟩)
      exact hx (Equiv.Perm.ofSubtype_apply_of_not_mem τ hi)
    have preserves (x : Nat) : σ x ∈ X ↔ x ∈ X := by
      by_cases h : σ x = x
      · rw [h]
      · have hy : σ (σ x) ≠ σ x := fun hh => h (σ.injective hh)
        exact iff_of_true (moved_mem (σ x) hy) (moved_mem x h)
    exact ⟨σ.subtypePerm preserves, Equiv.Perm.ofSubtype_subtypePerm preserves moved_mem⟩
  let : Finite (blockSym X) :=
    (Set.finite_range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ X))).to_subtype
  exact Finite.of_injective
    (fun h : H => (⟨(h.val : Equiv.Perm Nat), hsub ⟨h.val, h.property, rfl⟩⟩ : blockSym X))
    (fun _ _ hh => Subtype.ext (Subtype.ext (congrArg (fun y : blockSym X => y.val) hh)))

private theorem finiteWord {W : Type*} [Group W] {G A D F : Subgroup W}
    [Finite G] [Finite D]
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) :
    Finite ((MackeyDiagrams.Word.up a).tensor
      ((MackeyDiagrams.Word.down b).tensor (MackeyDiagrams.Word.up d))).basis.carrier := by
  refine Finite.of_surjective (fun p : G × D =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.up a).basis
      ((MackeyDiagrams.Word.down b).tensor (MackeyDiagrams.Word.up d)).basis
      p.1 (MackeyDiagrams.Generator.mixedPair b d p.2)) ?_
  intro z
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (MackeyDiagrams.Generator.mixedEquiv b d).symm.surjective y
  exact ⟨(g, x), rfl⟩

set_option maxHeartbeats 600000 in
private theorem endpointQuotient : (
let Sinf : Subgroup (Equiv.Perm Nat) :=
  Subgroup.closure {σ | Equiv.Perm.IsSwap σ}
let U := ↥Sinf
let blockSym : Finset Nat → Subgroup (Equiv.Perm Nat) :=
  fun X => MonoidHom.range (Equiv.Perm.ofSubtype (p := fun m : Nat => m ∈ X))
let parabolic : Subgroup U → Prop :=
  fun H => ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ l, Finset.Nonempty (blocks l)) ∧
    Pairwise (fun l m => Disjoint (blocks l) (blocks m)) ∧
    Subgroup.map (Subgroup.subtype Sinf) H = iSup (fun l => blockSym (blocks l))
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  ∀ (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let ga := up a
  let ad := down b
  let df := up d
  let gc := up c
  let ce := down e
  let ef := up f
  let bottom := tensor ga (tensor ad df)
  let top := tensor gc (tensor ce ef)
  let X := MackeyDiagrams.Word.basis bottom
  let Y := MackeyDiagrams.Word.basis top
  let Pair := X.carrier × Y.carrier
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis ga)
      (MackeyDiagrams.Word.basis (tensor ad df)) g (MackeyDiagrams.Generator.mixedPair b d x)
  let output := fun (g : G) (y : E) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis gc)
      (MackeyDiagrams.Word.basis (tensor ce ef)) g (MackeyDiagrams.Generator.mixedPair e f y)
  let pair := fun (r : D) (t : G) (s : E) => (input 1 r, output t s)
  letI : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  let orbit : Pair → Set Pair := MulAction.orbit (G × F)
  let stabilizer : Pair → Subgroup (G × F) := MulAction.stabilizer (G × F)
  let projected := fun z : Pair =>
    Subgroup.map (MonoidHom.comp (Subgroup.subtype F) (MonoidHom.snd G F)) (stabilizer z)
  let swaps := fun P : Subgroup U =>
    Subgroup.closure {σ : U | σ ∈ P ∧ Equiv.Perm.IsSwap (σ : Equiv.Perm Nat)}
  let RightData := fun B' : Subgroup U =>
    Σ (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      MackeyDiagrams.Dot (comp b i) (comp d j) ×
      MackeyDiagrams.Dot (comp a i) (comp c k) ×
      MackeyDiagrams.Dot (comp e k) (comp f j)
  let labels : {B' : Subgroup U} → RightData B' → D × G × E :=
    fun ⟨_, _, _, r, t, s⟩ =>
      (MackeyDiagrams.Dot.element r, MackeyDiagrams.Dot.element t, MackeyDiagrams.Dot.element s)
  let representative := fun {B'} (data : RightData B') =>
    let (r, t, s) := labels data
    pair r t s
  let Fiber : {B' : Subgroup U} → RightData B' → Type :=
    fun ⟨i, j, _, _, _, _⟩ => (MackeyDiagrams.Word.basis (tensor (up i) (down j))).carrier
  let lowerMap : {B' : Subgroup U} → (data : RightData B') → Fiber data →
      (MackeyDiagrams.Word.basis (tensor ad df)).carrier :=
    fun ⟨i, j, _, r, _, _⟩ => MackeyDiagrams.Generator.mixedMultiplicationBasis b d i j r
  let finiteFibers := fun {B'} (data : RightData B') =>
    ∀ z, Set.Finite {w : Fiber data | lowerMap data w = z}
  let RightTerm := {term : Σ B' : Subgroup U, RightData B' //
    parabolic term.1 ∧ finiteFibers term.2}
  let rightRepresentative := fun term : RightTerm => representative term.val.2
  let rightOrbit := fun term : RightTerm => orbit (rightRepresentative term)
  let image : {B' : Subgroup U} → RightData B' → Subgroup U :=
    fun ⟨_, j, _, _, _, _⟩ =>
      MonoidHom.range (MonoidHom.comp (Subgroup.subtype F)
        (MackeyDiagrams.ConjEmbedding.toHom j))
  let rightImage := fun term : RightTerm => image term.val.2
  let isInclusion := fun {B'} (data : RightData B') =>
    ∀ h : B', ((MackeyDiagrams.ConjEmbedding.toHom data.2.1) h : U) = (h : U)
  let drawId := fun (R : Type*) [CommRing R] {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
    MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (R := R) p)
  let rightDrawing := fun (R : Type _) [CommRing R] {B' : Subgroup U}
      (i : MackeyDiagrams.ConjEmbedding B' A) (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C)
      (r : List (R × MackeyDiagrams.ProjectionDot.Mixed b d i j))
      (t : List (R × MackeyDiagrams.Dot (comp a i) (comp c k)))
      (s : List (R × MackeyDiagrams.Dot (comp e k) (comp f j))) =>
    let ai := up i
    let fj := down j
    let ck := up k
    let lower := MackeyDiagrams.LabelledDrawing.compactProjection b d i j r
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp a i c k t
    let upper := MackeyDiagrams.LabelledDrawing.mixedMultiplication e f k j s
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal (drawId R ga) lower)
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ai fj))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.horizontal middle (drawId R fj))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ck fj))
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId R gc) upper))))
  let rightDiagramOf (R : Type _) [CommRing R] : {B' : Subgroup U} →
      (data : RightData B') → finiteFibers data → MackeyDiagrams.LabelledDrawing R bottom top :=
    fun ⟨i, j, k, r, t, s⟩ finite =>
      rightDrawing R i j k [(1, ⟨r, finite⟩)] [(1, t)] [(1, s)]
  let rightDiagram := fun (R : Type _) [CommRing R] (term : RightTerm) =>
    rightDiagramOf R term.val.2 term.property.2
  let RightLabels := fun (R : Type _) =>
    Σ (B' : Subgroup U)
      (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F)
      (k : MackeyDiagrams.ConjEmbedding B' C),
      List (R × MackeyDiagrams.ProjectionDot.Mixed b d i j) ×
      List (R × MackeyDiagrams.Dot (comp a i) (comp c k)) ×
      List (R × MackeyDiagrams.Dot (comp e k) (comp f j))
  let fullRightDiagram (R : Type _) [CommRing R] :
      {data : RightLabels R // parabolic data.1} → MackeyDiagrams.LabelledDrawing R bottom top :=
    fun ⟨⟨_, i, j, k, r, t, s⟩, _⟩ => rightDrawing R i j k r t s
  let LeftUpperFiber := fun {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (w : MackeyDiagrams.ConjEmbedding E B)
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) =>
    ∀ z, Set.Finite {p | MackeyDiagrams.Generator.mixedMultiplicationBasis u w c e s p = z}
  let leftDiagram := fun (R : Type _) [CommRing R] {B : Subgroup U}
      (u : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B)
      (r : MackeyDiagrams.Dot (comp u a) (comp v b))
      (t : MackeyDiagrams.Dot (comp v d) (comp w f))
      (s : MackeyDiagrams.Dot (comp u c) (comp w e)) (finite : LeftUpperFiber u w s) =>
    let lower := MackeyDiagrams.LabelledDrawing.mixedMultiplication (R := R) u v a b [(1, r)]
    let middle := MackeyDiagrams.LabelledDrawing.parallelUp (R := R) v d w f [(1, t)]
    let upper := MackeyDiagrams.LabelledDrawing.compactProjection (R := R) u w c e [(1, ⟨s, finite⟩)]
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate ga ad df))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal lower (drawId R df))
        (MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate (down u) (up v) df))
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal (drawId R (down u)) middle)
            (MackeyDiagrams.LabelledDrawing.vertical
              (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.unassociate (down u) (up w) ef))
              (MackeyDiagrams.LabelledDrawing.vertical
                (MackeyDiagrams.LabelledDrawing.horizontal upper (drawId R ef))
                (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.associate gc ce ef)))))))
  let Orbits := ↥(Set.range orbit)
  let rep : Orbits → Pair := fun O => Classical.choose O.property
  let P : Orbits → Subgroup U := fun O => projected (rep O)
  let L : Orbits → Subgroup U := fun O => swaps (P O)
  let index : Orbits → Nat := fun O => Subgroup.relIndex (L O) (P O)
  let coefficient := fun (R : Type _) [CommRing R]
      (M : (Finsupp X.carrier R) →ₗ[R] (Finsupp Y.carrier R)) (z : Pair) =>
    M (Finsupp.single z.1 (1 : R)) z.2
  let entry := fun (R : Type _) [CommRing R] (O : Set Pair) (r : R) (z : Pair) =>
    @ite R (z ∈ O) (Classical.propDecidable (z ∈ O)) r 0
  let evaluate := fun (R : Type _) [CommRing R]
      (T : MackeyDiagrams.LabelledDrawing R bottom top) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret T))
  let bimoduleMaps := fun (R : Type _) [CommRing R] =>
    ({ carrier := {m | ∀ (g : G × F) (x : Finsupp X.carrier R),
          m (MackeyDiagrams.Biset.actLinear R X g x) =
            MackeyDiagrams.Biset.actLinear R Y g (m x)}
       zero_mem' := by simp
       add_mem' := by
         intro m n hm hn g x
         change (m + n) (MackeyDiagrams.Biset.actLinear R X g x) =
           MackeyDiagrams.Biset.actLinear R Y g ((m + n) x)
         simp only [LinearMap.add_apply, map_add, hm g x, hn g x]
       smul_mem' := by
         intro r m hm g x
         change (r • m) (MackeyDiagrams.Biset.actLinear R X g x) =
           MackeyDiagrams.Biset.actLinear R Y g ((r • m) x)
         simp only [LinearMap.smul_apply, map_smul, hm g x] } :
      Submodule R ((Finsupp X.carrier R) →ₗ[R] (Finsupp Y.carrier R)))
  let rightHom := fun (R : Type _) [CommRing R]
      (data : {data : RightLabels R // parabolic data.1}) =>
    MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret (fullRightDiagram R data))
  let rightSpan := fun (R : Type _) [CommRing R] =>
    Submodule.span R (Set.range fun data : {data : RightLabels R // parabolic data.1} =>
      let M := rightHom R data
      (⟨MackeyDiagrams.Biset.Hom.toLinearMap M, MackeyDiagrams.Biset.Hom.commutes M⟩ :
        ↥(bimoduleMaps R)))
  let integerMaps :=
    ({ carrier := ↑(bimoduleMaps (ULift Int))
       zero_mem' := Submodule.zero_mem (bimoduleMaps (ULift Int))
       add_mem' := fun hm hn => Submodule.add_mem (bimoduleMaps (ULift Int)) hm hn
       neg_mem' := by
         intro m hm g x
         change (-m) (MackeyDiagrams.Biset.actLinear (ULift Int) X g x) =
           MackeyDiagrams.Biset.actLinear (ULift Int) Y g ((-m) x)
         simp only [LinearMap.neg_apply, map_neg, hm g x] } :
      AddSubgroup ((Finsupp X.carrier (ULift Int)) →ₗ[ULift Int]
        (Finsupp Y.carrier (ULift Int))))
  let integerRightSpan : AddSubgroup ↥integerMaps :=
    AddSubgroup.closure (Set.range fun data : {data : RightLabels (ULift Int) // parabolic data.1} =>
      let M := rightHom (ULift Int) data
      (⟨MackeyDiagrams.Biset.Hom.toLinearMap M, MackeyDiagrams.Biset.Hom.commutes M⟩ : ↥integerMaps))
  (∃ T : Module.Basis Orbits (ULift Int) ↥(bimoduleMaps (ULift Int)),
    (∀ M : ↥(bimoduleMaps (ULift Int)), M ∈ rightSpan (ULift Int) ↔
      ∀ O : Orbits, Module.Basis.repr T M O ∈ Ideal.span ({(index O : ULift Int)} : Set (ULift Int)))) →
  Nonempty ((↥integerMaps ⧸ integerRightSpan) ≃+
    DirectSum Orbits (fun O => ZMod (index O)))) := by
  classical
  intro Sinf U blockSym parabolic G A D F C E hG hA hD hF hC hE a b d c e f
  intro up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output pair pairAction
  intro orbit stabilizer projected swaps RightData labels representative Fiber lowerMap
  intro finiteFibers RightTerm rightRepresentative rightOrbit image rightImage isInclusion
  intro drawId rightDrawing rightDiagramOf rightDiagram RightLabels fullRightDiagram
  intro LeftUpperFiber leftDiagram Orbits rep P L index coefficient entry evaluate
  intro bimoduleMaps rightHom rightSpan integerMaps integerRightSpan hRingSpan
  haveI : Finite G := parabolic_finite hG
  haveI : Finite D := parabolic_finite hD
  haveI : Finite E := parabolic_finite hE
  letI : Finite X.carrier := finiteWord a b d
  letI : Finite Y.carrier := finiteWord c e f
  letI : Finite Pair := inferInstanceAs (Finite (X.carrier × Y.carrier))
  letI : Finite Orbits := (Set.finite_range orbit).to_subtype
  obtain ⟨T, hspan⟩ := hRingSpan
  let generators : Set ↥(bimoduleMaps (ULift Int)) :=
    Set.range fun data : {data : RightLabels (ULift Int) // parabolic data.1} =>
      let M := rightHom (ULift Int) data
      (⟨MackeyDiagrams.Biset.Hom.toLinearMap M, MackeyDiagrams.Biset.Hom.commutes M⟩ :
        ↥(bimoduleMaps (ULift Int)))
  change Nonempty ((↥(bimoduleMaps (ULift Int)) ⧸ AddSubgroup.closure generators) ≃+
    DirectSum Orbits (fun O => ZMod (index O)))
  exact ⟨quotientEquiv T index generators hspan⟩

end IntegralOrbitQuotient
