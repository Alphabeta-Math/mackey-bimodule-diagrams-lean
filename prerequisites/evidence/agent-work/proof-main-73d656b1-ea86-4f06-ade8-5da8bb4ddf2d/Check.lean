import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.FreeModulesAndPresentations
import NotesProofs.ModuleQuotientUniversalProperty

set_option maxHeartbeats 2000000

universe u v w t a

section Witness

variable {R : Type u} [Ring R] {B : Type v} [AddCommGroup B] [Module (MulOpposite R) B]
  {M : Type w} [AddCommGroup M] [Module R M]

local notation "right" => (fun (r : R) (b : B) => MulOpposite.op r • b)

local instance : AddCommGroup (ChoiceFreeWatts.Tensor right M) :=
  ChoiceFreeWatts.tensorAddCommGroup right

-- Ian X, Theorem 6.2, p. 18, https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=18
-- The notes absorb integer coefficients in the first factor of a pure tensor.
-- In the coordinator's presentation, induction on a free additive word gives
-- signed generators instead. Absorb each minus sign using first-variable
-- additivity and cancellation, and combine the two lists for a sum of words.
private theorem tensorFiniteSum {D : Type a} [AddCommGroup D]
    (h : ChoiceFreeWatts.Tensor right M →+ D) (x : ChoiceFreeWatts.Tensor right M) :
    ∃ pairs : List (B × M), (pairs.map fun bm => h (ChoiceFreeWatts.pure right bm.1 bm.2)).sum = h x := by
  refine AddCon.induction_on x ?_
  intro z
  change ∃ pairs : List (B × M), _ = (h.comp (ChoiceFreeWatts.wordMk _)) z
  let q := h.comp (ChoiceFreeWatts.wordMk (ChoiceFreeWatts.tensorRel right M))
  refine FreeAddGroup.induction_on (motive := fun z =>
    ∃ pairs : List (B × M), (pairs.map fun bm => h (ChoiceFreeWatts.pure right bm.1 bm.2)).sum = q z) z ?_ ?_ ?_ ?_
  · exact ⟨[], (map_zero q).symm⟩
  · intro bm
    exact ⟨[bm], by simp [q, ChoiceFreeWatts.pure, ChoiceFreeWatts.wordGen]⟩
  · rintro ⟨b, m⟩ _
    refine ⟨[(-b, m)], ?_⟩
    have hadd := (ChoiceFreeWatts.pureBalanced (X := M) right).1
    have hzero : ChoiceFreeWatts.pure right (0 : B) m = 0 := by
      apply add_left_cancel (a := ChoiceFreeWatts.pure right (0 : B) m)
      simpa only [zero_add, add_zero] using (hadd 0 0 m).symm
    have hneg : ChoiceFreeWatts.pure right (-b) m = -ChoiceFreeWatts.pure right b m := by
      apply eq_neg_of_add_eq_zero_left
      rw [← hadd, neg_add_cancel, hzero]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_neg]
    rw [hneg, map_neg]
    rfl
  · intro x y hx hy
    obtain ⟨xs, hxs⟩ := hx
    obtain ⟨ys, hys⟩ := hy
    exact ⟨xs ++ ys, by rw [List.map_append, List.sum_append, hxs, hys, map_add]⟩

end Witness

theorem BalancedTensorUniversalProperty : (∀ (R : Type u) [Ring R] (B : Type v) [AddCommGroup B] [Module (MulOpposite R) B]
    (M : Type w) [AddCommGroup M] [Module R M],
  let Bal := fun (A : AddCommGrpCat.{max v w t}) =>
    { f : B → M → A //
      (∀ (b b' : B) (m : M), f (b + b') m = f b m + f b' m) ∧
      (∀ (b : B) (m m' : M), f b (m + m') = f b m + f b m') ∧
      (∀ (r : R) (b : B) (m : M), f (MulOpposite.op r • b) m = f b (r • m)) }
  let Universal := fun (T : AddCommGrpCat.{max v w t}) (p : Bal T) =>
    ∀ (A : AddCommGrpCat.{max v w t}),
      ∃ e : Equiv (AddMonoidHom T A) (Bal A),
        ∀ (h : AddMonoidHom T A) (b : B) (m : M), (e h).val b m = h (p.val b m)
  ∃ (T : AddCommGrpCat.{max v w t}) (p : Bal T),
    Universal T p ∧
    (∀ x : T, ∃ pairs : List (Prod B M),
      List.sum (List.map (fun bm => p.val bm.1 bm.2) pairs) = x) ∧
    (∀ (T' : AddCommGrpCat.{max v w t}) (p' : Bal T'), Universal T' p' →
      ∃! e : AddEquiv T T', ∀ (b : B) (m : M), e (p.val b m) = p'.val b m)) :=
(by
  intro R _ B _ _ M _ _ Bal Universal
  -- Alphabeta Math, steps 1.1–6.1:
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  -- Step 1.1 works directly with additive homomorphisms. The right action
  -- from Definition 6.1 is the given opposite-ring module action.
  -- For steps 2.1–4.1 we use the coordinator's checked ChoiceFreeWatts
  -- quotient of a free additive group. Its relation includes commutativity
  -- as well as the two additivity laws and balance. The planned free-module
  -- and linear-quotient theorems describe the notes' integer-module model.
  -- The separate Finsupp model in ModuleTensorUniversalProperty would need a
  -- pure-preserving comparison. Mathlib's TensorProduct.liftAddHom requires
  -- a commutative base semiring; the quotient here works for the given Ring R.
  -- ULift puts the carrier in the common universe of the reviewed statement.
  let right : R → B → B := fun r b => MulOpposite.op r • b
  let V := ChoiceFreeWatts.Tensor right M
  let inst : AddCommGroup V := ChoiceFreeWatts.tensorAddCommGroup right
  let T := AddCommGrpCat.of (ULift.{t} V)
  let lift : V ≃+ T := AddEquiv.ulift.symm
  let pure : Bal T :=
    ⟨fun b m => lift (ChoiceFreeWatts.pure right b m),
     fun b b' m => (congrArg lift ((ChoiceFreeWatts.pureBalanced (X := M) right).1 b b' m)).trans
       (map_add lift _ _),
     fun b m m' => (congrArg lift ((ChoiceFreeWatts.pureBalanced (X := M) right).2.1 b m m')).trans
       (map_add lift _ _),
     fun r b m => congrArg lift ((ChoiceFreeWatts.pureBalanced (X := M) right).2.2 r b m)⟩
  have universal : Universal T pure := by
    intro A
    -- Step 1.2: restricting an additive map preserves all three laws.
    let restrict (h : AddMonoidHom T A) : Bal A :=
      ⟨fun b m => h (pure.val b m),
       fun b b' m => (congrArg h (pure.property.1 b b' m)).trans (map_add h _ _),
       fun b m m' => (congrArg h (pure.property.2.1 b m m')).trans (map_add h _ _),
       fun r b m => congrArg h (pure.property.2.2 r b m)⟩
    -- Steps 2.1–4.1: tensorLift extends the map on pairs and descends
    -- through the relations. Its input is exactly f.property, and
    -- commutativity in A takes care of the commutation relations.
    let extend (f : Bal A) : AddMonoidHom T A :=
      (ChoiceFreeWatts.tensorLift right f.val f.property).comp lift.symm.toAddMonoidHom
    have extend_pure (f : Bal A) (b : B) (m : M) :
        extend f (pure.val b m) = f.val b m := by
      change (ChoiceFreeWatts.tensorLift right f.val f.property)
        (lift.symm (lift (ChoiceFreeWatts.pure right b m))) = f.val b m
      rw [lift.symm_apply_apply]
      exact ChoiceFreeWatts.tensorLift_pure right f.val f.property b m
    -- Step 5.1: the lift has the required values. The supplier's
    -- extensionality applies to the composites on the unlifted quotient.
    refine ⟨⟨restrict, extend, ?_, ?_⟩, fun _ _ _ => rfl⟩
    · intro h
      have hcomp := ChoiceFreeWatts.tensorExt right
        ((extend (restrict h)).comp lift.toAddMonoidHom) (h.comp lift.toAddMonoidHom)
        (extend_pure (restrict h))
      apply AddMonoidHom.ext
      intro x
      obtain ⟨z, rfl⟩ := lift.surjective x
      exact DFunLike.congr_fun hcomp z
    · intro f
      exact Subtype.ext (funext fun b => funext fun m => extend_pure f b m)
  -- Step 6.1: the relations apply to all pairs, including when a factor
  -- is zero or the ring is the zero ring.
  refine ⟨T, pure, universal, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := lift.surjective x
    exact tensorFiniteSum lift.toAddMonoidHom z
  · -- Theorem 6.2 also asks for uniqueness of the representing group.
    -- Use both given precomposition equivalences to get maps in both
    -- directions. Their composites are identities by injectivity of
    -- precomposition, which also gives uniqueness of the isomorphism.
    intro T' pure' universal'
    have homExt (A : AddCommGrpCat.{max v w t}) (f g : AddMonoidHom T A)
        (h : ∀ b m, f (pure.val b m) = g (pure.val b m)) : f = g := by
      obtain ⟨e, he⟩ := universal A
      exact e.injective (Subtype.ext (funext fun b => funext fun m =>
        (he f b m).trans ((h b m).trans (he g b m).symm)))
    have homExt' (A : AddCommGrpCat.{max v w t}) (f g : AddMonoidHom T' A)
        (h : ∀ b m, f (pure'.val b m) = g (pure'.val b m)) : f = g := by
      obtain ⟨e, he⟩ := universal' A
      exact e.injective (Subtype.ext (funext fun b => funext fun m =>
        (he f b m).trans ((h b m).trans (he g b m).symm)))
    obtain ⟨e, he⟩ := universal T'
    obtain ⟨e', he'⟩ := universal' T
    let f := e.symm pure'
    let g := e'.symm pure
    have hf (b : B) (m : M) : f (pure.val b m) = pure'.val b m := by
      rw [← he, Equiv.apply_symm_apply]
    have hg (b : B) (m : M) : g (pure'.val b m) = pure.val b m := by
      rw [← he', Equiv.apply_symm_apply]
    have hgf : g.comp f = AddMonoidHom.id T := homExt _ _ _ fun b m => by
      rw [AddMonoidHom.comp_apply, hf, hg, AddMonoidHom.id_apply]
    have hfg : f.comp g = AddMonoidHom.id T' := homExt' _ _ _ fun b m => by
      rw [AddMonoidHom.comp_apply, hg, hf, AddMonoidHom.id_apply]
    let iso : T ≃+ T' :=
      { f with
        invFun := g
        left_inv := DFunLike.congr_fun hgf
        right_inv := DFunLike.congr_fun hfg }
    refine ⟨iso, hf, ?_⟩
    intro j hj
    have h := homExt T' j.toAddMonoidHom f (fun b m => (hj b m).trans (hf b m).symm)
    exact AddEquiv.ext (fun x => congrArg (fun k : AddMonoidHom T T' => k x) h))

#check ChoiceFreeWatts.pureBalanced
#check ChoiceFreeWatts.tensorLift
#check ChoiceFreeWatts.tensorLift_pure
#check ChoiceFreeWatts.tensorExt
#print axioms BalancedTensorUniversalProperty
