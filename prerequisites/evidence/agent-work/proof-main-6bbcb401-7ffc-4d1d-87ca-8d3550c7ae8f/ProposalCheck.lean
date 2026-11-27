import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BimoduleTensorFunctoriality
import NotesProofs.ModuleKernelsCokernelsAndImages
import NotesProofs.ModuleCategoriesAreAbelian
import NotesProofs.ExactPresentationsAreCokernels

set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits
universe r s v w t

theorem TensorPreservesCokernels : (∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
  let Bimod := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
  let star := CategoryTheory.SingleObj.star (MulOpposite R)
  ∀ (B : Bimod),
    let carrier := B.obj.obj star
    let right := fun (a : R) (b : carrier) =>
      (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
    let Balanced := fun (M : ModuleCat.{w} R)
        (A : Type (max v w t)) [AddCommGroup A] (p : carrier → M → A) =>
      (∀ (b b' : carrier) (m : M), p (b + b') m = p b m + p b' m) ∧
      (∀ (b : carrier) (m m' : M), p b (m + m') = p b m + p b m') ∧
      (∀ (a : R) (b : carrier) (m : M), p (right a b) m = p b (a • m))
    ∀ (T : CategoryTheory.Functor (ModuleCat.{w} R) (ModuleCat.{max v w t} S))
      [CategoryTheory.Functor.Additive T]
      (pure : ∀ M : ModuleCat.{w} R, carrier → M → T.obj M),
      (∀ M : ModuleCat.{w} R,
        Balanced M (T.obj M : Type (max v w t)) (pure M) ∧
        (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier → M → A),
          Balanced M A p →
          ∃! h : AddMonoidHom (T.obj M) A, ∀ b m, h (pure M b m) = p b m) ∧
        (∀ (a : S) (b : carrier) (m : M), a • pure M b m = pure M (a • b) m)) →
      (∀ {M N : ModuleCat.{w} R} (f : Quiver.Hom M N) (b : carrier) (m : M),
        (T.map f) (pure M b m) = pure N b (f m)) →
      (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
        CategoryTheory.ShortComplex.Exact C → CategoryTheory.Epi C.g →
        CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map C T) ∧
          CategoryTheory.Epi (T.map C.g)) ∧
      (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ C.g C.zero)) →
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ
            (CategoryTheory.ShortComplex.map C T).g (CategoryTheory.ShortComplex.map C T).zero)))) :=
(by
  classical
  intro R _ S _ Bimod star B carrier right Balanced T _ pure properties mapPure
  -- Alphabeta Math, steps 1.4–1.5. Uniqueness in the balanced universal
  -- property gives pure-tensor extensionality for the abstract T. Proposition
  -- 6.3 (BimoduleTensorFunctoriality) supplies the construction of a bifunctor.
  -- Its fixed-bimodule laws are hypotheses of this theorem.
  -- NotesProofs.balanced_tensor_preserves_cokernel groups both rings in one
  -- universe and all carriers in another, and assumes S-linear lifts.
  -- The descent here uses the reviewed T and leaves the universes independent.
  have addExt (M : ModuleCat.{w} R) (D : AddCommGrpCat.{max v w t})
      (f g : AddMonoidHom (T.obj M) D)
      (h : ∀ b m, f (pure M b m) = g (pure M b m)) : f = g := by
    let pairing : carrier → M → D := fun b m => g (pure M b m)
    have hb : Balanced M D pairing := by
      refine ⟨?_, ?_, ?_⟩
      · intro b b' m
        dsimp [pairing]
        rw [(properties M).1.1, map_add]
      · intro b m m'
        dsimp [pairing]
        rw [(properties M).1.2.1, map_add]
      · intro a b m
        dsimp [pairing]
        rw [(properties M).1.2.2]
    obtain ⟨k, _, unique⟩ := (properties M).2.1 D pairing hb
    exact (unique f h).trans (unique g (fun _ _ => rfl)).symm
  have homExt (M : ModuleCat.{w} R) (D : ModuleCat.{max v w t} S)
      (f g : T.obj M ⟶ D)
      (h : ∀ b m, f (pure M b m) = g (pure M b m)) : f = g := by
    have eq := addExt M (AddCommGrpCat.of D) f.hom.toAddMonoidHom g.hom.toAddMonoidHom h
    exact ModuleCat.hom_ext (LinearMap.ext fun x => DFunLike.congr_fun eq x)
  -- Step 2.1: the outer action formula holds for pure tensors by hypothesis.
  -- Compare two additive maps for each scalar to get linearity on every tensor.
  have lift (M : ModuleCat.{w} R) (D : ModuleCat.{max v w t} S)
      (p : carrier → M → D) (hp : Balanced M D p)
      (outer : ∀ (a : S) b m, p (a • b) m = a • p b m) :
      ∃ k : T.obj M ⟶ D, ∀ b m, k (pure M b m) = p b m := by
    obtain ⟨k, hk, _⟩ := (properties M).2.1 (AddCommGrpCat.of D) p hp
    have linear (a : S) (x : T.obj M) : k (a • x) = a • k x := by
      let scale (A : ModuleCat.{max v w t} S) : A →+ A :=
        { toFun := fun y => a • y
          map_zero' := smul_zero a
          map_add' := smul_add a }
      have he := addExt M (AddCommGrpCat.of D) (k.comp (scale (T.obj M)))
        ((scale D).comp k) (by
          intro b m
          change k (a • pure M b m) = a • k (pure M b m)
          rw [(properties M).2.2, hk, hk, outer])
      exact DFunLike.congr_fun he x
    let kLinear : T.obj M →ₗ[S] D :=
      { k with
        map_smul' := linear }
    exact ⟨ModuleCat.ofHom kLinear, hk⟩
  have preserve (C : ShortComplex (ModuleCat.{w} R))
      (exactC : C.Exact) (epiC : Epi C.g) :
      Nonempty (IsColimit (CokernelCofork.ofπ (C.map T).g (C.map T).zero)) := by
    -- Steps 1.4–1.5, F6 and F7: obtain actual lifts, including lifts of the
    -- differences of two representatives, from the two exactness hypotheses.
    have surj : Function.Surjective C.g :=
      (ModuleKernelsCokernelsAndImages R C.g).2.2.2.2.2.2.mp epiC
    have preimage (n : C.X₂) (hn : C.g n = 0) : ∃ m : C.X₁, C.f m = n := by
      have hrange : LinearMap.range C.f.hom = LinearMap.ker C.g.hom :=
        (ShortComplex.moduleCat_exact_iff_range_eq_ker C).mp exactC
      have hker := ((ModuleKernelsCokernelsAndImages R C.g).1 n).mpr hn
      exact ((ModuleKernelsCokernelsAndImages R C.f).2.1 n).mp (hrange.symm ▸ hker)
    -- Step 1.4: ShortComplex.map gives the zero composite because T is
    -- additive. Step 1.5 applies the notes' representative argument to each
    -- S-linear test map to obtain the universal property directly
    -- (Theorem 6.7, pp. 20–21).
    have factor (D : ModuleCat.{max v w t} S) (h : T.obj C.X₂ ⟶ D)
        (hh : T.map C.f ≫ h = 0) :
        ∃ k : T.obj C.X₃ ⟶ D, T.map C.g ≫ k = h := by
      have independent (b : carrier) (n n' : C.X₂) (eq : C.g n = C.g n') :
          h (pure C.X₂ b n) = h (pure C.X₂ b n') := by
        obtain ⟨m, hm⟩ := preimage (n - n') (by rw [map_sub, eq, sub_self])
        have vanish : h (pure C.X₂ b (n - n')) = 0 := by
          rw [← hm, ← mapPure C.f]
          exact ConcreteCategory.congr_hom hh (pure C.X₁ b m)
        calc
          h (pure C.X₂ b n) = h (pure C.X₂ b (n - n' + n')) := by rw [sub_add_cancel]
          _ = h (pure C.X₂ b n') := by
            rw [(properties C.X₂).1.2.1, map_add, vanish, zero_add]
      -- The notes permit ordinary choice. Both this representative and the
      -- colimit desc below use Classical.choice. The portal's steps 1.5
      -- and 3.1 rely on independence of the representative to obtain a
      -- uniquely defined value. The present article formalization chooses a
      -- representative from the given surjection and proves that independence.
      let p : carrier → C.X₃ → D := fun b x => h (pure C.X₂ b (surj x).choose)
      have p_apply (b : carrier) (n : C.X₂) : p b (C.g n) = h (pure C.X₂ b n) :=
        independent b _ _ (surj (C.g n)).choose_spec
      have bp : Balanced C.X₃ D p := by
        refine ⟨?_, ?_, ?_⟩
        · intro b b' x
          obtain ⟨n, rfl⟩ := surj x
          simp only [p_apply, (properties C.X₂).1.1, map_add]
        · intro b x x'
          obtain ⟨n, rfl⟩ := surj x
          obtain ⟨n', rfl⟩ := surj x'
          have qadd : C.g (n + n') = C.g n + C.g n' := C.g.hom.map_add n n'
          rw [← qadd, p_apply, p_apply, p_apply, (properties C.X₂).1.2.1, map_add]
        · intro a b x
          obtain ⟨n, rfl⟩ := surj x
          have qsmul : C.g (a • n) = a • C.g n := map_smul C.g.hom a n
          rw [← qsmul, p_apply, p_apply, (properties C.X₂).1.2.2]
      have outer (a : S) (b : carrier) (x : C.X₃) : p (a • b) x = a • p b x := by
        obtain ⟨n, rfl⟩ := surj x
        rw [p_apply, p_apply, ← (properties C.X₂).2.2, map_smul]
      obtain ⟨k, hk⟩ := lift C.X₃ D p bp outer
      refine ⟨k, homExt C.X₂ D _ _ ?_⟩
      intro b n
      change k ((T.map C.g) (pure C.X₂ b n)) = h (pure C.X₂ b n)
      rw [mapPure C.g, hk, p_apply]
    refine ⟨CokernelCofork.IsColimit.ofπ (T.map C.g) (C.map T).zero
      (fun {_} h hh => (factor _ h hh).choose)
      (fun {_} h hh => (factor _ h hh).choose_spec) ?_⟩
    intro D h hh k hk
    apply homExt C.X₃ D
    intro b x
    obtain ⟨n, rfl⟩ := surj x
    rw [← mapPure C.g]
    exact (ConcreteCategory.congr_hom hk (pure C.X₂ b n)).trans
      (ConcreteCategory.congr_hom (factor D h hh).choose_spec (pure C.X₂ b n)).symm
  -- Steps 1.4 and 3.1: the target cokernel gives both the kernel-image equality
  -- and epimorphy by Proposition 4.9 (ExactPresentationsAreCokernels). The
  -- same equivalence handles any input cokernel cofork. The zero-composite
  -- witnesses agree by proof irrelevance.
  -- Use the canonical ModuleCat abelian instance underlying
  -- ModuleCategoriesAreAbelian, so the existing zero-morphism instances match.
  constructor
  · intro C hexact hepi
    obtain ⟨_, h⟩ := (ExactPresentationsAreCokernels (T.map C.f) (T.map C.g)).mpr
      ⟨(C.map T).zero, preserve C hexact hepi⟩
    exact h
  · intro C hcokernel
    obtain ⟨_, hexact, hepi⟩ := (ExactPresentationsAreCokernels C.f C.g).mpr
      ⟨C.zero, hcokernel⟩
    exact preserve C hexact hepi)

#print axioms TensorPreservesCokernels
